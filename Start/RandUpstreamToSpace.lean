import Start.SpaceRandomizedRuns
import Start.LogspaceToSpaceCompile

/-!
# Upstream probabilistic machines into fair-coin host machines: the machine

This library's own module (task `M27-HOST-RANDOMIZED-SPACE`, direction upstream to host).  For a
machine `M` of `Start/LogspaceDeterministic.lean` and a window constant `c₀`, the fair-coin host
machine `RandFromLogspace.rcompile M c₀` extends the deterministic compiler `FromLogspace.compile`
(`Start/LogspaceToSpaceCompile.lean`) with one fair branching per simulated upstream step.  It is
the tape program

  `initProg M c₀; mvR 3;`
  `while (result register empty) {`
  `  mvL 2; if (running flag) {`
  `    mvR 2; flip; if (coin) { write false; mvL 3; stepProg (M with coin true); mvR 3 }`
  `                 else { write false; mvL 3; stepProg (M with coin false); mvR 3 } }`
  `  else halt }`

compiled by `Complexity.Space.Prog.delta`, where `flip` is the only state with two instructions —
write `false` or write `true` on the presence cell of the (empty) result register, each taken
with probability `1/2` — and `halt` is a halting, non-accepting state.  The loop exits to the
accepting final state when the simulated machine has output `true`, and reaches `halt` when it has
output `false`, so the host halts on every run.

* `RandFromLogspace.fixCoin M b` — `M` with its coin fixed to `b`;
* `RandFromLogspace.mainProg`, `RandFromLogspace.rcompile` — the program and the machine;
* `RandFromLogspace.rcompile_wellFormed`, `RandFromLogspace.rcompile_fairCoin`.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace RandFromLogspace

open Tracks Prog FromLogspace
open ExactDerandomization (Word InputSymbol Direction Configuration readInput CoinTape)

variable {q w h : ℕ} (M : ExactDerandomization.Machine q w h)

/-- `M` with its coin fixed to `b`. -/
def fixCoin (b : Bool) : ExactDerandomization.Machine q w h where
  initialState := M.initialState
  output := M.output
  transition := fun s i v _ => M.transition s i v b

theorem fixCoin_step (b b' : Bool) {x : Word} (c : Configuration q w h x.length) :
    (fixCoin M b).step x b' c = M.step x b c := rfl

theorem encC_fixCoin (b : Bool) (W : ℤ) {n : ℕ} (c : Configuration q w h n) :
    encC (fixCoin M b) W c = encC M W c := rfl

/-- One simulated step with coin `b`, from and to the head position `3`. -/
def bodyB (b : Bool) : Prog := .seq (mvL 3) (.seq (stepProg (fixCoin M b)) (mvR 3))

/-- The coin branch: `flip` writes the coin on the current cell; the test reads it back. -/
def coinTest : Prog :=
  .ite (fun _ w => w) (.seq (write false) (bodyB M true)) (.seq (write false) (bodyB M false))

/-- The `flip` state followed by the coin branch. -/
def coinPart : Prog := .seq (write false) (coinTest M)

/-- The running-flag test: `skip` in the `else` branch is the halting state. -/
def flagTest : Prog := .ite (fun _ w => w) (.seq (mvR 2) (coinPart M)) skip

/-- The loop body. -/
def iterProg : Prog := .seq (mvL 2) (flagTest M)

/-- Initialization, ending with the head on the result register. -/
def initPart (c₀ : ℕ) : Prog := .seq (initProg M c₀) (mvR 3)

/-- The whole program. -/
def mainProg (c₀ : ℕ) : Prog := .seq (initPart M c₀) (.loop runTest (iterProg M))

/-! ### The layout -/

/-- The loop test. -/
def stL (c₀ : ℕ) : ℕ := (initPart M c₀).size
/-- The running-flag test. -/
def stF (c₀ : ℕ) : ℕ := stL M c₀ + 1 + (mvL 2).size
/-- The `flip` state. -/
def stFlip (c₀ : ℕ) : ℕ := stF M c₀ + 1 + (mvR 2).size
/-- The halting state. -/
def stHalt (c₀ : ℕ) : ℕ := stF M c₀ + 1 + (Prog.seq (mvR 2) (coinPart M)).size
/-- The accepting final state. -/
def stAcc (c₀ : ℕ) : ℕ := (mainProg M c₀).size

theorem stHalt_eq (c₀ : ℕ) : stHalt M c₀ = stFlip M c₀ + 1 + (coinTest M).size := by
  simp only [stHalt, stFlip, size, coinPart, write]; omega

theorem mainProg_size (c₀ : ℕ) :
    (mainProg M c₀).size = stHalt M c₀ + 1 := by
  simp only [mainProg, stHalt, stF, stL, iterProg, flagTest, size, skip]; omega

/-- **The fair-coin host machine.** -/
def rcompile (c₀ : ℕ) : Machine where
  states := (mainProg M c₀).size + 1
  accept s := decide (s = (mainProg M c₀).size)
  delta s a v :=
    if s = stFlip M c₀ then [(stFlip M c₀ + 1, false, .stay, .stay), (stFlip M c₀ + 1, true, .stay, .stay)]
    else if s = stHalt M c₀ then []
    else (mainProg M c₀).machine.delta s a v

variable (c₀ : ℕ)

theorem rcompile_delta_of_ne {s : ℕ} (h1 : s ≠ stFlip M c₀) (h2 : s ≠ stHalt M c₀)
    (a : Option Bool) (v : Bool) :
    (rcompile M c₀).delta s a v = (mainProg M c₀).machine.delta s a v := by
  simp only [rcompile, if_neg h1, if_neg h2]

theorem rcompile_wellFormed : (rcompile M c₀).WellFormed := by
  refine ⟨Nat.succ_pos _, ?_⟩
  intro s a v i hi
  simp only [rcompile] at hi ⊢
  have hfl : stFlip M c₀ + 1 < (mainProg M c₀).size + 1 := by
    rw [mainProg_size, stHalt_eq]; have := size_pos (coinTest M); omega
  split at hi
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact hfl
  · split at hi
    · simp at hi
    · exact (machine_wellFormed _).2 s a v i hi

theorem rcompile_fairCoin : (rcompile M c₀).FairCoin := by
  intro s a v
  simp only [rcompile]
  split
  · simp
  · split
    · simp
    · exact le_trans (machine_deterministic _ s a v) (by omega)

theorem rcompile_length_le {s : ℕ} (h1 : s ≠ stFlip M c₀) (a : Option Bool) (v : Bool) :
    ((rcompile M c₀).delta s a v).length ≤ 1 := by
  simp only [rcompile, if_neg h1]
  split
  · simp
  · exact machine_deterministic _ s a v

theorem rcompile_accept (s : ℕ) : (rcompile M c₀).accept s = decide (s = stAcc M c₀) := rfl

/-! ### Hosting the sub-programs -/

theorem hosts_agree {M₁ M₂ : Machine} {p : Prog} {b e : ℕ} (h : Hosts M₁ p b e)
    (hag : ∀ s, b ≤ s → s < b + p.size → ∀ a v, M₂.delta s a v = M₁.delta s a v) :
    Hosts M₂ p b e := fun s h1 h2 a v => (hag s h1 h2 a v).trans (h s h1 h2 a v)

theorem hosts_main : Hosts (mainProg M c₀).machine (mainProg M c₀) 0 (mainProg M c₀).size :=
  machine_hosts _

theorem hosts_loop : Hosts (mainProg M c₀).machine (.loop runTest (iterProg M)) (stL M c₀)
    (stAcc M c₀) := by
  have := (hosts_main M c₀).seq_right
  simpa [stL, stAcc] using this

theorem hosts_initPart : Hosts (mainProg M c₀).machine (initPart M c₀) 0 (stL M c₀) := by
  have := (hosts_main M c₀).seq_left
  simpa [stL] using this

theorem hosts_iter : Hosts (mainProg M c₀).machine (iterProg M) (stL M c₀ + 1) (stL M c₀) :=
  (hosts_loop M c₀).loop_body

theorem hosts_mvL2 : Hosts (mainProg M c₀).machine (mvL 2) (stL M c₀ + 1) (stF M c₀) :=
  (hosts_iter M c₀).seq_left

theorem hosts_flagTest : Hosts (mainProg M c₀).machine (flagTest M) (stF M c₀) (stL M c₀) :=
  (hosts_iter M c₀).seq_right

theorem hosts_thenF : Hosts (mainProg M c₀).machine (.seq (mvR 2) (coinPart M)) (stF M c₀ + 1)
    (stL M c₀) :=
  (hosts_flagTest M c₀).ite_left

theorem hosts_mvR2 : Hosts (mainProg M c₀).machine (mvR 2) (stF M c₀ + 1) (stFlip M c₀) :=
  (hosts_thenF M c₀).seq_left

theorem hosts_coinPart : Hosts (mainProg M c₀).machine (coinPart M) (stFlip M c₀) (stL M c₀) :=
  (hosts_thenF M c₀).seq_right

theorem hosts_coinTest : Hosts (mainProg M c₀).machine (coinTest M) (stFlip M c₀ + 1)
    (stL M c₀) := by
  have := (hosts_coinPart M c₀).seq_right
  simpa [write, size] using this

theorem stFlip_lt_stHalt : stFlip M c₀ < stHalt M c₀ := by
  rw [stHalt_eq]; omega

/-- The machine agrees with the compiled table away from `flip` and `halt`. -/
theorem hosts_r {p : Prog} {b e : ℕ} (h : Hosts (mainProg M c₀).machine p b e)
    (hlo : stHalt M c₀ < b ∨ b + p.size ≤ stFlip M c₀ ∨
      (stFlip M c₀ < b ∧ b + p.size ≤ stHalt M c₀)) :
    Hosts (rcompile M c₀) p b e :=
  hosts_agree h fun s h1 h2 a v => by
    have := stFlip_lt_stHalt M c₀
    exact rcompile_delta_of_ne M c₀ (by omega) (by omega) a v

theorem rhosts_initPart : Hosts (rcompile M c₀) (initPart M c₀) 0 (stL M c₀) :=
  hosts_r M c₀ (hosts_initPart M c₀) (Or.inr (Or.inl (by simp only [stFlip, stF, stL]; omega)))

theorem rhosts_mvL2 : Hosts (rcompile M c₀) (mvL 2) (stL M c₀ + 1) (stF M c₀) :=
  hosts_r M c₀ (hosts_mvL2 M c₀) (Or.inr (Or.inl (by simp only [stFlip, stF]; omega)))

theorem rhosts_mvR2 : Hosts (rcompile M c₀) (mvR 2) (stF M c₀ + 1) (stFlip M c₀) :=
  hosts_r M c₀ (hosts_mvR2 M c₀) (Or.inr (Or.inl (by simp only [stFlip]; omega)))

theorem rhosts_coinTest : Hosts (rcompile M c₀) (coinTest M) (stFlip M c₀ + 1) (stL M c₀) :=
  hosts_r M c₀ (hosts_coinTest M c₀)
    (Or.inr (Or.inr ⟨by omega, by rw [stHalt_eq]⟩))

/-! ### The custom states -/

theorem stL_ne_flip : stL M c₀ ≠ stFlip M c₀ := by simp only [stFlip, stF]; omega
theorem stL_ne_halt : stL M c₀ ≠ stHalt M c₀ := by
  have := stFlip_lt_stHalt M c₀; simp only [stFlip, stF] at this; omega
theorem stF_ne_flip : stF M c₀ ≠ stFlip M c₀ := by simp only [stFlip]; omega
theorem stF_ne_halt : stF M c₀ ≠ stHalt M c₀ := by
  have := stFlip_lt_stHalt M c₀; simp only [stFlip] at this; omega
theorem stHalt_ne_flip : stHalt M c₀ ≠ stFlip M c₀ := (stFlip_lt_stHalt M c₀).ne'
theorem stAcc_ne_flip : stAcc M c₀ ≠ stFlip M c₀ := by
  have := stFlip_lt_stHalt M c₀; rw [stAcc, mainProg_size]; omega
theorem stAcc_ne_halt : stAcc M c₀ ≠ stHalt M c₀ := by rw [stAcc, mainProg_size]; omega

theorem delta_stL (a : Option Bool) (v : Bool) :
    (rcompile M c₀).delta (stL M c₀) a v =
      [(if runTest a v then stL M c₀ + 1 else stAcc M c₀, v, .stay, .stay)] := by
  rw [rcompile_delta_of_ne M c₀ (stL_ne_flip M c₀) (stL_ne_halt M c₀)]
  exact (hosts_loop M c₀).loop_test a v

theorem delta_stF (a : Option Bool) (v : Bool) :
    (rcompile M c₀).delta (stF M c₀) a v =
      [(if v then stF M c₀ + 1 else stHalt M c₀, v, .stay, .stay)] := by
  rw [rcompile_delta_of_ne M c₀ (stF_ne_flip M c₀) (stF_ne_halt M c₀)]
  exact (hosts_flagTest M c₀).test a v

theorem delta_stFlip (a : Option Bool) (v : Bool) :
    (rcompile M c₀).delta (stFlip M c₀) a v =
      [(stFlip M c₀ + 1, false, .stay, .stay), (stFlip M c₀ + 1, true, .stay, .stay)] := by
  simp [rcompile]

theorem delta_stHalt (a : Option Bool) (v : Bool) :
    (rcompile M c₀).delta (stHalt M c₀) a v = [] := by
  simp [rcompile, stHalt_ne_flip]

theorem delta_stAcc (a : Option Bool) (v : Bool) :
    (rcompile M c₀).delta (stAcc M c₀) a v = [] := by
  rw [rcompile_delta_of_ne M c₀ (stAcc_ne_flip M c₀) (stAcc_ne_halt M c₀)]
  simp [Prog.machine, stAcc]

end RandFromLogspace

end Complexity.Space
