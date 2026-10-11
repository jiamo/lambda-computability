import Start.RandUpstreamToSpace

/-!
# Upstream probabilistic machines into fair-coin host machines: the segments of one iteration

This library's own module (task `M27-HOST-RANDOMIZED-SPACE`).  For the host machine
`RandFromLogspace.rcompile M c₀` of `Start/RandUpstreamToSpace.lean`, the pieces of one loop
iteration as runs of the host machine, on the register file `FromLogspace.encTS M c₀ x c` of a
simulated configuration `c`:

* `RandFromLogspace.path_det` — an execution of a hosted sub-program avoiding `flip` and the final
  state is a deterministic run segment (`Machine.DetOK`);
* `RandFromLogspace.runs_initPart` — initialization, from the blank tape;
* `RandFromLogspace.runs_coinTest` — after the coin `b` is written, the coin branch simulates one
  step of `M` with coin `b`;
* `RandFromLogspace.view_res`, `RandFromLogspace.view_run` — the two cells the loop inspects.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace RandFromLogspace

open Tracks Prog FromLogspace
open ExactDerandomization (Word InputSymbol Direction Configuration readInput CoinTape)

variable {q w h : ℕ} (M : ExactDerandomization.Machine q w h) (c₀ : ℕ) {x : Word}

/-! ### Single steps -/

theorem stepList_of_delta {N : Machine} {c : Config} {i : ℕ × Bool × Dir × Dir}
    (hd : N.delta c.state (rdIn x c) (rdW c) = [i]) :
    N.stepList x c = [(eff x c (i.2.1, i.2.2.1, i.2.2.2)).at i.1] := by
  unfold Machine.stepList
  unfold rdIn rdW at hd
  rw [hd]
  rfl

theorem stepList_of_delta_pair {N : Machine} {c : Config} {i j : ℕ × Bool × Dir × Dir}
    (hd : N.delta c.state (rdIn x c) (rdW c) = [i, j]) :
    N.stepList x c = [(eff x c (i.2.1, i.2.2.1, i.2.2.2)).at i.1,
      (eff x c (j.2.1, j.2.2.1, j.2.2.2)).at j.1] := by
  unfold Machine.stepList
  unfold rdIn rdW at hd
  rw [hd]
  rfl

theorem stepList_of_delta_nil {N : Machine} {c : Config}
    (hd : N.delta c.state (rdIn x c) (rdW c) = []) : N.stepList x c = [] := by
  unfold Machine.stepList
  unfold rdIn rdW at hd
  rw [hd]
  rfl

theorem eff_touch (c : Config) : eff x c (rdW c, .stay, .stay) = touch x c := rfl

theorem rdW_eq_view (c : Config) : rdW c = c.abs.view c.abs.head := rfl

/-! ### Deterministic segments -/

/-- The side condition of the simulation: at most `spaceB` cells. -/
abbrev SpOK (x : Word) (c : Config) : Prop := c.space ≤ spaceB q w h c₀ x.length

theorem detOK_of_range {d : Config} (hsp : d.space ≤ spaceB q w h c₀ x.length)
    (h1 : d.state ≠ stFlip M c₀) (h2 : d.state ≠ stAcc M c₀) :
    (rcompile M c₀).DetOK x (SpOK (q := q) (w := w) (h := h) c₀ x) d := by
  refine ⟨?_, ?_, hsp⟩
  · unfold Machine.stepList
    rw [List.length_map]
    exact rcompile_length_le M c₀ h1 _ _
  · rw [rcompile_accept]; simpa using h2

/-- **An execution of a hosted sub-program is a deterministic run segment**, when the program's
states avoid `flip` and the final state. -/
theorem path_det {p : Prog} {b e : ℕ} (hH : Hosts (rcompile M c₀) p b e)
    (hr : ∀ s, b ≤ s → s < b + p.size → s ≠ stFlip M c₀ ∧ s ≠ stAcc M c₀)
    {c c' : Config} (hex : Exec x (SpOK (q := q) (w := w) (h := h) c₀ x) p c c')
    (hc : c.state = 0) :
    (rcompile M c₀).Path x ((rcompile M c₀).DetOK x (SpOK (q := q) (w := w) (h := h) c₀ x))
      (c.at b) (c'.at e) := by
  refine (path_of_exec hex hc hH).mono fun d hd => ?_
  obtain ⟨hsp, h1, h2⟩ := hd
  obtain ⟨hf, ha⟩ := hr d.state h1 h2
  exact detOK_of_range M c₀ hsp hf ha

/-- A `Runs` specification of a hosted sub-program gives a deterministic run segment. -/
theorem path_of_runs {p : Prog} {b e : ℕ} (hH : Hosts (rcompile M c₀) p b e)
    (hr : ∀ s, b ≤ s → s < b + p.size → s ≠ stFlip M c₀ ∧ s ≠ stAcc M c₀)
    {s s' : TState} (hR : Runs x (spaceB q w h c₀ x.length) p s s') {c : Config}
    (hcs : c.abs = s) (hcB : c.space ≤ spaceB q w h c₀ x.length) :
    ∃ d : Config, d.abs = s' ∧ d.space ≤ spaceB q w h c₀ x.length ∧ d.state = 0 ∧
      (rcompile M c₀).Path x ((rcompile M c₀).DetOK x (SpOK (q := q) (w := w) (h := h) c₀ x))
        (c.at b) (d.at e) := by
  obtain ⟨d, hd, hds, hdB⟩ := hR (c.at 0) hcs hcB
  refine ⟨d, hds, hdB, exec_state hd, ?_⟩
  have := path_det M c₀ hH hr hd rfl
  simpa using this

/-! ### Ranges -/

theorem range_initPart : ∀ s, 0 ≤ s → s < 0 + (initPart M c₀).size →
    s ≠ stFlip M c₀ ∧ s ≠ stAcc M c₀ := by
  intro s _ h2
  have := stFlip_lt_stHalt M c₀
  have h3 := mainProg_size M c₀
  simp only [stFlip, stF, stL, stAcc] at this h3 ⊢
  omega

theorem range_mvL2 : ∀ s, stL M c₀ + 1 ≤ s → s < stL M c₀ + 1 + (mvL 2).size →
    s ≠ stFlip M c₀ ∧ s ≠ stAcc M c₀ := by
  intro s _ h2
  have := stFlip_lt_stHalt M c₀
  have h3 := mainProg_size M c₀
  simp only [stFlip, stF, stAcc] at this h3 ⊢
  omega

theorem range_mvR2 : ∀ s, stF M c₀ + 1 ≤ s → s < stF M c₀ + 1 + (mvR 2).size →
    s ≠ stFlip M c₀ ∧ s ≠ stAcc M c₀ := by
  intro s _ h2
  have := stFlip_lt_stHalt M c₀
  have h3 := mainProg_size M c₀
  simp only [stFlip, stAcc] at this h3 ⊢
  omega

theorem range_coinTest : ∀ s, stFlip M c₀ + 1 ≤ s → s < stFlip M c₀ + 1 + (coinTest M).size →
    s ≠ stFlip M c₀ ∧ s ≠ stAcc M c₀ := by
  intro s h1 h2
  have := stHalt_eq M c₀
  have h3 := mainProg_size M c₀
  simp only [stAcc] at h3 ⊢
  omega

/-! ### The inspected cells -/

theorem regK_gt_one : 1 < regK h w := by unfold regK; omega

theorem view_res {n : ℕ} (c : Configuration q w h n) :
    lay (regK h w) (encC M (winR c₀ n : ℤ) c) 3 = decide (M.output c.state = some true) := by
  have := lay_pres (K := regK h w) (encC M (winR c₀ n : ℤ) c) 1 regK_gt_one 0
  simp only [zero_mul, zero_add] at this
  rw [this]
  simp only [encC, encR_RES]
  split_ifs with ho <;> simp [ho]

theorem view_run {n : ℕ} (c : Configuration q w h n) :
    lay (regK h w) (encC M (winR c₀ n : ℤ) c) 1 = decide (M.output c.state = none) := by
  have := lay_pres (K := regK h w) (encC M (winR c₀ n : ℤ) c) 0 (by unfold regK; omega) 0
  simp only [zero_mul, zero_add, mul_zero] at this
  rw [this]
  simp only [encC, encR_RF]
  split_ifs with ho <;> simp [ho]

/-! ### Programs -/

theorem three_lt_spaceB : 3 < spaceB q w h c₀ x.length := by
  have := Nat.mul_le_mul_right (wd (regK h w)) (show 3 ≤ nBound q c₀ x.length + 3 by omega)
  have : 7 ≤ regK h w := by unfold regK; omega
  unfold spaceB; unfold wd at *; omega

/-- Initialization: from the blank tape to the register file of the initial configuration, head
on the result register. -/
theorem runs_initPart :
    Runs x (spaceB q w h c₀ x.length) (initPart M c₀) ⟨fun _ => false, 0, 0⟩
      (encTS M c₀ x (M.initial x.length)) := by
  have hB : (nBound q c₀ x.length + 3) * wd (regK h w) ≤ spaceB q w h c₀ x.length := le_rfl
  exact (runs_initProg M c₀ _ hB (by unfold nBound; omega) (by unfold nBound; omega)
    (by unfold nBound; omega)).seq ((runs_mvR 3 _ 0 0 (by
      have := three_lt_spaceB (q := q) (w := w) (h := h) c₀ (x := x); omega)).of_eq rfl rfl)

/-- The upstream window condition along a run with arbitrary coins. -/
def WinOK (x : Word) (c : Configuration q w h x.length) : Prop :=
  ∀ k : Fin w, -(winR c₀ x.length : ℤ) ≤ c.workPos k ∧ c.workPos k ≤ winR c₀ x.length

theorem winOK_run (hLS : ∀ coins t, M.spaceThrough x coins t ≤ c₀ * Nat.clog 2 (x.length + 2))
    (coins : CoinTape) (t : ℕ) : WinOK c₀ x (M.run x coins t) := by
  intro k
  have hW := winR_eq_clog c₀ x.length
  have a1 := workPos_lt_of_spaceThrough M x coins (hLS coins) t k
  rw [hW]
  push_cast at a1 ⊢
  exact ⟨by linarith [a1.1], by linarith [a1.2]⟩

/-- One simulated step with coin `b`. -/
theorem runs_bodyB (b : Bool) (c : Configuration q w h x.length) (hc : WinOK c₀ x c)
    (hc' : WinOK c₀ x (M.step x b c)) :
    Runs x (spaceB q w h c₀ x.length) (bodyB M b) (encTS M c₀ x c)
      (encTS M c₀ x (M.step x b c)) := by
  have hB : (nBound q c₀ x.length + 3) * wd (regK h w) ≤ spaceB q w h c₀ x.length := le_rfl
  have hstep := runs_stepProg (x := x) (B := spaceB q w h c₀ x.length) (fixCoin M b)
    (winR c₀ x.length : ℤ) c (nBound q c₀ x.length) hB
    (by rw [toNat_window]; unfold nBound; omega) (by unfold nBound; omega)
    (by unfold nBound; omega) (fun k => ⟨(hc k).1, (hc k).2, (hc' k).1, (hc' k).2⟩)
  have h3B := three_lt_spaceB (q := q) (w := w) (h := h) c₀ (x := x)
  unfold bodyB encTS
  exact ((runs_mvL 3 _ 3 0).of_eq rfl rfl).seq
    ((hstep.of_eq rfl rfl).seq ((runs_mvR 3 _ 0 0 (by omega)).of_eq rfl rfl))

/-- **The coin branch**: with the coin `b` written on the result cell of a running
configuration, the branch restores the cell and simulates one step of `M` with coin `b`. -/
theorem runs_coinTest (b : Bool) (c : Configuration q w h x.length)
    (hrun : M.output c.state = none) (hc : WinOK c₀ x c) (hc' : WinOK c₀ x (M.step x b c)) :
    Runs x (spaceB q w h c₀ x.length) (coinTest M)
      ⟨Function.update (lay (regK h w) (encC M (winR c₀ x.length : ℤ) c)) 3 b, 3, 0⟩
      (encTS M c₀ x (M.step x b c)) := by
  have hv3 : lay (regK h w) (encC M (winR c₀ x.length : ℤ) c) 3 = false := by
    rw [view_res]; simp [hrun]
  have hrestore : Function.update (Function.update
      (lay (regK h w) (encC M (winR c₀ x.length : ℤ) c)) 3 b) 3 false =
      lay (regK h w) (encC M (winR c₀ x.length : ℤ) c) := by
    rw [Function.update_idem, ← hv3, Function.update_eq_self]
  have hw : ∀ b', Runs x (spaceB q w h c₀ x.length) (write false)
      ⟨Function.update (lay (regK h w) (encC M (winR c₀ x.length : ℤ) c)) 3 b', 3, 0⟩
      (encTS M c₀ x c) := fun b' => by
    refine (runs_write false _ 3 0).of_eq rfl ?_
    unfold encTS
    rw [Function.update_idem, ← hv3, Function.update_eq_self]
  unfold coinTest
  cases b with
  | false =>
      exact Runs.iteF (by simp) ((hw false).seq (runs_bodyB M c₀ false c hc hc'))
  | true =>
      exact Runs.iteT (by simp) ((hw true).seq (runs_bodyB M c₀ true c hc hc'))

end RandFromLogspace

end Complexity.Space
