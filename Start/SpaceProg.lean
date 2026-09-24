/-
**Structured tape programs, compiled into offline machines.**

The bridge of `Start/SpaceCompile.lean` reduces running an abstract machine in bounded space to a
step-level obligation: each abstract step has to be carried out by a segment of an offline machine
of `Start/SpaceMachine.lean` between the encodings of the two states.  Writing such segments as
raw transition tables is impractical, so this module supplies the second, reusable layer: a small
structured language of *tape programs* — one-step actions, sequencing, conditionals and while
loops, the tests reading the symbol under the input head and the bit under the work head — with a
big-step semantics that tracks a side condition on every configuration visited, and a compiler
into transition tables whose correctness is proved once.

A program's semantics is stated on configurations whose control state is irrelevant (it is kept
at `0`); the compiled program, laid out from a base state `b` with an exit state `e`, runs the
same configurations with the control states `b, …, b + size p - 1`, ending in `e`.  The side
condition — for a space bound, "at most `B` cells" — is carried along, so the compiled run is a
`Complexity.Space.Machine.Path` of exactly the kind `Complexity.Space.Realizes` asks for.

Main definitions:

* `Complexity.Space.Prog` — the programs; `Prog.size` — the number of control states they need;
* `Complexity.Space.Prog.Exec` — big-step semantics, with a side condition on every
  configuration before the last;
* `Complexity.Space.Prog.delta` — the compiled transition table of a program laid out at a base
  state with an exit state;
* `Complexity.Space.Prog.machine` — the offline machine of a program: its states are those of the
  program plus one final, accepting, halting state.

Main results:

* `Complexity.Space.Prog.Exec.loop_of_variant` — the while rule, with an invariant and a
  decreasing measure, for establishing executions of loops;
* `Complexity.Space.Prog.path_of_exec` — **compiler correctness**: an execution of a program is a
  run of any machine whose table agrees with the compiled table on the program's states, through
  configurations satisfying the side condition and lying in the program's states;
* `Complexity.Space.Prog.machine_wellFormed`, `.machine_deterministic` — the compiled machine is a
  well-formed deterministic offline machine;
* `Complexity.Space.Prog.loop_seg`, `.loop_exit` — for a program `loop t body`, one iteration of
  the body is a segment of the compiled machine in the sense of `Start/SpaceCompile.lean`, and
  leaving the loop reaches the final accepting halting state: the two facts a client of
  `Complexity.Space.Realizes` needs.
-/

import Mathlib
import Start.SpaceCompile

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

/-! ### Reading and acting on a configuration -/

/-- The symbol under the input head (`none` at the end marker). -/
def rdIn (x : List Bool) (c : Config) : Option Bool := x[c.inHead]?

/-- The bit under the work head. -/
def rdW (c : Config) : Bool := c.tape.getD c.wHead false

/-- The effect of one instruction on a configuration — write a bit, move the two heads — with the
control state reset to `0`. -/
def eff (x : List Bool) (c : Config) (i : Bool × Dir × Dir) : Config :=
  { state := 0
    inHead := moveIn x.length c.inHead i.2.1
    tape := writeAt c.tape c.wHead i.1
    wHead := moveWork c.wHead i.2.2 }

/-- Reading without changing anything: the bit under the work head is written back, both heads
stay.  (Writing it back may extend the used part of the tape by blanks, exactly as a machine
step does.) -/
def touch (x : List Bool) (c : Config) : Config := eff x c (rdW c, .stay, .stay)

/-- The same configuration in another control state. -/
def Config.at (c : Config) (q : ℕ) : Config := { c with state := q }

@[simp] theorem Config.at_state (c : Config) (q : ℕ) : (c.at q).state = q := rfl
@[simp] theorem Config.at_space (c : Config) (q : ℕ) : (c.at q).space = c.space := rfl
@[simp] theorem rdIn_at (x : List Bool) (c : Config) (q : ℕ) : rdIn x (c.at q) = rdIn x c := rfl
@[simp] theorem rdW_at (c : Config) (q : ℕ) : rdW (c.at q) = rdW c := rfl
@[simp] theorem eff_at (x : List Bool) (c : Config) (q : ℕ) (i : Bool × Dir × Dir) :
    eff x (c.at q) i = eff x c i := rfl
@[simp] theorem Config.at_at (c : Config) (q r : ℕ) : (c.at q).at r = c.at r := rfl
@[simp] theorem eff_state (x : List Bool) (c : Config) (i : Bool × Dir × Dir) :
    (eff x c i).state = 0 := rfl

theorem Config.at_self (c : Config) : c.at c.state = c := rfl

/-! ### Programs -/

/-- A test on what the two heads read. -/
abbrev Test := Option Bool → Bool → Bool

/-- Structured tape programs. -/
inductive Prog where
  /-- One machine step: the instruction (bit to write, input move, work move) is computed from
  what the heads read. -/
  | act (f : Option Bool → Bool → Bool × Dir × Dir)
  /-- Sequencing. -/
  | seq (p q : Prog)
  /-- A conditional; evaluating the test costs one step. -/
  | ite (t : Test) (p q : Prog)
  /-- A while loop; evaluating the test costs one step. -/
  | loop (t : Test) (p : Prog)

namespace Prog

/-- The number of control states a program occupies. -/
def size : Prog → ℕ
  | act _ => 1
  | seq p q => p.size + q.size
  | ite _ p q => 1 + p.size + q.size
  | loop _ p => 1 + p.size

theorem size_pos : ∀ p : Prog, 0 < p.size
  | act _ => by simp [size]
  | seq p _ => by have := size_pos p; simp [size]; omega
  | ite _ _ _ => by simp [size]
  | loop _ _ => by simp [size]

/-- Writing a bit. -/
def write (b : Bool) : Prog := act fun _ _ => (b, .stay, .stay)

/-- Moving the work head. -/
def wmove (d : Dir) : Prog := act fun _ w => (w, .stay, d)

/-- Moving the input head. -/
def imove (d : Dir) : Prog := act fun _ w => (w, d, .stay)

/-- Doing nothing, in one step. -/
def skip : Prog := act fun _ w => (w, .stay, .stay)

/-! ### Semantics -/

/-- `Exec x P p c c'`: the program `p`, started on the configuration `c`, ends on `c'`, and every
configuration it passes through before `c'` satisfies `P`.  Control states play no role: every
configuration produced by an instruction has control state `0`. -/
inductive Exec (x : List Bool) (P : Config → Prop) : Prog → Config → Config → Prop
  /-- One action. -/
  | act {f : Option Bool → Bool → Bool × Dir × Dir} {c : Config} (hc : P c) :
      Exec x P (act f) c (eff x c (f (rdIn x c) (rdW c)))
  /-- Sequencing. -/
  | seq {p q : Prog} {c d e : Config} (hp : Exec x P p c d) (hq : Exec x P q d e) :
      Exec x P (seq p q) c e
  /-- The test of a conditional succeeds. -/
  | iteT {t : Test} {p q : Prog} {c e : Config} (hc : P c) (ht : t (rdIn x c) (rdW c) = true)
      (hp : Exec x P p (touch x c) e) : Exec x P (ite t p q) c e
  /-- The test of a conditional fails. -/
  | iteF {t : Test} {p q : Prog} {c e : Config} (hc : P c) (ht : t (rdIn x c) (rdW c) = false)
      (hq : Exec x P q (touch x c) e) : Exec x P (ite t p q) c e
  /-- The test of a loop succeeds: run the body, then the loop again. -/
  | loopT {t : Test} {p : Prog} {c d e : Config} (hc : P c) (ht : t (rdIn x c) (rdW c) = true)
      (hp : Exec x P p (touch x c) d) (hl : Exec x P (loop t p) d e) :
      Exec x P (loop t p) c e
  /-- The test of a loop fails: leave it. -/
  | loopF {t : Test} {p : Prog} {c : Config} (hc : P c) (ht : t (rdIn x c) (rdW c) = false) :
      Exec x P (loop t p) c (touch x c)

/-- **The while rule.**  If an invariant `I` implies the side condition, and whenever the test
succeeds the body re-establishes `I` while decreasing a measure, then the loop, started in `I`,
terminates in a configuration `touch x c` where the test fails on `c` and `I c` holds. -/
theorem Exec.loop_of_variant {x : List Bool} {P : Config → Prop} {t : Test} {body : Prog}
    (I : Config → Prop) (μ : Config → ℕ) (hP : ∀ c, I c → P c)
    (hbody : ∀ c, I c → t (rdIn x c) (rdW c) = true →
      ∃ d, Exec x P body (touch x c) d ∧ I d ∧ μ d < μ c) :
    ∀ c, I c → ∃ c', I c' ∧ t (rdIn x c') (rdW c') = false ∧
      Exec x P (loop t body) c (touch x c') := by
  intro c
  induction h : μ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    intro hc
    cases ht : t (rdIn x c) (rdW c) with
    | false => exact ⟨c, hc, ht, Exec.loopF (hP c hc) ht⟩
    | true =>
        obtain ⟨d, hd, hId, hlt⟩ := hbody c hc ht
        obtain ⟨c', hc', ht', hl⟩ := ih (μ d) (h ▸ hlt) d rfl hId
        exact ⟨c', hc', ht', Exec.loopT (hP c hc) ht hd hl⟩

theorem Exec.mono {x : List Bool} {P Q : Config → Prop} (hPQ : ∀ c, P c → Q c) {p : Prog}
    {c d : Config} (h : Exec x P p c d) : Exec x Q p c d := by
  induction h with
  | act hc => exact .act (hPQ _ hc)
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteT hc ht _ ih => exact .iteT (hPQ _ hc) ht ih
  | iteF hc ht _ ih => exact .iteF (hPQ _ hc) ht ih
  | loopT hc ht _ _ ih₁ ih₂ => exact .loopT (hPQ _ hc) ht ih₁ ih₂
  | loopF hc ht => exact .loopF (hPQ _ hc) ht

/-! ### Compilation -/

/-- The transition table of the program `p` laid out from the base state `b`, with exit state
`e`: on the states `b, …, b + size p - 1` it is the program's table; control leaves to `e`. -/
def delta : Prog → ℕ → ℕ → ℕ → Option Bool → Bool → List (ℕ × Bool × Dir × Dir)
  | act f, b, e => fun q a w => if q = b then [(e, f a w)] else []
  | seq p q, b, e => fun st a w =>
      if st < b + p.size then delta p b (b + p.size) st a w
      else delta q (b + p.size) e st a w
  | ite t p q, b, e => fun st a w =>
      if st = b then [(if t a w then b + 1 else b + 1 + p.size, w, .stay, .stay)]
      else if st < b + 1 + p.size then delta p (b + 1) e st a w
      else delta q (b + 1 + p.size) e st a w
  | loop t p, b, e => fun st a w =>
      if st = b then [(if t a w then b + 1 else e, w, .stay, .stay)]
      else delta p (b + 1) b st a w

/-- The compiled table offers at most one instruction. -/
theorem delta_length_le : ∀ (p : Prog) (b e q : ℕ) (a : Option Bool) (w : Bool),
    (delta p b e q a w).length ≤ 1
  | act f, b, e, q, a, w => by unfold delta; split <;> simp
  | seq p r, b, e, q, a, w => by
      unfold delta; split
      · exact delta_length_le p _ _ _ _ _
      · exact delta_length_le r _ _ _ _ _
  | ite t p r, b, e, q, a, w => by
      unfold delta; split
      · simp
      · split
        · exact delta_length_le p _ _ _ _ _
        · exact delta_length_le r _ _ _ _ _
  | loop t p, b, e, q, a, w => by
      unfold delta; split
      · simp
      · exact delta_length_le p _ _ _ _ _

/-- The compiled table only jumps inside the program or to its exit. -/
theorem delta_target : ∀ (p : Prog) (b e q : ℕ) (a : Option Bool) (w : Bool),
    ∀ i ∈ delta p b e q a w, (b ≤ i.1 ∧ i.1 < b + p.size) ∨ i.1 = e
  | act f, b, e, q, a, w => by
      intro i hi; unfold delta at hi; split at hi <;> simp_all
  | seq p r, b, e, q, a, w => by
      have := size_pos r
      intro i hi; unfold delta at hi; simp only [size]; split at hi
      · rcases delta_target p _ _ _ _ _ i hi with h | h <;> omega
      · rcases delta_target r _ _ _ _ _ i hi with h | h <;> omega
  | ite t p r, b, e, q, a, w => by
      have := size_pos p; have := size_pos r
      intro i hi; unfold delta at hi; simp only [size]; split at hi
      · simp only [List.mem_singleton] at hi; subst hi; split <;> simp <;> omega
      · split at hi
        · rcases delta_target p _ _ _ _ _ i hi with h | h <;> omega
        · rcases delta_target r _ _ _ _ _ i hi with h | h <;> omega
  | loop t p, b, e, q, a, w => by
      have := size_pos p
      intro i hi; unfold delta at hi; simp only [size]; split at hi
      · simp only [List.mem_singleton] at hi; subst hi; split
        · simp; omega
        · simp
      · rcases delta_target p _ _ _ _ _ i hi with h | h <;> omega

/-! ### Compiler correctness -/

/-- A machine *hosts* the program `p` at base `b` with exit `e` when its table agrees with the
compiled one on the program's states. -/
def Hosts (M : Machine) (p : Prog) (b e : ℕ) : Prop :=
  ∀ q, b ≤ q → q < b + p.size → ∀ a w, M.delta q a w = delta p b e q a w

theorem step_of_delta {M : Machine} {x : List Bool} {c : Config} {i : ℕ × Bool × Dir × Dir}
    (h : M.delta c.state (rdIn x c) (rdW c) = [i]) :
    M.Step x c ((eff x c (i.2.1, i.2.2.1, i.2.2.2)).at i.1) := by
  unfold Machine.Step Machine.stepList
  unfold rdIn rdW at h
  rw [h]
  simp [eff, Config.at]

/-- Every execution ends in control state `0`. -/
theorem exec_state {x : List Bool} {P : Config → Prop} {p : Prog} {c c' : Config}
    (h : Exec x P p c c') : c'.state = 0 := by
  induction h <;> first | rfl | assumption

theorem Hosts.seq_left {M : Machine} {p q : Prog} {b e : ℕ} (h : Hosts M (seq p q) b e) :
    Hosts M p b (b + p.size) := by
  intro st h1 h2 a w
  rw [h st h1 (by simp only [size]; omega) a w]
  simp only [delta, if_pos h2]

theorem Hosts.seq_right {M : Machine} {p q : Prog} {b e : ℕ} (h : Hosts M (seq p q) b e) :
    Hosts M q (b + p.size) e := by
  intro st h1 h2 a w
  rw [h st (by omega) (by simp only [size]; omega) a w]
  simp only [delta, if_neg (show ¬ st < b + p.size by omega)]

theorem Hosts.ite_left {M : Machine} {t : Test} {p q : Prog} {b e : ℕ}
    (h : Hosts M (ite t p q) b e) : Hosts M p (b + 1) e := by
  intro st h1 h2 a w
  rw [h st (by omega) (by simp only [size]; omega) a w]
  simp only [delta, if_neg (show st ≠ b by omega), if_pos h2]

theorem Hosts.ite_right {M : Machine} {t : Test} {p q : Prog} {b e : ℕ}
    (h : Hosts M (ite t p q) b e) : Hosts M q (b + 1 + p.size) e := by
  intro st h1 h2 a w
  rw [h st (by omega) (by simp only [size]; omega) a w]
  simp only [delta, if_neg (show st ≠ b by omega), if_neg (show ¬ st < b + 1 + p.size by omega)]

theorem Hosts.loop_body {M : Machine} {t : Test} {p : Prog} {b e : ℕ}
    (h : Hosts M (loop t p) b e) : Hosts M p (b + 1) b := by
  intro st h1 h2 a w
  rw [h st (by omega) (by simp only [size]; omega) a w]
  simp only [delta, if_neg (show st ≠ b by omega)]

theorem Hosts.test {M : Machine} {t : Test} {p q : Prog} {b e : ℕ}
    (h : Hosts M (ite t p q) b e) (a : Option Bool) (w : Bool) :
    M.delta b a w = [(if t a w then b + 1 else b + 1 + p.size, w, .stay, .stay)] := by
  rw [h b le_rfl (by simp only [size]; omega) a w]
  simp only [delta, ↓reduceIte]

theorem Hosts.loop_test {M : Machine} {t : Test} {p : Prog} {b e : ℕ}
    (h : Hosts M (loop t p) b e) (a : Option Bool) (w : Bool) :
    M.delta b a w = [(if t a w then b + 1 else e, w, .stay, .stay)] := by
  rw [h b le_rfl (by simp only [size]; omega) a w]
  simp only [delta, ↓reduceIte]

/-- **Compiler correctness.**  If the machine hosts `p` at `b` with exit `e`, an execution of `p`
from `c` (in control state `0`) to `c'` is a run of the machine from `c` in state `b` to `c'` in
state `e`, all of whose configurations before the last satisfy the side condition and lie in the
program's states. -/
theorem path_of_exec {M : Machine} {x : List Bool} {P : Config → Prop} {p : Prog} {c c' : Config}
    (h : Exec x P p c c') : c.state = 0 → ∀ {b e : ℕ}, Hosts M p b e →
      M.Path x (fun d => P (d.at 0) ∧ b ≤ d.state ∧ d.state < b + p.size) (c.at b) (c'.at e) := by
  induction h with
  | @act f c hc =>
      intro hc0 b e hM
      have hd : M.delta (c.at b).state (rdIn x (c.at b)) (rdW (c.at b)) =
          [(e, f (rdIn x c) (rdW c))] := by
        rw [Config.at_state, hM b le_rfl (by simp [size]) _ _]
        simp [delta]
      refine Machine.Path.single ⟨?_, le_rfl, by simp [size]⟩ (step_of_delta hd)
      rw [Config.at_at, ← hc0]
      exact hc
  | @seq p q c d e hp hq ihp ihq =>
      intro hc0 b e' hM
      refine Machine.Path.trans ((ihp hc0 hM.seq_left).mono ?_)
        ((ihq (exec_state hp) hM.seq_right).mono ?_)
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, h2, by simp only [size]; omega⟩
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩
  | @iteT t p q c e hc ht hp ihp =>
      intro hc0 b e' hM
      have hd : M.delta (c.at b).state (rdIn x (c.at b)) (rdW (c.at b)) =
          [(b + 1, rdW c, .stay, .stay)] := by
        rw [Config.at_state, hM.test]; simp [ht]
      refine Machine.Path.head ⟨?_, le_rfl, by simp only [Config.at_state, size]; omega⟩
        (step_of_delta hd)
        ((ihp rfl hM.ite_left).mono ?_)
      · rw [Config.at_at, ← hc0]; exact hc
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩
  | @iteF t p q c e hc ht hq ihq =>
      intro hc0 b e' hM
      have hd : M.delta (c.at b).state (rdIn x (c.at b)) (rdW (c.at b)) =
          [(b + 1 + p.size, rdW c, .stay, .stay)] := by
        rw [Config.at_state, hM.test]; simp [ht]
      refine Machine.Path.head ⟨?_, le_rfl, by simp only [Config.at_state, size]; omega⟩
        (step_of_delta hd)
        ((ihq rfl hM.ite_right).mono ?_)
      · rw [Config.at_at, ← hc0]; exact hc
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩
  | @loopT t p c d e hc ht hp hl ihp ihl =>
      intro hc0 b e' hM
      have hd : M.delta (c.at b).state (rdIn x (c.at b)) (rdW (c.at b)) =
          [(b + 1, rdW c, .stay, .stay)] := by
        rw [Config.at_state, hM.loop_test]; simp [ht]
      refine Machine.Path.head ⟨?_, le_rfl, by simp only [Config.at_state, size]; omega⟩
        (step_of_delta hd)
        (Machine.Path.trans ((ihp rfl hM.loop_body).mono ?_) (ihl (exec_state hp) hM))
      · rw [Config.at_at, ← hc0]; exact hc
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩
  | @loopF t p c hc ht =>
      intro hc0 b e' hM
      have hd : M.delta (c.at b).state (rdIn x (c.at b)) (rdW (c.at b)) =
          [(e', rdW c, .stay, .stay)] := by
        rw [Config.at_state, hM.loop_test]; simp [ht]
      refine Machine.Path.single ⟨?_, le_rfl, by simp only [Config.at_state, size]; omega⟩
        (step_of_delta hd)
      rw [Config.at_at, ← hc0]; exact hc

/-! ### The machine of a program -/

/-- The offline machine of a program: the program occupies the states `0, …, size p - 1` and
exits to the final state `size p`, which is accepting and halting. -/
def machine (p : Prog) : Machine where
  states := p.size + 1
  accept q := decide (q = p.size)
  delta q a w := if q < p.size then delta p 0 p.size q a w else []

theorem machine_hosts (p : Prog) : Hosts p.machine p 0 p.size := by
  intro q _ hq a w
  simp only [machine, zero_add] at hq ⊢
  rw [if_pos hq]

theorem machine_wellFormed (p : Prog) : p.machine.WellFormed := by
  refine ⟨Nat.succ_pos _, ?_⟩
  intro q a w i hi
  simp only [machine] at hi ⊢
  split at hi
  · rcases delta_target p 0 p.size q a w i hi with h | h <;> omega
  · simp at hi

theorem machine_deterministic (p : Prog) : p.machine.Deterministic := by
  intro q a w
  simp only [machine]
  split
  · exact delta_length_le _ _ _ _ _ _
  · simp

/-- The final state of the machine of a program halts. -/
theorem machine_final_halts (p : Prog) (x : List Bool) (c : Config) (hc : c.state = p.size) :
    p.machine.stepList x c = [] := by
  simp [Machine.stepList, machine, hc]

/-- The final state is the only accepting one. -/
theorem machine_accept (p : Prog) (q : ℕ) : p.machine.accept q = decide (q = p.size) := rfl

/-! ### Loops: the interface to `Start/SpaceCompile.lean` -/

/-- **One iteration of the main loop is a segment.**  For the machine of `loop t body`: if the
test succeeds on `c`, and the body runs from `touch x c` to `d` within `B` cells, then the machine
goes from `c` in state `0` back to `d` in state `0` by a segment within `B` cells.  (The two ends
are not constrained by a segment; `Complexity.Space.Realizes` bounds them separately.) -/
theorem loop_seg {t : Test} {body : Prog} {x : List Bool} {B : ℕ} {c d : Config}
    (ht : t (rdIn x c) (rdW c) = true)
    (hb : Exec x (fun c => c.space ≤ B) body (touch x c) d) :
    (loop t body).machine.Seg x B (c.at 0) (d.at 0) := by
  have hM := machine_hosts (loop t body)
  have hd : (loop t body).machine.delta (c.at 0).state (rdIn x (c.at 0)) (rdW (c.at 0)) =
      [(1, rdW c, .stay, .stay)] := by
    rw [Config.at_state, hM.loop_test]; simp [ht]
  refine ⟨(touch x c).at 1, step_of_delta hd, ?_⟩
  refine (path_of_exec hb rfl (b := 0 + 1) (e := 0) hM.loop_body).mono ?_
  rintro d' ⟨h1, _, h3⟩
  refine ⟨by simpa using h1, ?_⟩
  rw [machine_accept, decide_eq_false_iff_not]
  simp only [size] at h3 ⊢
  omega

/-- **Leaving the main loop reaches the final state.**  For the machine of `loop t body`: if the
test fails on `c`, the machine steps from `c` in state `0` to the final, accepting, halting
state. -/
theorem loop_exit {t : Test} {body : Prog} {x : List Bool} {c : Config}
    (ht : t (rdIn x c) (rdW c) = false) :
    (loop t body).machine.Step x (c.at 0) ((touch x c).at (loop t body).size) := by
  have hM := machine_hosts (loop t body)
  have hd : (loop t body).machine.delta (c.at 0).state (rdIn x (c.at 0)) (rdW (c.at 0)) =
      [((loop t body).size, rdW c, .stay, .stay)] := by
    rw [Config.at_state, hM.loop_test]; simp [ht]
  exact step_of_delta hd


theorem space_touch (x : List Bool) (c : Config) : (touch x c).space = c.space := by
  simp only [touch, eff, Config.space, writeAt_length, moveWork]
  omega

/-- **The loop form of the bridge.**  An abstract machine is realized by the machine of the
program `loop t body` when, under an encoding `enc` of its states as configurations (the initial
state as the initial configuration):

* reachable states fit in `B x` cells, and are accepting exactly when they are halting;
* the initial state does not halt;
* the test `t` fails on the encoding of a halting state;
* for each step `s ↦ s'` the test succeeds on the encoding of `s`, and the body runs from it
  (after the test's step) to the encoding of `s'` within `B x` cells.

A rejecting computation is one that never halts — the abstract machine loops in a rejecting state,
and so does the program.  This is the form in which a client supplies its single bridge lemma: a
program for one step, and its execution on the encoding of each reachable state. -/
theorem realizes_loop {σ : Type*} {A : AbsMachine σ} {t : Test} {body : Prog}
    {enc : List Bool → σ → Config} {B : List Bool → ℕ}
    (h0 : ∀ x, enc x (A.start x) = init)
    (hstart : ∀ x, (A.step (A.start x)).isSome)
    (hsp : ∀ x s, A.Reaches x s → (enc x s).space ≤ B x)
    (hacc : ∀ x s, A.Reaches x s → (A.accept s = true ↔ A.step s = none))
    (hstop : ∀ x s, A.Reaches x s → A.step s = none →
      t (rdIn x (enc x s)) (rdW (enc x s)) = false)
    (hstep : ∀ x s s', A.Reaches x s → A.step s = some s' →
      t (rdIn x (enc x s)) (rdW (enc x s)) = true ∧
        Exec x (fun c => c.space ≤ B x) body (touch x (enc x s)) (enc x s')) :
    Realizes (loop t body).machine A
      (fun x s => if (A.step s).isSome then (enc x s).at 0
        else (touch x (enc x s)).at (loop t body).size) B := by
  have hpos : 0 < (loop t body).size := size_pos _
  have hq0 : (loop t body).machine.accept 0 = false := by
    rw [machine_accept]; simp only [decide_eq_false_iff_not]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [hstart x, if_true, h0]
    rfl
  · intro x s hs
    cases hA : A.step s with
    | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, if_false, Config.at_state,
          machine_accept, decide_true]
        exact ((hacc x s hs).2 hA).symm
    | some s' =>
        simp only [Option.isSome_some, if_true, Config.at_state, hq0]
        cases h : A.accept s
        · rfl
        · exact absurd ((hacc x s hs).1 h) (by simp [hA])
  · intro x s hs
    split
    · exact hsp x s hs
    · rw [Config.at_space, space_touch]; exact hsp x s hs
  · intro x s hs hA
    simp only [hA, Option.isSome_none, Bool.false_eq_true, if_false]
    exact machine_final_halts _ _ _ rfl
  · intro x s s' hs hA
    obtain ⟨ht, hb⟩ := hstep x s s' hs hA
    have hseg := loop_seg ht hb
    have hs' := hs.tail hA
    simp only [hA, Option.isSome_some, if_true]
    split
    · exact hseg
    · rename_i hn
      have hA' : A.step s' = none := by simpa using hn
      refine hseg.trans ⟨hsp x s' hs', hq0⟩ (Machine.Seg.single (loop_exit ?_))
      exact hstop x s' hs' hA'

/-- **Membership in `DSPACE` from the loop form of the bridge.** -/
theorem dspace_loop {σ : Type*} {A : AbsMachine σ} {t : Test} {body : Prog}
    {enc : List Bool → σ → Config} {B : List Bool → ℕ} {s : ℕ → ℕ}
    (h0 : ∀ x, enc x (A.start x) = init)
    (hstart : ∀ x, (A.step (A.start x)).isSome)
    (hsp : ∀ x s, A.Reaches x s → (enc x s).space ≤ B x)
    (hacc : ∀ x s, A.Reaches x s → (A.accept s = true ↔ A.step s = none))
    (hstop : ∀ x s, A.Reaches x s → A.step s = none →
      t (rdIn x (enc x s)) (rdW (enc x s)) = false)
    (hstep : ∀ x s s', A.Reaches x s → A.step s = some s' →
      t (rdIn x (enc x s)) (rdW (enc x s)) = true ∧
        Exec x (fun c => c.space ≤ B x) body (touch x (enc x s)) (enc x s'))
    (hB : ∀ x, B x ≤ s x.length) :
    DSPACE s A.Accepts :=
  (realizes_loop h0 hstart hsp hacc hstop hstep).dspace (machine_wellFormed _)
    (machine_deterministic _) hB

end Prog

end Complexity.Space
