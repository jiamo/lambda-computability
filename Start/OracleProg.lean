/-
**Structured tape programs with oracle queries, compiled into oracle machines.**

This is the relativized counterpart of `Start/SpaceProg.lean`.  The language
`Complexity.Space.OProg`
has the constructors of `Complexity.Space.Prog` (one action, sequencing, conditionals and while
loops on what the two heads read) and two more:

* `qbit` — append the bit under the work head to the query tape;
* `ask p q` — hand the query tape to the oracle, erase it, and continue with `p` or `q` according
  to the answer.

Plain programs embed by `Complexity.Space.OProg.lift`, and an execution of a plain program is an
execution of its lift with the query tape left alone (`Complexity.Space.OProg.oexec_lift`), so every
specification proved for the combinators of `Start/SpaceProgLib.lean` and
`Start/SpaceProgTracks.lean` is available unchanged.

Main results:

* `Complexity.Space.OProg.opath_of_oexec` — **compiler correctness**: an execution is a run of any
  oracle machine hosting the compiled tables;
* `Complexity.Space.OProg.omachine` — the oracle machine of a program followed by a final test of
  the bit under the work head, with an accepting and a rejecting halting state; it is well formed
  and deterministic;
* `Complexity.Space.OProg.odspace_of_oexec` — **membership in `DSPACE^A`**: if on every input the
  program runs from the initial configuration within `B x ≤ s |x|` cells (work tape and query tape
  together) to a configuration whose scanned bit says whether `x ∈ L`, then `L ∈ DSPACE^A s`.
-/

import Mathlib
import Start.OracleSpace
import Start.SpaceProg

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

open Complexity (Oracle Word)

/-! ### Configurations -/

/-- The symbol under the input head. -/
def ordIn (x : List Bool) (c : OConfig) : Option Bool := x[c.inHead]?

/-- The bit under the work head. -/
def ordW (c : OConfig) : Bool := c.tape.getD c.wHead false

/-- The effect of one instruction — write a bit, optionally append a bit to the query tape, move
the two heads — with the control state reset to `0`. -/
def oeff (x : List Bool) (c : OConfig) (i : Bool × Option Bool × Dir × Dir) : OConfig :=
  { state := 0
    inHead := moveIn x.length c.inHead i.2.2.1
    tape := writeAt c.tape c.wHead i.1
    wHead := moveWork c.wHead i.2.2.2
    qtape := match i.2.1 with
      | none => c.qtape
      | some b => c.qtape ++ [b] }

/-- Reading without changing anything. -/
def otouch (x : List Bool) (c : OConfig) : OConfig := oeff x c (ordW c, none, .stay, .stay)

/-- The same configuration in another control state. -/
def OConfig.at (c : OConfig) (q : ℕ) : OConfig := { c with state := q }

@[simp] theorem OConfig.at_state (c : OConfig) (q : ℕ) : (c.at q).state = q := rfl
@[simp] theorem OConfig.at_at (c : OConfig) (q r : ℕ) : (c.at q).at r = c.at r := rfl
@[simp] theorem OConfig.at_space (c : OConfig) (q : ℕ) : (c.at q).space = c.space := rfl
@[simp] theorem OConfig.at_qtape (c : OConfig) (q : ℕ) : (c.at q).qtape = c.qtape := rfl
@[simp] theorem ordIn_at (x : List Bool) (c : OConfig) (q : ℕ) : ordIn x (c.at q) = ordIn x c := rfl
@[simp] theorem ordW_at (c : OConfig) (q : ℕ) : ordW (c.at q) = ordW c := rfl
@[simp] theorem oeff_at (x : List Bool) (c : OConfig) (q : ℕ)
    (i : Bool × Option Bool × Dir × Dir) : oeff x (c.at q) i = oeff x c i := rfl

/-- A plain configuration with a query tape attached. -/
def Config.withQ (c : Config) (q : List Bool) : OConfig := ⟨c.state, c.inHead, c.tape, c.wHead, q⟩

theorem oeff_withQ (x : List Bool) (c : Config) (q : List Bool) (b : Bool) (di dw : Dir) :
    oeff x (c.withQ q) (b, none, di, dw) = (eff x c (b, di, dw)).withQ q := rfl

theorem otouch_withQ (x : List Bool) (c : Config) (q : List Bool) :
    otouch x (c.withQ q) = (touch x c).withQ q := rfl

@[simp] theorem ordIn_withQ (x : List Bool) (c : Config) (q : List Bool) :
    ordIn x (c.withQ q) = rdIn x c := rfl

@[simp] theorem ordW_withQ (c : Config) (q : List Bool) : ordW (c.withQ q) = rdW c := rfl

@[simp] theorem withQ_qtape (c : Config) (q : List Bool) : (c.withQ q).qtape = q := rfl

theorem space_withQ_nil (c : Config) : (c.withQ []).space = c.space := by
  simp [OConfig.space, Config.withQ, Config.space]

theorem space_withQ (c : Config) (q : List Bool) :
    (c.withQ q).space = max c.space q.length := rfl

/-! ### Programs -/

/-- Structured tape programs with oracle queries. -/
inductive OProg where
  /-- One machine step on the work and input tapes. -/
  | act (f : Option Bool → Bool → Bool × Dir × Dir)
  /-- Append the bit under the work head to the query tape. -/
  | qbit
  /-- Ask the oracle about the query tape, erase it, and branch on the answer. -/
  | ask (p q : OProg)
  /-- Sequencing. -/
  | seq (p q : OProg)
  /-- A conditional; evaluating the test costs one step. -/
  | ite (t : Test) (p q : OProg)
  /-- A while loop; evaluating the test costs one step. -/
  | loop (t : Test) (p : OProg)

namespace OProg

/-- The number of control states a program occupies. -/
def size : OProg → ℕ
  | act _ => 1
  | qbit => 1
  | ask p q => 1 + p.size + q.size
  | seq p q => p.size + q.size
  | ite _ p q => 1 + p.size + q.size
  | loop _ p => 1 + p.size

theorem size_pos : ∀ p : OProg, 0 < p.size
  | act _ => by simp [size]
  | qbit => by simp [size]
  | ask _ _ => by simp [size]
  | seq p _ => by have := size_pos p; simp [size]; omega
  | ite _ _ _ => by simp [size]
  | loop _ _ => by simp [size]

/-- A plain program as an oracle program that never touches the query tape. -/
def lift : Prog → OProg
  | .act f => act f
  | .seq p q => seq (lift p) (lift q)
  | .ite t p q => ite t (lift p) (lift q)
  | .loop t p => loop t (lift p)

/-! ### Semantics -/

/-- `OExec A x P p c c'`: with the oracle `A`, the program `p` started on `c` ends on `c'`, and
every configuration it passes through before `c'` satisfies `P`. -/
inductive OExec (A : Oracle) (x : List Bool) (P : OConfig → Prop) : OProg → OConfig → OConfig → Prop
  | act {f : Option Bool → Bool → Bool × Dir × Dir} {c : OConfig} (hc : P c) :
      OExec A x P (act f) c
        (oeff x c ((f (ordIn x c) (ordW c)).1, none, (f (ordIn x c) (ordW c)).2.1,
          (f (ordIn x c) (ordW c)).2.2))
  | qbit {c : OConfig} (hc : P c) :
      OExec A x P qbit c (oeff x c (ordW c, some (ordW c), .stay, .stay))
  | askT {p q : OProg} {c e : OConfig} (hc : P c) (hA : A c.qtape = true)
      (hp : OExec A x P p { c with qtape := [] } e) : OExec A x P (ask p q) c e
  | askF {p q : OProg} {c e : OConfig} (hc : P c) (hA : A c.qtape = false)
      (hq : OExec A x P q { c with qtape := [] } e) : OExec A x P (ask p q) c e
  | seq {p q : OProg} {c d e : OConfig} (hp : OExec A x P p c d) (hq : OExec A x P q d e) :
      OExec A x P (seq p q) c e
  | iteT {t : Test} {p q : OProg} {c e : OConfig} (hc : P c) (ht : t (ordIn x c) (ordW c) = true)
      (hp : OExec A x P p (otouch x c) e) : OExec A x P (ite t p q) c e
  | iteF {t : Test} {p q : OProg} {c e : OConfig} (hc : P c) (ht : t (ordIn x c) (ordW c) = false)
      (hq : OExec A x P q (otouch x c) e) : OExec A x P (ite t p q) c e
  | loopT {t : Test} {p : OProg} {c d e : OConfig} (hc : P c)
      (ht : t (ordIn x c) (ordW c) = true)
      (hp : OExec A x P p (otouch x c) d) (hl : OExec A x P (loop t p) d e) :
      OExec A x P (loop t p) c e
  | loopF {t : Test} {p : OProg} {c : OConfig} (hc : P c) (ht : t (ordIn x c) (ordW c) = false) :
      OExec A x P (loop t p) c (otouch x c)

theorem OExec.mono {A : Oracle} {x : List Bool} {P Q : OConfig → Prop} (hPQ : ∀ c, P c → Q c)
    {p : OProg} {c d : OConfig} (h : OExec A x P p c d) : OExec A x Q p c d := by
  induction h with
  | act hc => exact .act (hPQ _ hc)
  | qbit hc => exact .qbit (hPQ _ hc)
  | askT hc hA _ ih => exact .askT (hPQ _ hc) hA ih
  | askF hc hA _ ih => exact .askF (hPQ _ hc) hA ih
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteT hc ht _ ih => exact .iteT (hPQ _ hc) ht ih
  | iteF hc ht _ ih => exact .iteF (hPQ _ hc) ht ih
  | loopT hc ht _ _ ih₁ ih₂ => exact .loopT (hPQ _ hc) ht ih₁ ih₂
  | loopF hc ht => exact .loopF (hPQ _ hc) ht

/-- **An execution of a plain program is an execution of its lift**, with the query tape left
alone. -/
theorem oexec_lift {A : Oracle} {x : List Bool} {P : Config → Prop} {Q : OConfig → Prop}
    {q : List Bool} (hPQ : ∀ c, P c → Q (c.withQ q)) {p : Prog} {c c' : Config}
    (h : Prog.Exec x P p c c') : OExec A x Q (lift p) (c.withQ q) (c'.withQ q) := by
  induction h with
  | @act f c hc =>
      exact OExec.act (A := A) (x := x) (P := Q) (f := f) (c := c.withQ q) (hPQ _ hc)
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteT hc ht _ ih =>
      exact .iteT (hPQ _ hc) (by simpa using ht) (by rw [otouch_withQ]; exact ih)
  | iteF hc ht _ ih =>
      exact .iteF (hPQ _ hc) (by simpa using ht) (by rw [otouch_withQ]; exact ih)
  | loopT hc ht _ _ ih₁ ih₂ =>
      exact .loopT (hPQ _ hc) (by simpa using ht) (by rw [otouch_withQ]; exact ih₁) ih₂
  | @loopF t p c hc ht =>
      have := OExec.loopF (A := A) (x := x) (P := Q) (p := lift p) (hPQ _ hc)
        (show t (ordIn x (c.withQ q)) (ordW (c.withQ q)) = false by simpa using ht)
      rw [otouch_withQ] at this
      exact this

/-! ### Compilation -/

/-- An instruction of an oracle machine. -/
abbrev OInstr := ℕ × Bool × Option Bool × Dir × Dir

/-- The compiled transition table of `p` laid out from the base state `b` with exit state `e`. -/
def odelta : OProg → ℕ → ℕ → ℕ → Option Bool → Bool → List OInstr
  | act f, b, e => fun st a w =>
      if st = b then [(e, (f a w).1, none, (f a w).2.1, (f a w).2.2)] else []
  | qbit, b, e => fun st _ w => if st = b then [(e, w, some w, .stay, .stay)] else []
  | ask p q, b, e => fun st a w =>
      if st = b then []
      else if st < b + 1 + p.size then odelta p (b + 1) e st a w
      else odelta q (b + 1 + p.size) e st a w
  | seq p q, b, e => fun st a w =>
      if st < b + p.size then odelta p b (b + p.size) st a w
      else odelta q (b + p.size) e st a w
  | ite t p q, b, e => fun st a w =>
      if st = b then [(if t a w then b + 1 else b + 1 + p.size, w, none, .stay, .stay)]
      else if st < b + 1 + p.size then odelta p (b + 1) e st a w
      else odelta q (b + 1 + p.size) e st a w
  | loop t p, b, e => fun st a w =>
      if st = b then [(if t a w then b + 1 else e, w, none, .stay, .stay)]
      else odelta p (b + 1) b st a w

/-- The compiled query states of `p` laid out from `b` with exit `e`. -/
def oquery : OProg → ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | act _, _, _ => fun _ => none
  | qbit, _, _ => fun _ => none
  | ask p q, b, e => fun st =>
      if st = b then some (b + 1, b + 1 + p.size)
      else if st < b + 1 + p.size then oquery p (b + 1) e st
      else oquery q (b + 1 + p.size) e st
  | seq p q, b, e => fun st =>
      if st < b + p.size then oquery p b (b + p.size) st
      else oquery q (b + p.size) e st
  | ite _ p q, b, e => fun st =>
      if st = b then none
      else if st < b + 1 + p.size then oquery p (b + 1) e st
      else oquery q (b + 1 + p.size) e st
  | loop _ p, b, _ => fun st =>
      if st = b then none
      else oquery p (b + 1) b st

theorem odelta_length_le : ∀ (p : OProg) (b e q : ℕ) (a : Option Bool) (w : Bool),
    (odelta p b e q a w).length ≤ 1
  | act f, b, e, q, a, w => by unfold odelta; split <;> simp
  | qbit, b, e, q, a, w => by unfold odelta; split <;> simp
  | ask p r, b, e, q, a, w => by
      unfold odelta; split
      · simp
      · split
        · exact odelta_length_le p _ _ _ _ _
        · exact odelta_length_le r _ _ _ _ _
  | seq p r, b, e, q, a, w => by
      unfold odelta; split
      · exact odelta_length_le p _ _ _ _ _
      · exact odelta_length_le r _ _ _ _ _
  | ite t p r, b, e, q, a, w => by
      unfold odelta; split
      · simp
      · split
        · exact odelta_length_le p _ _ _ _ _
        · exact odelta_length_le r _ _ _ _ _
  | loop t p, b, e, q, a, w => by
      unfold odelta; split
      · simp
      · exact odelta_length_le p _ _ _ _ _

theorem odelta_target : ∀ (p : OProg) (b e q : ℕ) (a : Option Bool) (w : Bool),
    ∀ i ∈ odelta p b e q a w, (b ≤ i.1 ∧ i.1 < b + p.size) ∨ i.1 = e
  | act f, b, e, q, a, w => by
      intro i hi; unfold odelta at hi; split at hi <;> simp_all
  | qbit, b, e, q, a, w => by
      intro i hi; unfold odelta at hi; split at hi <;> simp_all
  | ask p r, b, e, q, a, w => by
      have := size_pos p; have := size_pos r
      intro i hi; unfold odelta at hi; simp only [size]; split at hi
      · simp at hi
      · split at hi
        · rcases odelta_target p _ _ _ _ _ i hi with h | h <;> omega
        · rcases odelta_target r _ _ _ _ _ i hi with h | h <;> omega
  | seq p r, b, e, q, a, w => by
      have := size_pos r
      intro i hi; unfold odelta at hi; simp only [size]; split at hi
      · rcases odelta_target p _ _ _ _ _ i hi with h | h <;> omega
      · rcases odelta_target r _ _ _ _ _ i hi with h | h <;> omega
  | ite t p r, b, e, q, a, w => by
      have := size_pos p; have := size_pos r
      intro i hi; unfold odelta at hi; simp only [size]; split at hi
      · simp only [List.mem_singleton] at hi; subst hi; split <;> simp <;> omega
      · split at hi
        · rcases odelta_target p _ _ _ _ _ i hi with h | h <;> omega
        · rcases odelta_target r _ _ _ _ _ i hi with h | h <;> omega
  | loop t p, b, e, q, a, w => by
      have := size_pos p
      intro i hi; unfold odelta at hi; simp only [size]; split at hi
      · simp only [List.mem_singleton] at hi; subst hi; split
        · simp; omega
        · simp
      · rcases odelta_target p _ _ _ _ _ i hi with h | h <;> omega

theorem oquery_target : ∀ (p : OProg) (b e q : ℕ) (r : ℕ × ℕ), oquery p b e q = some r →
    ((b ≤ r.1 ∧ r.1 < b + p.size) ∨ r.1 = e) ∧ ((b ≤ r.2 ∧ r.2 < b + p.size) ∨ r.2 = e)
  | act _, b, e, q, r => by intro h; simp [oquery] at h
  | qbit, b, e, q, r => by intro h; simp [oquery] at h
  | ask p s, b, e, q, r => by
      have := size_pos p; have := size_pos s
      intro h; unfold oquery at h; simp only [size]; split at h
      · simp only [Option.some.injEq] at h; subst h; simp; omega
      · split at h
        · have := oquery_target p _ _ _ _ h; omega
        · have := oquery_target s _ _ _ _ h; omega
  | seq p s, b, e, q, r => by
      have := size_pos s
      intro h; unfold oquery at h; simp only [size]; split at h
      · have := oquery_target p _ _ _ _ h; omega
      · have := oquery_target s _ _ _ _ h; omega
  | ite _ p s, b, e, q, r => by
      have := size_pos p; have := size_pos s
      intro h; unfold oquery at h; simp only [size]; split at h
      · simp at h
      · split at h
        · have := oquery_target p _ _ _ _ h; omega
        · have := oquery_target s _ _ _ _ h; omega
  | loop _ p, b, e, q, r => by
      have := size_pos p
      intro h; unfold oquery at h; simp only [size]; split at h
      · simp at h
      · have := oquery_target p _ _ _ _ h; omega

/-! ### Compiler correctness -/

/-- An oracle machine *hosts* `p` at base `b` with exit `e` when its tables agree with the
compiled ones on the program's states. -/
def Hosts (M : OMachine) (p : OProg) (b e : ℕ) : Prop :=
  ∀ q, b ≤ q → q < b + p.size →
    M.query q = oquery p b e q ∧ ∀ a w, M.delta q a w = odelta p b e q a w

/-- A run of an oracle machine all of whose configurations before the last satisfy `P`. -/
inductive OPath (M : OMachine) (A : Oracle) (x : List Bool) (P : OConfig → Prop) :
    OConfig → OConfig → Prop
  | refl (c : OConfig) : OPath M A x P c c
  | head {c d e : OConfig} (hc : P c) (hs : M.Step A x c d) (hr : OPath M A x P d e) :
      OPath M A x P c e

namespace OPath

variable {M : OMachine} {A : Oracle} {x : List Bool} {P : OConfig → Prop}

theorem trans {a b c : OConfig} (h₁ : OPath M A x P a b) (h₂ : OPath M A x P b c) :
    OPath M A x P a c := by
  induction h₁ with
  | refl => exact h₂
  | head hc hs _ ih => exact .head hc hs (ih h₂)

theorem single {a b : OConfig} (ha : P a) (h : M.Step A x a b) : OPath M A x P a b :=
  .head ha h (.refl b)

theorem mono {Q : OConfig → Prop} (hPQ : ∀ c, P c → Q c) {a b : OConfig}
    (h : OPath M A x P a b) : OPath M A x Q a b := by
  induction h with
  | refl => exact .refl _
  | head hc hs _ ih => exact .head (hPQ _ hc) hs ih

end OPath

theorem ostep_of_delta {M : OMachine} {A : Oracle} {x : List Bool} {c : OConfig} {i : OInstr}
    (hq : M.query c.state = none) (h : M.delta c.state (ordIn x c) (ordW c) = [i]) :
    M.Step A x c ((oeff x c (i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2)).at i.1) := by
  unfold OMachine.Step OMachine.stepList
  unfold ordIn ordW at h
  rw [hq]
  simp only [h, List.map_cons, List.map_nil, List.mem_singleton]
  rcases i with ⟨q, b, o, d1, d2⟩
  cases o <;> rfl

theorem ostep_of_query {M : OMachine} {A : Oracle} {x : List Bool} {c : OConfig} {qy qn : ℕ}
    (hq : M.query c.state = some (qy, qn)) :
    M.Step A x c (({ c with qtape := [] } : OConfig).at (if A c.qtape then qy else qn)) := by
  unfold OMachine.Step OMachine.stepList
  rw [hq]
  simp only [List.mem_singleton]
  rfl

theorem oexec_state {A : Oracle} {x : List Bool} {P : OConfig → Prop} {p : OProg}
    {c c' : OConfig} (h : OExec A x P p c c') (hc : c.state = 0) : c'.state = 0 := by
  induction h with
  | act => rfl
  | qbit => rfl
  | askT _ _ _ ih => exact ih hc
  | askF _ _ _ ih => exact ih hc
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hc)
  | iteT _ _ _ ih => exact ih rfl
  | iteF _ _ _ ih => exact ih rfl
  | loopT _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ rfl)
  | loopF => rfl

/-- The states of the program at the head of a hosted program. -/
theorem Hosts.at_base {M : OMachine} {p : OProg} {b e : ℕ} (h : Hosts M p b e) :
    M.query b = oquery p b e b ∧ ∀ a w, M.delta b a w = odelta p b e b a w :=
  h b le_rfl (by have := size_pos p; omega)

theorem Hosts.ask_left {M : OMachine} {p q : OProg} {b e : ℕ} (h : Hosts M (ask p q) b e) :
    Hosts M p (b + 1) e := by
  intro st h1 h2
  obtain ⟨hq, hd⟩ := h st (by omega) (by simp only [size]; omega)
  refine ⟨?_, fun a w => ?_⟩
  · rw [hq]; simp only [oquery, if_neg (show st ≠ b by omega), if_pos h2]
  · rw [hd]; simp only [odelta, if_neg (show st ≠ b by omega), if_pos h2]

theorem Hosts.ask_right {M : OMachine} {p q : OProg} {b e : ℕ} (h : Hosts M (ask p q) b e) :
    Hosts M q (b + 1 + p.size) e := by
  intro st h1 h2
  obtain ⟨hq, hd⟩ := h st (by omega) (by simp only [size]; omega)
  refine ⟨?_, fun a w => ?_⟩
  · rw [hq]; simp only [oquery, if_neg (show st ≠ b by omega),
      if_neg (show ¬ st < b + 1 + p.size by omega)]
  · rw [hd]; simp only [odelta, if_neg (show st ≠ b by omega),
      if_neg (show ¬ st < b + 1 + p.size by omega)]

theorem Hosts.seq_left {M : OMachine} {p q : OProg} {b e : ℕ} (h : Hosts M (seq p q) b e) :
    Hosts M p b (b + p.size) := by
  intro st h1 h2
  obtain ⟨hq, hd⟩ := h st h1 (by simp only [size]; omega)
  refine ⟨?_, fun a w => ?_⟩
  · rw [hq]; simp only [oquery, if_pos h2]
  · rw [hd]; simp only [odelta, if_pos h2]

theorem Hosts.seq_right {M : OMachine} {p q : OProg} {b e : ℕ} (h : Hosts M (seq p q) b e) :
    Hosts M q (b + p.size) e := by
  intro st h1 h2
  obtain ⟨hq, hd⟩ := h st (by omega) (by simp only [size]; omega)
  refine ⟨?_, fun a w => ?_⟩
  · rw [hq]; simp only [oquery, if_neg (show ¬ st < b + p.size by omega)]
  · rw [hd]; simp only [odelta, if_neg (show ¬ st < b + p.size by omega)]

theorem Hosts.ite_left {M : OMachine} {t : Test} {p q : OProg} {b e : ℕ}
    (h : Hosts M (ite t p q) b e) : Hosts M p (b + 1) e := by
  intro st h1 h2
  obtain ⟨hq, hd⟩ := h st (by omega) (by simp only [size]; omega)
  refine ⟨?_, fun a w => ?_⟩
  · rw [hq]; simp only [oquery, if_neg (show st ≠ b by omega), if_pos h2]
  · rw [hd]; simp only [odelta, if_neg (show st ≠ b by omega), if_pos h2]

theorem Hosts.ite_right {M : OMachine} {t : Test} {p q : OProg} {b e : ℕ}
    (h : Hosts M (ite t p q) b e) : Hosts M q (b + 1 + p.size) e := by
  intro st h1 h2
  obtain ⟨hq, hd⟩ := h st (by omega) (by simp only [size]; omega)
  refine ⟨?_, fun a w => ?_⟩
  · rw [hq]; simp only [oquery, if_neg (show st ≠ b by omega),
      if_neg (show ¬ st < b + 1 + p.size by omega)]
  · rw [hd]; simp only [odelta, if_neg (show st ≠ b by omega),
      if_neg (show ¬ st < b + 1 + p.size by omega)]

theorem Hosts.loop_body {M : OMachine} {t : Test} {p : OProg} {b e : ℕ}
    (h : Hosts M (loop t p) b e) : Hosts M p (b + 1) b := by
  intro st h1 h2
  obtain ⟨hq, hd⟩ := h st (by omega) (by simp only [size]; omega)
  refine ⟨?_, fun a w => ?_⟩
  · rw [hq]; simp only [oquery, if_neg (show st ≠ b by omega)]
  · rw [hd]; simp only [odelta, if_neg (show st ≠ b by omega)]

/-- **Compiler correctness.** -/
theorem opath_of_oexec {M : OMachine} {A : Oracle} {x : List Bool} {P : OConfig → Prop}
    {p : OProg} {c c' : OConfig} (h : OExec A x P p c c') : c.state = 0 → ∀ {b e : ℕ},
      Hosts M p b e →
      OPath M A x (fun d => P (d.at 0) ∧ b ≤ d.state ∧ d.state < b + p.size) (c.at b)
        (c'.at e) := by
  induction h with
  | @act f c hc =>
      intro hc0 b e hM
      obtain ⟨hq, hd⟩ := hM.at_base
      have hd' : M.delta (c.at b).state (ordIn x (c.at b)) (ordW (c.at b)) =
          [(e, (f (ordIn x c) (ordW c)).1, none, (f (ordIn x c) (ordW c)).2.1,
            (f (ordIn x c) (ordW c)).2.2)] := by
        rw [OConfig.at_state, hd]; simp [odelta]
      have hq' : M.query (c.at b).state = none := by rw [OConfig.at_state, hq]; rfl
      refine OPath.single ⟨?_, le_rfl, by simp [size]⟩ (ostep_of_delta hq' hd')
      rw [OConfig.at_at, ← hc0]
      exact hc
  | @qbit c hc =>
      intro hc0 b e hM
      obtain ⟨hq, hd⟩ := hM.at_base
      have hd' : M.delta (c.at b).state (ordIn x (c.at b)) (ordW (c.at b)) =
          [(e, ordW c, some (ordW c), .stay, .stay)] := by
        rw [OConfig.at_state, hd]; simp [odelta]
      have hq' : M.query (c.at b).state = none := by rw [OConfig.at_state, hq]; rfl
      refine OPath.single ⟨?_, le_rfl, by simp [size]⟩ (ostep_of_delta hq' hd')
      rw [OConfig.at_at, ← hc0]
      exact hc
  | @askT p q c e hc hA hp ihp =>
      intro hc0 b e' hM
      obtain ⟨hq, -⟩ := hM.at_base
      have hq' : M.query (c.at b).state = some (b + 1, b + 1 + p.size) := by
        rw [OConfig.at_state, hq]; simp [oquery]
      have hs := ostep_of_query (A := A) (x := x) hq'
      simp only [OConfig.at_qtape, hA, if_true] at hs
      refine OPath.head ⟨?_, le_rfl, by simp only [OConfig.at_state, size]; omega⟩ hs
        ((ihp hc0 hM.ask_left).mono ?_)
      · rw [OConfig.at_at, ← hc0]; exact hc
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩
  | @askF p q c e hc hA hq ihq =>
      intro hc0 b e' hM
      obtain ⟨hqq, -⟩ := hM.at_base
      have hq' : M.query (c.at b).state = some (b + 1, b + 1 + p.size) := by
        rw [OConfig.at_state, hqq]; simp [oquery]
      have hs := ostep_of_query (A := A) (x := x) hq'
      simp only [OConfig.at_qtape, hA, Bool.false_eq_true, if_false] at hs
      refine OPath.head ⟨?_, le_rfl, by simp only [OConfig.at_state, size]; omega⟩ hs
        ((ihq hc0 hM.ask_right).mono ?_)
      · rw [OConfig.at_at, ← hc0]; exact hc
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩
  | @seq p q c d e hp hq ihp ihq =>
      intro hc0 b e' hM
      refine OPath.trans ((ihp hc0 hM.seq_left).mono ?_)
        ((ihq (oexec_state hp hc0) hM.seq_right).mono ?_)
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, h2, by simp only [size]; omega⟩
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩
  | @iteT t p q c e hc ht hp ihp =>
      intro hc0 b e' hM
      obtain ⟨hq, hd⟩ := hM.at_base
      have hd' : M.delta (c.at b).state (ordIn x (c.at b)) (ordW (c.at b)) =
          [(b + 1, ordW c, none, .stay, .stay)] := by
        rw [OConfig.at_state, hd]; simp [odelta, ht]
      have hq' : M.query (c.at b).state = none := by rw [OConfig.at_state, hq]; simp [oquery]
      refine OPath.head ⟨?_, le_rfl, by simp only [OConfig.at_state, size]; omega⟩
        (ostep_of_delta hq' hd') ((ihp rfl hM.ite_left).mono ?_)
      · rw [OConfig.at_at, ← hc0]; exact hc
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩
  | @iteF t p q c e hc ht hq ihq =>
      intro hc0 b e' hM
      obtain ⟨hqq, hd⟩ := hM.at_base
      have hd' : M.delta (c.at b).state (ordIn x (c.at b)) (ordW (c.at b)) =
          [(b + 1 + p.size, ordW c, none, .stay, .stay)] := by
        rw [OConfig.at_state, hd]; simp [odelta, ht]
      have hq' : M.query (c.at b).state = none := by rw [OConfig.at_state, hqq]; simp [oquery]
      refine OPath.head ⟨?_, le_rfl, by simp only [OConfig.at_state, size]; omega⟩
        (ostep_of_delta hq' hd') ((ihq rfl hM.ite_right).mono ?_)
      · rw [OConfig.at_at, ← hc0]; exact hc
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩
  | @loopT t p c d e hc ht hp hl ihp ihl =>
      intro hc0 b e' hM
      obtain ⟨hq, hd⟩ := hM.at_base
      have hd' : M.delta (c.at b).state (ordIn x (c.at b)) (ordW (c.at b)) =
          [(b + 1, ordW c, none, .stay, .stay)] := by
        rw [OConfig.at_state, hd]; simp [odelta, ht]
      have hq' : M.query (c.at b).state = none := by rw [OConfig.at_state, hq]; simp [oquery]
      refine OPath.head ⟨?_, le_rfl, by simp only [OConfig.at_state, size]; omega⟩
        (ostep_of_delta hq' hd')
        (OPath.trans ((ihp rfl hM.loop_body).mono ?_) (ihl (oexec_state hp rfl) hM))
      · rw [OConfig.at_at, ← hc0]; exact hc
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩
  | @loopF t p c hc ht =>
      intro hc0 b e' hM
      obtain ⟨hq, hd⟩ := hM.at_base
      have hd' : M.delta (c.at b).state (ordIn x (c.at b)) (ordW (c.at b)) =
          [(e', ordW c, none, .stay, .stay)] := by
        rw [OConfig.at_state, hd]; simp [odelta, ht]
      have hq' : M.query (c.at b).state = none := by rw [OConfig.at_state, hq]; simp [oquery]
      refine OPath.single ⟨?_, le_rfl, by simp only [OConfig.at_state, size]; omega⟩
        (ostep_of_delta hq' hd')
      rw [OConfig.at_at, ← hc0]; exact hc

/-! ### The machine of a program -/

/-- The oracle machine of `p`: the program on the states `0, …, size p - 1`, a test state
`size p` reading the bit under the work head, an accepting halting state `size p + 1` and a
rejecting halting state `size p + 2`. -/
def omachine (p : OProg) : OMachine where
  states := p.size + 3
  accept q := decide (q = p.size + 1)
  query q := if q < p.size then oquery p 0 p.size q else none
  delta q a w :=
    if q < p.size then odelta p 0 p.size q a w
    else if q = p.size then [(if w then p.size + 1 else p.size + 2, w, none, .stay, .stay)]
    else []

theorem omachine_hosts (p : OProg) : Hosts p.omachine p 0 p.size := by
  intro q _ hq
  simp only [zero_add] at hq
  refine ⟨?_, fun a w => ?_⟩
  · simp only [omachine, if_pos hq]
  · simp only [omachine, if_pos hq]

theorem omachine_wellFormed (p : OProg) : p.omachine.WellFormed := by
  refine ⟨by simp [omachine], ?_, ?_⟩
  · intro q a w i hi
    simp only [omachine] at hi ⊢
    split at hi
    · rcases odelta_target p 0 p.size q a w i hi with h | h <;> omega
    · split at hi
      · simp only [List.mem_singleton] at hi; subst hi; split <;> simp
      · simp at hi
  · intro q r hr
    simp only [omachine] at hr ⊢
    split at hr
    · have := oquery_target p 0 p.size q r hr; omega
    · simp at hr

theorem omachine_deterministic (p : OProg) : p.omachine.Deterministic := by
  intro q a w
  simp only [omachine]
  split
  · exact odelta_length_le _ _ _ _ _ _
  · split <;> simp

/-! ### Deterministic runs -/

theorem step_unique {M : OMachine} (hdet : M.Deterministic) {A : Oracle} {x : List Bool}
    {c d d' : OConfig} (h : M.Step A x c d) (h' : M.Step A x c d') : d = d' := by
  unfold OMachine.Step OMachine.stepList at h h'
  cases hq : M.query c.state with
  | some r =>
      rcases r with ⟨qy, qn⟩
      rw [hq] at h h'
      simp only [List.mem_singleton] at h h'
      rw [h, h']
  | none =>
      rw [hq] at h h'
      have hl := hdet c.state x[c.inHead]? (c.tape.getD c.wHead false)
      generalize M.delta c.state x[c.inHead]? (c.tape.getD c.wHead false) = l at h h' hl
      match l, hl with
      | [], _ => simp at h
      | [i], _ =>
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at h h'
          rw [h, h']

theorem OPath.exists_steps {M : OMachine} {A : Oracle} {x : List Bool} {P : OConfig → Prop}
    {a b : OConfig} (h : OPath M A x P a b) : ∃ n, Reach.steps (M.Step A x) n a b := by
  induction h with
  | refl c => exact ⟨0, rfl⟩
  | @head c d e _ hs _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨1 + n, (Reach.steps_add _ 1 n c e).2 ⟨d, (Reach.steps_one _ _ _).2 hs, hn⟩⟩

/-- In a deterministic machine, everything reachable from the start of a path ending in a halting
configuration lies on the path. -/
theorem reach_on_path {M : OMachine} (hdet : M.Deterministic) {A : Oracle} {x : List Bool}
    {Q : OConfig → Prop} {b : OConfig} (hb : M.stepList A x b = []) :
    ∀ (n : ℕ) (a c : OConfig), OPath M A x Q a b → Reach.steps (M.Step A x) n a c →
      Q c ∨ c = b := by
  intro n
  induction n with
  | zero =>
      intro a c hp hs
      cases hs
      cases hp with
      | refl => exact Or.inr rfl
      | head hc _ _ => exact Or.inl hc
  | succ n ih =>
      intro a c hp hs
      rw [add_comm] at hs
      obtain ⟨m, hm, hmc⟩ := (Reach.steps_add _ 1 n a c).1 hs
      have hm' := (Reach.steps_one _ _ _).1 hm
      cases hp with
      | refl =>
          exfalso
          unfold OMachine.Step at hm'
          rw [hb] at hm'
          simp at hm'
      | head _ hs' hr =>
          rw [step_unique hdet hm' hs'] at hmc
          exact ih _ _ hr hmc

theorem ospace_otouch (x : List Bool) (c : OConfig) : (otouch x c).space = c.space := by
  simp only [otouch, oeff, OConfig.space, writeAt_length, moveWork]
  omega

/-- **Membership in `DSPACE^A` from an execution.**  If on every input `x` the program `p` runs
with the oracle `A` from the initial configuration, within `B x ≤ s |x|` cells (work tape and query
tape), to a configuration whose scanned bit is set exactly when `x ∈ L`, then `L ∈ DSPACE^A s`. -/
theorem odspace_of_oexec (A : Oracle) (p : OProg) (L : Language) (B : List Bool → ℕ)
    (s : ℕ → ℕ) (out : List Bool → OConfig) (hBs : ∀ x, B x ≤ s x.length)
    (hrun : ∀ x, OExec A x (fun c => c.space ≤ B x) p oinit (out x))
    (hspace : ∀ x, (out x).space ≤ B x)
    (hout : ∀ x, ordW (out x) = true ↔ L x) : ODSPACE A s L := by
  set M := p.omachine with hM
  have hdet := omachine_deterministic p
  -- the final configuration and the whole run
  let fin : List Bool → OConfig := fun x =>
    (otouch x (out x)).at (if ordW (out x) then p.size + 1 else p.size + 2)
  have hfin_halt : ∀ x, M.stepList A x (fin x) = [] := by
    intro x
    have h1 : ¬ (fin x).state < p.size := by
      simp only [fin, OConfig.at_state]; split <;> omega
    have h2 : (fin x).state ≠ p.size := by
      simp only [fin, OConfig.at_state]; split <;> omega
    simp only [OMachine.stepList, hM, omachine, if_neg h1, if_neg h2, List.map_nil]
  have hpath : ∀ x, OPath M A x (fun d => d.space ≤ B x ∧ d.state ≤ p.size) oinit (fin x) := by
    intro x
    have h := opath_of_oexec (hrun x) rfl (omachine_hosts p)
    have h' : OPath M A x (fun d => d.space ≤ B x ∧ d.state ≤ p.size) (oinit.at 0)
        ((out x).at p.size) := by
      refine h.mono ?_
      rintro d ⟨h1, h2, h3⟩
      exact ⟨by simpa using h1, by omega⟩
    refine h'.trans (OPath.single ⟨by simpa using hspace x, le_rfl⟩ ?_)
    have hq : M.query ((out x).at p.size).state = none := by
      simp [hM, omachine]
    have hd : M.delta ((out x).at p.size).state (ordIn x ((out x).at p.size))
        (ordW ((out x).at p.size)) =
        [(if ordW (out x) then p.size + 1 else p.size + 2, ordW (out x), none, .stay, .stay)] := by
      simp [hM, omachine]
    have := ostep_of_delta (A := A) hq hd
    simpa [fin, otouch] using this
  have hreach : ∀ x n c, Reach.steps (M.Step A x) n oinit c →
      (c.space ≤ B x ∧ c.state ≤ p.size) ∨ c = fin x :=
    fun x n c hc => reach_on_path hdet (hfin_halt x) n oinit c (hpath x) hc
  refine ⟨M, omachine_wellFormed p, hdet, ?_, ?_⟩
  · intro x n c hc
    rcases hreach x n c hc with h | h
    · exact le_trans h.1 (hBs x)
    · subst h
      simp only [fin, OConfig.at_space, ospace_otouch]
      exact le_trans (hspace x) (hBs x)
  · intro x
    rw [← hout x]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := (hpath x).exists_steps
      refine ⟨n, fin x, hn, ?_⟩
      simp [fin, hM, omachine, hx]
    · rintro ⟨n, c, hc, hacc⟩
      rcases hreach x n c hc with h | h
      · simp only [hM, omachine, decide_eq_true_eq] at hacc; omega
      · subst h
        by_contra hne
        simp only [Bool.not_eq_true] at hne
        simp [fin, hM, omachine, hne] at hacc

end OProg

end Complexity.Space
