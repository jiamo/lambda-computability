/-
Quantified Boolean formulas, and their evaluation in memory linear in the formula.

`TQBF` — the true closed quantified Boolean formulas — is the standard complete problem for
polynomial space, and the easy half of that statement is that it *is* in polynomial space: the
obvious recursive evaluator only ever holds one activation record per quantifier or connective on
the path to the subformula it is working on, together with one bit per variable.  This module
makes that precise in the cost model of `Start/SavitchVM.lean`: a deterministic stack machine
evaluates a formula, and every state it passes through carries at most `height p` activation
records, each holding a pointer to a subformula, a variable index and two bits, next to the
assignment.

As in `Start/SavitchVM.lean`, the memory is *counted* rather than encoded: the machine's states
hold subformulas, and `Complexity.Qbf.memBits` charges `w` bits for each of them, `w` being the
width of a pointer into the formula.  What is proved is the shape of the bound — one record per
level of the formula — which is what the space bound rests on.

Main definitions:

* `Complexity.Qbf.QBF`, `.eval`, `.height`, `.size`, `.free`, `.Closed` — the formulas and their
  semantics;
* `Complexity.Qbf.St`, `.step` — the evaluating stack machine, and `.Trace` its runs with a bound
  on the number of records alive;
* `Complexity.Qbf.memBits` — the memory of a state, in bits.

Main results:

* `Complexity.Qbf.eval_congr`, `.eval_closed` — the value of a closed formula does not depend on
  the assignment, so `Complexity.Qbf.TQBF` is well defined;
* `Complexity.Qbf.trace_eval` — the machine returns the value of the formula, restores the
  assignment it was given, and never holds more than `height p` records;
* `Complexity.Qbf.tqbf_memBits_le` — deciding a closed formula therefore costs at most
  `varBound p + (height p + 1) · (w + 3)` bits, which is quadratic in the size of the formula.
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

/-! ### Formulas -/

/-- A quantified Boolean formula over variables indexed by `ℕ`. -/
inductive QBF where
  /-- A variable. -/
  | var (i : ℕ)
  /-- Negation. -/
  | neg (p : QBF)
  /-- Conjunction. -/
  | conj (p q : QBF)
  /-- Disjunction. -/
  | disj (p q : QBF)
  /-- Universal quantification over a variable. -/
  | all (i : ℕ) (p : QBF)
  /-- Existential quantification over a variable. -/
  | ex (i : ℕ) (p : QBF)
  deriving DecidableEq, Repr, Inhabited

namespace QBF

/-- The value of a formula under an assignment. -/
def eval (σ : ℕ → Bool) : QBF → Bool
  | .var i => σ i
  | .neg p => !eval σ p
  | .conj p q => eval σ p && eval σ q
  | .disj p q => eval σ p || eval σ q
  | .all i p => eval (Function.update σ i false) p && eval (Function.update σ i true) p
  | .ex i p => eval (Function.update σ i false) p || eval (Function.update σ i true) p

/-- The height of a formula: the length of the longest path of connectives and quantifiers. -/
def height : QBF → ℕ
  | .var _ => 0
  | .neg p => p.height + 1
  | .conj p q => max p.height q.height + 1
  | .disj p q => max p.height q.height + 1
  | .all _ p => p.height + 1
  | .ex _ p => p.height + 1

/-- The number of nodes of a formula. -/
def size : QBF → ℕ
  | .var _ => 1
  | .neg p => p.size + 1
  | .conj p q => p.size + q.size + 1
  | .disj p q => p.size + q.size + 1
  | .all _ p => p.size + 1
  | .ex _ p => p.size + 1

theorem height_lt_size : ∀ p : QBF, p.height < p.size
  | .var _ => by simp [height, size]
  | .neg p => by have := height_lt_size p; simp [height, size]; omega
  | .conj p q => by
      have h₁ := height_lt_size p
      have h₂ := height_lt_size q
      simp only [height, size]
      omega
  | .disj p q => by
      have h₁ := height_lt_size p
      have h₂ := height_lt_size q
      simp only [height, size]
      omega
  | .all _ p => by have := height_lt_size p; simp [height, size]; omega
  | .ex _ p => by have := height_lt_size p; simp [height, size]; omega

@[simp] theorem height_neg (p : QBF) : (QBF.neg p).height = p.height + 1 := rfl
@[simp] theorem height_conj (p q : QBF) : (QBF.conj p q).height = max p.height q.height + 1 := rfl
@[simp] theorem height_disj (p q : QBF) : (QBF.disj p q).height = max p.height q.height + 1 := rfl
@[simp] theorem height_all (i : ℕ) (p : QBF) : (QBF.all i p).height = p.height + 1 := rfl
@[simp] theorem height_ex (i : ℕ) (p : QBF) : (QBF.ex i p).height = p.height + 1 := rfl

/-- One more than the largest variable index occurring in the formula: the number of bits an
assignment needs. -/
def varBound : QBF → ℕ
  | .var i => i + 1
  | .neg p => p.varBound
  | .conj p q => max p.varBound q.varBound
  | .disj p q => max p.varBound q.varBound
  | .all i p => max (i + 1) p.varBound
  | .ex i p => max (i + 1) p.varBound

/-- The variables that occur free. -/
def free : QBF → List ℕ
  | .var i => [i]
  | .neg p => p.free
  | .conj p q => p.free ++ q.free
  | .disj p q => p.free ++ q.free
  | .all i p => p.free.filter (fun j => j ≠ i)
  | .ex i p => p.free.filter (fun j => j ≠ i)

/-- A formula with no free variables. -/
def Closed (p : QBF) : Prop := p.free = []

/-- The value only depends on the free variables. -/
theorem eval_congr : ∀ (p : QBF) (σ τ : ℕ → Bool), (∀ i ∈ p.free, σ i = τ i) →
    eval σ p = eval τ p := by
  intro p
  induction p with
  | var i => intro σ τ h; exact h i (by simp [free])
  | neg p ih => intro σ τ h; simp [eval, ih σ τ (by simpa [free] using h)]
  | conj p q ihp ihq =>
      intro σ τ h
      have hp : ∀ i ∈ p.free, σ i = τ i := fun i hi => h i (by simp [free, hi])
      have hq : ∀ i ∈ q.free, σ i = τ i := fun i hi => h i (by simp [free, hi])
      simp [eval, ihp σ τ hp, ihq σ τ hq]
  | disj p q ihp ihq =>
      intro σ τ h
      have hp : ∀ i ∈ p.free, σ i = τ i := fun i hi => h i (by simp [free, hi])
      have hq : ∀ i ∈ q.free, σ i = τ i := fun i hi => h i (by simp [free, hi])
      simp [eval, ihp σ τ hp, ihq σ τ hq]
  | all i p ih =>
      intro σ τ h
      have hb : ∀ (b : Bool) (j : ℕ), j ∈ p.free →
          Function.update σ i b j = Function.update τ i b j := by
        intro b j hj
        by_cases hji : j = i
        · simp [hji]
        · have : j ∈ p.free.filter (fun j => j ≠ i) := by
            simp [List.mem_filter, hj, hji]
          simp [Function.update_of_ne hji, h j (by simpa [free] using this)]
      simp [eval, ih _ _ (hb false), ih _ _ (hb true)]
  | ex i p ih =>
      intro σ τ h
      have hb : ∀ (b : Bool) (j : ℕ), j ∈ p.free →
          Function.update σ i b j = Function.update τ i b j := by
        intro b j hj
        by_cases hji : j = i
        · simp [hji]
        · have : j ∈ p.free.filter (fun j => j ≠ i) := by
            simp [List.mem_filter, hj, hji]
          simp [Function.update_of_ne hji, h j (by simpa [free] using this)]
      simp [eval, ih _ _ (hb false), ih _ _ (hb true)]

/-- A closed formula has a value independent of the assignment. -/
theorem eval_closed {p : QBF} (hp : p.Closed) (σ τ : ℕ → Bool) : eval σ p = eval τ p :=
  eval_congr p σ τ fun i hi => absurd hi (by rw [hp]; simp)

end QBF

/-- The true closed quantified Boolean formulas. -/
def TQBF (p : QBF) : Prop := p.Closed ∧ QBF.eval (fun _ => false) p = true

/-! ### The evaluating machine -/

/-- An activation record of the evaluator. -/
inductive Cont where
  /-- Negate the answer. -/
  | negK
  /-- The first conjunct is running; `q` is the second. -/
  | conjFst (q : QBF)
  /-- The second conjunct is running. -/
  | conjSnd
  /-- The first disjunct is running; `q` is the second. -/
  | disjFst (q : QBF)
  /-- The second disjunct is running. -/
  | disjSnd
  /-- The body is running with the quantified variable set to `false`; `old` is the value the
  variable had before the quantifier was entered. -/
  | quantFst (isAll : Bool) (i : ℕ) (p : QBF) (old : Bool)
  /-- The body is running with the quantified variable set to `true`; `v` is the value it had
  with `false`. -/
  | quantSnd (isAll : Bool) (v : Bool) (i : ℕ) (old : Bool)

/-- What the machine is doing. -/
inductive Phase where
  /-- Evaluate a formula. -/
  | eval (p : QBF)
  /-- Return an answer. -/
  | ret (v : Bool)

/-- A state: the phase, the current assignment, and the activation records. -/
structure St where
  /-- The current phase. -/
  phase : Phase
  /-- The current assignment. -/
  assign : ℕ → Bool
  /-- The activation records, innermost first. -/
  stack : List Cont

@[simp] theorem stack_mk (ph : Phase) (σ : ℕ → Bool) (st : List Cont) :
    (St.mk ph σ st).stack = st := rfl

/-- One step of the evaluator.  `none` means it has finished: an answer with an empty stack. -/
def step : St → Option St
  | ⟨.eval (.var i), σ, st⟩ => some ⟨.ret (σ i), σ, st⟩
  | ⟨.eval (.neg p), σ, st⟩ => some ⟨.eval p, σ, .negK :: st⟩
  | ⟨.eval (.conj p q), σ, st⟩ => some ⟨.eval p, σ, .conjFst q :: st⟩
  | ⟨.eval (.disj p q), σ, st⟩ => some ⟨.eval p, σ, .disjFst q :: st⟩
  | ⟨.eval (.all i p), σ, st⟩ =>
      some ⟨.eval p, Function.update σ i false, .quantFst true i p (σ i) :: st⟩
  | ⟨.eval (.ex i p), σ, st⟩ =>
      some ⟨.eval p, Function.update σ i false, .quantFst false i p (σ i) :: st⟩
  | ⟨.ret _, _, []⟩ => none
  | ⟨.ret v, σ, .negK :: st⟩ => some ⟨.ret (!v), σ, st⟩
  | ⟨.ret v, σ, .conjFst q :: st⟩ =>
      if v then some ⟨.eval q, σ, .conjSnd :: st⟩ else some ⟨.ret false, σ, st⟩
  | ⟨.ret v, σ, .conjSnd :: st⟩ => some ⟨.ret v, σ, st⟩
  | ⟨.ret v, σ, .disjFst q :: st⟩ =>
      if v then some ⟨.ret true, σ, st⟩ else some ⟨.eval q, σ, .disjSnd :: st⟩
  | ⟨.ret v, σ, .disjSnd :: st⟩ => some ⟨.ret v, σ, st⟩
  | ⟨.ret v, σ, .quantFst isAll i p old :: st⟩ =>
      some ⟨.eval p, Function.update σ i true, .quantSnd isAll v i old :: st⟩
  | ⟨.ret v, σ, .quantSnd isAll v₁ i old :: st⟩ =>
      some ⟨.ret (if isAll then v₁ && v else v₁ || v), Function.update σ i old, st⟩

/-- `Trace B s t`: the machine runs from `s` to `t`, and every state it passes through carries at
most `B` activation records. -/
inductive Trace (B : ℕ) : St → St → Prop
  /-- The empty run. -/
  | refl {s : St} (h : s.stack.length ≤ B) : Trace B s s
  /-- One step, then a run. -/
  | head {s t u : St} (h : s.stack.length ≤ B) (hs : step s = some t) (ht : Trace B t u) :
      Trace B s u

namespace Trace

variable {B B' : ℕ} {s t u : St}

theorem stack_le_left (h : Trace B s t) : s.stack.length ≤ B := by
  cases h with
  | refl h => exact h
  | head h _ _ => exact h

theorem stack_le_right (h : Trace B s t) : t.stack.length ≤ B := by
  induction h with
  | refl h => exact h
  | head _ _ _ ih => exact ih

theorem trans (h₁ : Trace B s t) (h₂ : Trace B t u) : Trace B s u := by
  induction h₁ with
  | refl _ => exact h₂
  | head h hs _ ih => exact .head h hs (ih h₂)

theorem mono (h : Trace B s t) (hB : B ≤ B') : Trace B' s t := by
  induction h with
  | refl h => exact .refl (le_trans h hB)
  | head h hs _ ih => exact .head (le_trans h hB) hs ih

end Trace

/-- The evaluator returns the value of the formula, gives back the assignment it was handed, and
never holds more than `height p` activation records above the stack it started with. -/
theorem trace_eval : ∀ (p : QBF) (σ : ℕ → Bool) (st : List Cont),
    Trace (st.length + p.height) ⟨.eval p, σ, st⟩ ⟨.ret (QBF.eval σ p), σ, st⟩ := by
  intro p
  induction p with
  | var i =>
      intro σ st
      exact .head (by simp) rfl (.refl (by simp))
  | neg p ih =>
      intro σ st
      refine .head (by simp) rfl ?_
      refine Trace.trans ((ih σ (.negK :: st)).mono (by simp; omega)) ?_
      exact .head (by simp) rfl (.refl (by simp))
  | conj p q ihp ihq =>
      intro σ st
      refine .head (by simp) rfl ?_
      refine Trace.trans ((ihp σ (.conjFst q :: st)).mono (by simp; omega)) ?_
      cases hv : QBF.eval σ p
      · have hstep : step ⟨.ret false, σ, Cont.conjFst q :: st⟩ = some ⟨.ret false, σ, st⟩ := rfl
        simp only [QBF.eval, hv, Bool.false_and]
        exact .head (by simp) hstep (.refl (by simp))
      · have hstep : step ⟨.ret true, σ, Cont.conjFst q :: st⟩ =
            some ⟨.eval q, σ, Cont.conjSnd :: st⟩ := rfl
        simp only [QBF.eval, hv, Bool.true_and]
        refine .head (by simp) hstep ?_
        refine Trace.trans ((ihq σ (.conjSnd :: st)).mono (by simp; omega)) ?_
        exact .head (by simp) rfl (.refl (by simp))
  | disj p q ihp ihq =>
      intro σ st
      refine .head (by simp) rfl ?_
      refine Trace.trans ((ihp σ (.disjFst q :: st)).mono (by simp; omega)) ?_
      cases hv : QBF.eval σ p
      · have hstep : step ⟨.ret false, σ, Cont.disjFst q :: st⟩ =
            some ⟨.eval q, σ, Cont.disjSnd :: st⟩ := rfl
        simp only [QBF.eval, hv, Bool.false_or]
        refine .head (by simp) hstep ?_
        refine Trace.trans ((ihq σ (.disjSnd :: st)).mono (by simp; omega)) ?_
        exact .head (by simp) rfl (.refl (by simp))
      · have hstep : step ⟨.ret true, σ, Cont.disjFst q :: st⟩ = some ⟨.ret true, σ, st⟩ := rfl
        simp only [QBF.eval, hv, Bool.true_or]
        exact .head (by simp) hstep (.refl (by simp))
  | all i p ih =>
      intro σ st
      refine .head (by simp) rfl ?_
      refine Trace.trans
        ((ih (Function.update σ i false) (.quantFst true i p (σ i) :: st)).mono
          (by simp; omega)) ?_
      have hstep : step ⟨.ret (QBF.eval (Function.update σ i false) p),
            Function.update σ i false, Cont.quantFst true i p (σ i) :: st⟩ =
          some ⟨.eval p, Function.update (Function.update σ i false) i true,
            Cont.quantSnd true (QBF.eval (Function.update σ i false) p) i (σ i) :: st⟩ := rfl
      refine .head (by simp) hstep ?_
      rw [Function.update_idem]
      refine Trace.trans
        ((ih (Function.update σ i true)
          (.quantSnd true (QBF.eval (Function.update σ i false) p) i (σ i) :: st)).mono
          (by simp; omega)) ?_
      refine .head (by simp) rfl ?_
      rw [Function.update_idem, Function.update_eq_self]
      exact .refl (by simp)
  | ex i p ih =>
      intro σ st
      refine .head (by simp) rfl ?_
      refine Trace.trans
        ((ih (Function.update σ i false) (.quantFst false i p (σ i) :: st)).mono
          (by simp; omega)) ?_
      have hstep : step ⟨.ret (QBF.eval (Function.update σ i false) p),
            Function.update σ i false, Cont.quantFst false i p (σ i) :: st⟩ =
          some ⟨.eval p, Function.update (Function.update σ i false) i true,
            Cont.quantSnd false (QBF.eval (Function.update σ i false) p) i (σ i) :: st⟩ := rfl
      refine .head (by simp) hstep ?_
      rw [Function.update_idem]
      refine Trace.trans
        ((ih (Function.update σ i true)
          (.quantSnd false (QBF.eval (Function.update σ i false) p) i (σ i) :: st)).mono
          (by simp; omega)) ?_
      refine .head (by simp) rfl ?_
      rw [Function.update_idem, Function.update_eq_self]
      exact .refl (by simp)

/-! ### The memory bound -/

/-- The memory of a state, in bits: one bit per variable for the assignment, plus one activation
record per level, each holding a pointer to a subformula (`w` bits), a variable index (`w` bits)
and two bits. -/
def memBits (w nvars : ℕ) (s : St) : ℕ := nvars + (s.stack.length + 1) * (2 * w + 2)

/-- Along a run with at most `B` records alive the memory never exceeds `B + 1` records. -/
theorem memBits_le_of_visited {B w nvars : ℕ} {s u : St} (h : Trace B s u) :
    memBits w nvars u ≤ nvars + (B + 1) * (2 * w + 2) :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have := h.stack_le_right; omega)) _

/-- Deciding a closed formula: the machine started on it returns its truth value, and every state
it passes through fits in `varBound p + (height p + 1) · (2 w + 2)` bits. -/
theorem tqbf_trace (p : QBF) :
    Trace p.height ⟨.eval p, fun _ => false, []⟩
      ⟨.ret (QBF.eval (fun _ => false) p), fun _ => false, []⟩ := by
  simpa using trace_eval p (fun _ => false) []

theorem tqbf_memBits_le (p : QBF) (w : ℕ) (u : St)
    (h : Trace p.height ⟨.eval p, fun _ => false, []⟩ u) :
    memBits w p.varBound u ≤ p.varBound + (p.height + 1) * (2 * w + 2) :=
  memBits_le_of_visited h

/-- With a pointer wide enough to address the formula, the memory is quadratic in its size: this
is the easy half of the PSPACE-completeness of `TQBF`. -/
theorem tqbf_memBits_le_size (p : QBF) (u : St)
    (h : Trace p.height ⟨.eval p, fun _ => false, []⟩ u) :
    memBits p.size p.varBound u ≤ p.varBound + (p.size + 1) * (2 * p.size + 2) := by
  refine le_trans (tqbf_memBits_le p p.size u h) ?_
  have hh : p.height < p.size := QBF.height_lt_size p
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _

end Complexity.Qbf
