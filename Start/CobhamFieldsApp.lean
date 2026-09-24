/-
**Parameter words that carry a word after their unary fields.**

`Start/CobhamFields.lean` reads the `k`-th unary field of a word of the shape
`Complexity.fieldsWord as`.  A compiler that sweeps a counter has only two arguments available
inside the sweep — the counter and one parameter word — so any further *word* it needs, in
particular the input of the machine being simulated, has to travel inside the parameter word as
well.  This module reads the fields of a parameter word of the shape `fieldsWord as ++ x`, and
recovers `x` itself by skipping the fields.

Main definitions:

* `Complexity.Cob.dropFieldsT` — skipping the first `k` unary fields.

Main results:

* `Complexity.Cob.eval_dropField_app`, `.eval_dropFieldsT` — skipping fields of a parameter word
  with a tail;
* `Complexity.Cob.eval_fieldTerm_app` — **the fields of such a parameter word are readable**;
* `Complexity.Cob.eval_tailWord` — **the appended word is recovered** by skipping every field.
-/

import Mathlib
import Start.CobhamFields

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

theorem fieldsWord_cons_append (a : ℕ) (as : List ℕ) (x : Word) :
    fieldsWord (a :: as) ++ x
      = List.replicate a true ++ (false :: (fieldsWord as ++ x)) := by
  simp [fieldsWord, List.append_assoc]

theorem Cob.eval_dropField_app (t : Cob) (a : ℕ) (as : List ℕ) (x : Word) (args : List Word)
    (ht : t.eval args = fieldsWord (a :: as) ++ x) :
    (Cob.dropField t).eval args = fieldsWord as ++ x := by
  rw [fieldsWord_cons_append] at ht
  simp only [Cob.dropField, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_tail,
    Cob.eval_dropOnes, ht, drop1_replicate_append, List.tail_cons]

/-- Skipping the first `k` unary fields of the value of `t`. -/
def Cob.dropFieldsT : ℕ → Cob → Cob
  | 0, t => t
  | k + 1, t => Cob.dropFieldsT k (Cob.dropField t)

theorem Cob.eval_dropFieldsT : ∀ (k : ℕ) (t : Cob) (as : List ℕ) (x : Word) (args : List Word),
    t.eval args = fieldsWord as ++ x → k ≤ as.length →
    (Cob.dropFieldsT k t).eval args = fieldsWord (as.drop k) ++ x := by
  intro k
  induction k with
  | zero =>
      intro t as x args ht _
      rw [Cob.dropFieldsT, List.drop_zero]
      exact ht
  | succ k ih =>
      intro t as x args ht hk
      match as with
      | [] => simp at hk
      | a :: as =>
          have ht' : (Cob.dropField t).eval args = fieldsWord as ++ x :=
            Cob.eval_dropField_app t a as x args ht
          have hk' : k ≤ as.length := by simpa using hk
          rw [Cob.dropFieldsT, ih (Cob.dropField t) as x args ht' hk']
          simp

/-- **Reading the `k`-th unary field of a parameter word that carries a word after its fields.** -/
theorem Cob.eval_fieldTerm_app : ∀ (k : ℕ) (t : Cob) (as : List ℕ) (x : Word) (args : List Word),
    t.eval args = fieldsWord as ++ x → k < as.length →
    (Cob.fieldTerm k t).eval args = List.replicate (as.getD k 0) true := by
  intro k
  induction k with
  | zero =>
      intro t as x args ht hk
      match as with
      | [] => simp at hk
      | a :: as =>
          rw [fieldsWord_cons_append] at ht
          simp only [Cob.fieldTerm, Cob.eval_comp, List.map_cons, List.map_nil,
            Cob.eval_leadOnes, ht, lead1_replicate_append]
          rfl
  | succ k ih =>
      intro t as x args ht hk
      match as with
      | [] => simp at hk
      | a :: as =>
          have ht' : (Cob.dropField t).eval args = fieldsWord as ++ x :=
            Cob.eval_dropField_app t a as x args ht
          have hk' : k < as.length := by simpa using hk
          rw [Cob.fieldTerm, ih (Cob.dropField t) as x args ht' hk']
          rfl

/-- **Recovering the word that a parameter word carries after its fields.** -/
theorem Cob.eval_tailWord (t : Cob) (as : List ℕ) (x : Word) (args : List Word)
    (ht : t.eval args = fieldsWord as ++ x) :
    (Cob.dropFieldsT as.length t).eval args = x := by
  have := Cob.eval_dropFieldsT as.length t as x args ht le_rfl
  simpa [fieldsWord] using this

end Complexity
