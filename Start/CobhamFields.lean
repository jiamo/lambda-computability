/-
**Reading a list of unary fields off a parameter word.**

The emitter of `Start/CobhamRange.lean` passes a *parameter word* to the term that writes a block.
The blocks of the reduction of `Start/QbfWordStream.lean` need several numbers — a width, two block
indices, an offset — so the parameter has to carry a list of them.  This module fixes the format
and the accessors: a list of naturals is written as its members in unary, each terminated by a
zero bit (`Complexity.fieldsWord`), and `Complexity.Cob.fieldTerm k` reads the `k`-th of them.

Main definitions:

* `Complexity.fieldsWord` — a list of naturals as a word of unary fields;
* `Complexity.Cob.dropField`, `Complexity.Cob.fieldTerm` — skipping one field, and reading the
  `k`-th one.

Main results:

* `Complexity.lead1_fieldsWord`, `Complexity.drop1_fieldsWord` — the leading ones of the word are
  the first field, and dropping them uncovers the separator;
* `Complexity.Cob.eval_fieldTerm` — **reading the `k`-th unary field is a Cobham function**.
-/

import Mathlib
import Start.CobhamRange

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### The format -/

/-- A list of naturals written as unary fields, each terminated by a zero bit. -/
def fieldsWord : List ℕ → Word
  | [] => []
  | a :: as => List.replicate a true ++ [false] ++ fieldsWord as

@[simp] theorem lead1_replicate_append (a : ℕ) (w : Word) :
    lead1 (List.replicate a true ++ (false :: w)) = a := by
  induction a with
  | zero => simp [lead1]
  | succ a ih => rw [List.replicate_succ, List.cons_append, lead1, ih]

@[simp] theorem drop1_replicate_append (a : ℕ) (w : Word) :
    drop1 (List.replicate a true ++ (false :: w)) = false :: w := by
  induction a with
  | zero => simp [drop1]
  | succ a ih => rw [List.replicate_succ, List.cons_append, drop1, ih]

@[simp] theorem lead1_fieldsWord (a : ℕ) (as : List ℕ) :
    lead1 (fieldsWord (a :: as)) = a := by
  rw [fieldsWord]
  simp

@[simp] theorem drop1_fieldsWord (a : ℕ) (as : List ℕ) :
    drop1 (fieldsWord (a :: as)) = false :: fieldsWord as := by
  rw [fieldsWord]
  simp

/-! ### The accessors -/

/-- Skipping one unary field of the value of `t`. -/
def Cob.dropField (t : Cob) : Cob := .comp Cob.tail [.comp Cob.dropOnes [t]]

@[simp] theorem Cob.eval_dropField (t : Cob) (a : ℕ) (as : List ℕ) (args : List Word)
    (ht : t.eval args = fieldsWord (a :: as)) :
    (Cob.dropField t).eval args = fieldsWord as := by
  simp only [Cob.dropField, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_tail,
    Cob.eval_dropOnes, ht, drop1_fieldsWord, List.tail_cons]

/-- Reading the `k`-th unary field of the value of `t`. -/
def Cob.fieldTerm : ℕ → Cob → Cob
  | 0, t => .comp Cob.leadOnes [t]
  | k + 1, t => Cob.fieldTerm k (Cob.dropField t)

/-- **Reading the `k`-th unary field is a Cobham function.** -/
theorem Cob.eval_fieldTerm : ∀ (k : ℕ) (t : Cob) (as : List ℕ) (args : List Word),
    t.eval args = fieldsWord as → k < as.length →
    (Cob.fieldTerm k t).eval args = List.replicate (as.getD k 0) true := by
  intro k
  induction k with
  | zero =>
      intro t as args ht hk
      match as with
      | [] => simp at hk
      | a :: as =>
          simp only [Cob.fieldTerm, Cob.eval_comp, List.map_cons, List.map_nil,
            Cob.eval_leadOnes, ht, lead1_fieldsWord]
          rfl
  | succ k ih =>
      intro t as args ht hk
      match as with
      | [] => simp at hk
      | a :: as =>
          have ht' : (Cob.dropField t).eval args = fieldsWord as :=
            Cob.eval_dropField t a as args ht
          have hk' : k < as.length := by simpa using hk
          rw [Cob.fieldTerm, ih (Cob.dropField t) as args ht' hk']
          rfl

end Complexity
