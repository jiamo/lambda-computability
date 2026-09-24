/-
**Unary arithmetic, and the assembly of parameter words, with Cobham terms.**

The compiler of the reduction to `TQBF` carries its data — widths, offsets, head positions — as
*unary* words, and the pieces it composes expect their arguments as a `Complexity.fieldsWord`: a
list of unary fields separated by zero bits.  This module supplies the two things that composition
needs and that the toolkit did not have: the arithmetic of unary words (successor, predecessor,
sum, minimum) and the assembly of a parameter word from terms computing its fields.

Main definitions:

* `Complexity.Cob.uSucc`, `.uPred`, `.uAdd`, `.uMin` — unary arithmetic;
* `Complexity.Cob.fieldsT` — the parameter word assembled from the terms of its fields.

Main results:

* `Complexity.Cob.eval_uSucc`, `.eval_uPred`, `.eval_uAdd`, `.eval_uMin` — the arithmetic is
  correct;
* `Complexity.Cob.eval_fieldsT` — **a parameter word of unary fields is assembled by a Cobham
  term** from terms computing its fields.
-/

import Mathlib
import Start.CobhamCond
import Start.CobhamFields
import Start.CobhamTseitin

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Unary arithmetic -/

/-- The successor of a unary number. -/
def Cob.uSucc (t : Cob) : Cob := .comp (.app true) [t]

theorem Cob.eval_uSucc {t : Cob} {args : List Word} {k : ℕ}
    (ht : t.eval args = List.replicate k true) :
    (Cob.uSucc t).eval args = List.replicate (k + 1) true := by
  simp [Cob.uSucc, ht, List.replicate_succ]

/-- The predecessor of a unary number. -/
def Cob.uPred (t : Cob) : Cob := .comp Cob.tailC [t]

theorem Cob.eval_uPred {t : Cob} {args : List Word} {k : ℕ}
    (ht : t.eval args = List.replicate k true) :
    (Cob.uPred t).eval args = List.replicate (k - 1) true := by
  cases k with
  | zero => simp [Cob.uPred, ht]
  | succ k => simp [Cob.uPred, ht, List.replicate_succ]

/-- The sum of two unary numbers. -/
def Cob.uAdd (t u : Cob) : Cob := .comp Cob.concat [t, u]

theorem Cob.eval_uAdd {t u : Cob} {args : List Word} {k m : ℕ}
    (ht : t.eval args = List.replicate k true) (hu : u.eval args = List.replicate m true) :
    (Cob.uAdd t u).eval args = List.replicate (k + m) true := by
  simp only [Cob.uAdd, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, ht, hu]
  rw [List.replicate_add]

/-- The minimum of two unary numbers. -/
def Cob.uMin (t u : Cob) : Cob := Cob.iteT (Cob.ltU t u) t u

theorem Cob.eval_uMin {t u : Cob} {args : List Word} {k m : ℕ}
    (ht : t.eval args = List.replicate k true) (hu : u.eval args = List.replicate m true) :
    (Cob.uMin t u).eval args = List.replicate (min k m) true := by
  have hlt : (Cob.ltU t u).eval args = bw (decide (k < m)) := by
    rw [Cob.eval_ltU, ht, hu]
    simp
  rw [Cob.uMin, Cob.eval_iteW hlt ht hu]
  by_cases h : k < m
  · simp [h, Nat.min_eq_left (le_of_lt h)]
  · simp [h, Nat.min_eq_right (Nat.le_of_not_lt h)]

/-! ### Assembling a parameter word -/

/-- The parameter word whose fields are computed by the terms `ts`. -/
def Cob.fieldsT (ts : List Cob) : Cob :=
  Cob.catL (ts.flatMap fun t => [t, Cob.constT [false]])

theorem Cob.eval_fieldsT : ∀ {ts : List Cob} {as : List ℕ} {args : List Word},
    List.Forall₂ (fun (t : Cob) (a : ℕ) => t.eval args = List.replicate a true) ts as →
    (Cob.fieldsT ts).eval args = fieldsWord as := by
  intro ts
  induction ts with
  | nil =>
      intro as args h
      cases h
      simp [Cob.fieldsT, fieldsWord, Cob.eval_catL]
  | cons t ts ih =>
      intro as args h
      cases h with
      | cons h0 hrest =>
          rename_i a as'
          have hih := ih hrest
          have hcat : Cob.fieldsT (t :: ts)
              = Cob.catL ([t, Cob.constT [false]]
                  ++ (ts.flatMap fun u => [u, Cob.constT [false]])) := by
            simp [Cob.fieldsT]
          have hflat : (List.map (fun u : Cob => u.eval args)
              (ts.flatMap fun u => [u, Cob.constT [false]])).flatten = fieldsWord as' := by
            simpa [Cob.fieldsT, Cob.eval_catL] using hih
          rw [hcat]
          simp only [Cob.eval_catL, List.map_append, List.flatten_append, List.map_cons,
            List.map_nil, Cob.eval_constT, List.flatten_cons, List.flatten_nil, h0, hflat]
          simp [fieldsWord, List.append_assoc]

end Complexity
