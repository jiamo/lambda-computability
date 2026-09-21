/-
**The block of one level of the midpoint recursion is written by a Cobham term.**

`Start/QbfWordStream.lean` writes the code of the reachability formula as one block
`Complexity.Qbf.QBF.reachPre m a b t` per level of the midpoint recursion.  This module writes
that block with a single Cobham term, by composing the terms of `Start/QbfCobPrefix.lean` (the
three quantifier prefixes over the scratch blocks) and of `Start/QbfCobEqBlock.lean` (the four
block equalities of the antecedent).

The parameter word of the level carries, in unary, the width `m` and the five products
`t·m`, `(t+1)·m`, `(t+2)·m`, `a·m`, `b·m` (`Complexity.Qbf.QBF.levelParam`): the multiplications
happen once, outside every sweep, and the pieces read the fields they need and assemble their own
parameter words.  The padding constants of the term do not depend on the instance, so one term
serves every level of every machine.

Main definitions:

* `Complexity.Qbf.QBF.levelParam` — the parameter word of a level;
* `Complexity.Qbf.QBF.prefixArg`, `Complexity.Qbf.QBF.eqArg` — the parameter words the pieces
  expect, assembled from the fields of the level;
* `Complexity.Qbf.QBF.levelTerm` — the term writing the block of a level.

Main results:

* `Complexity.Qbf.QBF.eval_prefixArg`, `Complexity.Qbf.QBF.eval_eqArg` — the assembled parameter
  words are the expected ones;
* `Complexity.Qbf.QBF.reachPre_eval` — **the block of a level is the value of one Cobham term at
  `1^m` and the parameter word of the level**.
-/

import Mathlib
import Start.QbfCobPrefix
import Start.QbfCobEqBlock

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

open Complexity

/-! ### The parameter word of a level -/

/-- The parameter word of a level of the recursion: the width and the five products of a block
index with the width, in unary. -/
def levelParam (m a b t : ℕ) : List Bool :=
  fieldsWord [m, t * m, (t + 1) * m, (t + 2) * m, a * m, b * m]

/-- The parameter word a quantifier prefix expects, assembled from the width and the field `k`. -/
def prefixArg (k : ℕ) : Cob :=
  Cob.catL [Cob.fieldTerm 0 (.proj 1), Cob.constT [false], Cob.fieldTerm k (.proj 1)]

/-- The parameter word a block equality expects, assembled from the width and the fields `ki`,
`kj`. -/
def eqArg (ki kj : ℕ) : Cob :=
  Cob.catL
    [Cob.fieldTerm 0 (.proj 1), Cob.constT [false], Cob.fieldTerm ki (.proj 1),
      Cob.constT [false], Cob.fieldTerm kj (.proj 1), Cob.constT [false]]

theorem eval_prefixArg (k : ℕ) (as : List ℕ) (hk : k < as.length) (h0 : 0 < as.length)
    (y : Word) :
    (prefixArg k).eval [y, fieldsWord as]
      = widthOffsetWord (as.getD 0 0) (as.getD k 0) := by
  have h0' : (Cob.fieldTerm 0 (Cob.proj 1)).eval [y, fieldsWord as]
      = List.replicate (as.getD 0 0) true :=
    Cob.eval_fieldTerm 0 (.proj 1) as _ (by simp) h0
  have hk' : (Cob.fieldTerm k (Cob.proj 1)).eval [y, fieldsWord as]
      = List.replicate (as.getD k 0) true :=
    Cob.eval_fieldTerm k (.proj 1) as _ (by simp) hk
  simp only [prefixArg, Cob.eval_catL, List.map_cons, List.map_nil, h0', hk', Cob.eval_constT,
    List.flatten_cons, List.flatten_nil, widthOffsetWord]
  simp [List.append_assoc]

theorem eval_eqArg (ki kj : ℕ) (as : List ℕ) (hki : ki < as.length) (hkj : kj < as.length)
    (h0 : 0 < as.length) (y : Word) :
    (eqArg ki kj).eval [y, fieldsWord as]
      = fieldsWord [as.getD 0 0, as.getD ki 0, as.getD kj 0] := by
  have h0' : (Cob.fieldTerm 0 (Cob.proj 1)).eval [y, fieldsWord as]
      = List.replicate (as.getD 0 0) true :=
    Cob.eval_fieldTerm 0 (.proj 1) as _ (by simp) h0
  have hi' : (Cob.fieldTerm ki (Cob.proj 1)).eval [y, fieldsWord as]
      = List.replicate (as.getD ki 0) true :=
    Cob.eval_fieldTerm ki (.proj 1) as _ (by simp) hki
  have hj' : (Cob.fieldTerm kj (Cob.proj 1)).eval [y, fieldsWord as]
      = List.replicate (as.getD kj 0) true :=
    Cob.eval_fieldTerm kj (.proj 1) as _ (by simp) hkj
  simp only [eqArg, Cob.eval_catL, List.map_cons, List.map_nil, h0', hi', hj', Cob.eval_constT,
    List.flatten_cons, List.flatten_nil, fieldsWord]
  simp [List.append_assoc]

/-! ### The term of a level -/

/-- One quantifier prefix of the level, run on the width with the parameter it expects. -/
def levelPrefix (tag : Word) (k : ℕ) : Cob :=
  .comp (quantPrefixTerm tag (tag.length + 1)) [.proj 0, prefixArg k]

/-- One block equality of the level, run on the width with the parameter it expects, followed by
the code of the constant that closes the conjunction. -/
def levelEq (ki kj : ℕ) : Cob :=
  .comp Cob.concat [.comp (eqBlockTerm 1 2 24) [.proj 0, eqArg ki kj], Cob.constT (enc tt)]

/-- **The term writing the block of one level of the midpoint recursion.** -/
def levelTerm : Cob :=
  Cob.catL
    [levelPrefix [true, true, true] 1,
      levelPrefix [true, true, false] 2,
      levelPrefix [true, true, false] 3,
      Cob.constT [true, false, true, false, true],
      Cob.constT [true, false, true],
      Cob.constT [true, false, false],
      levelEq 2 4,
      levelEq 3 1,
      Cob.constT [true, false, false],
      levelEq 2 1,
      levelEq 3 5]

/-- **The block of a level is written by a Cobham term** from the width in unary and the parameter
word of the level. -/
theorem reachPre_eval (m a b t : ℕ) :
    reachPre m a b t = levelTerm.eval [List.replicate m true, levelParam m a b t] := by
  have hpre : ∀ (tag : Word) (k : ℕ) (v : ℕ), k < 6 →
      ([m, t * m, (t + 1) * m, (t + 2) * m, a * m, b * m] : List ℕ).getD k 0 = v →
      (levelPrefix tag k).eval [List.replicate m true, levelParam m a b t]
        = (List.range m).flatMap fun l => tag ++ unary (v + l) := by
    intro tag k v hk hv
    have harg := eval_prefixArg k [m, t * m, (t + 1) * m, (t + 2) * m, a * m, b * m]
      (by simpa using hk) (by simp) (List.replicate m true)
    rw [hv] at harg
    have h0 : ([m, t * m, (t + 1) * m, (t + 2) * m, a * m, b * m] : List ℕ).getD 0 0 = m := rfl
    rw [h0] at harg
    simp only [levelPrefix, levelParam, Cob.eval_comp, List.map_cons, List.map_nil,
      Cob.eval_proj, List.getD_cons_zero, harg]
    exact eval_quantPrefixTerm tag m v
  have heq : ∀ (ki kj i j : ℕ), ki < 6 → kj < 6 →
      ([m, t * m, (t + 1) * m, (t + 2) * m, a * m, b * m] : List ℕ).getD ki 0 = i * m →
      ([m, t * m, (t + 1) * m, (t + 2) * m, a * m, b * m] : List ℕ).getD kj 0 = j * m →
      (levelEq ki kj).eval [List.replicate m true, levelParam m a b t]
        = enc (eqBlock m i j) := by
    intro ki kj i j hki hkj hi hj
    have harg := eval_eqArg ki kj [m, t * m, (t + 1) * m, (t + 2) * m, a * m, b * m]
      (by simpa using hki) (by simpa using hkj) (by simp) (List.replicate m true)
    have h0 : ([m, t * m, (t + 1) * m, (t + 2) * m, a * m, b * m] : List ℕ).getD 0 0 = m := rfl
    rw [hi, hj, h0] at harg
    simp only [levelEq, levelParam, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat,
      Cob.eval_proj, List.getD_cons_zero, harg, Cob.eval_constT]
    exact (enc_eqBlock_eval m i j).symm
  have h1 := hpre [true, true, true] 1 (t * m) (by omega) rfl
  have h2 := hpre [true, true, false] 2 ((t + 1) * m) (by omega) rfl
  have h3 := hpre [true, true, false] 3 ((t + 2) * m) (by omega) rfl
  have e1 := heq 2 4 (t + 1) a (by omega) (by omega) rfl rfl
  have e2 := heq 3 1 (t + 2) t (by omega) (by omega) rfl rfl
  have e3 := heq 2 1 (t + 1) t (by omega) (by omega) rfl rfl
  have e4 := heq 3 5 (t + 2) b (by omega) (by omega) rfl rfl
  simp only [levelTerm, Cob.eval_catL, List.map_cons, List.map_nil, h1, h2, h3, e1, e2, e3, e4,
    Cob.eval_constT, List.flatten_cons, List.flatten_nil]
  simp only [reachPre, legsF, enc_disj, enc_conj, List.append_assoc, List.append_nil]

end QBF

end Complexity.Qbf
