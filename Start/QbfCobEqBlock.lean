/-
**The block-equality formula of the reduction is written by a Cobham term.**

`Complexity.Qbf.QBF.eqBlock m i j` — the two blocks `i` and `j` of `m` variables carry the same
word — is the workhorse of the reduction formula: every level of the midpoint recursion contains
four of them.  Its code is a concatenation of `m` blocks, one per position of the words
(`Complexity.Qbf.QBF.enc_conjAll`), each holding the two variable indices `i * m + l` and
`j * m + l` in unary.  This module writes it with one Cobham term, using the emitter of
`Start/CobhamRange.lean` and the unary fields of `Start/CobhamFields.lean`: the parameter word
carries `m` and the two products `i * m` and `j * m` in unary — the multiplications are done once,
outside the sweep, so that the block written at a position stays short — and the sum with the
position is a concatenation.  The padding constant of the term does not depend on the instance, so
one term serves all widths and all block indices.

Main definitions:

* `Complexity.Qbf.QBF.idxTerm` — the variable index `i * m + l` in unary, from the field `i * m`
  and the position `l`;
* `Complexity.Qbf.QBF.eqBlockBlockTerm`, `Complexity.Qbf.QBF.eqBlockTerm` — the block of one
  position, and the term writing the whole code.

Main results:

* `Complexity.Qbf.QBF.eval_idxTerm` — the index term is correct;
* `Complexity.Qbf.QBF.eval_eqBlockBlockTerm` — the block term writes the code of one conjunct;
* `Complexity.Qbf.QBF.enc_eqBlock_eval` — **the code of `eqBlock m i j` is the value of one Cobham
  term at `1^m` and the unary fields `m, i * m, j * m`, followed by the code of the constant
  `tt`**.
-/

import Mathlib
import Start.CobhamFields
import Start.CobhamTseitin
import Start.QbfWordStream

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

open Complexity

/-! ### The variable index -/

/-- The unary code of the variable index `a + l`, where `a` is the field `fi` of the parameter and
`l` is the first argument.  The parameter carries the *product* `i * m` as a field, so that the
block written at a position stays short: the multiplication is done once, outside the sweep. -/
def idxTerm (fi : ℕ) : Cob :=
  .comp Cob.concat
    [.comp Cob.concat [Cob.fieldTerm fi (.proj 1), .proj 0], Cob.pre [false] .empty]

theorem eval_idxTerm (fi : ℕ) (as : List ℕ) (hfi : fi < as.length) (l : ℕ) :
    (idxTerm fi).eval [List.replicate l true, fieldsWord as]
      = unary (as.getD fi 0 + l) := by
  have ha : (Cob.fieldTerm fi (Cob.proj 1)).eval [List.replicate l true, fieldsWord as]
      = List.replicate (as.getD fi 0) true :=
    Cob.eval_fieldTerm fi (.proj 1) as _ (by simp) hfi
  simp only [idxTerm, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat,
    Cob.eval_proj, List.getD_cons_zero, ha,
    Cob.eval_pre, Cob.eval_empty, List.append_nil]
  rw [unary, ← List.replicate_add]

/-! ### The block of one position -/

/-- The block emitted at the position `l`: the code of the conjunct saying that the `l`-th bits of
the two blocks agree. -/
def eqBlockBlockTerm (fi fj : ℕ) : Cob :=
  Cob.catL
    [Cob.constT [true, false, false, true, false, true, true, false, false, false, false],
      idxTerm fi,
      Cob.constT [false, false],
      idxTerm fj,
      Cob.constT [true, false, false, false, true, false, false],
      idxTerm fi,
      Cob.constT [false, true, false, false],
      idxTerm fj]

theorem eval_eqBlockBlockTerm (fi fj : ℕ) (as : List ℕ) (hfi : fi < as.length)
    (hfj : fj < as.length) (l : ℕ) :
    (eqBlockBlockTerm fi fj).eval [List.replicate l true, fieldsWord as]
      = [true, false, false] ++ enc (iffVar (as.getD fi 0 + l) (as.getD fj 0 + l)) := by
  simp only [eqBlockBlockTerm, Cob.eval_catL, List.map_cons, List.map_nil, Cob.eval_constT,
    eval_idxTerm fi as hfi l, eval_idxTerm fj as hfj l, List.flatten_cons, List.flatten_nil]
  simp [iffVar, enc, List.append_assoc]

/-! ### The whole code -/

/-- The term writing the code of `eqBlock`, except for the code of the constant that closes the
conjunction. -/
def eqBlockTerm (fi fj K : ℕ) : Cob := rangeEmitTerm (eqBlockBlockTerm fi fj) K

/-- **The code of `eqBlock m i j` is written by a Cobham term** from `1^m` and the unary fields
`m, i * m, j * m`.  The padding constant `24` does not depend on the instance, so this is one term
for all widths and all block indices. -/
theorem enc_eqBlock_eval (m i j : ℕ) :
    enc (eqBlock m i j)
      = (eqBlockTerm 1 2 24).eval
          [List.replicate m true, fieldsWord [m, i * m, j * m]] ++ enc tt := by
  have hfi : (1 : ℕ) < ([m, i * m, j * m] : List ℕ).length := by simp
  have hfj : (2 : ℕ) < ([m, i * m, j * m] : List ℕ).length := by simp
  have hlead : lead1 (fieldsWord [m, i * m, j * m]) = m := by simp
  have hlen : (fieldsWord [m, i * m, j * m]).length = m + (i * m + (j * m + 3)) := by
    simp [fieldsWord]
    omega
  have hW : ∀ l : ℕ,
      (eqBlockBlockTerm 1 2).eval [List.replicate l true, fieldsWord [m, i * m, j * m]]
        = [true, false, false] ++ enc (iffVar (i * m + l) (j * m + l)) := by
    intro l
    have h := eval_eqBlockBlockTerm 1 2 [m, i * m, j * m] hfi hfj l
    simpa using h
  have hb : ∀ l : ℕ, l ≤ m →
      ([true, false, false] ++ enc (iffVar (i * m + l) (j * m + l))).length
        ≤ 24 * ((fieldsWord [m, i * m, j * m]).length + 1) := by
    intro l hl
    simp only [List.length_append, List.length_cons, List.length_nil, iffVar, enc,
      length_unary, hlen]
    nlinarith [hl, Nat.zero_le (i * m), Nat.zero_le (j * m)]
  rw [eqBlock, enc_conjAll, eqBlockTerm,
    eval_rangeEmitTerm (eqBlockBlockTerm 1 2)
      (fun l => [true, false, false] ++ enc (iffVar (i * m + l) (j * m + l)))
      (fieldsWord [m, i * m, j * m]) hlead hW hb]
  rw [List.flatMap_map]

end QBF

end Complexity.Qbf
