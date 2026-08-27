/-
**The P-uniformity hypothesis is inhabited.**

`Start/CookLevinCode.lean` derives NP-completeness of SAT from `Complexity.CodeUniform`: that the
description of the `n`-th acceptance circuit is produced by a Cobham term from any word of length
`n`.  A hypothesis is only worth stating if it can be met, so this module exhibits an explicit
family that meets it.

The family is the chain of negations: the circuit `cfNeg (n + 1)` has one input gate at the bottom
and `n` negations on top of it, so its output is the `n`-fold negation of the first input bit.  It
has `n + 1` gates, so its description grows without bound, and the generator is the composite of
the two schemes of the Cobham toolkit: the `n`-th word is smashed to `1^n`, and a block-emitting
recursion writes one gate token per position, the counter supplying the identifier of the gate.

Main definitions:

* `Complexity.CircCode.cfNeg` — the chain of negations;
* `Complexity.CircCode.negGen` — the Cobham term writing its description.

Main results:

* `Complexity.CircCode.wf_cfNeg`, `Complexity.CircCode.csat_cfNeg` — the family is well formed and
  its circuits are satisfiable;
* `Complexity.CircCode.eval_negGen` — the description is produced by the Cobham term;
* `Complexity.codeUniform_cfNeg` — **the P-uniformity hypothesis is inhabited.**
-/

import Start.CookLevinCode

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### The chain of negations -/

/-- The `n`-fold negation of a bit. -/
def negIter : ℕ → Bool → Bool
  | 0, b => b
  | n + 1, b => !(negIter n b)

theorem negIter_not (n : ℕ) (b : Bool) : negIter n (!b) = !(negIter n b) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [negIter, ih, negIter]

theorem negIter_negIter (n : ℕ) (b : Bool) : negIter n (negIter n b) = b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [negIter, negIter, negIter_not, ih, Bool.not_not]

/-- The circuit with one input gate and a chain of negations on top of it. -/
def cfNeg : ℕ → Circuit
  | 0 => []
  | 1 => [.inp 0]
  | n + 2 => .neg n :: cfNeg (n + 1)

@[simp] theorem length_cfNeg (n : ℕ) : (cfNeg n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      match n with
      | 0 => rfl
      | m + 1 => rw [cfNeg, List.length_cons, ih]

theorem wf_cfNeg (n : ℕ) : wf (cfNeg n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      match n with
      | 0 => exact ⟨trivial, trivial⟩
      | m + 1 => exact ⟨by simp [gateWf], ih⟩

theorem vals_cfNeg (x : Word) (n : ℕ) :
    vals x (cfNeg (n + 1)) = (List.range (n + 1)).map fun j => negIter j (x.getD 0 false) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hget : ((List.range (n + 1)).map
          fun j => negIter j (x.getD 0 false)).getD n false
          = negIter n (x.getD 0 false) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range (Nat.lt_succ_self n)]
        rfl
      rw [cfNeg, vals, ih, gateVal, hget, List.range_succ (n := n + 1), List.map_append]
      rfl

theorem out_cfNeg (x : Word) (n : ℕ) :
    out x (cfNeg (n + 1)) = negIter n (x.getD 0 false) := by
  match n with
  | 0 => rfl
  | m + 1 =>
      have hget : ((List.range (m + 1)).map
          fun j => negIter j (x.getD 0 false)).getD m false
          = negIter m (x.getD 0 false) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range (Nat.lt_succ_self m)]
        rfl
      rw [cfNeg, out, vals_cfNeg, gateVal, hget]
      rfl

/-- Every circuit of the family is satisfiable. -/
theorem csat_cfNeg (n : ℕ) : csat (cfNeg (n + 1)) :=
  ⟨[negIter n true], by rw [out_cfNeg]; exact negIter_negIter n true⟩

/-! ### Generating the description -/

/-- The control of the generator: state `0` is the rightmost position, which carries the input
gate; state `1` carries a negation. -/
def ngState (_ : ℕ) (_ : Bool) : ℕ := 1

theorem ngState_lt (s : ℕ) (b : Bool) : ngState s b < 2 := by
  rw [ngState]
  omega

/-- The counter of the generator counts the gates already written. -/
def ngInc (_ : ℕ) (_ : Bool) : ℕ := 1

theorem ngInc_le (s : ℕ) (b : Bool) : ngInc s b ≤ 1 := le_refl _

/-- The block written at a position: the token of the gate with that identifier. -/
def ngBlk (s : ℕ) (_ : Bool) (_ : Word) (c : ℕ) : Word :=
  if s = 0 then encGate (.inp 0) else encGate (.neg (c - 1))

/-- The term written at a position. -/
def ngBlkT (s : ℕ) (_ : Bool) : Cob :=
  if s = 0 then Cob.constT (encGate (.inp 0))
  else Cob.catL [Cob.constT [false, true, true, true, true, false],
    .comp (.app true) [.comp Cob.tail [.proj 1]], Cob.constT [false, true]]

theorem eval_ngBlkT (y p : Word) (s : ℕ) (b : Bool) (c : ℕ) :
    (ngBlkT s b).eval [y, List.replicate c true, p] = ngBlk s b y c := by
  rw [ngBlkT, ngBlk]
  split
  · simp
  · simp only [Cob.eval_catL, List.map_cons, List.map_nil, Cob.eval_constT, Cob.eval_comp,
      Cob.eval_app, Cob.eval_tail, Cob.eval_proj, List.getD_cons_zero, List.getD_cons_succ,
      List.tail_replicate, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [encGate]
    simp only [tag, fld1, fld2]
    cases c with
    | zero => rfl
    | succ k => simp [List.replicate_succ]

theorem length_ngBlk (y : Word) (s : ℕ) (b : Bool) (c : ℕ) (hc : c ≤ y.length * 1) :
    (ngBlk s b y c).length ≤ 9 * (y.length + ([] : Word).length + 1) := by
  rw [ngBlk]
  simp only [List.length_nil, Nat.mul_one] at hc ⊢
  split
  · rw [length_encGate]
    simp only [tag, fld1, fld2]
    omega
  · rw [length_encGate]
    simp only [tag, fld1, fld2]
    omega

/-- The Cobham term writing the description of the `n`-th circuit of the family. -/
def negGen : Cob :=
  .comp (blkRunTerm 2 ngState ngInc ngBlkT 1 9)
    [.comp .smash [.proj 0, Cob.constT [true]], .empty]

theorem rcnt_ngInc (k : ℕ) : rcnt ngState ngInc (List.replicate k true) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h1 : ngInc (rst ngState 0 (List.replicate k true)) true = 1 := rfl
      rw [List.replicate_succ, rcnt, ih, h1]
      omega

theorem rst_ngState (k : ℕ) :
    rst ngState 0 (List.replicate (k + 1) true) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, rst, ih]; rfl

theorem brun_ngBlk (k : ℕ) :
    brun ngState ngInc ngBlk (List.replicate k true) = encCirc (cfNeg k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, brun, ih, rcnt_ngInc]
      match k with
      | 0 => rfl
      | m + 1 =>
          rw [rst_ngState, cfNeg, encCirc, ngBlk, if_neg (by omega)]
          rfl

theorem eval_negGen (x : Word) : negGen.eval [x] = encCirc (cfNeg x.length) := by
  have h := eval_blkRunTerm (m := 2) (Ki := 1) (K := 9) (by norm_num) ngState_lt ngInc_le ngBlkT
    (blk := ngBlk) [] (fun s b y c => eval_ngBlkT y [] s b c)
    (fun s b y c hc => length_ngBlk y s b c hc) (List.replicate x.length true)
  rw [negGen]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, Cob.eval_proj,
    List.getD_cons_zero, List.getD_cons_succ, Cob.eval_constT, Cob.eval_empty,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one]
  rw [h, brun_ngBlk]

end CircCode

/-- **The P-uniformity hypothesis is inhabited**: an explicit family of well-formed satisfiable
circuits, of unbounded size, has descriptions produced by a single Cobham term. -/
theorem codeUniform_cfNeg : CodeUniform CircCode.cfNeg :=
  ⟨CircCode.negGen, CircCode.eval_negGen⟩

end Complexity
