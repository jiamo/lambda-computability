/-
**The configuration-block formulas of the reduction are written by Cobham terms.**

The reduction of `Start/QbfMachine.lean` says that a block of variables carries the word of a
configuration (`Complexity.Qbf.QBF.cfgF`) and that a second block carries the word of a successor
configuration (`Complexity.Qbf.QBF.tgtF`).  Both are conjunctions with one conjunct per position
of the block, and the conjunct at a position depends on *where the position lies*: in the control
state, in the input head, on the work tape, or in the work head — and on whether it is the
position marked by the state or by one of the heads.

This module writes the codes of both formulas with a single Cobham term each.  The sweep is the
range emitter of `Start/CobhamRange.lean`; the tests are the unary comparisons of
`Start/CobhamCond.lean`; and the parameter word carries, in unary, the width, the offset of the
block (a product, computed once outside the sweep) and the four boundaries and three marked
positions of the layout.  The padding constants do not depend on the instance, so one term serves
every machine, width and situation.

Main definitions:

* `Complexity.Qbf.QBF.cfgConj`, `.tgtConj` — the conjunct of the two formulas at a position;
* `Complexity.Qbf.QBF.cfgParam`, `.tgtParam` — their parameter words;
* `Complexity.Qbf.QBF.cfgEmitTerm`, `.tgtEmitTerm` — the terms writing their codes.

Main results:

* `Complexity.Qbf.QBF.enc_cfgF_eval` — **the code of `cfgF` is the value of one Cobham term** at
  the width in unary and the parameter word, followed by the code of `tt`;
* `Complexity.Qbf.QBF.enc_tgtF_eval` — the same for `tgtF`.
-/

import Mathlib
import Start.CobhamCond
import Start.QbfCobEqBlock
import Start.QbfMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

open Complexity Complexity.Space

/-! ### Reading the parameter -/

/-- The `k`-th unary field of the parameter word, which is the second argument. -/
def fldT (k : ℕ) : Cob := Cob.fieldTerm k (.proj 1)

theorem eval_fldT (k : ℕ) (as : List ℕ) (hk : k < as.length) (y : Word) :
    (fldT k).eval [y, fieldsWord as] = List.replicate (as.getD k 0) true :=
  Cob.eval_fieldTerm k (.proj 1) as _ (by simp) hk

theorem eval_eqPos (k l : ℕ) (as : List ℕ) (hk : k < as.length) :
    (Cob.eqU (.proj 0) (fldT k)).eval [List.replicate l true, fieldsWord as]
      = bw (decide (l = as.getD k 0)) := by
  rw [Cob.eval_eqU, eval_fldT k as hk]
  simp

theorem eval_ltPos (k l : ℕ) (as : List ℕ) (hk : k < as.length) :
    (Cob.ltU (.proj 0) (fldT k)).eval [List.replicate l true, fieldsWord as]
      = bw (decide (l < as.getD k 0)) := by
  rw [Cob.eval_ltU, eval_fldT k as hk]
  simp

theorem eval_lePos (k l : ℕ) (as : List ℕ) (hk : k < as.length) :
    (Cob.leU (fldT k) (.proj 0)).eval [List.replicate l true, fieldsWord as]
      = bw (decide (as.getD k 0 ≤ l)) := by
  rw [Cob.eval_leU, eval_fldT k as hk]
  simp

/-! ### The shared shape of the two block terms -/

/-- The test that the position lies on the work tape: between the fields `k₁` and `k₂`. -/
def inTapeT (k₁ k₂ : ℕ) : Cob :=
  Cob.andT (Cob.leU (fldT k₁) (.proj 0)) (Cob.ltU (.proj 0) (fldT k₂))

theorem eval_inTapeT (k₁ k₂ l : ℕ) (as : List ℕ) (hk₁ : k₁ < as.length) (hk₂ : k₂ < as.length) :
    (inTapeT k₁ k₂).eval [List.replicate l true, fieldsWord as]
      = bw (decide (as.getD k₁ 0 ≤ l) && decide (l < as.getD k₂ 0)) :=
  Cob.eval_andT (eval_lePos k₁ l as hk₁) (eval_ltPos k₂ l as hk₂)

/-- The test that the position is one of the three marked ones. -/
def markedT (k₁ k₂ k₃ : ℕ) : Cob :=
  Cob.orT (Cob.eqU (.proj 0) (fldT k₁))
    (Cob.orT (Cob.eqU (.proj 0) (fldT k₂)) (Cob.eqU (.proj 0) (fldT k₃)))

theorem eval_markedT (k₁ k₂ k₃ l : ℕ) (as : List ℕ) (hk₁ : k₁ < as.length)
    (hk₂ : k₂ < as.length) (hk₃ : k₃ < as.length) :
    (markedT k₁ k₂ k₃).eval [List.replicate l true, fieldsWord as]
      = bw (decide (l = as.getD k₁ 0) ||
          (decide (l = as.getD k₂ 0) || decide (l = as.getD k₃ 0))) :=
  Cob.eval_orT (eval_eqPos k₁ l as hk₁)
    (Cob.eval_orT (eval_eqPos k₂ l as hk₂) (eval_eqPos k₃ l as hk₃))

/-- The tag bits of a literal, according to its polarity. -/
def litPolT (c : Cob) : Cob :=
  Cob.iteT c (Cob.constT [false, false]) (Cob.constT [false, true, false, false])

theorem eval_litPolT (c : Cob) (args : List Word) (b : Bool) (hc : c.eval args = bw b) :
    (litPolT c).eval args = if b then [false, false] else [false, true, false, false] :=
  Cob.eval_iteW hc (Cob.eval_constT _ _) (Cob.eval_constT _ _)

theorem enc_litF (v : ℕ) (b : Bool) :
    enc (litF v b) = (if b then [false, false] else [false, true, false, false]) ++ unary v := by
  cases b <;> simp [litF, enc]

/-- The literal part of a block: the tag bits of the polarity given by `c`, and the index carried
by the field `kA` shifted by the position. -/
def litBlockT (c : Cob) (kA : ℕ) : Cob := Cob.catL [litPolT c, idxTerm kA]

theorem eval_litBlockT (c : Cob) (kA l : ℕ) (as : List ℕ) (hkA : kA < as.length) (b : Bool)
    (hc : c.eval [List.replicate l true, fieldsWord as] = bw b) :
    (litBlockT c kA).eval [List.replicate l true, fieldsWord as]
      = enc (litF (as.getD kA 0 + l) b) := by
  rw [litBlockT, Cob.eval_catL]
  simp only [List.map_cons, List.map_nil, eval_litPolT c _ b hc,
    eval_idxTerm kA as hkA l, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [enc_litF]

/-! ### The block formula of a configuration -/

/-- The conjunct of `Complexity.Qbf.QBF.cfgF` at the position `l`. -/
def cfgConj (M : Machine) (x : List Bool) (s : ℕ) (a q i j l : ℕ) : QBF :=
  if l < M.states then litF (a * cfgWidth M x s + l) (decide (l = q))
  else if l < M.states + (x.length + 1) then
    litF (a * cfgWidth M x s + l) (decide (l - M.states = i))
  else if l < M.states + (x.length + 1) + s then tt
  else litF (a * cfgWidth M x s + l) (decide (l - (M.states + (x.length + 1) + s) = j))

theorem cfgF_eq_conjAll (M : Machine) (x : List Bool) (s : ℕ) (a q i j : ℕ) :
    cfgF M x s a q i j
      = conjAll ((List.range (cfgWidth M x s)).map (cfgConj M x s a q i j)) := rfl

/-- The parameter word of the configuration-block term: the width, the offset of the block, the
three boundaries of the layout and the three marked positions, all in unary. -/
def cfgParam (M : Machine) (x : List Bool) (s : ℕ) (a q i j : ℕ) : Word :=
  fieldsWord [cfgWidth M x s, a * cfgWidth M x s, M.states, M.states + (x.length + 1),
    M.states + (x.length + 1) + s, q, M.states + i, M.states + (x.length + 1) + s + j]

/-- **The block of one position of the configuration formula.** -/
def cfgBlockTerm : Cob :=
  Cob.catL
    [Cob.constT [true, false, false],
      Cob.iteT (inTapeT 3 4) (Cob.constT (enc tt)) (litBlockT (markedT 5 6 7) 1)]

theorem eval_cfgBlockTerm (M : Machine) (x : List Bool) (s : ℕ) (a q i j l : ℕ)
    (hq : q < M.states) (hi : i ≤ x.length) :
    cfgBlockTerm.eval [List.replicate l true, cfgParam M x s a q i j]
      = [true, false, false] ++ enc (cfgConj M x s a q i j l) := by
  set as : List ℕ := [cfgWidth M x s, a * cfgWidth M x s, M.states, M.states + (x.length + 1),
    M.states + (x.length + 1) + s, q, M.states + i, M.states + (x.length + 1) + s + j] with has
  have hlen : as.length = 8 := by simp [has]
  have h1 : as.getD 1 0 = a * cfgWidth M x s := rfl
  have h3 : as.getD 3 0 = M.states + (x.length + 1) := rfl
  have h4 : as.getD 4 0 = M.states + (x.length + 1) + s := rfl
  have h5 : as.getD 5 0 = q := rfl
  have h6 : as.getD 6 0 = M.states + i := rfl
  have h7 : as.getD 7 0 = M.states + (x.length + 1) + s + j := rfl
  have htape := eval_inTapeT 3 4 l as (by omega) (by omega)
  have hmark := eval_markedT 5 6 7 l as (by omega) (by omega) (by omega)
  rw [h3, h4] at htape
  rw [h5, h6, h7] at hmark
  have hcfgParam : cfgParam M x s a q i j = fieldsWord as := rfl
  rw [hcfgParam, cfgBlockTerm, Cob.eval_catL]
  simp only [List.map_cons, List.map_nil, Cob.eval_constT, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  congr 1
  by_cases htp : M.states + (x.length + 1) ≤ l ∧ l < M.states + (x.length + 1) + s
  · have hc : (inTapeT 3 4).eval [List.replicate l true, fieldsWord as] = bw true := by
      rw [htape]
      simp [htp.1, htp.2]
    rw [Cob.eval_iteW hc (Cob.eval_constT _ _) rfl]
    have : cfgConj M x s a q i j l = tt := by
      have h1' : ¬ l < M.states := by omega
      have h2' : ¬ l < M.states + (x.length + 1) := by omega
      simp [cfgConj, h1', h2', htp.2]
    rw [this]
    simp
  · have hc : (inTapeT 3 4).eval [List.replicate l true, fieldsWord as] = bw false := by
      rw [htape]
      by_cases h1' : M.states + (x.length + 1) ≤ l
      · have h2' : ¬ l < M.states + (x.length + 1) + s := by tauto
        simp [h1', h2']
      · simp [h1']
    rw [Cob.eval_iteW hc (Cob.eval_constT _ _) rfl]
    simp only [Bool.false_eq_true, if_false]
    -- outside the tape region the conjunct is a literal, marked exactly at the three positions
    have hc' : (markedT 5 6 7).eval [List.replicate l true, fieldsWord as]
        = bw (decide (l = q) || (decide (l = M.states + i) ||
            decide (l = M.states + (x.length + 1) + s + j))) := by
      rw [hmark]
    rw [eval_litBlockT (markedT 5 6 7) 1 l as (by omega) _ hc', h1]
    have hconj : cfgConj M x s a q i j l
        = litF (a * cfgWidth M x s + l) (decide (l = q) || (decide (l = M.states + i) ||
            decide (l = M.states + (x.length + 1) + s + j))) := by
      by_cases hA : l < M.states
      · have e2 : ¬ (l = M.states + i) := by omega
        have e3 : ¬ (l = M.states + (x.length + 1) + s + j) := by omega
        simp [cfgConj, hA, e2, e3]
      · by_cases hB : l < M.states + (x.length + 1)
        · have e1 : ¬ (l = q) := by omega
          have e3 : ¬ (l = M.states + (x.length + 1) + s + j) := by omega
          have e2 : (l - M.states = i) ↔ (l = M.states + i) := by omega
          simp only [cfgConj, if_neg hA, if_pos hB, e1, e3, decide_false, Bool.false_or,
            Bool.or_false]
          congr 1
          simp [e2]
        · have hC : ¬ l < M.states + (x.length + 1) + s := fun h => htp ⟨by omega, h⟩
          have e1 : ¬ (l = q) := by omega
          have e2 : ¬ (l = M.states + i) := by omega
          have e3 : (l - (M.states + (x.length + 1) + s) = j) ↔
              (l = M.states + (x.length + 1) + s + j) := by omega
          simp only [cfgConj, if_neg hA, if_neg hB, if_neg hC, e1, e2, decide_false,
            Bool.false_or]
          congr 1
          simp [e3]
    rw [hconj]

/-- **The term writing the code of the configuration-block formula.** -/
def cfgEmitTerm : Cob := rangeEmitTerm cfgBlockTerm 16

theorem length_cfgParam (M : Machine) (x : List Bool) (s : ℕ) (a q i j : ℕ) :
    cfgWidth M x s + a * cfgWidth M x s ≤ (cfgParam M x s a q i j).length := by
  simp [cfgParam, fieldsWord]
  omega

theorem lead1_cfgParam (M : Machine) (x : List Bool) (s : ℕ) (a q i j : ℕ) :
    lead1 (cfgParam M x s a q i j) = cfgWidth M x s := by
  simp [cfgParam]

/-- **The code of the configuration-block formula is written by a Cobham term** from the width in
unary and the parameter word of the situation. -/
theorem enc_cfgF_eval (M : Machine) (x : List Bool) (s : ℕ) (a q i j : ℕ)
    (hq : q < M.states) (hi : i ≤ x.length) :
    enc (cfgF M x s a q i j)
      = cfgEmitTerm.eval [List.replicate (cfgWidth M x s) true, cfgParam M x s a q i j]
        ++ enc tt := by
  have hW : ∀ l : ℕ, cfgBlockTerm.eval [List.replicate l true, cfgParam M x s a q i j]
      = [true, false, false] ++ enc (cfgConj M x s a q i j l) :=
    fun l => eval_cfgBlockTerm M x s a q i j l hq hi
  have hb : ∀ l : ℕ, l ≤ cfgWidth M x s →
      ([true, false, false] ++ enc (cfgConj M x s a q i j l)).length
        ≤ 16 * ((cfgParam M x s a q i j).length + 1) := by
    intro l hl
    have hlen := length_cfgParam M x s a q i j
    have hsmall : (enc (cfgConj M x s a q i j l)).length
        ≤ 11 + (a * cfgWidth M x s + l + 1) := by
      by_cases hA : l < M.states
      · simp only [cfgConj, if_pos hA, enc_litF]
        cases (decide (l = q)) <;> simp [length_unary] <;> omega
      · by_cases hB : l < M.states + (x.length + 1)
        · simp only [cfgConj, if_neg hA, if_pos hB, enc_litF]
          cases (decide (l - M.states = i)) <;> simp [length_unary] <;> omega
        · by_cases hC : l < M.states + (x.length + 1) + s
          · simp only [cfgConj, if_neg hA, if_neg hB, if_pos hC]
            simp [tt, enc, unary]
          · simp only [cfgConj, if_neg hA, if_neg hB, if_neg hC, enc_litF]
            cases (decide (l - (M.states + (x.length + 1) + s) = j)) <;>
              simp [length_unary] <;> omega
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  rw [cfgF_eq_conjAll, enc_conjAll, cfgEmitTerm,
    eval_rangeEmitTerm cfgBlockTerm
      (fun l => [true, false, false] ++ enc (cfgConj M x s a q i j l))
      (cfgParam M x s a q i j) (lead1_cfgParam M x s a q i j) hW hb,
    List.flatMap_map]

/-! ### The block formula of a successor configuration -/

/-- The conjunct of `Complexity.Qbf.QBF.tgtF` at the position `l`. -/
def tgtConj (M : Machine) (x : List Bool) (s : ℕ) (a b q' i' j' : ℕ) (w : Bool) (j l : ℕ) :
    QBF :=
  if l < M.states then litF (b * cfgWidth M x s + l) (decide (l = q'))
  else if l < M.states + (x.length + 1) then
    litF (b * cfgWidth M x s + l) (decide (l - M.states = i'))
  else if l < M.states + (x.length + 1) + s then
    (if l - (M.states + (x.length + 1)) = j then litF (b * cfgWidth M x s + l) w
      else iffVar (b * cfgWidth M x s + l) (a * cfgWidth M x s + l))
  else litF (b * cfgWidth M x s + l)
    (decide (l - (M.states + (x.length + 1) + s) = j'))

theorem tgtF_eq_conjAll (M : Machine) (x : List Bool) (s : ℕ) (a b q' i' j' : ℕ) (w : Bool)
    (j : ℕ) :
    tgtF M x s a b q' i' j' w j
      = conjAll ((List.range (cfgWidth M x s)).map (tgtConj M x s a b q' i' j' w j)) := rfl

/-- The parameter word of the successor-block term: the width, the offsets of the two blocks, the
two boundaries, the three marked positions and the position written by the instruction. -/
def tgtParam (M : Machine) (x : List Bool) (s : ℕ) (a b q' i' j' j : ℕ) : Word :=
  fieldsWord [cfgWidth M x s, b * cfgWidth M x s, a * cfgWidth M x s,
    M.states + (x.length + 1), M.states + (x.length + 1) + s, q', M.states + i',
    M.states + (x.length + 1) + s + j', M.states + (x.length + 1) + j]

/-- The polarity of the literal written at a position: the marked positions, and — when the
instruction writes a one — the position under the work head. -/
def tgtPolT (w : Bool) : Cob :=
  if w then Cob.orT (markedT 5 6 7) (Cob.eqU (.proj 0) (fldT 8)) else markedT 5 6 7

/-- **The block of one position of the successor formula.** -/
def tgtBlockTerm (w : Bool) : Cob :=
  Cob.iteT (Cob.andT (inTapeT 3 4) (Cob.notT (Cob.eqU (.proj 0) (fldT 8))))
    (eqBlockBlockTerm 1 2)
    (Cob.catL [Cob.constT [true, false, false], litBlockT (tgtPolT w) 1])

theorem eval_tgtBlockTerm (M : Machine) (x : List Bool) (s : ℕ) (a b q' i' j' : ℕ) (w : Bool)
    (j l : ℕ) (hq' : q' < M.states) (hi' : i' ≤ x.length) (hj : j < s) :
    (tgtBlockTerm w).eval [List.replicate l true, tgtParam M x s a b q' i' j' j]
      = [true, false, false] ++ enc (tgtConj M x s a b q' i' j' w j l) := by
  set as : List ℕ := [cfgWidth M x s, b * cfgWidth M x s, a * cfgWidth M x s,
    M.states + (x.length + 1), M.states + (x.length + 1) + s, q', M.states + i',
    M.states + (x.length + 1) + s + j', M.states + (x.length + 1) + j] with has
  have hlen : as.length = 9 := by simp [has]
  have h1 : as.getD 1 0 = b * cfgWidth M x s := rfl
  have h2 : as.getD 2 0 = a * cfgWidth M x s := rfl
  have h3 : as.getD 3 0 = M.states + (x.length + 1) := rfl
  have h4 : as.getD 4 0 = M.states + (x.length + 1) + s := rfl
  have h5 : as.getD 5 0 = q' := rfl
  have h6 : as.getD 6 0 = M.states + i' := rfl
  have h7 : as.getD 7 0 = M.states + (x.length + 1) + s + j' := rfl
  have h8 : as.getD 8 0 = M.states + (x.length + 1) + j := rfl
  have hparam : tgtParam M x s a b q' i' j' j = fieldsWord as := rfl
  have htape := eval_inTapeT 3 4 l as (by omega) (by omega)
  have hmark := eval_markedT 5 6 7 l as (by omega) (by omega) (by omega)
  have hpw := eval_eqPos 8 l as (by omega)
  rw [h3, h4] at htape
  rw [h5, h6, h7] at hmark
  rw [h8] at hpw
  rw [hparam]
  have hnot : (Cob.notT (Cob.eqU (.proj 0) (fldT 8))).eval
      [List.replicate l true, fieldsWord as]
        = bw (!decide (l = M.states + (x.length + 1) + j)) := Cob.eval_notT hpw
  have hand := Cob.eval_andT htape hnot
  by_cases hwrite : M.states + (x.length + 1) ≤ l ∧ l < M.states + (x.length + 1) + s ∧
      l ≠ M.states + (x.length + 1) + j
  · obtain ⟨hA, hB, hC⟩ := hwrite
    have hc : (Cob.andT (inTapeT 3 4) (Cob.notT (Cob.eqU (.proj 0) (fldT 8)))).eval
        [List.replicate l true, fieldsWord as] = bw true := by
      rw [hand]; simp [hA, hB, hC]
    rw [tgtBlockTerm, Cob.eval_iteW hc (rfl : (eqBlockBlockTerm 1 2).eval _ = _) rfl]
    have hblk := eval_eqBlockBlockTerm 1 2 as (by omega) (by omega) l
    rw [h1, h2] at hblk
    have hconj : tgtConj M x s a b q' i' j' w j l
        = iffVar (b * cfgWidth M x s + l) (a * cfgWidth M x s + l) := by
      have hA' : ¬ l < M.states := by omega
      have hB' : ¬ l < M.states + (x.length + 1) := by omega
      have hne : ¬ (l - (M.states + (x.length + 1)) = j) := by omega
      simp [tgtConj, hA', hB', hB, hne]
    rw [hconj, if_pos rfl, hblk]
  · have hc : (Cob.andT (inTapeT 3 4) (Cob.notT (Cob.eqU (.proj 0) (fldT 8)))).eval
        [List.replicate l true, fieldsWord as] = bw false := by
      rw [hand]
      by_cases hA : M.states + (x.length + 1) ≤ l
      · by_cases hB : l < M.states + (x.length + 1) + s
        · have hC : l = M.states + (x.length + 1) + j := by
            by_contra hne
            exact hwrite ⟨hA, hB, hne⟩
          simp [hC]
        · simp [hB]
      · simp [hA]
    rw [tgtBlockTerm, Cob.eval_iteW hc rfl (rfl : (Cob.catL _).eval _ = _)]
    simp only [Bool.false_eq_true, if_false]
    rw [Cob.eval_catL]
    simp only [List.map_cons, List.map_nil, Cob.eval_constT, List.flatten_cons,
      List.flatten_nil, List.append_nil]
    congr 1
    -- the polarity of the literal
    have hpol : (tgtPolT w).eval [List.replicate l true, fieldsWord as]
        = bw ((decide (l = q') || (decide (l = M.states + i') ||
            decide (l = M.states + (x.length + 1) + s + j'))) ||
              (w && decide (l = M.states + (x.length + 1) + j))) := by
      cases w with
      | false => simpa [tgtPolT] using hmark
      | true =>
          simp only [tgtPolT]
          exact Cob.eval_orT hmark hpw
    rw [eval_litBlockT (tgtPolT w) 1 l as (by omega) _ hpol, h1]
    have hconj : tgtConj M x s a b q' i' j' w j l
        = litF (b * cfgWidth M x s + l)
            ((decide (l = q') || (decide (l = M.states + i') ||
              decide (l = M.states + (x.length + 1) + s + j'))) ||
                (w && decide (l = M.states + (x.length + 1) + j))) := by
      by_cases hA : l < M.states
      · have e2 : ¬ (l = M.states + i') := by omega
        have e3 : ¬ (l = M.states + (x.length + 1) + s + j') := by omega
        have e4 : ¬ (l = M.states + (x.length + 1) + j) := by omega
        simp [tgtConj, hA, e2, e3, e4]
      · by_cases hB : l < M.states + (x.length + 1)
        · have e1 : ¬ (l = q') := by omega
          have e3 : ¬ (l = M.states + (x.length + 1) + s + j') := by omega
          have e4 : ¬ (l = M.states + (x.length + 1) + j) := by omega
          have e2 : (l - M.states = i') ↔ (l = M.states + i') := by omega
          simp only [tgtConj, if_neg hA, if_pos hB, e1, e3, e4, decide_false, Bool.false_or,
            Bool.or_false, Bool.and_false]
          congr 1
          simp [e2]
        · by_cases hC : l < M.states + (x.length + 1) + s
          · have hPW : l = M.states + (x.length + 1) + j := by
              by_contra hne
              exact hwrite ⟨by omega, hC, hne⟩
            have e1 : ¬ (l = q') := by omega
            have e2 : ¬ (l = M.states + i') := by omega
            have e3 : ¬ (l = M.states + (x.length + 1) + s + j') := by omega
            have e5 : l - (M.states + (x.length + 1)) = j := by omega
            have hbool : ((decide (l = q') || (decide (l = M.states + i') ||
                decide (l = M.states + (x.length + 1) + s + j'))) ||
                  (w && decide (l = M.states + (x.length + 1) + j))) = w := by
              have d4 : (decide (l = M.states + (x.length + 1) + j)) = true := decide_eq_true hPW
              simp [e1, e2, e3, d4]
            simp only [tgtConj, if_neg hA, if_neg hB, if_pos hC, if_pos e5, hbool]
          · have e1 : ¬ (l = q') := by omega
            have e2 : ¬ (l = M.states + i') := by omega
            have e4 : ¬ (l = M.states + (x.length + 1) + j) := by omega
            have e3 : (l - (M.states + (x.length + 1) + s) = j') ↔
                (l = M.states + (x.length + 1) + s + j') := by omega
            simp only [tgtConj, if_neg hA, if_neg hB, if_neg hC, e1, e2, e4, decide_false,
              Bool.false_or, Bool.and_false, Bool.or_false]
            congr 1
            simp [e3]
    rw [hconj]

/-- **The term writing the code of the successor-block formula.** -/
def tgtEmitTerm (w : Bool) : Cob := rangeEmitTerm (tgtBlockTerm w) 64

theorem lead1_tgtParam (M : Machine) (x : List Bool) (s : ℕ) (a b q' i' j' j : ℕ) :
    lead1 (tgtParam M x s a b q' i' j' j) = cfgWidth M x s := by
  simp [tgtParam]

theorem length_tgtParam (M : Machine) (x : List Bool) (s : ℕ) (a b q' i' j' j : ℕ) :
    cfgWidth M x s + (b * cfgWidth M x s + a * cfgWidth M x s)
      ≤ (tgtParam M x s a b q' i' j' j).length := by
  simp [tgtParam, fieldsWord]
  omega

/-- **The code of the successor-block formula is written by a Cobham term** from the width in
unary and the parameter word of the situation. -/
theorem enc_tgtF_eval (M : Machine) (x : List Bool) (s : ℕ) (a b q' i' j' : ℕ) (w : Bool)
    (j : ℕ) (hq' : q' < M.states) (hi' : i' ≤ x.length) (hj : j < s) :
    enc (tgtF M x s a b q' i' j' w j)
      = (tgtEmitTerm w).eval
          [List.replicate (cfgWidth M x s) true, tgtParam M x s a b q' i' j' j] ++ enc tt := by
  have hW : ∀ l : ℕ, (tgtBlockTerm w).eval
      [List.replicate l true, tgtParam M x s a b q' i' j' j]
        = [true, false, false] ++ enc (tgtConj M x s a b q' i' j' w j l) :=
    fun l => eval_tgtBlockTerm M x s a b q' i' j' w j l hq' hi' hj
  have hb : ∀ l : ℕ, l ≤ cfgWidth M x s →
      ([true, false, false] ++ enc (tgtConj M x s a b q' i' j' w j l)).length
        ≤ 64 * ((tgtParam M x s a b q' i' j' j).length + 1) := by
    intro l hl
    have hlen := length_tgtParam M x s a b q' i' j' j
    have hsmall : (enc (tgtConj M x s a b q' i' j' w j l)).length
        ≤ 40 + 2 * (b * cfgWidth M x s + l + 1) + 2 * (a * cfgWidth M x s + l + 1) := by
      by_cases hA : l < M.states
      · simp only [tgtConj, if_pos hA, enc_litF]
        cases (decide (l = q')) <;> simp [length_unary] <;> omega
      · by_cases hB : l < M.states + (x.length + 1)
        · simp only [tgtConj, if_neg hA, if_pos hB, enc_litF]
          cases (decide (l - M.states = i')) <;> simp [length_unary] <;> omega
        · by_cases hC : l < M.states + (x.length + 1) + s
          · by_cases hD : l - (M.states + (x.length + 1)) = j
            · simp only [tgtConj, if_neg hA, if_neg hB, if_pos hC, if_pos hD, enc_litF]
              cases w <;> simp [length_unary] <;> omega
            · simp only [tgtConj, if_neg hA, if_neg hB, if_pos hC, if_neg hD]
              simp [iffVar, enc, length_unary]
              omega
          · simp only [tgtConj, if_neg hA, if_neg hB, if_neg hC, enc_litF]
            cases (decide (l - (M.states + (x.length + 1) + s) = j')) <;>
              simp [length_unary] <;> omega
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  rw [tgtF_eq_conjAll, enc_conjAll, tgtEmitTerm,
    eval_rangeEmitTerm (tgtBlockTerm w)
      (fun l => [true, false, false] ++ enc (tgtConj M x s a b q' i' j' w j l))
      (tgtParam M x s a b q' i' j' j) (lead1_tgtParam M x s a b q' i' j' j) hW hb,
    List.flatMap_map]

end QBF

end Complexity.Qbf
