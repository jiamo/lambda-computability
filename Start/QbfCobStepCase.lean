/-
**One case of the step formula is written by a Cobham term, guarded by the transition table.**

The step formula of the reduction (`Complexity.Qbf.QBF.stepF`) is a disjunction over the
*situations* of the machine — a control state, a position of each head, the bit read on the work
tape — and over the instructions the transition function offers in them.  This module writes the
block of one such case: the tag bit of the disjunction, the code of the two configuration-block
formulas of `Start/QbfCobCfg.lean` and, between them, the literal of the bit read.

Two points make the case a *case* rather than a plain block.  First, the situation is written in a
single parameter word, from which the term assembles, by unary arithmetic, the parameter words the
two block emitters expect — in particular the positions of the heads after the move, which are the
successor, the predecessor or the capped successor of the current ones.  Second, a case is only
present in the formula when the instruction belongs to the transition table at the bit the machine
reads and when the move stays inside the space bound: the term computes that *guard* — the table
is a constant of the term, the bit read off the input word at a unary position — and emits the
empty word when it fails, so that the concatenation over all candidate cases is exactly the code
of the disjunction over the filtered list.

Main definitions:

* `Complexity.Qbf.QBF.caseParam` — the parameter word of a situation;
* `Complexity.Qbf.QBF.moveInT`, `.moveWorkT` — the head positions after a move;
* `Complexity.Qbf.QBF.cfgArgT`, `.tgtArgT` — the parameter words of the two block emitters;
* `Complexity.Qbf.QBF.stepCaseTerm`, `.guardT`, `.caseTerm` — the block of a case, its guard, and
  the guarded block.

Main results:

* `Complexity.Qbf.QBF.eval_cfgArgT`, `.eval_tgtArgT` — the assembled parameter words are the ones
  the emitters of `Start/QbfCobCfg.lean` expect;
* `Complexity.Qbf.QBF.eval_stepCaseTerm` — **the code of one case of the step formula is the value
  of one Cobham term** at the input word and the parameter word of the situation;
* `Complexity.Qbf.QBF.eval_guardT` — the guard of a case is computed by a Cobham term;
* `Complexity.Qbf.QBF.eval_caseTerm` — **a case contributes its block exactly when it belongs to
  the list of cases**.
-/

import Mathlib
import Start.CobhamUnary
import Start.QbfCobCfg

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

open Complexity Complexity.Space

/-! ### The parameter word of a situation -/

/-- The parameter word of a situation: the width, the offsets of the two blocks, the three
boundaries of the layout, the two head positions, the length of the input and the space bound,
all in unary. -/
def caseParam (M : Machine) (x : List Bool) (s : ℕ) (a b i j : ℕ) : Word :=
  fieldsWord [cfgWidth M x s, a * cfgWidth M x s, b * cfgWidth M x s, M.states,
    M.states + (x.length + 1), M.states + (x.length + 1) + s, i, j, x.length, s]

/-- The list of the fields of `caseParam`. -/
def caseFields (M : Machine) (x : List Bool) (s : ℕ) (a b i j : ℕ) : List ℕ :=
  [cfgWidth M x s, a * cfgWidth M x s, b * cfgWidth M x s, M.states,
    M.states + (x.length + 1), M.states + (x.length + 1) + s, i, j, x.length, s]

theorem caseParam_eq (M : Machine) (x : List Bool) (s : ℕ) (a b i j : ℕ) :
    caseParam M x s a b i j = fieldsWord (caseFields M x s a b i j) := rfl

@[simp] theorem length_caseFields (M : Machine) (x : List Bool) (s : ℕ) (a b i j : ℕ) :
    (caseFields M x s a b i j).length = 10 := rfl

theorem eval_fld (M : Machine) (x : List Bool) (s : ℕ) (a b i j k : ℕ) (hk : k < 10) :
    (fldT k).eval [x, caseParam M x s a b i j]
      = List.replicate ((caseFields M x s a b i j).getD k 0) true :=
  eval_fldT k (caseFields M x s a b i j) (by simpa using hk) x

/-- The unary word of a constant. -/
def constU (k : ℕ) : Cob := Cob.constT (List.replicate k true)

@[simp] theorem eval_constU (k : ℕ) (args : List Word) :
    (constU k).eval args = List.replicate k true := Cob.eval_constT _ _

/-! ### The head positions after a move -/

/-- The position of the input head after the move `d`. -/
def moveInT : Dir → Cob
  | .left => Cob.uPred (fldT 6)
  | .right => Cob.uMin (Cob.uSucc (fldT 6)) (fldT 8)
  | .stay => fldT 6

/-- The position of the work head after the move `d`. -/
def moveWorkT : Dir → Cob
  | .left => Cob.uPred (fldT 7)
  | .right => Cob.uSucc (fldT 7)
  | .stay => fldT 7

theorem eval_moveInT (M : Machine) (x : List Bool) (s : ℕ) (a b i j : ℕ) (d : Dir) :
    (moveInT d).eval [x, caseParam M x s a b i j]
      = List.replicate (moveIn x.length i d) true := by
  have h6 := eval_fld M x s a b i j 6 (by omega)
  have h8 := eval_fld M x s a b i j 8 (by omega)
  have e6 : (caseFields M x s a b i j).getD 6 0 = i := rfl
  have e8 : (caseFields M x s a b i j).getD 8 0 = x.length := rfl
  rw [e6] at h6
  rw [e8] at h8
  cases d with
  | left => simpa [moveInT, moveIn] using Cob.eval_uPred h6
  | right =>
      simpa [moveInT, moveIn] using Cob.eval_uMin (Cob.eval_uSucc h6) h8
  | stay => simpa [moveInT, moveIn] using h6

theorem eval_moveWorkT (M : Machine) (x : List Bool) (s : ℕ) (a b i j : ℕ) (d : Dir) :
    (moveWorkT d).eval [x, caseParam M x s a b i j]
      = List.replicate (moveWork j d) true := by
  have h7 := eval_fld M x s a b i j 7 (by omega)
  have e7 : (caseFields M x s a b i j).getD 7 0 = j := rfl
  rw [e7] at h7
  cases d with
  | left => simpa [moveWorkT, moveWork] using Cob.eval_uPred h7
  | right => simpa [moveWorkT, moveWork] using Cob.eval_uSucc h7
  | stay => simpa [moveWorkT, moveWork] using h7

/-! ### The parameter words of the two block emitters -/

/-- The parameter word the configuration-block emitter expects. -/
def cfgArgT (q : ℕ) : Cob :=
  Cob.fieldsT [fldT 0, fldT 1, fldT 3, fldT 4, fldT 5, constU q,
    Cob.uAdd (fldT 3) (fldT 6), Cob.uAdd (fldT 5) (fldT 7)]

theorem eval_cfgArgT (M : Machine) (x : List Bool) (s : ℕ) (a b i j q : ℕ) :
    (cfgArgT q).eval [x, caseParam M x s a b i j] = cfgParam M x s a q i j := by
  have h0 := eval_fld M x s a b i j 0 (by omega)
  have h1 := eval_fld M x s a b i j 1 (by omega)
  have h3 := eval_fld M x s a b i j 3 (by omega)
  have h4 := eval_fld M x s a b i j 4 (by omega)
  have h5 := eval_fld M x s a b i j 5 (by omega)
  have h6 := eval_fld M x s a b i j 6 (by omega)
  have h7 := eval_fld M x s a b i j 7 (by omega)
  have e0 : (caseFields M x s a b i j).getD 0 0 = cfgWidth M x s := rfl
  have e1 : (caseFields M x s a b i j).getD 1 0 = a * cfgWidth M x s := rfl
  have e3 : (caseFields M x s a b i j).getD 3 0 = M.states := rfl
  have e4 : (caseFields M x s a b i j).getD 4 0 = M.states + (x.length + 1) := rfl
  have e5 : (caseFields M x s a b i j).getD 5 0 = M.states + (x.length + 1) + s := rfl
  have e6 : (caseFields M x s a b i j).getD 6 0 = i := rfl
  have e7 : (caseFields M x s a b i j).getD 7 0 = j := rfl
  rw [e0] at h0; rw [e1] at h1; rw [e3] at h3; rw [e4] at h4; rw [e5] at h5
  rw [e6] at h6; rw [e7] at h7
  rw [cfgArgT, cfgParam]
  refine Cob.eval_fieldsT ?_
  exact .cons h0 (.cons h1 (.cons h3 (.cons h4 (.cons h5 (.cons (eval_constU q _)
    (.cons (Cob.eval_uAdd h3 h6) (.cons (Cob.eval_uAdd h5 h7) .nil)))))))

/-- The parameter word the successor-block emitter expects. -/
def tgtArgT (q' : ℕ) (d₁ d₂ : Dir) : Cob :=
  Cob.fieldsT [fldT 0, fldT 2, fldT 1, fldT 4, fldT 5, constU q',
    Cob.uAdd (fldT 3) (moveInT d₁), Cob.uAdd (fldT 5) (moveWorkT d₂),
    Cob.uAdd (fldT 4) (fldT 7)]

theorem eval_tgtArgT (M : Machine) (x : List Bool) (s : ℕ) (a b i j q' : ℕ) (d₁ d₂ : Dir) :
    (tgtArgT q' d₁ d₂).eval [x, caseParam M x s a b i j]
      = tgtParam M x s a b q' (moveIn x.length i d₁) (moveWork j d₂) j := by
  have h0 := eval_fld M x s a b i j 0 (by omega)
  have h1 := eval_fld M x s a b i j 1 (by omega)
  have h2 := eval_fld M x s a b i j 2 (by omega)
  have h3 := eval_fld M x s a b i j 3 (by omega)
  have h4 := eval_fld M x s a b i j 4 (by omega)
  have h5 := eval_fld M x s a b i j 5 (by omega)
  have h7 := eval_fld M x s a b i j 7 (by omega)
  have e0 : (caseFields M x s a b i j).getD 0 0 = cfgWidth M x s := rfl
  have e1 : (caseFields M x s a b i j).getD 1 0 = a * cfgWidth M x s := rfl
  have e2 : (caseFields M x s a b i j).getD 2 0 = b * cfgWidth M x s := rfl
  have e3 : (caseFields M x s a b i j).getD 3 0 = M.states := rfl
  have e4 : (caseFields M x s a b i j).getD 4 0 = M.states + (x.length + 1) := rfl
  have e5 : (caseFields M x s a b i j).getD 5 0 = M.states + (x.length + 1) + s := rfl
  have e7 : (caseFields M x s a b i j).getD 7 0 = j := rfl
  rw [e0] at h0; rw [e1] at h1; rw [e2] at h2; rw [e3] at h3; rw [e4] at h4; rw [e5] at h5
  rw [e7] at h7
  have hin := eval_moveInT M x s a b i j d₁
  have hwk := eval_moveWorkT M x s a b i j d₂
  rw [tgtArgT, tgtParam]
  refine Cob.eval_fieldsT ?_
  exact .cons h0 (.cons h2 (.cons h1 (.cons h4 (.cons h5 (.cons (eval_constU q' _)
    (.cons (Cob.eval_uAdd h3 hin) (.cons (Cob.eval_uAdd h5 hwk)
      (.cons (Cob.eval_uAdd h4 h7) .nil))))))))

/-! ### The block of a case -/

/-- The literal of the bit the machine reads under its work head. -/
def readLitT (bit : Bool) : Cob :=
  Cob.catL
    [Cob.constT (if bit then [false, false] else [false, true, false, false]),
      Cob.uAdd (fldT 1) (Cob.uAdd (fldT 4) (fldT 7)), Cob.constT [false]]

theorem eval_readLitT (M : Machine) (x : List Bool) (s : ℕ) (a b i j : ℕ) (bit : Bool) :
    (readLitT bit).eval [x, caseParam M x s a b i j]
      = enc (litF (a * cfgWidth M x s + (M.states + (x.length + 1) + j)) bit) := by
  have h1 := eval_fld M x s a b i j 1 (by omega)
  have h4 := eval_fld M x s a b i j 4 (by omega)
  have h7 := eval_fld M x s a b i j 7 (by omega)
  have e1 : (caseFields M x s a b i j).getD 1 0 = a * cfgWidth M x s := rfl
  have e4 : (caseFields M x s a b i j).getD 4 0 = M.states + (x.length + 1) := rfl
  have e7 : (caseFields M x s a b i j).getD 7 0 = j := rfl
  rw [e1] at h1; rw [e4] at h4; rw [e7] at h7
  have hidx := Cob.eval_uAdd h1 (Cob.eval_uAdd h4 h7)
  rw [readLitT, Cob.eval_catL]
  simp only [List.map_cons, List.map_nil, Cob.eval_constT, hidx, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  rw [enc_litF, unary, ← List.append_assoc]

/-- **The block of one case of the step formula**: the tag bit of the disjunction, then the code
of the case itself. -/
def stepCaseTerm (q q' : ℕ) (bit w : Bool) (d₁ d₂ : Dir) : Cob :=
  Cob.catL
    [Cob.constT [true, false, true], Cob.constT [true, false, false],
      Cob.constT [true, false, false],
      .comp cfgEmitTerm [fldT 0, cfgArgT q], Cob.constT (enc tt),
      readLitT bit,
      .comp (tgtEmitTerm w) [fldT 0, tgtArgT q' d₁ d₂], Cob.constT (enc tt)]

theorem eval_stepCaseTerm (M : Machine) (x : List Bool) (s : ℕ) (a b i j q : ℕ) (bit : Bool)
    (t : ℕ × Bool × Dir × Dir) (hq : q < M.states) (hq' : t.1 < M.states) (hi : i ≤ x.length)
    (hj : j < s) :
    (stepCaseTerm q t.1 bit t.2.1 t.2.2.1 t.2.2.2).eval [x, caseParam M x s a b i j]
      = [true, false, true] ++ enc (stepCase M x s a b q i j bit t) := by
  have h0 := eval_fld M x s a b i j 0 (by omega)
  have e0 : (caseFields M x s a b i j).getD 0 0 = cfgWidth M x s := rfl
  rw [e0] at h0
  have hcfg : (Cob.comp cfgEmitTerm [fldT 0, cfgArgT q]).eval [x, caseParam M x s a b i j]
      ++ enc tt = enc (cfgF M x s a q i j) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, h0,
      eval_cfgArgT M x s a b i j q]
    exact (enc_cfgF_eval M x s a q i j hq hi).symm
  have hi' : moveIn x.length i t.2.2.1 ≤ x.length := moveIn_le _ _ _ hi
  have htgt : (Cob.comp (tgtEmitTerm t.2.1) [fldT 0, tgtArgT t.1 t.2.2.1 t.2.2.2]).eval
      [x, caseParam M x s a b i j] ++ enc tt
      = enc (tgtF M x s a b t.1 (moveIn x.length i t.2.2.1) (moveWork j t.2.2.2) t.2.1 j) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, h0,
      eval_tgtArgT M x s a b i j t.1 t.2.2.1 t.2.2.2]
    exact (enc_tgtF_eval M x s a b t.1 (moveIn x.length i t.2.2.1) (moveWork j t.2.2.2)
      t.2.1 j hq' hi' hj).symm
  rw [stepCaseTerm, Cob.eval_catL]
  simp only [List.map_cons, List.map_nil, Cob.eval_constT,
    eval_readLitT M x s a b i j bit, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [stepCase]
  simp only [enc_conj]
  rw [← hcfg, ← htgt]
  simp [List.append_assoc]

/-! ### The guard of a case -/

/-- The guard of a case: the instruction belongs to the transition table at the bit the machine
reads, and the move of the work head stays inside the space bound.  The table is a constant of the
term; only the bit of the input word is read at run time. -/
def guardT (M : Machine) (q : ℕ) (bit : Bool) (t : ℕ × Bool × Dir × Dir) : Cob :=
  Cob.andT
    (Cob.iteT (Cob.eqU (fldT 6) (fldT 8))
      (Cob.constT (bw (decide (t ∈ M.delta q none bit))))
      (Cob.iteT (Cob.bitU (fldT 6) (.proj 0))
        (Cob.constT (bw (decide (t ∈ M.delta q (some true) bit))))
        (Cob.constT (bw (decide (t ∈ M.delta q (some false) bit))))))
    (Cob.ltU (moveWorkT t.2.2.2) (fldT 9))

theorem eval_guardT (M : Machine) (x : List Bool) (s : ℕ) (a b i j q : ℕ) (bit : Bool)
    (t : ℕ × Bool × Dir × Dir) (hi : i ≤ x.length) :
    (guardT M q bit t).eval [x, caseParam M x s a b i j]
      = bw (decide (t ∈ M.delta q x[i]? bit) && decide (moveWork j t.2.2.2 < s)) := by
  have h6 := eval_fld M x s a b i j 6 (by omega)
  have h8 := eval_fld M x s a b i j 8 (by omega)
  have h9 := eval_fld M x s a b i j 9 (by omega)
  have e6 : (caseFields M x s a b i j).getD 6 0 = i := rfl
  have e8 : (caseFields M x s a b i j).getD 8 0 = x.length := rfl
  have e9 : (caseFields M x s a b i j).getD 9 0 = s := rfl
  rw [e6] at h6; rw [e8] at h8; rw [e9] at h9
  have hmove : (Cob.ltU (moveWorkT t.2.2.2) (fldT 9)).eval [x, caseParam M x s a b i j]
      = bw (decide (moveWork j t.2.2.2 < s)) := by
    rw [Cob.eval_ltU, eval_moveWorkT M x s a b i j t.2.2.2, h9]
    simp
  have hdelta : (Cob.iteT (Cob.eqU (fldT 6) (fldT 8))
      (Cob.constT (bw (decide (t ∈ M.delta q none bit))))
      (Cob.iteT (Cob.bitU (fldT 6) (.proj 0))
        (Cob.constT (bw (decide (t ∈ M.delta q (some true) bit))))
        (Cob.constT (bw (decide (t ∈ M.delta q (some false) bit)))))).eval
        [x, caseParam M x s a b i j]
      = bw (decide (t ∈ M.delta q x[i]? bit)) := by
    have heq : (Cob.eqU (fldT 6) (fldT 8)).eval [x, caseParam M x s a b i j]
        = bw (decide (i = x.length)) := by
      rw [Cob.eval_eqU, h6, h8]
      simp
    by_cases hend : i = x.length
    · have hnone : x[i]? = none := by
        rw [hend]
        simp
      rw [Cob.eval_iteW (p := true) (by rw [heq]; simp [hend])
        (Cob.eval_constT _ _) rfl, hnone]
      simp
    · have hlt : i < x.length := by omega
      have hsome : x[i]? = some (x.getD i false) := by
        rw [List.getElem?_eq_getElem hlt]
        congr 1
        rw [List.getD_eq_getElem _ _ hlt]
      have hbit : (Cob.bitU (fldT 6) (.proj 0)).eval [x, caseParam M x s a b i j]
          = bw (x.getD i false) := by
        rw [Cob.eval_bitU, h6]
        simp
      rw [Cob.eval_iteW (p := false) (by rw [heq]; simp [hend]) rfl rfl]
      simp only [Bool.false_eq_true, if_false, hsome]
      cases hx : x.getD i false with
      | false =>
          rw [Cob.eval_iteW (p := false) (by rw [hbit, hx]) (Cob.eval_constT _ _)
            (Cob.eval_constT _ _)]
          simp
      | true =>
          rw [Cob.eval_iteW (p := true) (by rw [hbit, hx]) (Cob.eval_constT _ _)
            (Cob.eval_constT _ _)]
          simp
  rw [guardT]
  exact Cob.eval_andT hdelta hmove

/-- **The guarded block of a case**: the block when the case belongs to the list of cases, and
the empty word otherwise. -/
def caseTerm (M : Machine) (q : ℕ) (bit : Bool) (t : ℕ × Bool × Dir × Dir) : Cob :=
  Cob.iteT (guardT M q bit t) (stepCaseTerm q t.1 bit t.2.1 t.2.2.1 t.2.2.2) (Cob.constT [])

theorem eval_caseTerm (M : Machine) (x : List Bool) (s : ℕ) (a b i j q : ℕ) (bit : Bool)
    (t : ℕ × Bool × Dir × Dir) (hq : q < M.states) (hq' : t.1 < M.states) (hi : i ≤ x.length)
    (hj : j < s) :
    (caseTerm M q bit t).eval [x, caseParam M x s a b i j]
      = (if t ∈ M.delta q x[i]? bit ∧ moveWork j t.2.2.2 < s then
          [true, false, true] ++ enc (stepCase M x s a b q i j bit t) else []) := by
  have hg := eval_guardT M x s a b i j q bit t hi
  rw [caseTerm, Cob.eval_iteW hg (eval_stepCaseTerm M x s a b i j q bit t hq hq' hi hj)
    (Cob.eval_constT _ _)]
  by_cases h : t ∈ M.delta q x[i]? bit ∧ moveWork j t.2.2.2 < s
  · simp [h.1, h.2]
  · rw [if_neg h]
    by_cases h₁ : t ∈ M.delta q x[i]? bit
    · have h₂ : ¬ moveWork j t.2.2.2 < s := fun hc => h ⟨h₁, hc⟩
      simp [h₁, h₂]
    · simp [h₁]

end QBF

end Complexity.Qbf
