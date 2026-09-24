/-
**The initial and accepting constraints of the reduction are written by Cobham terms.**

Besides the step formula, the reduction of `Start/QbfMachine.lean` has two more constraints: that
the first block carries the padded initial configuration (`Complexity.Qbf.QBF.initF`) and that the
second one carries an accepting configuration (`Complexity.Qbf.QBF.accF`).  Both are built from
the configuration-block formula, whose code `Start/QbfCobCfg.lean` writes with a single Cobham
term, so what is left is the shape around it: for the initial constraint, one literal per cell of
the blank work tape; for the accepting one, a disjunction over every accepting situation — the
accepting control states, which are finitely many for a fixed machine and are unrolled into the
term, and the two head positions, which are swept.

Main definitions:

* `Complexity.Qbf.QBF.initParam`, `.initTerm` — the initial constraint;
* `Complexity.Qbf.QBF.accParam`, `.accTerm` — the accepting constraint.

Main results:

* `Complexity.Qbf.QBF.enc_initF_eval` — **the code of `initF M x s a` is the value of one Cobham
  term**;
* `Complexity.Qbf.QBF.enc_accF_stream` — the code of the accepting constraint is one block per
  accepting situation;
* `Complexity.Qbf.QBF.enc_accF_eval` — **the code of `accF M x s b` is the value of one Cobham
  term**.
-/

import Mathlib
import Start.QbfCobStep

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

open Complexity Complexity.Space

/-! ### A padding field from two fields -/

/-- The padding field, computed from two fields of the parameter word. -/
def padFrom2T (k₀ k₁ : ℕ) : Cob :=
  .comp .smash
    [Cob.uAdd (fldT k₀) (Cob.uAdd (fldT k₁) (constU 3)),
      Cob.uAdd (fldT k₀) (Cob.uAdd (fldT k₁) (constU 3))]

theorem eval_padFrom2T (k₀ k₁ : ℕ) (args : List Word) (w u : ℕ)
    (h₀ : (fldT k₀).eval args = List.replicate w true)
    (h₁ : (fldT k₁).eval args = List.replicate u true) :
    (padFrom2T k₀ k₁).eval args = List.replicate ((w + u + 3) * (w + u + 3)) true := by
  have hu : (Cob.uAdd (fldT k₀) (Cob.uAdd (fldT k₁) (constU 3))).eval args
      = List.replicate (w + (u + 3)) true :=
    Cob.eval_uAdd h₀ (Cob.eval_uAdd h₁ (eval_constU 3 args))
  have hsum : w + (u + 3) = w + u + 3 := by omega
  rw [hsum] at hu
  simp [padFrom2T, hu]

/-! ### The initial constraint -/

/-- The parameter word of the sweep over the cells of the blank work tape. -/
def initTapeParam (M : Machine) (x : List Bool) (s : ℕ) (a : ℕ) : Word :=
  fieldsWord [s, a * cfgWidth M x s + (M.states + (x.length + 1))]

/-- The block of one cell of the blank work tape. -/
def initTapeBlockT : Cob :=
  Cob.catL [Cob.constT [true, false, false, false, true, false, false], idxTerm 1]

/-- The term sweeping the cells of the blank work tape. -/
def initTapeT : Cob := rangeEmitTerm initTapeBlockT 8

theorem eval_initTapeT (M : Machine) (x : List Bool) (s : ℕ) (a : ℕ) :
    initTapeT.eval [List.replicate s true, initTapeParam M x s a]
      = (List.range s).flatMap fun l =>
          [true, false, false] ++
            enc (litF (a * cfgWidth M x s + (M.states + (x.length + 1) + l)) false) := by
  set A := a * cfgWidth M x s + (M.states + (x.length + 1)) with hA
  have hlead : lead1 (initTapeParam M x s a) = s := by
    simp [initTapeParam]
  have hW : ∀ l : ℕ, initTapeBlockT.eval [List.replicate l true, initTapeParam M x s a]
      = [true, false, false] ++ enc (litF (A + l) false) := by
    intro l
    have hidx := eval_idxTerm 1 [s, A] (by simp) l
    have hgd : ([s, A] : List ℕ).getD 1 0 = A := rfl
    rw [hgd] at hidx
    simp only [initTapeBlockT, Cob.eval_catL, List.map_cons, List.map_nil, Cob.eval_constT,
      initTapeParam, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [← hA, hidx, enc_litF]
    simp
  have hb : ∀ l : ℕ, l ≤ s →
      ([true, false, false] ++ enc (litF (A + l) false)).length
        ≤ 8 * ((initTapeParam M x s a).length + 1) := by
    intro l hl
    have hlen : (initTapeParam M x s a).length = s + (A + 2) := by
      simp [initTapeParam, fieldsWord]
      omega
    simp only [List.length_append, List.length_cons, List.length_nil, enc_litF, length_unary,
      hlen]
    simp only [if_neg (by simp : ¬ (false = true))]
    simp only [List.length_cons, List.length_nil]
    omega
  rw [initTapeT, eval_rangeEmitTerm initTapeBlockT
    (fun l => [true, false, false] ++ enc (litF (A + l) false))
    (initTapeParam M x s a) hlead hW hb]
  refine List.flatMap_congr ?_
  intro l _
  have hassoc : A + l = a * cfgWidth M x s + (M.states + (x.length + 1) + l) := by
    rw [hA]; omega
  rw [hassoc]

/-- The parameter word of the initial constraint. -/
def initParam (M : Machine) (x : List Bool) (s : ℕ) (a : ℕ) : Word :=
  fieldsWord [cfgWidth M x s, a * cfgWidth M x s, M.states, M.states + (x.length + 1),
    M.states + (x.length + 1) + s, s]

/-- **The term writing the code of the initial constraint.** -/
def initTerm : Cob :=
  Cob.catL
    [Cob.constT [true, false, false],
      .comp cfgEmitTerm
        [fldT 0, Cob.fieldsT [fldT 0, fldT 1, fldT 2, fldT 3, fldT 4, constU 0, fldT 2, fldT 4]],
      Cob.constT (enc tt),
      .comp initTapeT [fldT 5, Cob.fieldsT [fldT 5, Cob.uAdd (fldT 1) (fldT 3)]],
      Cob.constT (enc tt)]

/-- **The code of the initial constraint is the value of one Cobham term.** -/
theorem enc_initF_eval (M : Machine) (x : List Bool) (s : ℕ) (a : ℕ) (hstates : 0 < M.states)
    (y : Word) :
    enc (initF M x s a) = initTerm.eval [y, initParam M x s a] := by
  set as : List ℕ := [cfgWidth M x s, a * cfgWidth M x s, M.states, M.states + (x.length + 1),
    M.states + (x.length + 1) + s, s] with has
  have hlen : as.length = 6 := rfl
  have hfld : ∀ k, ∀ _ : k < 6, (fldT k).eval [y, initParam M x s a]
      = List.replicate (as.getD k 0) true := by
    intro k hk
    exact eval_fldT k as (by omega) y
  have e0 : as.getD 0 0 = cfgWidth M x s := rfl
  have e1 : as.getD 1 0 = a * cfgWidth M x s := rfl
  have e2 : as.getD 2 0 = M.states := rfl
  have e3 : as.getD 3 0 = M.states + (x.length + 1) := rfl
  have e4 : as.getD 4 0 = M.states + (x.length + 1) + s := rfl
  have e5 : as.getD 5 0 = s := rfl
  have hcfgArg : (Cob.fieldsT [fldT 0, fldT 1, fldT 2, fldT 3, fldT 4, constU 0, fldT 2,
      fldT 4]).eval [y, initParam M x s a] = cfgParam M x s a 0 0 0 := by
    have hz : cfgParam M x s a 0 0 0
        = fieldsWord [cfgWidth M x s, a * cfgWidth M x s, M.states, M.states + (x.length + 1),
            M.states + (x.length + 1) + s, 0, M.states, M.states + (x.length + 1) + s] := by
      simp [cfgParam]
    rw [hz]
    refine Cob.eval_fieldsT ?_
    exact .cons (by rw [hfld 0 (by omega), e0]) (.cons (by rw [hfld 1 (by omega), e1])
      (.cons (by rw [hfld 2 (by omega), e2]) (.cons (by rw [hfld 3 (by omega), e3])
        (.cons (by rw [hfld 4 (by omega), e4]) (.cons (eval_constU 0 _)
          (.cons (by rw [hfld 2 (by omega), e2]) (.cons (by rw [hfld 4 (by omega), e4])
            .nil)))))))
  have hcfg : (Cob.comp cfgEmitTerm
      [fldT 0, Cob.fieldsT [fldT 0, fldT 1, fldT 2, fldT 3, fldT 4, constU 0, fldT 2,
        fldT 4]]).eval [y, initParam M x s a] ++ enc tt = enc (cfgF M x s a 0 0 0) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, hcfgArg, hfld 0 (by omega), e0]
    exact (enc_cfgF_eval M x s a 0 0 0 hstates (Nat.zero_le _)).symm
  have htapeArg : (Cob.fieldsT [fldT 5, Cob.uAdd (fldT 1) (fldT 3)]).eval
      [y, initParam M x s a] = initTapeParam M x s a := by
    rw [initTapeParam]
    refine Cob.eval_fieldsT ?_
    refine .cons (by rw [hfld 5 (by omega), e5]) (.cons ?_ .nil)
    exact Cob.eval_uAdd (by rw [hfld 1 (by omega), e1]) (by rw [hfld 3 (by omega), e3])
  have htape : (Cob.comp initTapeT [fldT 5, Cob.fieldsT [fldT 5, Cob.uAdd (fldT 1) (fldT 3)]]).eval
      [y, initParam M x s a]
      = (List.range s).flatMap fun l =>
          [true, false, false] ++
            enc (litF (a * cfgWidth M x s + (M.states + (x.length + 1) + l)) false) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, htapeArg, hfld 5 (by omega), e5]
    exact eval_initTapeT M x s a
  rw [initTerm, Cob.eval_catL]
  simp only [List.map_cons, List.map_nil, Cob.eval_constT, List.flatten_cons, List.flatten_nil,
    List.append_nil, htape]
  rw [initF, enc_conj, enc_conjAll, List.flatMap_map]
  rw [← hcfg]
  simp [List.append_assoc]

/-! ### The accepting constraint -/

/-- The accepting control states of a machine. -/
def accStates (M : Machine) : List ℕ := (List.range M.states).filter fun q => M.accept q

theorem mem_accStates {M : Machine} {q : ℕ} (h : q ∈ accStates M) : q < M.states := by
  rw [accStates, List.mem_filter] at h
  exact List.mem_range.1 h.1

/-- **The code of the accepting constraint is one block per accepting situation.** -/
theorem enc_accF_stream (M : Machine) (x : List Bool) (s : ℕ) (b : ℕ) :
    enc (accF M x s b)
      = ((accStates M).flatMap fun q =>
          (List.range (x.length + 1)).flatMap fun i =>
            (List.range s).flatMap fun j =>
              [true, false, true] ++ enc (cfgF M x s b q i j)) ++ enc ff := by
  rw [accF, enc_disjAny, List.flatMap_map, accCases, accStates]
  simp only [List.flatMap_assoc, List.flatMap_map]

/-- The parameter word of the sweep over the position of the work head. -/
def accjParam (M : Machine) (x : List Bool) (s : ℕ) (b q i : ℕ) : Word :=
  fieldsWord [s, cfgWidth M x s, b * cfgWidth M x s, M.states, M.states + (x.length + 1),
    M.states + (x.length + 1) + s, q, i,
    (cfgWidth M x s + b * cfgWidth M x s + 3) * (cfgWidth M x s + b * cfgWidth M x s + 3)]

/-- The block of one position of the work head. -/
def accjBlockT : Cob :=
  Cob.catL
    [Cob.constT [true, false, true],
      .comp cfgEmitTerm
        [fldT 1, Cob.fieldsT [fldT 1, fldT 2, fldT 3, fldT 4, fldT 5, fldT 6,
          Cob.uAdd (fldT 3) (fldT 7), Cob.uAdd (fldT 5) (.proj 0)]],
      Cob.constT (enc tt)]

theorem eval_accjBlockT (M : Machine) (x : List Bool) (s : ℕ) (b q i j : ℕ)
    (hq : q < M.states) (hi : i ≤ x.length) :
    accjBlockT.eval [List.replicate j true, accjParam M x s b q i]
      = [true, false, true] ++ enc (cfgF M x s b q i j) := by
  set as : List ℕ := [s, cfgWidth M x s, b * cfgWidth M x s, M.states,
    M.states + (x.length + 1), M.states + (x.length + 1) + s, q, i,
    (cfgWidth M x s + b * cfgWidth M x s + 3) * (cfgWidth M x s + b * cfgWidth M x s + 3)]
    with has
  have hlen : as.length = 9 := rfl
  have hfld : ∀ k, ∀ _ : k < 9, (fldT k).eval [List.replicate j true, accjParam M x s b q i]
      = List.replicate (as.getD k 0) true := by
    intro k hk
    exact eval_fldT k as (by omega) _
  have e1 : as.getD 1 0 = cfgWidth M x s := rfl
  have e2 : as.getD 2 0 = b * cfgWidth M x s := rfl
  have e3 : as.getD 3 0 = M.states := rfl
  have e4 : as.getD 4 0 = M.states + (x.length + 1) := rfl
  have e5 : as.getD 5 0 = M.states + (x.length + 1) + s := rfl
  have e6 : as.getD 6 0 = q := rfl
  have e7 : as.getD 7 0 = i := rfl
  have hproj : (Cob.proj 0).eval [List.replicate j true, accjParam M x s b q i]
      = List.replicate j true := by simp
  have harg : (Cob.fieldsT [fldT 1, fldT 2, fldT 3, fldT 4, fldT 5, fldT 6,
      Cob.uAdd (fldT 3) (fldT 7), Cob.uAdd (fldT 5) (.proj 0)]).eval
        [List.replicate j true, accjParam M x s b q i] = cfgParam M x s b q i j := by
    rw [cfgParam]
    refine Cob.eval_fieldsT ?_
    exact .cons (by rw [hfld 1 (by omega), e1]) (.cons (by rw [hfld 2 (by omega), e2])
      (.cons (by rw [hfld 3 (by omega), e3]) (.cons (by rw [hfld 4 (by omega), e4])
        (.cons (by rw [hfld 5 (by omega), e5]) (.cons (by rw [hfld 6 (by omega), e6])
          (.cons (Cob.eval_uAdd (by rw [hfld 3 (by omega), e3]) (by rw [hfld 7 (by omega), e7]))
            (.cons (Cob.eval_uAdd (by rw [hfld 5 (by omega), e5]) hproj) .nil)))))))
  have hcfg : (Cob.comp cfgEmitTerm
      [fldT 1, Cob.fieldsT [fldT 1, fldT 2, fldT 3, fldT 4, fldT 5, fldT 6,
        Cob.uAdd (fldT 3) (fldT 7), Cob.uAdd (fldT 5) (.proj 0)]]).eval
        [List.replicate j true, accjParam M x s b q i] ++ enc tt = enc (cfgF M x s b q i j) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, harg, hfld 1 (by omega), e1]
    exact (enc_cfgF_eval M x s b q i j hq hi).symm
  rw [accjBlockT, Cob.eval_catL]
  simp only [List.map_cons, List.map_nil, Cob.eval_constT, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  rw [← hcfg]

theorem length_enc_cfgF_le (M : Machine) (x : List Bool) (s : ℕ) (b q i j : ℕ) :
    ([true, false, true] ++ enc (cfgF M x s b q i j)).length
      ≤ 6 * ((cfgWidth M x s + b * cfgWidth M x s + 3) *
          (cfgWidth M x s + b * cfgWidth M x s + 3)) := by
  set W := cfgWidth M x s with hW
  have hvar : (cfgF M x s b q i j).varBound ≤ (b + 1) * W :=
    varBound_cfgF_le (M := M) (x := x) (s := s) (show b < b + 1 by omega)
  have hlen := length_enc_le (cfgF M x s b q i j) ((b + 1) * W) hvar
  have hsize := size_cfgF_le (M := M) (x := x) (s := s) b q i j
  have h1 : (cfgF M x s b q i j).size * ((b + 1) * W + 3) ≤ (W * 5 + 4) * ((b + 1) * W + 3) :=
    Nat.mul_le_mul_right _ hsize
  have hexp : (b + 1) * W = W + b * W := by ring
  have hu : W * 5 + 4 ≤ 5 * (W + b * W + 3) := by
    have h₂ : 0 ≤ b * W := Nat.zero_le _
    nlinarith [h₂]
  have h2 : (W * 5 + 4) * ((b + 1) * W + 3) ≤ 5 * ((W + b * W + 3) * (W + b * W + 3)) := by
    rw [hexp]
    calc (W * 5 + 4) * (W + b * W + 3)
        ≤ (5 * (W + b * W + 3)) * (W + b * W + 3) := Nat.mul_le_mul_right _ hu
      _ = 5 * ((W + b * W + 3) * (W + b * W + 3)) := by ring
  have h3 : 3 ≤ (W + b * W + 3) * (W + b * W + 3) := by
    have h : 3 * 1 ≤ (W + b * W + 3) * (W + b * W + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- The term sweeping the position of the work head. -/
def accjSweepT : Cob := rangeEmitTerm accjBlockT 6

theorem eval_accjSweepT (M : Machine) (x : List Bool) (s : ℕ) (b q i : ℕ)
    (hq : q < M.states) (hi : i ≤ x.length) :
    accjSweepT.eval [List.replicate s true, accjParam M x s b q i]
      = (List.range s).flatMap fun j => [true, false, true] ++ enc (cfgF M x s b q i j) := by
  have hlead : lead1 (accjParam M x s b q i) = s := by simp [accjParam]
  have hpad : (cfgWidth M x s + b * cfgWidth M x s + 3) * (cfgWidth M x s + b * cfgWidth M x s + 3)
      ≤ (accjParam M x s b q i).length := by
    simp [accjParam, fieldsWord]
    omega
  have hb : ∀ j : ℕ, j ≤ s →
      ([true, false, true] ++ enc (cfgF M x s b q i j)).length
        ≤ 6 * ((accjParam M x s b q i).length + 1) := by
    intro j _
    exact le_trans (length_enc_cfgF_le M x s b q i j) (Nat.mul_le_mul_left _ (by omega))
  exact eval_rangeEmitTerm accjBlockT _ (accjParam M x s b q i) hlead
    (fun j => eval_accjBlockT M x s b q i j hq hi) hb

/-- The parameter word of the sweep over the position of the input head. -/
def acciParam (M : Machine) (x : List Bool) (s : ℕ) (b q : ℕ) : Word :=
  fieldsWord [x.length + 1, s, cfgWidth M x s, b * cfgWidth M x s, M.states,
    M.states + (x.length + 1), M.states + (x.length + 1) + s, q,
    (s + 1) * ((cfgWidth M x s + b * cfgWidth M x s + 3) *
      (cfgWidth M x s + b * cfgWidth M x s + 3))]

/-- The block of one position of the input head. -/
def acciBlockT : Cob :=
  Cob.iteT (Cob.ltU (.proj 0) (fldT 0))
    (.comp accjSweepT
      [fldT 1, Cob.fieldsT [fldT 1, fldT 2, fldT 3, fldT 4, fldT 5, fldT 6, fldT 7,
        .proj 0, padFrom2T 2 3]])
    (Cob.constT [])

/-- The word contributed by one position of the input head. -/
def acciWord (M : Machine) (x : List Bool) (s : ℕ) (b q i : ℕ) : Word :=
  if i < x.length + 1 then
    (List.range s).flatMap (fun j => [true, false, true] ++ enc (cfgF M x s b q i j)) else []

theorem eval_acciBlockT (M : Machine) (x : List Bool) (s : ℕ) (b q i : ℕ) (hq : q < M.states) :
    acciBlockT.eval [List.replicate i true, acciParam M x s b q]
      = acciWord M x s b q i := by
  set as : List ℕ := [x.length + 1, s, cfgWidth M x s, b * cfgWidth M x s, M.states,
    M.states + (x.length + 1), M.states + (x.length + 1) + s, q,
    (s + 1) * ((cfgWidth M x s + b * cfgWidth M x s + 3) *
      (cfgWidth M x s + b * cfgWidth M x s + 3))] with has
  have hlen : as.length = 9 := rfl
  have hfld : ∀ k, ∀ _ : k < 9, (fldT k).eval [List.replicate i true, acciParam M x s b q]
      = List.replicate (as.getD k 0) true := by
    intro k hk
    exact eval_fldT k as (by omega) _
  have e0 : as.getD 0 0 = x.length + 1 := rfl
  have e1 : as.getD 1 0 = s := rfl
  have e2 : as.getD 2 0 = cfgWidth M x s := rfl
  have e3 : as.getD 3 0 = b * cfgWidth M x s := rfl
  have e4 : as.getD 4 0 = M.states := rfl
  have e5 : as.getD 5 0 = M.states + (x.length + 1) := rfl
  have e6 : as.getD 6 0 = M.states + (x.length + 1) + s := rfl
  have e7 : as.getD 7 0 = q := rfl
  have hcond : (Cob.ltU (.proj 0) (fldT 0)).eval [List.replicate i true, acciParam M x s b q]
      = bw (decide (i < x.length + 1)) := by
    rw [Cob.eval_ltU, hfld 0 (by omega), e0]
    simp
  by_cases hi : i < x.length + 1
  · have hproj : (Cob.proj 0).eval [List.replicate i true, acciParam M x s b q]
        = List.replicate i true := by simp
    have hpad : (padFrom2T 2 3).eval [List.replicate i true, acciParam M x s b q]
        = List.replicate ((cfgWidth M x s + b * cfgWidth M x s + 3) *
            (cfgWidth M x s + b * cfgWidth M x s + 3)) true :=
      eval_padFrom2T 2 3 _ _ _ (by rw [hfld 2 (by omega), e2]) (by rw [hfld 3 (by omega), e3])
    have harg : (Cob.fieldsT [fldT 1, fldT 2, fldT 3, fldT 4, fldT 5, fldT 6, fldT 7,
        .proj 0, padFrom2T 2 3]).eval [List.replicate i true, acciParam M x s b q]
          = accjParam M x s b q i := by
      rw [accjParam]
      refine Cob.eval_fieldsT ?_
      exact .cons (by rw [hfld 1 (by omega), e1]) (.cons (by rw [hfld 2 (by omega), e2])
        (.cons (by rw [hfld 3 (by omega), e3]) (.cons (by rw [hfld 4 (by omega), e4])
          (.cons (by rw [hfld 5 (by omega), e5]) (.cons (by rw [hfld 6 (by omega), e6])
            (.cons (by rw [hfld 7 (by omega), e7]) (.cons hproj (.cons hpad .nil))))))))
    have hcore : (Cob.comp accjSweepT
        [fldT 1, Cob.fieldsT [fldT 1, fldT 2, fldT 3, fldT 4, fldT 5, fldT 6, fldT 7,
          .proj 0, padFrom2T 2 3]]).eval [List.replicate i true, acciParam M x s b q]
          = (List.range s).flatMap fun j =>
              [true, false, true] ++ enc (cfgF M x s b q i j) := by
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, harg, hfld 1 (by omega), e1]
      exact eval_accjSweepT M x s b q i hq (by omega)
    rw [acciBlockT, Cob.eval_iteW (p := true) (by rw [hcond]; simp [hi]) hcore rfl,
      acciWord, if_pos hi]
    simp
  · rw [acciBlockT, Cob.eval_iteW (p := false) (by rw [hcond]; simp [hi]) rfl
      (Cob.eval_constT _ _), acciWord, if_neg hi]
    simp

/-- The term sweeping the position of the input head. -/
def acciSweepT : Cob := rangeEmitTerm acciBlockT 6

theorem eval_acciSweepT (M : Machine) (x : List Bool) (s : ℕ) (b q : ℕ) (hq : q < M.states) :
    acciSweepT.eval [List.replicate (x.length + 1) true, acciParam M x s b q]
      = (List.range (x.length + 1)).flatMap fun i =>
          (List.range s).flatMap fun j => [true, false, true] ++ enc (cfgF M x s b q i j) := by
  have hlead : lead1 (acciParam M x s b q) = x.length + 1 := by simp [acciParam]
  have hpad : (s + 1) * ((cfgWidth M x s + b * cfgWidth M x s + 3) *
      (cfgWidth M x s + b * cfgWidth M x s + 3)) ≤ (acciParam M x s b q).length := by
    simp [acciParam, fieldsWord]
    omega
  have hb : ∀ i : ℕ, i ≤ x.length + 1 →
      (acciWord M x s b q i).length ≤ 6 * ((acciParam M x s b q).length + 1) := by
    intro i _
    by_cases hi : i < x.length + 1
    · rw [acciWord, if_pos hi]
      have hall : ∀ j ∈ List.range s,
          ([true, false, true] ++ enc (cfgF M x s b q i j)).length
            ≤ 6 * ((cfgWidth M x s + b * cfgWidth M x s + 3) *
                (cfgWidth M x s + b * cfgWidth M x s + 3)) := by
        intro j _
        exact length_enc_cfgF_le M x s b q i j
      have h1 := length_flatMap_le (List.range s) _ _ hall
      rw [List.length_range] at h1
      refine le_trans h1 ?_
      have h2 : s * (6 * ((cfgWidth M x s + b * cfgWidth M x s + 3) *
          (cfgWidth M x s + b * cfgWidth M x s + 3)))
          = 6 * (s * ((cfgWidth M x s + b * cfgWidth M x s + 3) *
              (cfgWidth M x s + b * cfgWidth M x s + 3))) := by ring
      rw [h2]
      refine Nat.mul_le_mul_left _ ?_
      have h3 : s * ((cfgWidth M x s + b * cfgWidth M x s + 3) *
          (cfgWidth M x s + b * cfgWidth M x s + 3))
          ≤ (s + 1) * ((cfgWidth M x s + b * cfgWidth M x s + 3) *
              (cfgWidth M x s + b * cfgWidth M x s + 3)) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    · rw [acciWord, if_neg hi]
      simp
  rw [acciSweepT, eval_rangeEmitTerm acciBlockT (acciWord M x s b q) (acciParam M x s b q)
    hlead (fun i => eval_acciBlockT M x s b q i hq) hb]
  refine List.flatMap_congr ?_
  intro i hi
  rw [acciWord, if_pos (List.mem_range.1 hi)]

/-- The parameter word of the accepting constraint. -/
def accParam (M : Machine) (x : List Bool) (s : ℕ) (b : ℕ) : Word :=
  fieldsWord [cfgWidth M x s, b * cfgWidth M x s, M.states, M.states + (x.length + 1),
    M.states + (x.length + 1) + s, x.length, s]

/-- **The term writing the code of the accepting constraint.** -/
def accTerm (M : Machine) : Cob :=
  Cob.catL
    (((accStates M).map fun q =>
        Cob.comp acciSweepT
          [Cob.uSucc (fldT 5),
            Cob.fieldsT [Cob.uSucc (fldT 5), fldT 6, fldT 0, fldT 1, fldT 2, fldT 3, fldT 4,
              constU q, .comp .smash [Cob.uSucc (fldT 6), padFrom2T 0 1]]])
      ++ [Cob.constT (enc ff)])

/-- **The code of the accepting constraint is the value of one Cobham term.** -/
theorem enc_accF_eval (M : Machine) (x : List Bool) (s : ℕ) (b : ℕ) (y : Word) :
    enc (accF M x s b) = (accTerm M).eval [y, accParam M x s b] := by
  set as : List ℕ := [cfgWidth M x s, b * cfgWidth M x s, M.states, M.states + (x.length + 1),
    M.states + (x.length + 1) + s, x.length, s] with has
  have hlen : as.length = 7 := rfl
  have hfld : ∀ k, ∀ _ : k < 7, (fldT k).eval [y, accParam M x s b]
      = List.replicate (as.getD k 0) true := by
    intro k hk
    exact eval_fldT k as (by omega) _
  have e0 : as.getD 0 0 = cfgWidth M x s := rfl
  have e1 : as.getD 1 0 = b * cfgWidth M x s := rfl
  have e2 : as.getD 2 0 = M.states := rfl
  have e3 : as.getD 3 0 = M.states + (x.length + 1) := rfl
  have e4 : as.getD 4 0 = M.states + (x.length + 1) + s := rfl
  have e5 : as.getD 5 0 = x.length := rfl
  have e6 : as.getD 6 0 = s := rfl
  have hsucc : (Cob.uSucc (fldT 5)).eval [y, accParam M x s b]
      = List.replicate (x.length + 1) true :=
    Cob.eval_uSucc (by rw [hfld 5 (by omega), e5])
  have hsucc' : (Cob.uSucc (fldT 6)).eval [y, accParam M x s b] = List.replicate (s + 1) true :=
    Cob.eval_uSucc (by rw [hfld 6 (by omega), e6])
  have hpad : (padFrom2T 0 1).eval [y, accParam M x s b]
      = List.replicate ((cfgWidth M x s + b * cfgWidth M x s + 3) *
          (cfgWidth M x s + b * cfgWidth M x s + 3)) true :=
    eval_padFrom2T 0 1 _ _ _ (by rw [hfld 0 (by omega), e0]) (by rw [hfld 1 (by omega), e1])
  have hpadI : (Cob.comp .smash [Cob.uSucc (fldT 6), padFrom2T 0 1]).eval [y, accParam M x s b]
      = List.replicate ((s + 1) * ((cfgWidth M x s + b * cfgWidth M x s + 3) *
          (cfgWidth M x s + b * cfgWidth M x s + 3))) true := by
    simp [hsucc', hpad]
  have hq : ∀ q ∈ accStates M,
      (Cob.comp acciSweepT [Cob.uSucc (fldT 5),
        Cob.fieldsT [Cob.uSucc (fldT 5), fldT 6, fldT 0, fldT 1, fldT 2, fldT 3, fldT 4,
          constU q, .comp .smash [Cob.uSucc (fldT 6), padFrom2T 0 1]]]).eval
            [y, accParam M x s b]
        = (List.range (x.length + 1)).flatMap fun i =>
            (List.range s).flatMap fun j => [true, false, true] ++ enc (cfgF M x s b q i j) := by
    intro q hqm
    have harg : (Cob.fieldsT [Cob.uSucc (fldT 5), fldT 6, fldT 0, fldT 1, fldT 2, fldT 3, fldT 4,
        constU q, .comp .smash [Cob.uSucc (fldT 6), padFrom2T 0 1]]).eval [y, accParam M x s b]
          = acciParam M x s b q := by
      rw [acciParam]
      refine Cob.eval_fieldsT ?_
      exact .cons hsucc (.cons (by rw [hfld 6 (by omega), e6])
        (.cons (by rw [hfld 0 (by omega), e0]) (.cons (by rw [hfld 1 (by omega), e1])
          (.cons (by rw [hfld 2 (by omega), e2]) (.cons (by rw [hfld 3 (by omega), e3])
            (.cons (by rw [hfld 4 (by omega), e4]) (.cons (eval_constU q _)
              (.cons hpadI .nil))))))))
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, harg, hsucc]
    exact eval_acciSweepT M x s b q (mem_accStates hqm)
  have hmap := eval_catL_map (accStates M)
    (fun q => Cob.comp acciSweepT [Cob.uSucc (fldT 5),
      Cob.fieldsT [Cob.uSucc (fldT 5), fldT 6, fldT 0, fldT 1, fldT 2, fldT 3, fldT 4,
        constU q, .comp .smash [Cob.uSucc (fldT 6), padFrom2T 0 1]]])
    (fun q => (List.range (x.length + 1)).flatMap fun i =>
      (List.range s).flatMap fun j => [true, false, true] ++ enc (cfgF M x s b q i j))
    [y, accParam M x s b] hq
  rw [enc_accF_stream, accTerm, Cob.eval_catL, List.map_append, List.flatten_append]
  simp only [List.map_cons, List.map_nil, Cob.eval_constT, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  congr 1
  simpa [Cob.eval_catL, List.map_map] using hmap.symm

end QBF

end Complexity.Qbf
