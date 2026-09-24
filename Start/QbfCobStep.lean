/-
**The step formula of the reduction is written by a Cobham term.**

`Start/QbfCobStepCase.lean` writes the block of *one* case of the step formula
(`Complexity.Qbf.QBF.stepF`), guarded by the transition table.  The formula itself is the
disjunction over every case: a control state, a position of the input head, a position of the work
head, the bit read on the work tape, and an instruction.  For a fixed machine the states and the
instructions are finitely many, so those two loops are unrolled into the term; the two head
positions are swept, by a nest of two range emitters.

The module first puts the code of the step formula in streaming shape — one block per case, in the
order of the case list, the filtered-out cases contributing the empty word — and then writes each
loop with a Cobham term.  The parameter words of the sweeps carry the input of the simulated
machine after their unary fields (`Start/CobhamFieldsApp.lean`), because inside a sweep only the
counter and one parameter word are available, and a padding field long enough for the emitted
blocks.

Main definitions:

* `Complexity.Qbf.QBF.caseIdx` — the finite list of (bit read, instruction) pairs;
* `Complexity.Qbf.QBF.innerT` — the blocks of one situation, unrolled;
* `Complexity.Qbf.QBF.jParam`, `.jSweepT`, `.iParam`, `.iSweepT` — the two sweeps;
* `Complexity.Qbf.QBF.stepParam`, `.stepTerm` — the whole step formula.

Main results:

* `Complexity.Qbf.QBF.enc_stepF_stream` — **the code of the step formula is one block per case**;
* `Complexity.Qbf.QBF.eval_innerT` — the blocks of one situation are written by one term;
* `Complexity.Qbf.QBF.eval_jSweepT`, `.eval_iSweepT` — the two sweeps are correct;
* `Complexity.Qbf.QBF.enc_stepF_eval` — **the code of `stepF M x s a b` is the value of one
  Cobham term** at the input word and the parameter word of the two blocks.
-/

import Mathlib
import Start.CobhamFieldsApp
import Start.QbfCobStepCase

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-- Concatenating the values of a family of terms, one per element of a list. -/
theorem eval_catL_map {α : Type} (l : List α) (F : α → Cob) (Wf : α → Word)
    (args : List Word) (h : ∀ z ∈ l, (F z).eval args = Wf z) :
    (Cob.catL (l.map F)).eval args = l.flatMap Wf := by
  induction l with
  | nil => simp [Cob.catL]
  | cons z l ih =>
      have hz := h z (by simp)
      have hrest := ih fun y hy => h y (by simp [hy])
      simp only [List.map_cons, Cob.eval_catL, List.map_cons, List.flatten_cons,
        List.flatMap_cons, hz]
      simpa [Cob.eval_catL] using congrArg (fun w => (F z).eval args ++ w) hrest

/-- Flattening over a filtered list is flattening over the whole list, the rejected elements
contributing the empty word. -/
theorem flatMap_filter_eq {α : Type} (l : List α) (P : α → Bool) (f : α → List Bool) :
    (l.filter P).flatMap f = l.flatMap (fun z => if P z then f z else []) := by
  induction l with
  | nil => simp
  | cons z l ih =>
      by_cases h : P z
      · simp [h, ih]
      · simp [h, ih]

end Complexity

namespace Complexity.Qbf

namespace QBF

open Complexity Complexity.Space

/-! ### The code of the step formula as a stream of blocks -/

/-- The finite list of the (bit read, instruction) pairs of a machine. -/
def caseIdx (M : Machine) : List (Bool × (ℕ × Bool × Dir × Dir)) :=
  ([false, true] : List Bool).flatMap fun bit => (allInstr M.states).map fun t => (bit, t)

theorem mem_caseIdx {M : Machine} {z : Bool × (ℕ × Bool × Dir × Dir)} :
    z ∈ caseIdx M → z.2.1 < M.states := by
  intro hz
  simp only [caseIdx, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  obtain ⟨bit, -, t, ht, rfl⟩ := hz
  exact mem_allInstr.1 ht

/-- The word contributed by one situation: one block per candidate instruction, the ones the
transition table does not offer contributing the empty word. -/
def innerWord (M : Machine) (x : List Bool) (s : ℕ) (a b q i j : ℕ) : Word :=
  (caseIdx M).flatMap fun z =>
    if z.2 ∈ M.delta q x[i]? z.1 ∧ moveWork j z.2.2.2.2 < s then
      [true, false, true] ++ enc (stepCase M x s a b q i j z.1 z.2) else []

/-- **The code of the step formula is one block per case**, in the order of the case list. -/
theorem enc_stepF_stream (M : Machine) (x : List Bool) (s : ℕ) (a b : ℕ) :
    enc (stepF M x s a b)
      = ((List.range M.states).flatMap fun q =>
          (List.range (x.length + 1)).flatMap fun i =>
            (List.range s).flatMap fun j => innerWord M x s a b q i j) ++ enc ff := by
  rw [stepF, enc_disjAny, List.flatMap_map]
  congr 1
  rw [caseList]
  simp only [List.flatMap_assoc]
  refine List.flatMap_congr ?_
  intro q _
  refine List.flatMap_congr ?_
  intro i _
  refine List.flatMap_congr ?_
  intro j _
  rw [innerWord, caseIdx]
  simp only [List.flatMap_assoc, List.flatMap_map]
  refine List.flatMap_congr ?_
  intro bit _
  rw [flatMap_filter_eq]
  refine List.flatMap_congr ?_
  intro t _
  by_cases h : t ∈ M.delta q x[i]? bit ∧ moveWork j t.2.2.2 < s
  · simp [h.1, h.2]
  · by_cases h₁ : t ∈ M.delta q x[i]? bit
    · have h₂ : ¬ moveWork j t.2.2.2 < s := fun hc => h ⟨h₁, hc⟩
      simp [h₁, h₂]
    · simp [h₁]

/-! ### The blocks of one situation -/

/-- The blocks of one situation, the instructions unrolled into the term. -/
def innerT (M : Machine) (q : ℕ) : Cob :=
  Cob.catL ((caseIdx M).map fun z => caseTerm M q z.1 z.2)

theorem eval_innerT (M : Machine) (x : List Bool) (s : ℕ) (a b i j q : ℕ)
    (hq : q < M.states) (hi : i ≤ x.length) (hj : j < s) :
    (innerT M q).eval [x, caseParam M x s a b i j] = innerWord M x s a b q i j := by
  rw [innerT, innerWord]
  refine eval_catL_map (caseIdx M) _ _ _ ?_
  intro z hz
  exact eval_caseTerm M x s a b i j q z.1 z.2 hq (mem_caseIdx hz) hi hj

/-! ### The length of the blocks -/

/-- A variant of `Complexity.Qbf.QBF.varBound_stepCase_le` whose hypothesis on the work head is
the one available inside a sweep, where the head may sit at the space bound itself. -/
theorem varBound_stepCase_le' (M : Machine) (x : List Bool) (s : ℕ) {a b q i j : ℕ} {bit : Bool}
    {t : ℕ × Bool × Dir × Dir} {N : ℕ} (ha : a < N) (hb : b < N)
    (hj : M.states + (x.length + 1) + j < cfgWidth M x s) :
    (stepCase M x s a b q i j bit t).varBound ≤ N * cfgWidth M x s := by
  have hcfg : (cfgF M x s a q i j).varBound ≤ N * cfgWidth M x s :=
    varBound_cfgF_le (M := M) (x := x) (s := s) ha
  have hlit : (litF (a * cfgWidth M x s + (M.states + (x.length + 1) + j)) bit).varBound
      ≤ N * cfgWidth M x s := varBound_litF_le (block_index_lt ha hj)
  have htgt : (tgtF M x s a b t.1 (moveIn x.length i t.2.2.1) (moveWork j t.2.2.2)
      t.2.1 j).varBound ≤ N * cfgWidth M x s :=
    varBound_tgtF_le (M := M) (x := x) (s := s) ha hb
  simp only [stepCase, varBound]
  omega

/-- The padding field of the parameter words: a square large enough for every block. -/
def padOf (M : Machine) (x : List Bool) (s : ℕ) (a b : ℕ) : ℕ :=
  (cfgWidth M x s + a * cfgWidth M x s + b * cfgWidth M x s + 3) *
    (cfgWidth M x s + a * cfgWidth M x s + b * cfgWidth M x s + 3)

theorem length_enc_stepCase_le (M : Machine) (x : List Bool) (s : ℕ) (a b q i j : ℕ)
    (bit : Bool) (t : ℕ × Bool × Dir × Dir)
    (hj : M.states + (x.length + 1) + j < cfgWidth M x s) :
    ([true, false, true] ++ enc (stepCase M x s a b q i j bit t)).length
      ≤ 16 * padOf M x s a b := by
  set W := cfgWidth M x s with hW
  have hvar : (stepCase M x s a b q i j bit t).varBound ≤ (a + b + 1) * W :=
    varBound_stepCase_le' M x s (show a < a + b + 1 by omega) (show b < a + b + 1 by omega) hj
  have hlen := length_enc_le (stepCase M x s a b q i j bit t) ((a + b + 1) * W) hvar
  have hsize := size_stepCase_le (M := M) (x := x) (s := s) a b q i j bit t
  have h1 : (stepCase M x s a b q i j bit t).size * ((a + b + 1) * W + 3)
      ≤ (W * 15 + 12) * ((a + b + 1) * W + 3) := Nat.mul_le_mul_right _ hsize
  have hexp : (a + b + 1) * W = W + a * W + b * W := by ring
  have hu : W * 15 + 12 ≤ 15 * (W + a * W + b * W + 3) := by
    have h₁ : 0 ≤ a * W := Nat.zero_le _
    have h₂ : 0 ≤ b * W := Nat.zero_le _
    nlinarith [h₁, h₂]
  have h2 : (W * 15 + 12) * ((a + b + 1) * W + 3)
      ≤ 15 * padOf M x s a b := by
    rw [hexp, padOf, ← hW]
    calc (W * 15 + 12) * (W + a * W + b * W + 3)
        ≤ (15 * (W + a * W + b * W + 3)) * (W + a * W + b * W + 3) :=
          Nat.mul_le_mul_right _ hu
      _ = 15 * ((W + a * W + b * W + 3) * (W + a * W + b * W + 3)) := by ring
  have h3 : 3 ≤ padOf M x s a b := by
    have : 3 * 3 ≤ (W + a * W + b * W + 3) * (W + a * W + b * W + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    rw [padOf, ← hW]
    omega
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

theorem length_innerWord_le (M : Machine) (x : List Bool) (s : ℕ) (a b q i j : ℕ)
    (hjs : j ≤ s) :
    (innerWord M x s a b q i j).length
      ≤ (caseIdx M).length * (16 * padOf M x s a b) := by
  refine length_flatMap_le _ _ _ ?_
  intro z _
  by_cases hg : z.2 ∈ M.delta q x[i]? z.1 ∧ moveWork j z.2.2.2.2 < s
  · have hs : 0 < s := lt_of_le_of_lt (Nat.zero_le _) hg.2
    have hj : M.states + (x.length + 1) + j < cfgWidth M x s := by
      simp only [cfgWidth]
      omega
    rw [if_pos hg]
    exact length_enc_stepCase_le M x s a b q i j z.1 z.2 hj
  · rw [if_neg hg]
    simp

/-! ### The sweep over the position of the work head -/

/-- The fields of the parameter word of the work-head sweep; the range length comes first. -/
def jFields (M : Machine) (x : List Bool) (s : ℕ) (a b i : ℕ) : List ℕ :=
  [s, cfgWidth M x s, a * cfgWidth M x s, b * cfgWidth M x s, M.states,
    M.states + (x.length + 1), M.states + (x.length + 1) + s, i, x.length, padOf M x s a b]

/-- The parameter word of the work-head sweep: its unary fields, then the input. -/
def jParam (M : Machine) (x : List Bool) (s : ℕ) (a b i : ℕ) : Word :=
  fieldsWord (jFields M x s a b i) ++ x

theorem eval_fldT_app (k : ℕ) (as : List ℕ) (hk : k < as.length) (y x : Word) :
    (fldT k).eval [y, fieldsWord as ++ x] = List.replicate (as.getD k 0) true :=
  Cob.eval_fieldTerm_app k (.proj 1) as x _ (by simp) hk

theorem eval_dropFieldsT_app (k : ℕ) (as : List ℕ) (hk : k = as.length) (y x : Word) :
    (Cob.dropFieldsT k (.proj 1)).eval [y, fieldsWord as ++ x] = x := by
  subst hk
  exact Cob.eval_tailWord (.proj 1) as x _ (by simp)

/-- The blocks of one position of the work head. -/
def jBlockCore (M : Machine) (q : ℕ) : Cob :=
  .comp (innerT M q)
    [Cob.dropFieldsT 10 (.proj 1),
      Cob.fieldsT [fldT 1, fldT 2, fldT 3, fldT 4, fldT 5, fldT 6, fldT 7, .proj 0,
        fldT 8, fldT 0]]

/-- The block of the work-head sweep: empty outside the range. -/
def jBlockT (M : Machine) (q : ℕ) : Cob :=
  Cob.iteT (Cob.ltU (.proj 0) (fldT 0)) (jBlockCore M q) (Cob.constT [])

/-- The word contributed by one position of the work head. -/
def jWord (M : Machine) (x : List Bool) (s : ℕ) (a b q i j : ℕ) : Word :=
  if j < s then innerWord M x s a b q i j else []

theorem eval_jBlockT (M : Machine) (x : List Bool) (s : ℕ) (a b i q j : ℕ)
    (hq : q < M.states) (hi : i ≤ x.length) :
    (jBlockT M q).eval [List.replicate j true, jParam M x s a b i]
      = jWord M x s a b q i j := by
  set as := jFields M x s a b i with has
  have hlen : as.length = 10 := rfl
  have hfld : ∀ k, ∀ _ : k < 10, (fldT k).eval [List.replicate j true, jParam M x s a b i]
      = List.replicate (as.getD k 0) true := by
    intro k hk
    exact eval_fldT_app k as (by omega) _ _
  have hcond : (Cob.ltU (.proj 0) (fldT 0)).eval [List.replicate j true, jParam M x s a b i]
      = bw (decide (j < s)) := by
    rw [Cob.eval_ltU, hfld 0 (by omega)]
    simp [has, jFields]
  by_cases hj : j < s
  · have hx : (Cob.dropFieldsT 10 (.proj 1)).eval [List.replicate j true, jParam M x s a b i]
        = x := eval_dropFieldsT_app 10 as (by omega) _ _
    have hparam : (Cob.fieldsT [fldT 1, fldT 2, fldT 3, fldT 4, fldT 5, fldT 6, fldT 7,
        .proj 0, fldT 8, fldT 0]).eval [List.replicate j true, jParam M x s a b i]
          = caseParam M x s a b i j := by
      rw [caseParam_eq]
      refine Cob.eval_fieldsT ?_
      have e1 : as.getD 1 0 = cfgWidth M x s := rfl
      have e2 : as.getD 2 0 = a * cfgWidth M x s := rfl
      have e3 : as.getD 3 0 = b * cfgWidth M x s := rfl
      have e4 : as.getD 4 0 = M.states := rfl
      have e5 : as.getD 5 0 = M.states + (x.length + 1) := rfl
      have e6 : as.getD 6 0 = M.states + (x.length + 1) + s := rfl
      have e7 : as.getD 7 0 = i := rfl
      have e8 : as.getD 8 0 = x.length := rfl
      have e0 : as.getD 0 0 = s := rfl
      have hproj : (Cob.proj 0).eval [List.replicate j true, jParam M x s a b i]
          = List.replicate j true := by simp
      exact .cons (by rw [hfld 1 (by omega), e1]) (.cons (by rw [hfld 2 (by omega), e2])
        (.cons (by rw [hfld 3 (by omega), e3]) (.cons (by rw [hfld 4 (by omega), e4])
          (.cons (by rw [hfld 5 (by omega), e5]) (.cons (by rw [hfld 6 (by omega), e6])
            (.cons (by rw [hfld 7 (by omega), e7]) (.cons hproj
              (.cons (by rw [hfld 8 (by omega), e8]) (.cons (by rw [hfld 0 (by omega), e0])
                .nil)))))))))
    have hcore : (jBlockCore M q).eval [List.replicate j true, jParam M x s a b i]
        = innerWord M x s a b q i j := by
      simp only [jBlockCore, Cob.eval_comp, List.map_cons, List.map_nil, hx, hparam]
      exact eval_innerT M x s a b i j q hq hi hj
    rw [jBlockT, Cob.eval_iteW (p := true) (by rw [hcond]; simp [hj]) hcore rfl, jWord,
      if_pos hj]
    simp
  · rw [jBlockT, Cob.eval_iteW (p := false) (by rw [hcond]; simp [hj]) rfl
      (Cob.eval_constT _ _), jWord, if_neg hj]
    simp

/-- The term sweeping the position of the work head. -/
def jSweepT (M : Machine) (q : ℕ) : Cob :=
  rangeEmitTerm (jBlockT M q) (16 * (caseIdx M).length)

theorem lead1_jParam (M : Machine) (x : List Bool) (s : ℕ) (a b i : ℕ) :
    lead1 (jParam M x s a b i) = s := by
  simp [jParam, jFields, fieldsWord, List.append_assoc]

theorem pad_le_length_jParam (M : Machine) (x : List Bool) (s : ℕ) (a b i : ℕ) :
    padOf M x s a b ≤ (jParam M x s a b i).length := by
  simp [jParam, jFields, fieldsWord]
  omega

theorem eval_jSweepT (M : Machine) (x : List Bool) (s : ℕ) (a b i q : ℕ)
    (hq : q < M.states) (hi : i ≤ x.length) :
    (jSweepT M q).eval [List.replicate s true, jParam M x s a b i]
      = (List.range s).flatMap (fun j => innerWord M x s a b q i j) := by
  have hb : ∀ j : ℕ, j ≤ s → (jWord M x s a b q i j).length
      ≤ 16 * (caseIdx M).length * ((jParam M x s a b i).length + 1) := by
    intro j hj
    have hpad := pad_le_length_jParam M x s a b i
    by_cases h : j < s
    · have := length_innerWord_le M x s a b q i j hj
      rw [jWord, if_pos h]
      calc (innerWord M x s a b q i j).length
          ≤ (caseIdx M).length * (16 * padOf M x s a b) := this
        _ ≤ 16 * (caseIdx M).length * ((jParam M x s a b i).length + 1) := by
            have : padOf M x s a b ≤ (jParam M x s a b i).length + 1 := by omega
            calc (caseIdx M).length * (16 * padOf M x s a b)
                = 16 * (caseIdx M).length * padOf M x s a b := by ring
              _ ≤ 16 * (caseIdx M).length * ((jParam M x s a b i).length + 1) :=
                  Nat.mul_le_mul_left _ this
    · rw [jWord, if_neg h]
      simp
  rw [jSweepT, eval_rangeEmitTerm (jBlockT M q) (jWord M x s a b q i)
    (jParam M x s a b i) (lead1_jParam M x s a b i)
    (fun j => eval_jBlockT M x s a b i q j hq hi) hb]
  refine List.flatMap_congr ?_
  intro j hj
  rw [jWord, if_pos (List.mem_range.1 hj)]

/-! ### The sweep over the position of the input head -/

/-- The padding field, computed from three fields of the parameter word. -/
def padFromT (k₀ k₁ k₂ : ℕ) : Cob :=
  .comp .smash
    [Cob.uAdd (fldT k₀) (Cob.uAdd (fldT k₁) (Cob.uAdd (fldT k₂) (constU 3))),
      Cob.uAdd (fldT k₀) (Cob.uAdd (fldT k₁) (Cob.uAdd (fldT k₂) (constU 3)))]

theorem eval_padFromT (k₀ k₁ k₂ : ℕ) (args : List Word) (w u v : ℕ)
    (h₀ : (fldT k₀).eval args = List.replicate w true)
    (h₁ : (fldT k₁).eval args = List.replicate u true)
    (h₂ : (fldT k₂).eval args = List.replicate v true) :
    (padFromT k₀ k₁ k₂).eval args
      = List.replicate ((w + u + v + 3) * (w + u + v + 3)) true := by
  have hu : (Cob.uAdd (fldT k₀) (Cob.uAdd (fldT k₁) (Cob.uAdd (fldT k₂) (constU 3)))).eval args
      = List.replicate (w + (u + (v + 3))) true :=
    Cob.eval_uAdd h₀ (Cob.eval_uAdd h₁ (Cob.eval_uAdd h₂ (eval_constU 3 args)))
  have hsum : w + (u + (v + 3)) = w + u + v + 3 := by omega
  rw [hsum] at hu
  simp [padFromT, hu]

/-- The fields of the parameter word of the input-head sweep; the range length comes first. -/
def iFields (M : Machine) (x : List Bool) (s : ℕ) (a b : ℕ) : List ℕ :=
  [x.length + 1, s, cfgWidth M x s, a * cfgWidth M x s, b * cfgWidth M x s, M.states,
    M.states + (x.length + 1), M.states + (x.length + 1) + s, x.length,
    (s + 1) * padOf M x s a b]

/-- The parameter word of the input-head sweep: its unary fields, then the input. -/
def iParam (M : Machine) (x : List Bool) (s : ℕ) (a b : ℕ) : Word :=
  fieldsWord (iFields M x s a b) ++ x

/-- The blocks of one position of the input head. -/
def iBlockCore (M : Machine) (q : ℕ) : Cob :=
  .comp (jSweepT M q)
    [fldT 1,
      Cob.catL
        [Cob.fieldsT [fldT 1, fldT 2, fldT 3, fldT 4, fldT 5, fldT 6, fldT 7, .proj 0,
            fldT 8, padFromT 2 3 4],
          Cob.dropFieldsT 10 (.proj 1)]]

/-- The block of the input-head sweep: empty outside the range. -/
def iBlockT (M : Machine) (q : ℕ) : Cob :=
  Cob.iteT (Cob.ltU (.proj 0) (fldT 0)) (iBlockCore M q) (Cob.constT [])

/-- The word contributed by one position of the input head. -/
def iWord (M : Machine) (x : List Bool) (s : ℕ) (a b q i : ℕ) : Word :=
  if i < x.length + 1 then (List.range s).flatMap (fun j => innerWord M x s a b q i j) else []

theorem eval_iBlockT (M : Machine) (x : List Bool) (s : ℕ) (a b q i : ℕ) (hq : q < M.states) :
    (iBlockT M q).eval [List.replicate i true, iParam M x s a b]
      = iWord M x s a b q i := by
  set as := iFields M x s a b with has
  have hlen : as.length = 10 := rfl
  have hfld : ∀ k, ∀ _ : k < 10, (fldT k).eval [List.replicate i true, iParam M x s a b]
      = List.replicate (as.getD k 0) true := by
    intro k hk
    exact eval_fldT_app k as (by omega) _ _
  have e0 : as.getD 0 0 = x.length + 1 := rfl
  have e1 : as.getD 1 0 = s := rfl
  have e2 : as.getD 2 0 = cfgWidth M x s := rfl
  have e3 : as.getD 3 0 = a * cfgWidth M x s := rfl
  have e4 : as.getD 4 0 = b * cfgWidth M x s := rfl
  have e5 : as.getD 5 0 = M.states := rfl
  have e6 : as.getD 6 0 = M.states + (x.length + 1) := rfl
  have e7 : as.getD 7 0 = M.states + (x.length + 1) + s := rfl
  have e8 : as.getD 8 0 = x.length := rfl
  have hcond : (Cob.ltU (.proj 0) (fldT 0)).eval [List.replicate i true, iParam M x s a b]
      = bw (decide (i < x.length + 1)) := by
    rw [Cob.eval_ltU, hfld 0 (by omega), e0]
    simp
  by_cases hi : i < x.length + 1
  · have hx : (Cob.dropFieldsT 10 (.proj 1)).eval [List.replicate i true, iParam M x s a b]
        = x := eval_dropFieldsT_app 10 as (by omega) _ _
    have hpad : (padFromT 2 3 4).eval [List.replicate i true, iParam M x s a b]
        = List.replicate (padOf M x s a b) true := by
      have := eval_padFromT 2 3 4 [List.replicate i true, iParam M x s a b]
        (cfgWidth M x s) (a * cfgWidth M x s) (b * cfgWidth M x s)
        (by rw [hfld 2 (by omega), e2]) (by rw [hfld 3 (by omega), e3])
        (by rw [hfld 4 (by omega), e4])
      rw [this, padOf]
    have hparam : (Cob.catL
        [Cob.fieldsT [fldT 1, fldT 2, fldT 3, fldT 4, fldT 5, fldT 6, fldT 7, .proj 0,
            fldT 8, padFromT 2 3 4],
          Cob.dropFieldsT 10 (.proj 1)]).eval [List.replicate i true, iParam M x s a b]
        = jParam M x s a b i := by
      have hfields : (Cob.fieldsT [fldT 1, fldT 2, fldT 3, fldT 4, fldT 5, fldT 6, fldT 7,
          .proj 0, fldT 8, padFromT 2 3 4]).eval [List.replicate i true, iParam M x s a b]
          = fieldsWord (jFields M x s a b i) := by
        refine Cob.eval_fieldsT ?_
        have hproj : (Cob.proj 0).eval [List.replicate i true, iParam M x s a b]
            = List.replicate i true := by simp
        exact .cons (by rw [hfld 1 (by omega), e1]) (.cons (by rw [hfld 2 (by omega), e2])
          (.cons (by rw [hfld 3 (by omega), e3]) (.cons (by rw [hfld 4 (by omega), e4])
            (.cons (by rw [hfld 5 (by omega), e5]) (.cons (by rw [hfld 6 (by omega), e6])
              (.cons (by rw [hfld 7 (by omega), e7]) (.cons hproj
                (.cons (by rw [hfld 8 (by omega), e8]) (.cons hpad .nil)))))))))
      simp only [Cob.eval_catL, List.map_cons, List.map_nil, hfields, hx, List.flatten_cons,
        List.flatten_nil, List.append_nil]
      rw [jParam]
    have hcore : (iBlockCore M q).eval [List.replicate i true, iParam M x s a b]
        = (List.range s).flatMap (fun j => innerWord M x s a b q i j) := by
      simp only [iBlockCore, Cob.eval_comp, List.map_cons, List.map_nil, hparam,
        hfld 1 (by omega), e1]
      exact eval_jSweepT M x s a b i q hq (by omega)
    rw [iBlockT, Cob.eval_iteW (p := true) (by rw [hcond]; simp [hi]) hcore rfl, iWord,
      if_pos hi]
    simp
  · rw [iBlockT, Cob.eval_iteW (p := false) (by rw [hcond]; simp [hi]) rfl
      (Cob.eval_constT _ _), iWord, if_neg hi]
    simp

/-- The term sweeping the position of the input head. -/
def iSweepT (M : Machine) (q : ℕ) : Cob :=
  rangeEmitTerm (iBlockT M q) (16 * (caseIdx M).length)

theorem lead1_iParam (M : Machine) (x : List Bool) (s : ℕ) (a b : ℕ) :
    lead1 (iParam M x s a b) = x.length + 1 := by
  simp [iParam, iFields, fieldsWord, List.append_assoc]

theorem padI_le_length_iParam (M : Machine) (x : List Bool) (s : ℕ) (a b : ℕ) :
    (s + 1) * padOf M x s a b ≤ (iParam M x s a b).length := by
  simp [iParam, iFields, fieldsWord]
  omega

theorem eval_iSweepT (M : Machine) (x : List Bool) (s : ℕ) (a b q : ℕ) (hq : q < M.states) :
    (iSweepT M q).eval [List.replicate (x.length + 1) true, iParam M x s a b]
      = (List.range (x.length + 1)).flatMap fun i =>
          (List.range s).flatMap fun j => innerWord M x s a b q i j := by
  have hb : ∀ i : ℕ, i ≤ x.length + 1 → (iWord M x s a b q i).length
      ≤ 16 * (caseIdx M).length * ((iParam M x s a b).length + 1) := by
    intro i _
    have hpad := padI_le_length_iParam M x s a b
    by_cases h : i < x.length + 1
    · rw [iWord, if_pos h]
      have hall : ∀ j ∈ List.range s, (innerWord M x s a b q i j).length
          ≤ (caseIdx M).length * (16 * padOf M x s a b) := by
        intro j hj
        exact length_innerWord_le M x s a b q i j (le_of_lt (List.mem_range.1 hj))
      have h1 := length_flatMap_le (List.range s) _ _ hall
      rw [List.length_range] at h1
      refine le_trans h1 ?_
      have h2 : s * ((caseIdx M).length * (16 * padOf M x s a b))
          = 16 * (caseIdx M).length * (s * padOf M x s a b) := by ring
      rw [h2]
      have h3 : s * padOf M x s a b ≤ (iParam M x s a b).length + 1 := by
        have : s * padOf M x s a b ≤ (s + 1) * padOf M x s a b :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      exact Nat.mul_le_mul_left _ h3
    · rw [iWord, if_neg h]
      simp
  rw [iSweepT, eval_rangeEmitTerm (iBlockT M q) (iWord M x s a b q)
    (iParam M x s a b) (lead1_iParam M x s a b)
    (fun i => eval_iBlockT M x s a b q i hq) hb]
  refine List.flatMap_congr ?_
  intro i hi
  rw [iWord, if_pos (List.mem_range.1 hi)]

/-! ### The whole step formula -/

/-- The fields of the parameter word of the step formula. -/
def stepFields (M : Machine) (x : List Bool) (s : ℕ) (a b : ℕ) : List ℕ :=
  [cfgWidth M x s, a * cfgWidth M x s, b * cfgWidth M x s, M.states,
    M.states + (x.length + 1), M.states + (x.length + 1) + s, x.length, s]

/-- The parameter word of the step formula: its unary fields, then the input. -/
def stepParam (M : Machine) (x : List Bool) (s : ℕ) (a b : ℕ) : Word :=
  fieldsWord (stepFields M x s a b) ++ x

/-- The parameter word of the input-head sweep, assembled from that of the step formula. -/
def iParamT : Cob :=
  Cob.catL
    [Cob.fieldsT [Cob.uSucc (fldT 6), fldT 7, fldT 0, fldT 1, fldT 2, fldT 3, fldT 4, fldT 5,
        fldT 6, .comp .smash [Cob.uSucc (fldT 7), padFromT 0 1 2]],
      Cob.dropFieldsT 8 (.proj 1)]

/-- **The term writing the code of the step formula**: one input-head sweep per control state,
then the code of the closing constant. -/
def stepTerm (M : Machine) : Cob :=
  Cob.catL
    (((List.range M.states).map fun q => Cob.comp (iSweepT M q) [Cob.uSucc (fldT 6), iParamT])
      ++ [Cob.constT (enc ff)])

theorem eval_iParamT (M : Machine) (x : List Bool) (s : ℕ) (a b : ℕ) :
    iParamT.eval [x, stepParam M x s a b] = iParam M x s a b := by
  set as := stepFields M x s a b with has
  have hlen : as.length = 8 := rfl
  have hfld : ∀ k, ∀ _ : k < 8, (fldT k).eval [x, stepParam M x s a b]
      = List.replicate (as.getD k 0) true := by
    intro k hk
    exact eval_fldT_app k as (by omega) _ _
  have e0 : as.getD 0 0 = cfgWidth M x s := rfl
  have e1 : as.getD 1 0 = a * cfgWidth M x s := rfl
  have e2 : as.getD 2 0 = b * cfgWidth M x s := rfl
  have e3 : as.getD 3 0 = M.states := rfl
  have e4 : as.getD 4 0 = M.states + (x.length + 1) := rfl
  have e5 : as.getD 5 0 = M.states + (x.length + 1) + s := rfl
  have e6 : as.getD 6 0 = x.length := rfl
  have e7 : as.getD 7 0 = s := rfl
  have hx : (Cob.dropFieldsT 8 (.proj 1)).eval [x, stepParam M x s a b] = x :=
    eval_dropFieldsT_app 8 as (by omega) _ _
  have hsucc : (Cob.uSucc (fldT 6)).eval [x, stepParam M x s a b]
      = List.replicate (x.length + 1) true :=
    Cob.eval_uSucc (by rw [hfld 6 (by omega), e6])
  have hsucc' : (Cob.uSucc (fldT 7)).eval [x, stepParam M x s a b]
      = List.replicate (s + 1) true :=
    Cob.eval_uSucc (by rw [hfld 7 (by omega), e7])
  have hpad : (padFromT 0 1 2).eval [x, stepParam M x s a b]
      = List.replicate (padOf M x s a b) true := by
    have := eval_padFromT 0 1 2 [x, stepParam M x s a b]
      (cfgWidth M x s) (a * cfgWidth M x s) (b * cfgWidth M x s)
      (by rw [hfld 0 (by omega), e0]) (by rw [hfld 1 (by omega), e1])
      (by rw [hfld 2 (by omega), e2])
    rw [this, padOf]
  have hpadI : (Cob.comp .smash [Cob.uSucc (fldT 7), padFromT 0 1 2]).eval
      [x, stepParam M x s a b] = List.replicate ((s + 1) * padOf M x s a b) true := by
    simp [hsucc', hpad]
  have hfields : (Cob.fieldsT [Cob.uSucc (fldT 6), fldT 7, fldT 0, fldT 1, fldT 2, fldT 3,
      fldT 4, fldT 5, fldT 6, .comp .smash [Cob.uSucc (fldT 7), padFromT 0 1 2]]).eval
        [x, stepParam M x s a b] = fieldsWord (iFields M x s a b) := by
    refine Cob.eval_fieldsT ?_
    exact .cons hsucc (.cons (by rw [hfld 7 (by omega), e7]) (.cons (by rw [hfld 0 (by omega), e0])
      (.cons (by rw [hfld 1 (by omega), e1]) (.cons (by rw [hfld 2 (by omega), e2])
        (.cons (by rw [hfld 3 (by omega), e3]) (.cons (by rw [hfld 4 (by omega), e4])
          (.cons (by rw [hfld 5 (by omega), e5]) (.cons (by rw [hfld 6 (by omega), e6])
            (.cons hpadI .nil))))))))) 
  simp only [iParamT, Cob.eval_catL, List.map_cons, List.map_nil, hfields, hx,
    List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [iParam]

/-- **The code of the step formula is the value of one Cobham term** at the input word and the
parameter word of the two blocks. -/
theorem enc_stepF_eval (M : Machine) (x : List Bool) (s : ℕ) (a b : ℕ) :
    enc (stepF M x s a b) = (stepTerm M).eval [x, stepParam M x s a b] := by
  have hsucc : (Cob.uSucc (fldT 6)).eval [x, stepParam M x s a b]
      = List.replicate (x.length + 1) true := by
    have hfld6 : (fldT 6).eval [x, stepParam M x s a b]
        = List.replicate ((stepFields M x s a b).getD 6 0) true :=
      eval_fldT_app 6 (stepFields M x s a b) (by simp [stepFields]) _ _
    have e6 : (stepFields M x s a b).getD 6 0 = x.length := rfl
    exact Cob.eval_uSucc (by rw [hfld6, e6])
  have hq : ∀ q ∈ List.range M.states,
      (Cob.comp (iSweepT M q) [Cob.uSucc (fldT 6), iParamT]).eval [x, stepParam M x s a b]
        = (List.range (x.length + 1)).flatMap fun i =>
            (List.range s).flatMap fun j => innerWord M x s a b q i j := by
    intro q hq
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, hsucc,
      eval_iParamT M x s a b]
    exact eval_iSweepT M x s a b q (List.mem_range.1 hq)
  have hmap := eval_catL_map (List.range M.states)
    (fun q => Cob.comp (iSweepT M q) [Cob.uSucc (fldT 6), iParamT])
    (fun q => (List.range (x.length + 1)).flatMap fun i =>
      (List.range s).flatMap fun j => innerWord M x s a b q i j)
    [x, stepParam M x s a b] hq
  rw [enc_stepF_stream, stepTerm, Cob.eval_catL, List.map_append, List.flatten_append]
  simp only [List.map_cons, List.map_nil, Cob.eval_constT, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  congr 1
  simpa [Cob.eval_catL, List.map_map] using hmap.symm

end QBF

end Complexity.Qbf
