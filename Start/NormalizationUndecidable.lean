/-
Undecidability of normalization for lambda terms.

`Start/Undecidable.lean` shows that "reduces to a Church numeral" is undecidable.  This file
strengthens that to the standard statement: **whether a lambda term has a normal form at all is
undecidable**.

The extra ingredient is that the strict realizer of `Start/PartialCapstone.lean` diverges *badly*
when the computation it simulates diverges: it then has no weak head normal form
(`Lambda.partialTerm_not_hasWhnfEval`), hence no normal form.  `Lambda.exists_strict_realizer`
repackages the construction so that both halves are available at once, and the reduction from the
halting problem is then the same as in `Start/Undecidable.lean`.
-/

import Start.Undecidable
import Start.Leftmost

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- A realizer that converges exactly when the function does
------------------------------------------------------------------------

/-- Every partial recursive function has a lambda realizer which computes its values and which,
on divergence, has no weak head normal form. -/
theorem exists_strict_realizer {f : ℕ →. ℕ} (hf : Partrec f) :
    ∃ F : Lambda,
      (∀ n m, f n = Part.some m →
        Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church m)) ∧
      (∀ n, (∀ m, m ∉ f n) → ¬ HasWhnfEval (Lambda.app F (Lambda.church n))) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hf)
  obtain ⟨H, hH⟩ := Lambda.exists_realizer_of_primrec (Lambda.kleeneTest_primrec c)
  obtain ⟨G, hG⟩ := Lambda.exists_realizer_of_primrec (Lambda.kleeneValue_primrec c)
  refine ⟨Lambda.partialTerm H G, fun n m hfn => ?_, fun n hn => ?_⟩
  · have hm : m ∈ f n := by rw [hfn]; exact Part.mem_some m
    obtain ⟨k, hk⟩ := Lambda.exists_kleene_witness hc hm
    have hex : ∃ k, Lambda.kleeneTest c (Nat.pair n k) = 0 := ⟨k, hk⟩
    have hk0 : Lambda.kleeneTest c (Nat.pair n (Nat.find hex)) = 0 := Nat.find_spec hex
    have hlt : ∀ y, y < Nat.find hex → Lambda.kleeneTest c (Nat.pair n y) ≠ 0 :=
      fun y hy => Nat.find_min hex hy
    have hval : Lambda.kleeneValue c (Nat.pair n (Nat.find hex)) ∈ f n :=
      Lambda.kleeneValue_mem hc hk0
    have hveq : Lambda.kleeneValue c (Nat.pair n (Nat.find hex)) = m := Part.mem_unique hval hm
    have hred := Lambda.partialTerm_reduces_church hH hG n (Nat.find hex) hlt hk0
    rwa [hveq] at hred
  · exact Lambda.partialTerm_not_hasWhnfEval hH hG.1 n (Lambda.kleene_no_witness hc hn)

------------------------------------------------------------------------
-- Normalizability
------------------------------------------------------------------------

/-- A term normalizes if it reduces to a term in normal form. -/
def HasNormalForm (t : Lambda) : Prop := ∃ u : Lambda, Lambda.reduces t u ∧ Lambda.is_normal u

/-- The code-level normalization predicate. -/
def CodeHasNormalForm (c : ℕ) : Prop :=
  ∃ t : Lambda, Lambda.decode c = some t ∧ HasNormalForm t

@[simp] theorem codeHasNormalForm_encode (t : Lambda) :
    CodeHasNormalForm (Lambda.encode t) ↔ HasNormalForm t := by
  constructor
  · rintro ⟨u, hu, h⟩
    rw [decode_encode] at hu
    exact (Option.some_inj.mp hu) ▸ h
  · intro h
    exact ⟨t, decode_encode t, h⟩

theorem hasWhnfEval_of_hasNormalForm {t : Lambda} (h : HasNormalForm t) : HasWhnfEval t := by
  obtain ⟨u, hu, hnu⟩ := h
  exact hasWhnfEval_of_reduces_whnf hu (isWhnf_of_is_normal hnu)

------------------------------------------------------------------------
-- The reduction
------------------------------------------------------------------------

/-- A strict realizer of the universal partial function. -/
def strictHaltTerm : Lambda := Classical.choose (exists_strict_realizer univHalt_partrec)

theorem strictHaltTerm_reduces (k m : ℕ) (h : univHalt k = Part.some m) :
    Lambda.reduces (Lambda.app strictHaltTerm (Lambda.church k)) (Lambda.church m) :=
  (Classical.choose_spec (exists_strict_realizer univHalt_partrec)).1 k m h

theorem strictHaltTerm_diverges (k : ℕ) (h : ∀ m, m ∉ univHalt k) :
    ¬ HasWhnfEval (Lambda.app strictHaltTerm (Lambda.church k)) :=
  (Classical.choose_spec (exists_strict_realizer univHalt_partrec)).2 k h

theorem univHalt_dom_iff_hasNormalForm (k : ℕ) :
    (univHalt k).Dom ↔ HasNormalForm (Lambda.app strictHaltTerm (Lambda.church k)) := by
  constructor
  · intro hdom
    refine ⟨Lambda.church ((univHalt k).get hdom), ?_, Lambda.church_normal _⟩
    exact strictHaltTerm_reduces k _ (Part.get_eq_iff_eq_some.mp rfl)
  · intro hnf
    by_contra hdom
    exact strictHaltTerm_diverges k (fun m hm => hdom hm.fst) (hasWhnfEval_of_hasNormalForm hnf)

/-- The code of the reducing term, as a function of `k`. -/
def strictHaltCode (k : ℕ) : ℕ :=
  Lambda.app_code (Lambda.encode strictHaltTerm) (Lambda.church_code k)

theorem strictHaltCode_primrec : Primrec strictHaltCode :=
  Primrec₂.comp Lambda.app_code_primrec (Primrec.const _) Lambda.church_code_primrec

theorem strictHaltCode_eq (k : ℕ) :
    strictHaltCode k = Lambda.encode (Lambda.app strictHaltTerm (Lambda.church k)) := by
  rw [encode_app, strictHaltCode, Lambda.encode_church_eq_church_code]

theorem codeHasNormalForm_strictHaltCode (k : ℕ) :
    CodeHasNormalForm (strictHaltCode k) ↔ (univHalt k).Dom := by
  rw [strictHaltCode_eq, codeHasNormalForm_encode, univHalt_dom_iff_hasNormalForm]

------------------------------------------------------------------------
-- Undecidability
------------------------------------------------------------------------

/-- **Normalization is undecidable.**  No computable predicate on codes of lambda terms decides
whether the coded term has a normal form. -/
theorem not_computablePred_codeHasNormalForm : ¬ ComputablePred CodeHasNormalForm := by
  intro h
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  refine ComputablePred.halting_problem 0 (ComputablePred.computable_iff.mpr
    ⟨fun c : Nat.Partrec.Code => f (strictHaltCode (Encodable.encode c)), ?_, ?_⟩)
  · exact hf.comp (strictHaltCode_primrec.to_comp.comp (Primrec.encode.to_comp.comp Computable.id))
  · funext c
    have hk : univHalt (Encodable.encode c) = Nat.Partrec.Code.eval c 0 := by
      simp only [univHalt, Denumerable.ofNat_encode]
    have hiff := codeHasNormalForm_strictHaltCode (Encodable.encode c)
    rw [hfe] at hiff
    rw [eq_iff_iff, ← hk]
    exact hiff.symm

/-- `omega` has no normal form, so the predicate is not everything. -/
theorem not_hasNormalForm_omega : ¬ HasNormalForm Lambda.omega := by
  rintro ⟨u, hu, hnu⟩
  have hueq : u = Lambda.omega := reduces_omega_eq hu rfl
  exact hnu Lambda.omega (hueq ▸ Lambda.step_omega_omega)

theorem not_codeHasNormalForm_omega : ¬ CodeHasNormalForm (Lambda.encode Lambda.omega) :=
  fun h => not_hasNormalForm_omega ((codeHasNormalForm_encode _).1 h)

/-- Church numerals normalize, so the predicate is not empty. -/
theorem codeHasNormalForm_church (k : ℕ) :
    CodeHasNormalForm (Lambda.encode (Lambda.church k)) :=
  (codeHasNormalForm_encode _).2 ⟨Lambda.church k, Lambda.reduces.refl _, Lambda.church_normal k⟩

end Lambda
