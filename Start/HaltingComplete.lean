/-
Σ₁-completeness of the lambda-calculus halting set.

`Start/NormalizationUndecidable.lean` shows that `Lambda.CodeHasNormalForm` — "the code `c`
decodes to a lambda term with a normal form" — is not a computable predicate.  This file upgrades
that to the exact recursion-theoretic classification of the set, using Mathlib's `REPred` and
Post's theorem (`ComputablePred.computable_iff_re_compl_re'`):

* `Lambda.rePred_codeHasNormalForm` — the halting set is recursively enumerable (Σ₁).  The
  leftmost-outermost clock of `Start/LeftmostRun.lean` gives the semi-decision procedure.
* `Lambda.rePred_le_codeHasNormalForm` — it is Σ₁-*hard*: every r.e. predicate on `ℕ`
  many-one reduces to it, by an explicitly primitive recursive reduction.
* `Lambda.codeHasNormalForm_sigma1_complete` — the two halves packaged as Σ₁-completeness.
* `Lambda.not_rePred_not_codeHasNormalForm` — consequently the halting set is r.e. but *not*
  co-r.e.; this is the sharp form of undecidability.

The same statements are proved for `Lambda.CodeConverges` ("reduces to a Church numeral").
-/

import Start.NormalizationUndecidable
import Start.LeftmostRun
import Start.OmegaUncomputable
import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- A generic semi-decision procedure over valid codes
------------------------------------------------------------------------

/-- If a predicate on codes is "valid code, and some stage of a primitive recursive test
succeeds", then it is recursively enumerable. -/
theorem rePred_of_valid_test {P : ℕ → Prop} (g : ℕ → ℕ → Bool) (hg : Primrec₂ g)
    (h : ∀ c, P c ↔ is_valid_code c = Bool.true ∧ ∃ k, g c k = Bool.true) : REPred P := by
  have hc : Computable fun c : ℕ => is_valid_code c := Lambda.is_valid_code_primrec.to_comp
  have hr : Partrec fun c : ℕ => Nat.rfind fun k => Part.some (g c k) :=
    Partrec.rfind (Primrec₂.to_comp hg).partrec
  have hpart : Partrec fun c : ℕ =>
      if is_valid_code c = Bool.true then Nat.rfind (fun k => Part.some (g c k))
      else Part.none := by
    refine (Partrec.cond hc hr Partrec.none).of_eq fun c => ?_
    cases is_valid_code c <;> simp
  refine hpart.dom_re.of_eq fun c => ?_
  rw [h c]
  by_cases hv : is_valid_code c = Bool.true
  · rw [if_pos hv]
    simp only [hv, true_and]
    constructor
    · intro hdom
      obtain ⟨k, hk, -⟩ := Nat.rfind_dom.1 hdom
      exact ⟨k, by simpa using hk⟩
    · rintro ⟨k, hk⟩
      exact Nat.rfind_dom.2 ⟨k, by simp [hk], fun {_} _ => trivial⟩
  · simp [hv]

------------------------------------------------------------------------
-- The halting set is r.e.
------------------------------------------------------------------------

/-- On *valid* codes the leftmost-outermost clock decides normalization in the limit; on invalid
codes there is nothing to run. -/
theorem codeHasNormalForm_iff_valid_and_haltsBy (c : ℕ) :
    CodeHasNormalForm c ↔ is_valid_code c = Bool.true ∧ ∃ k, haltsBy_code c k = Bool.true := by
  constructor
  · intro h
    obtain ⟨t, rfl, hnf⟩ := (codeHasNormalForm_iff c).1 h
    exact ⟨is_valid_code_encode t, (hasNormalForm_iff_exists_haltsBy_code t).1 hnf⟩
  · rintro ⟨hv, hk⟩
    obtain ⟨t, rfl⟩ := (is_valid_code_iff c).1 hv
    exact (codeHasNormalForm_iff _).2
      ⟨t, rfl, (hasNormalForm_iff_exists_haltsBy_code t).2 hk⟩

/-- **The lambda-calculus halting set is r.e.** -/
theorem rePred_codeHasNormalForm : REPred CodeHasNormalForm :=
  rePred_of_valid_test haltsBy_code haltsBy_code_primrec codeHasNormalForm_iff_valid_and_haltsBy

------------------------------------------------------------------------
-- Convergence to a numeral is r.e.
------------------------------------------------------------------------

/-- The stage test for convergence: at stage `n = ⟨k, m⟩`, has the leftmost run of `c` reached the
code of the Church numeral `m` after `k` steps? -/
def convTest (c n : ℕ) : Bool :=
  decide (nstep_code^[n.unpair.1] c = Lambda.church_code n.unpair.2)

theorem convTest_primrec : Primrec₂ convTest := by
  have h1 : Primrec fun p : ℕ × ℕ => nstep_code^[p.2.unpair.1] p.1 :=
    nstep_code_iterate_primrec.comp Primrec.fst
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
  have h2 : Primrec fun p : ℕ × ℕ => Lambda.church_code p.2.unpair.2 :=
    Lambda.church_code_primrec.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  have h : PrimrecPred fun p : ℕ × ℕ =>
      nstep_code^[p.2.unpair.1] p.1 = Lambda.church_code p.2.unpair.2 :=
    PrimrecRel.comp (Primrec.eq (α := ℕ)) h1 h2
  obtain ⟨_inst, h⟩ := h
  exact h.of_eq fun p => by simp [convTest]

theorem codeConverges_iff_valid_and_convTest (c : ℕ) :
    CodeConverges c ↔ is_valid_code c = Bool.true ∧ ∃ n, convTest c n = Bool.true := by
  constructor
  · rintro ⟨t, hd, m, hm⟩
    have hc : Lambda.encode t = c := encode_of_decode c t hd
    subst hc
    refine ⟨is_valid_code_encode t, ?_⟩
    have hnf : nf t = Lambda.church m := nf_eq_of_reduces_normal hm (Lambda.church_normal m)
    refine ⟨Nat.pair (haltTime t) m, ?_⟩
    simp only [convTest, Nat.unpair_pair, decide_eq_true_eq, nstep_code_iterate]
    rw [show nstep^[haltTime t] t = nf t from rfl, hnf, encode_church_eq_church_code]
  · rintro ⟨hv, n, hn⟩
    obtain ⟨t, rfl⟩ := (is_valid_code_iff c).1 hv
    simp only [convTest, decide_eq_true_eq, nstep_code_iterate,
      ← encode_church_eq_church_code] at hn
    refine ⟨t, decode_encode t, n.unpair.2, ?_⟩
    have h := reduces_nstep_iterate t n.unpair.1
    rwa [Lambda.encode_injective hn] at h

/-- **Convergence to a Church numeral is r.e.** -/
theorem rePred_codeConverges : REPred CodeConverges :=
  rePred_of_valid_test convTest convTest_primrec codeConverges_iff_valid_and_convTest

------------------------------------------------------------------------
-- Σ₁-hardness: every r.e. predicate reduces to the halting set
------------------------------------------------------------------------

/-- From an r.e. predicate, a partial recursive function whose domain it is. -/
theorem exists_partrec_dom_eq {p : ℕ → Prop} (hp : REPred p) :
    ∃ f : ℕ →. ℕ, Partrec f ∧ (∀ a, p a → f a = Part.some 0) ∧ (∀ a, ¬ p a → ∀ m, m ∉ f a) := by
  refine ⟨fun a => (Part.assert (p a) fun _ => Part.some ()).map fun _ => 0,
    hp.map (Computable.const (0 : ℕ)).to₂, ?_, ?_⟩
  · intro a ha
    exact Part.eq_some_iff.2 (Part.mem_map _ (Part.mem_assert ha (Part.mem_some ())))
  · intro a ha m hm
    obtain ⟨u, hu, -⟩ := (Part.mem_map_iff _).1 hm
    exact ha (Part.mem_assert_iff.1 hu).1

/-- The reduction term for an r.e. predicate: a lambda realizer which reduces `church a` to
`church 0` when `p a` holds, and which has no weak head normal form otherwise. -/
theorem exists_reduction_term {p : ℕ → Prop} (hp : REPred p) :
    ∃ F : Lambda, ∀ a,
      (p a → Lambda.reduces (Lambda.app F (Lambda.church a)) (Lambda.church 0)) ∧
      (¬ p a → ¬ HasWhnfEval (Lambda.app F (Lambda.church a))) := by
  obtain ⟨f, hf, hpos, hneg⟩ := exists_partrec_dom_eq hp
  obtain ⟨F, hF1, hF2⟩ := exists_strict_realizer hf
  exact ⟨F, fun a => ⟨fun ha => hF1 a 0 (hpos a ha), fun ha => hF2 a (hneg a ha)⟩⟩

/-- The reduction function attached to a lambda term `F`: `a ↦ ⌜F (church a)⌝`. -/
def reduceCode (F : Lambda) (a : ℕ) : ℕ :=
  Lambda.app_code (Lambda.encode F) (Lambda.church_code a)

theorem reduceCode_primrec (F : Lambda) : Primrec (reduceCode F) := by
  unfold reduceCode
  exact Primrec₂.comp Lambda.app_code_primrec (Primrec.const _) Lambda.church_code_primrec

theorem reduceCode_eq (F : Lambda) (a : ℕ) :
    reduceCode F a = Lambda.encode (Lambda.app F (Lambda.church a)) := by
  rw [encode_app, reduceCode, Lambda.encode_church_eq_church_code]

/-- The reduction function is injective, so the reductions above are in fact one-one. -/
theorem reduceCode_injective (F : Lambda) : Function.Injective (reduceCode F) := by
  intro a b h
  rw [reduceCode_eq, reduceCode_eq] at h
  have happ : Lambda.app F (Lambda.church a) = Lambda.app F (Lambda.church b) :=
    Lambda.encode_injective h
  exact Lambda.church_injective (Lambda.app.inj happ).2

/-- **One-one hardness of the lambda halting set.**  Every recursively enumerable predicate is
reducible to it by an *injective* computable function. -/
theorem rePred_le_one_codeHasNormalForm {p : ℕ → Prop} (hp : REPred p) :
    p ≤₁ CodeHasNormalForm := by
  obtain ⟨F, hF⟩ := exists_reduction_term hp
  refine ⟨reduceCode F, (reduceCode_primrec F).to_comp, reduceCode_injective F, fun a => ?_⟩
  rw [reduceCode_eq, codeHasNormalForm_encode]
  refine ⟨fun ha => ⟨Lambda.church 0, (hF a).1 ha, Lambda.church_normal 0⟩, fun ha => ?_⟩
  by_contra hna
  exact (hF a).2 hna (hasWhnfEval_of_hasNormalForm ha)

/-- One-one hardness of convergence to a Church numeral. -/
theorem rePred_le_one_codeConverges {p : ℕ → Prop} (hp : REPred p) : p ≤₁ CodeConverges := by
  obtain ⟨F, hF⟩ := exists_reduction_term hp
  refine ⟨reduceCode F, (reduceCode_primrec F).to_comp, reduceCode_injective F, fun a => ?_⟩
  rw [reduceCode_eq, codeConverges_encode]
  refine ⟨fun ha => ⟨0, (hF a).1 ha⟩, ?_⟩
  rintro ⟨m, hm⟩
  by_contra hna
  exact (hF a).2 hna
    (hasWhnfEval_of_hasNormalForm ⟨Lambda.church m, hm, Lambda.church_normal m⟩)

/-- **Σ₁-hardness of the lambda halting set.**  Every recursively enumerable predicate on `ℕ`
many-one reduces to "this code is a lambda term with a normal form". -/
theorem rePred_le_codeHasNormalForm {p : ℕ → Prop} (hp : REPred p) :
    p ≤₀ CodeHasNormalForm := (rePred_le_one_codeHasNormalForm hp).to_many_one

/-- Σ₁-hardness of convergence to a Church numeral. -/
theorem rePred_le_codeConverges {p : ℕ → Prop} (hp : REPred p) : p ≤₀ CodeConverges :=
  (rePred_le_one_codeConverges hp).to_many_one

------------------------------------------------------------------------
-- Σ₁-completeness, and Post's theorem
------------------------------------------------------------------------

/-- **Σ₁-completeness of the lambda-calculus halting set.**  It is r.e., and every r.e. predicate
many-one reduces to it. -/
theorem codeHasNormalForm_sigma1_complete :
    REPred CodeHasNormalForm ∧ ∀ p : ℕ → Prop, REPred p → p ≤₀ CodeHasNormalForm :=
  ⟨rePred_codeHasNormalForm, fun _ hp => rePred_le_codeHasNormalForm hp⟩

/-- **Σ₁-completeness of lambda-calculus convergence.** -/
theorem codeConverges_sigma1_complete :
    REPred CodeConverges ∧ ∀ p : ℕ → Prop, REPred p → p ≤₀ CodeConverges :=
  ⟨rePred_codeConverges, fun _ hp => rePred_le_codeConverges hp⟩

/-- **One-one completeness of the lambda halting set.**  It is r.e., and every r.e. predicate is
reducible to it by an injective computable function. -/
theorem codeHasNormalForm_one_complete :
    REPred CodeHasNormalForm ∧ ∀ p : ℕ → Prop, REPred p → p ≤₁ CodeHasNormalForm :=
  ⟨rePred_codeHasNormalForm, fun _ hp => rePred_le_one_codeHasNormalForm hp⟩

/-- One-one completeness of lambda-calculus convergence. -/
theorem codeConverges_one_complete :
    REPred CodeConverges ∧ ∀ p : ℕ → Prop, REPred p → p ≤₁ CodeConverges :=
  ⟨rePred_codeConverges, fun _ hp => rePred_le_one_codeConverges hp⟩

/-- Having a normal form and converging to a Church numeral are one-one equivalent: both are
r.e. and both are one-one complete. -/
theorem oneOneEquiv_codeHasNormalForm_codeConverges :
    OneOneEquiv CodeHasNormalForm CodeConverges :=
  ⟨rePred_le_one_codeConverges rePred_codeHasNormalForm,
    rePred_le_one_codeHasNormalForm rePred_codeConverges⟩

/-- **The halting set is r.e. but not co-r.e.**  By Post's theorem a set that is both r.e. and
co-r.e. is computable, and the halting set is not. -/
theorem not_rePred_not_codeHasNormalForm :
    ¬ REPred fun c => ¬ CodeHasNormalForm c := fun h =>
  not_computablePred_codeHasNormalForm
    (ComputablePred.computable_iff_re_compl_re'.2 ⟨rePred_codeHasNormalForm, h⟩)

/-- Convergence is r.e. but not co-r.e. -/
theorem not_rePred_not_codeConverges : ¬ REPred fun c => ¬ CodeConverges c := fun h =>
  not_computablePred_codeConverges
    (ComputablePred.computable_iff_re_compl_re'.2 ⟨rePred_codeConverges, h⟩)

end Lambda
