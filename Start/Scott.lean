/-
Scott's theorem and Rice's theorem for the lambda calculus.

`Start/SecondRecursion.lean` provides Kleene's second recursion theorem in its lambda form: every
closed `F` has a term `X` with `X ↠ F ⌜X⌝`.  That is exactly what is needed for the two classical
"no non-trivial property is decidable" results:

* `Lambda.scott_theorem` — no closed lambda term decides (in the sense of reducing to `true` or
  `false` on the code of its argument) a non-trivial, convertibility-invariant set of terms;
* `Lambda.not_computablePred_codeSet` — the corresponding statement one level down: the set of
  *codes* of such a set of terms is not computable (Rice's theorem for the lambda calculus).

Both are stated for a set `A` of terms that is invariant under convertibility and has a closed
term inside it and a closed term outside it.  The witnesses have to be closed because the
diagonal term built in the proof must itself be closed.

The concrete corollaries at the end instantiate `A` with "convertible to `church 0`", which is
non-trivial because `Lambda.omega` is not convertible to a normal form.
-/

import Start.SecondRecursion

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Convertibility
------------------------------------------------------------------------

/-- Two terms are *convertible* when they have a common reduct.  By confluence this is exactly
β-convertibility (the equivalence closure of one-step reduction). -/
def Conv (s t : Lambda) : Prop := ∃ u : Lambda, Lambda.reduces s u ∧ Lambda.reduces t u

theorem conv_refl (t : Lambda) : Conv t t := ⟨t, Lambda.reduces.refl t, Lambda.reduces.refl t⟩

theorem Conv.symm {s t : Lambda} (h : Conv s t) : Conv t s := by
  obtain ⟨u, h1, h2⟩ := h
  exact ⟨u, h2, h1⟩

theorem conv_of_reduces {s t : Lambda} (h : Lambda.reduces s t) : Conv s t :=
  ⟨t, h, Lambda.reduces.refl t⟩

theorem Conv.trans {s t u : Lambda} (h1 : Conv s t) (h2 : Conv t u) : Conv s u := by
  obtain ⟨a, hsa, hta⟩ := h1
  obtain ⟨b, htb, hub⟩ := h2
  obtain ⟨c, hac, hbc⟩ := Lambda.confluence_theorem hta htb
  exact ⟨c, Lambda.reduces_trans hsa hac, Lambda.reduces_trans hub hbc⟩

/-- A set of terms is *convertibility-invariant* (a "semantic" property) when convertible terms
are indistinguishable by it. -/
def ConvInvariant (A : Lambda → Prop) : Prop := ∀ s t : Lambda, Conv s t → A s → A t

theorem ConvInvariant.of_reduces {A : Lambda → Prop} (hA : ConvInvariant A) {s t : Lambda}
    (h : Lambda.reduces s t) (hs : A s) : A t :=
  hA s t (conv_of_reduces h) hs

------------------------------------------------------------------------
-- Closedness helper
------------------------------------------------------------------------

theorem IsClosedAt_of_IsClosed {t : Lambda} (h : Lambda.IsClosed t) (k : ℕ) :
    Lambda.IsClosedAt t k := fun s x _ => h s x

------------------------------------------------------------------------
-- Lambda-decidability
------------------------------------------------------------------------

/-- `F` *decides* the set of terms `A` if, applied to the Church numeral of the code of a term
`X`, it reduces to `true` when `X ∈ A` and to `false` when `X ∉ A`. -/
def Decides (F : Lambda) (A : Lambda → Prop) : Prop :=
  ∀ X : Lambda,
    (A X → Lambda.reduces (Lambda.app F (Lambda.church (Lambda.encode X))) Lambda.true) ∧
    (¬ A X → Lambda.reduces (Lambda.app F (Lambda.church (Lambda.encode X))) Lambda.false)

/-- The diagonal term used in Scott's theorem: on the code of a term it runs the supposed decider
and returns `N` (outside `A`) when the answer is "inside", and `M` (inside `A`) otherwise. -/
def scottBody (F N M : Lambda) : Lambda :=
  Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app F (Lambda.var 0))) N) M

/-- `scottTerm F N M = λc. if F c then N else M`. -/
def scottTerm (F N M : Lambda) : Lambda := Lambda.lam (scottBody F N M)

theorem scottTerm_closed {F N M : Lambda} (hF : Lambda.IsClosed F) (hN : Lambda.IsClosed N)
    (hM : Lambda.IsClosed M) : Lambda.IsClosed (scottTerm F N M) := by
  rw [← Lambda.IsClosedAt_zero_iff_IsClosed]
  refine Lambda.IsClosedAt_lam ?_
  refine Lambda.IsClosedAt_app (Lambda.IsClosedAt_app (Lambda.IsClosedAt_app ?_ ?_) ?_) ?_
  · exact IsClosedAt_of_IsClosed Lambda.ifThenElse_closed 1
  · exact Lambda.IsClosedAt_app (IsClosedAt_of_IsClosed hF 1) (Lambda.IsClosedAt_var 0 1 (by omega))
  · exact IsClosedAt_of_IsClosed hN 1
  · exact IsClosedAt_of_IsClosed hM 1

theorem scottTerm_app_reduces {F N M : Lambda} (hF : Lambda.IsClosed F) (hN : Lambda.IsClosed N)
    (hM : Lambda.IsClosed M) (n : ℕ) :
    Lambda.reduces (Lambda.app (scottTerm F N M) (Lambda.church n))
      (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
        (Lambda.app F (Lambda.church n))) N) M) := by
  have hsubst : Lambda.subst (Lambda.church n) 0 (scottBody F N M) =
      Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
        (Lambda.app F (Lambda.church n))) N) M := by
    simp [scottBody, Lambda.subst, hF _ _, hN _ _, hM _ _, Lambda.ifThenElse_closed _ _]
  rw [scottTerm, ← hsubst]
  exact Lambda.beta_reduces

------------------------------------------------------------------------
-- Scott's theorem
------------------------------------------------------------------------

/-- **Scott's theorem.**  A convertibility-invariant set of lambda terms with a closed member and
a closed non-member is not decided by any closed lambda term. -/
theorem scott_theorem {A : Lambda → Prop} (hA : ConvInvariant A) {M N : Lambda}
    (hM : Lambda.IsClosed M) (hN : Lambda.IsClosed N) (hAM : A M) (hAN : ¬ A N)
    {F : Lambda} (hF : Lambda.IsClosed F) : ¬ Decides F A := by
  intro hdec
  obtain ⟨X, hX⟩ := exists_code_fixed_point (scottTerm_closed hF hN hM)
  have hstep := scottTerm_app_reduces hF hN hM (Lambda.encode X)
  by_cases hAX : A X
  · have htrue := (hdec X).1 hAX
    have hite : Lambda.reduces
        (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
          (Lambda.app F (Lambda.church (Lambda.encode X)))) N) M) N :=
      Lambda.reduces_trans
        (Lambda.reduces_app_left (Lambda.reduces_app_left
          (Lambda.reduces_app_right htrue))) (Lambda.ifThenElse_true N M)
    exact hAN (hA.of_reduces (Lambda.reduces_trans hX (Lambda.reduces_trans hstep hite)) hAX)
  · have hfalse := (hdec X).2 hAX
    have hite : Lambda.reduces
        (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
          (Lambda.app F (Lambda.church (Lambda.encode X)))) N) M) M :=
      Lambda.reduces_trans
        (Lambda.reduces_app_left (Lambda.reduces_app_left
          (Lambda.reduces_app_right hfalse))) (Lambda.ifThenElse_false N M)
    have hXM : Lambda.reduces X M := Lambda.reduces_trans hX (Lambda.reduces_trans hstep hite)
    exact hAX (hA M X (conv_of_reduces hXM).symm hAM)

/-- Restated existentially: no closed term decides a non-trivial semantic property. -/
theorem not_exists_decider {A : Lambda → Prop} (hA : ConvInvariant A) {M N : Lambda}
    (hM : Lambda.IsClosed M) (hN : Lambda.IsClosed N) (hAM : A M) (hAN : ¬ A N) :
    ¬ ∃ F : Lambda, Lambda.IsClosed F ∧ Decides F A := by
  rintro ⟨F, hF, hdec⟩
  exact scott_theorem hA hM hN hAM hAN hF hdec

------------------------------------------------------------------------
-- Rice's theorem for codes
------------------------------------------------------------------------

/-- The set of codes of the terms in `A`. -/
def CodeSet (A : Lambda → Prop) (c : ℕ) : Prop := ∃ t : Lambda, Lambda.decode c = some t ∧ A t

@[simp] theorem codeSet_encode (A : Lambda → Prop) (t : Lambda) :
    CodeSet A (Lambda.encode t) ↔ A t := by
  constructor
  · rintro ⟨u, hu, h⟩
    rw [decode_encode] at hu
    exact (Option.some_inj.mp hu) ▸ h
  · intro h
    exact ⟨t, decode_encode t, h⟩

/-- From a computable characteristic function for `CodeSet A` we can build a closed lambda term
that decides `A`. -/
theorem exists_decider_of_computablePred {A : Lambda → Prop} (h : ComputablePred (CodeSet A)) :
    ∃ F : Lambda, Lambda.IsClosed F ∧ Decides F A := by
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  have hg : Computable fun c : ℕ => cond (f c) 0 1 :=
    hf.cond (Computable.const 0) (Computable.const 1)
  obtain ⟨F₀, hF₀⟩ := Lambda.exists_realizer_of_computable hg
  refine ⟨Lambda.lam (Lambda.app Lambda.isZero (Lambda.app F₀ (Lambda.var 0))), ?_, ?_⟩
  · rw [← Lambda.IsClosedAt_zero_iff_IsClosed]
    refine Lambda.IsClosedAt_lam (Lambda.IsClosedAt_app
      (IsClosedAt_of_IsClosed Lambda.isZero_closed 1)
      (Lambda.IsClosedAt_app (IsClosedAt_of_IsClosed hF₀.1 1)
        (Lambda.IsClosedAt_var 0 1 (by omega))))
  · intro X
    have hbeta : Lambda.reduces
        (Lambda.app (Lambda.lam (Lambda.app Lambda.isZero (Lambda.app F₀ (Lambda.var 0))))
          (Lambda.church (Lambda.encode X)))
        (Lambda.app Lambda.isZero
          (Lambda.app F₀ (Lambda.church (Lambda.encode X)))) := by
      have hsubst : Lambda.subst (Lambda.church (Lambda.encode X)) 0
          (Lambda.app Lambda.isZero (Lambda.app F₀ (Lambda.var 0))) =
          Lambda.app Lambda.isZero (Lambda.app F₀ (Lambda.church (Lambda.encode X))) := by
        simp [Lambda.subst, Lambda.isZero_closed _ _, hF₀.1 _ _]
      rw [← hsubst]
      exact Lambda.beta_reduces
    have hval : Lambda.reduces (Lambda.app F₀ (Lambda.church (Lambda.encode X)))
        (Lambda.church (cond (f (Lambda.encode X)) 0 1)) := hF₀.2 _
    have hred : Lambda.reduces
        (Lambda.app (Lambda.lam (Lambda.app Lambda.isZero (Lambda.app F₀ (Lambda.var 0))))
          (Lambda.church (Lambda.encode X)))
        (Lambda.app Lambda.isZero
          (Lambda.church (cond (f (Lambda.encode X)) 0 1))) :=
      Lambda.reduces_trans hbeta (Lambda.reduces_app_right hval)
    have hiff : f (Lambda.encode X) = Bool.true ↔ A X := by
      rw [← codeSet_encode A X, hfe]
    constructor
    · intro hAX
      have hfx : f (Lambda.encode X) = Bool.true := hiff.2 hAX
      rw [hfx] at hred
      simp only [cond_true] at hred
      exact Lambda.reduces_trans hred Lambda.isZero_zero
    · intro hAX
      have hfx : f (Lambda.encode X) = Bool.false := by
        by_cases hb : f (Lambda.encode X) = Bool.true
        · exact absurd (hiff.1 hb) hAX
        · simpa using hb
      rw [hfx] at hred
      simp only [cond_false] at hred
      exact Lambda.reduces_trans hred (Lambda.isZero_succ 0)

/-- **Rice's theorem for the lambda calculus.**  If a set of lambda terms is invariant under
convertibility and has a closed member and a closed non-member, then the set of codes of its
elements is not computable. -/
theorem not_computablePred_codeSet {A : Lambda → Prop} (hA : ConvInvariant A) {M N : Lambda}
    (hM : Lambda.IsClosed M) (hN : Lambda.IsClosed N) (hAM : A M) (hAN : ¬ A N) :
    ¬ ComputablePred (CodeSet A) := fun h =>
  not_exists_decider hA hM hN hAM hAN (exists_decider_of_computablePred h)

------------------------------------------------------------------------
-- A concrete non-trivial property: convertibility with `church 0`
------------------------------------------------------------------------

theorem omega_closed : Lambda.IsClosed Lambda.omega := by
  intro s x
  simp [Lambda.omega, Lambda.subst]

theorem not_conv_omega_church (k : ℕ) : ¬ Conv Lambda.omega (Lambda.church k) := by
  rintro ⟨u, hu, hk⟩
  have h1 : u = Lambda.omega := reduces_omega_eq hu rfl
  have h2 : Lambda.church k = u := Lambda.reduces_normal_eq (Lambda.church_normal k) hk
  rw [h1] at h2
  simp [Lambda.omega, Lambda.church] at h2

/-- The property "convertible with `church 0`" is convertibility-invariant and non-trivial. -/
theorem convInvariant_conv_church_zero :
    ConvInvariant (fun t => Conv t (Lambda.church 0)) :=
  fun _ _ hst hs => hst.symm.trans hs

/-- **No lambda term decides convertibility with `church 0`.** -/
theorem not_decides_conv_church_zero {F : Lambda} (hF : Lambda.IsClosed F) :
    ¬ Decides F (fun t => Conv t (Lambda.church 0)) :=
  scott_theorem convInvariant_conv_church_zero (Lambda.church_closed 0) omega_closed
    (conv_refl _) (not_conv_omega_church 0) hF

/-- **Convertibility with `church 0` is undecidable**: no computable predicate on codes decides
whether the coded term is convertible with `church 0`. -/
theorem not_computablePred_codeSet_conv_church_zero :
    ¬ ComputablePred (CodeSet (fun t => Conv t (Lambda.church 0))) :=
  not_computablePred_codeSet convInvariant_conv_church_zero (Lambda.church_closed 0) omega_closed
    (conv_refl _) (not_conv_omega_church 0)

end Lambda
