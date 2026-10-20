/-
**Expansion postponement for λP2 (M29-EP-IMPREDICATIVE): the reduction to hereditary
substitution.**

The λPω̲ argument of `Start/PTSExpansionLambdaPOmegaBarEP.lean` is corner-independent except at
one point: the application case, where a created head redex `(λx:C. e) a'` is fired by
hereditary substitution on canonical (`HasTypeNW`) derivations.  This file isolates that point.

* `PureTypeSystem.HSubstNW P` — the hereditary substitution property for canonical derivations of
  a specification `P` (the statement of the missing lemma `HasTypeNW.hsubst_lambdaP2` for
  `P = cubeSpec lambdaP2`);
* `PureTypeSystem.HasTypeR.normalizeNW_of_hsubst` — in every corner `f` of the cube, `HSubstNW`
  implies that every reduction-only derivation normalizes to a canonical one;
* `PureTypeSystem.productNormalizationR_of_hsubst`, `expansionPostponement_of_hsubst` — and hence
  product normalization and expansion postponement;
* `PureTypeSystem.lambdaP2_expansionPostponement_of_hsubst` — the λP2 instance;
* `PureTypeSystem.hsubstNW_lambdaPOmegaBar` — sanity check: the property holds for λPω̲.

So `lambdaP2_productNormalizationR` and `lambdaP2_expansionPostponement` are reduced, with no other
gap, to `HSubstNW (cubeSpec lambdaP2)`; see `docs/goal/evidence/M29-EP.md`.
-/

import Start.PTSExpansionLambdaPOmegaBarEP

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

open LambdaPi (Srt)

/-- **Hereditary substitution on canonical derivations**: substituting a canonical argument into
a canonical derivation gives, after reduction, a canonical derivation. -/
def HSubstNW (P : Specification Srt) : Prop :=
  ∀ {Γ : List (Expr Srt)} {N A M B : Expr Srt}, HasTypeNW P Γ N A → HasTypeNW P (A :: Γ) M B →
    ∃ M' B', Reduces (M.instantiate N) M' ∧ Reduces (B.instantiate N) B' ∧ HasTypeNW P Γ M' B'

/-- Sanity check: the property holds for λPω̲ (it is what `hsubst_obj` and `hsubst_con` prove), so
λPω̲'s expansion postponement is an instance of `expansionPostponement_of_hsubst`. -/
theorem hsubstNW_lambdaPOmegaBar : HSubstNW (cubeSpec lambdaPOmegaBar) := by
  intro Γ N A M B hN hM
  cases hCk : A.isKindB with
  | false => exact HasTypeNW.hsubst_obj hCk hN hM
  | true => exact HasTypeNW.hsubst_con hCk hN hM

/-- **Normalization of derivations from hereditary substitution**, in every corner of the cube. -/
theorem HasTypeR.normalizeNW_of_hsubst (f : CubeFeatures) (hs : HSubstNW (cubeSpec f))
    {Γ : List (Expr Srt)} {M T : Expr Srt} (h : HasTypeR (cubeSpec f) Γ M T) :
    ∃ Γ' M' T', List.Forall₂ Reduces Γ Γ' ∧ Reduces M M' ∧ Reduces T T' ∧
      HasTypeNW (cubeSpec f) Γ' M' T' := by
  have hw : SystemWeaklyNormalizing (cubeSpec f) := fun Γ hΓ M hM =>
    weaklyNormalizing_of_stronglyNormalizing (cube_stronglyNormalizing _ Γ hΓ M hM)
  induction h with
  | ax h => exact ⟨[], _, _, .nil, .refl, .refl, .ax h⟩
  | var _ ih =>
      obtain ⟨Γ', A', T', hc, hAr, hT, hA'⟩ := ih
      rw [Reduces.sort_eq hT] at hA'
      exact ⟨_, _, _, .cons hAr hc, .refl, hAr.rename _, .var hA'⟩
  | weaken _ _ ihM ihA =>
      obtain ⟨Γ₁, M', B', hc₁, hMr, hBr, hM'⟩ := ihM
      obtain ⟨Γ₂, A', T', hc₂, hAr, hT, hA'⟩ := ihA
      rw [Reduces.sort_eq hT] at hA'
      obtain rfl := forall₂_reduces_unique hc₁ hc₂ hM'.normal.2.2 hA'.normal.2.2
      exact ⟨_, _, _, .cons hAr hc₁, hMr.rename _, hBr.rename _, .weaken hM' hA'⟩
  | product _ _ hr ihA ihB =>
      obtain ⟨Γ₁, A', T₁, hc₁, hAr, hT₁, hA'⟩ := ihA
      obtain ⟨Γ₂, B', T₂, hc₂, hBr, hT₂, hB'⟩ := ihB
      rw [Reduces.sort_eq hT₁] at hA'
      rw [Reduces.sort_eq hT₂] at hB'
      cases hc₂ with
      | cons hA'' hc₂ =>
          have hn := hB'.normal.2.2
          obtain rfl := Reduces.normal_unique hA'' hAr (hn _ (List.mem_cons_self ..))
            hA'.normal.1
          obtain rfl := forall₂_reduces_unique hc₂ hc₁
            (fun X hX => hn X (List.mem_cons_of_mem _ hX)) hA'.normal.2.2
          exact ⟨_, _, _, hc₁, Reduces.pi hA'' hBr, .refl, .product hA' hB' hr⟩
  | abstraction _ _ ihb ihP =>
      obtain ⟨Γ₂, b', B', hc₂, hbr, hBr, hb'⟩ := ihb
      obtain ⟨Γ₁, X, T₁, hc₁, hXr, hT₁, hX⟩ := ihP
      rw [Reduces.sort_eq hT₁] at hX
      obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Reduces.pi_inv hXr
      cases hc₂ with
      | cons hA'' hc₂ =>
          have hn := hb'.normal
          have hXn := hX.normal.1
          obtain rfl := Reduces.normal_unique hA'' hA₁ (hn.2.2 _ (List.mem_cons_self ..))
            hXn.pi_domain
          obtain rfl := Reduces.normal_unique hBr hB₁ hn.2.1 hXn.pi_body
          obtain rfl := forall₂_reduces_unique hc₂ hc₁
            (fun X hX => hn.2.2 X (List.mem_cons_of_mem _ hX)) hX.normal.2.2
          exact ⟨_, _, _, hc₁, Reduces.lam hA'' hbr, Reduces.pi hA'' hBr,
            .abstraction hb' hX⟩
  | @application Γ g a A B hf _ ihf iha =>
      obtain ⟨Γ₁, f', T', hc₁, hfr, hTr, hf'⟩ := ihf
      obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Reduces.pi_inv hTr
      obtain ⟨Γ₂, a', A₂, hc₂, har, hAr, ha'⟩ := iha
      obtain rfl := Reduces.normal_unique hAr hA₁ ha'.normal.2.1 hf'.normal.2.1.pi_domain
      obtain rfl := forall₂_reduces_unique hc₂ hc₁ ha'.normal.2.2 hf'.normal.2.2
      have hTy : Reduces (B.instantiate a) (B₁.instantiate a') := Reduces.instantiate hB₁ har
      by_cases hlam : ∃ C e, f' = .lam C e
      · obtain ⟨C, e, rfl⟩ := hlam
        obtain ⟨E, s, heqT, he, _⟩ := hf'.lam_inv _ _ rfl
        obtain ⟨rfl, rfl⟩ := Expr.pi.inj heqT
        have hsub : ∃ e' E', Reduces (e.instantiate a') e' ∧ Reduces (B₁.instantiate a') E' ∧
            HasTypeNW (cubeSpec f) Γ₂ e' E' := hs ha' he
        obtain ⟨e', E', her, hEr, he'⟩ := hsub
        exact ⟨_, e', E', hc₂,
          ((Reduces.app hfr har).tail (Beta.head _ e a')).trans her, hTy.trans hEr, he'⟩
      · simp only [not_exists] at hlam
        have happ' : Normal (.app f' a') := Normal.app_of hf'.normal.1 ha'.normal.1 hlam
        have hT : HasType (cubeSpec f) Γ₂ (.app f' a') (B₁.instantiate a') :=
          .application hf'.toHasType ha'.toHasType
        obtain ⟨B'', hred, hnorm⟩ := hw _ hT.valid _ ⟨_, .inr hT⟩
        exact ⟨_, _, B'', hc₂, Reduces.app hfr har, hTy.trans hred,
          .application hf' ha' hred hnorm happ'⟩
  | reduction _ hAB ih =>
      obtain ⟨Γ', M', A', hc, hMr, hAr, hM'⟩ := ih
      exact ⟨Γ', M', A', hc, hMr,
        Reduces.to_normal (Relation.ReflTransGen.single hAB) hAr hM'.normal.2.1, hM'⟩

/-- Product normalization from hereditary substitution, in every corner of the cube. -/
theorem productNormalizationR_of_hsubst (f : CubeFeatures) (hs : HSubstNW (cubeSpec f)) :
    ProductNormalizationR (cubeSpec f) := by
  intro Γ A B B' s hP hBB' hB'n
  obtain ⟨s₁, s₂, s₃, hA, hB, hr, hs'⟩ := hP.generation_pi A B rfl
  obtain ⟨Γ', M', T', hc, hM, hT, hNW⟩ := hB.normalizeNW_of_hsubst f hs
  rw [Reduces.sort_eq hT] at hNW
  obtain rfl := Reduces.normal_unique hM hBB' hNW.normal.1 hB'n
  have hB' := hNW.toHasTypeR.ctx_expand (A :: Γ) hB.valid hc
  cases hs'
  exact .product hA hB' hr

/-- Expansion postponement from hereditary substitution, in every corner of the cube. -/
theorem expansionPostponement_of_hsubst (f : CubeFeatures) (hs : HSubstNW (cubeSpec f)) :
    ExpansionPostponement (cubeSpec f) :=
  cube_expansionPostponement_of_productNormalizationR f (productNormalizationR_of_hsubst f hs)

/-- **λP2: product normalization and expansion postponement follow from hereditary
substitution** on canonical λP2 derivations. -/
theorem lambdaP2_expansionPostponement_of_hsubst (hs : HSubstNW (cubeSpec lambdaP2)) :
    ProductNormalizationR (cubeSpec lambdaP2) ∧ ExpansionPostponement (cubeSpec lambdaP2) :=
  ⟨productNormalizationR_of_hsubst lambdaP2 hs, expansionPostponement_of_hsubst lambdaP2 hs⟩

end PureTypeSystem
