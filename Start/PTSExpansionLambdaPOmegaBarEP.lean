/-
**Expansion postponement for λPω̲ (M29-EP-CUBE-REST, steps 4 and 5).**

* `HasTypeR.normalizeNW`: every reduction-only λPω̲ derivation reduces, context, subject and type
  together, to a canonical `HasTypeNW` derivation (the λPω̲ analogue of `HasTypeR.normalizeNR`).
  A head redex created in the application case is fired by `HasTypeNW.hsubst_obj` when the
  domain is a type and by `HasTypeNW.hsubst_con` when it is a kind.
* `lambdaPOmegaBar_productNormalizationR` and `lambdaPOmegaBar_expansionPostponement`.
-/

import Start.PTSExpansionLambdaPOmegaBarCon
import Start.PTSExpansionCube

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

open LambdaPi (Srt)

/-- **Normalization of derivations (λPω̲).**  Every reduction-only λPω̲ derivation reduces,
context, subject and type together, to a canonical derivation. -/
theorem HasTypeR.normalizeNW {Γ : List (Expr Srt)} {M T : Expr Srt}
    (h : HasTypeR PWbar Γ M T) :
    ∃ Γ' M' T', List.Forall₂ Reduces Γ Γ' ∧ Reduces M M' ∧ Reduces T T' ∧
      HasTypeNW PWbar Γ' M' T' := by
  have hw : SystemWeaklyNormalizing PWbar := fun Γ hΓ M hM =>
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
  | @application Γ f a A B hf _ ihf iha =>
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
            HasTypeNW PWbar Γ₂ e' E' := by
          cases hCk : A₂.isKindB with
          | false => exact HasTypeNW.hsubst_obj hCk ha' he
          | true => exact HasTypeNW.hsubst_con hCk ha' he
        obtain ⟨e', E', her, hEr, he'⟩ := hsub
        exact ⟨_, e', E', hc₂,
          ((Reduces.app hfr har).tail (Beta.head _ e a')).trans her, hTy.trans hEr, he'⟩
      · simp only [not_exists] at hlam
        have happ' : Normal (.app f' a') := Normal.app_of hf'.normal.1 ha'.normal.1 hlam
        have hT : HasType PWbar Γ₂ (.app f' a') (B₁.instantiate a') :=
          .application hf'.toHasType ha'.toHasType
        obtain ⟨B'', hred, hnorm⟩ := hw _ hT.valid _ ⟨_, .inr hT⟩
        exact ⟨_, _, B'', hc₂, Reduces.app hfr har, hTy.trans hred,
          .application hf' ha' hred hnorm happ'⟩
  | reduction _ hAB ih =>
      obtain ⟨Γ', M', A', hc, hMr, hAr, hM'⟩ := ih
      exact ⟨Γ', M', A', hc, hMr,
        Reduces.to_normal (Relation.ReflTransGen.single hAB) hAr hM'.normal.2.1, hM'⟩

/-- Product normalization for λPω̲. -/
theorem lambdaPOmegaBar_productNormalizationR : ProductNormalizationR (cubeSpec lambdaPOmegaBar) := by
  intro Γ A B B' s hP hBB' hB'n
  obtain ⟨s₁, s₂, s₃, hA, hB, hr, hs⟩ := hP.generation_pi A B rfl
  obtain ⟨Γ', M', T', hc, hM, hT, hNW⟩ := hB.normalizeNW
  rw [Reduces.sort_eq hT] at hNW
  obtain rfl := Reduces.normal_unique hM hBB' hNW.normal.1 hB'n
  have hB' := hNW.toHasTypeR.ctx_expand (A :: Γ) hB.valid hc
  cases hs
  exact .product hA hB' hr

/-- **Expansion postponement for λPω̲** (TLCA open problem 23, the λPω̲ corner of the cube). -/
theorem lambdaPOmegaBar_expansionPostponement :
    ExpansionPostponement (cubeSpec lambdaPOmegaBar) :=
  cube_expansionPostponement_of_productNormalizationR lambdaPOmegaBar
    lambdaPOmegaBar_productNormalizationR

end PureTypeSystem
