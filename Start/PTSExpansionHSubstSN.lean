/-
**Hereditary substitution from strong normalization (M29-EP-IMPREDICATIVE, route (iii)).**

Route (iii): prove `HSubstNW (cubeSpec f)` by well-founded induction on the strong normalization
of the substituted term `M[N]`, with an inner induction on the canonical derivation of `M`.

* `Expr.DescStep`: one step down, i.e. a one-step reduct or an immediate subterm.
* `Expr.acc_descStep_of_sn`: a strongly normalizing term is accessible for `DescStep`, hence for
  its transitive closure (`Expr.acc_desc_of_sn`).  This is the order of route (iii).
* `HSubstPi P`: hereditary substitution restricted to **product premises** `Θ ⊢ Π C E : s`, at
  depth, into a context that is already canonically valid.
* `hsubst_route3_aux`: route (iii) itself.  The outer induction is on `Acc` of `M[N]` (up to
  renaming); the inner induction is on the canonical derivation of `M`.  The variable and
  weakening cases read their context declarations off the (canonically valid) target context, the
  created head redex `(λx:C'. e) a'` of the application case is fired by the outer hypothesis
  (`e[a']` is a reduct of `M[N]`), and the abstraction case takes its product premise from
  `HSubstPi`.
* `hsubstNW_of_hsubstPi`: in every corner of the cube, `HSubstPi` implies `HSubstNW`;
  `cube_expansionPostponement_of_hsubstPi`: and hence expansion postponement.

**Where route (iii) stops.**  The one recursive call of the inner induction that is not at a
smaller point of the order is the call on the product premise `Θ ⊢ Π C E : s` of the abstraction
rule `Θ ⊢ λC. b : Π C E`.  Its subject `(Π C E)[N]` contains `E[N]`, where `E` is the *type* of
the body `b`; `E[N]` is neither a reduct nor a subterm of `M[N]` (nor of a renaming of it), so the
invariant `Below ((Π C E)[N]) root` that the inner hypothesis needs is not available.  Head redexes
created inside `E[N]` would then need the outer hypothesis at points that are not below `root`.
This is isolated as the hypothesis `HSubstPi`; it is the first missing lemma
(`hsubstPi_lambdaP2 : HSubstPi (cubeSpec lambdaP2)`).
-/

import Start.PTSExpansionLambdaP2

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

open LambdaPi (Srt)

universe u

namespace Expr

variable {S : Type u}

/-- Immediate subterms. -/
inductive ImmSub : Expr S → Expr S → Prop
  | app_left (f a : Expr S) : ImmSub f (.app f a)
  | app_right (f a : Expr S) : ImmSub a (.app f a)
  | lam_domain (A b : Expr S) : ImmSub A (.lam A b)
  | lam_body (A b : Expr S) : ImmSub b (.lam A b)
  | pi_domain (A B : Expr S) : ImmSub A (.pi A B)
  | pi_body (A B : Expr S) : ImmSub B (.pi A B)

/-- One step down the order of route (iii): a one-step reduct or an immediate subterm. -/
def DescStep (x y : Expr S) : Prop := Beta y x ∨ ImmSub x y

theorem ImmSub.beta {u t u' : Expr S} (h : ImmSub u t) (hb : Beta u u') :
    ∃ t', Beta t t' ∧ ImmSub u' t' := by
  cases h with
  | app_left f a => exact ⟨_, .app_left hb, .app_left _ _⟩
  | app_right f a => exact ⟨_, .app_right hb, .app_right _ _⟩
  | lam_domain A b => exact ⟨_, .lam_domain hb, .lam_domain _ _⟩
  | lam_body A b => exact ⟨_, .lam_body hb, .lam_body _ _⟩
  | pi_domain A B => exact ⟨_, .pi_domain hb, .pi_domain _ _⟩
  | pi_body A B => exact ⟨_, .pi_body hb, .pi_body _ _⟩

theorem sub_beta {u t u' : Expr S} (h : Relation.ReflTransGen ImmSub u t) (hb : Beta u u') :
    ∃ t', Beta t t' ∧ Relation.ReflTransGen ImmSub u' t' := by
  induction h with
  | refl => exact ⟨u', hb, .refl⟩
  | tail _ hmt ih =>
      obtain ⟨m', hm, hsub⟩ := ih
      obtain ⟨t', ht, hs⟩ := hmt.beta hm
      exact ⟨t', ht, hsub.tail hs⟩

/-- **Strongly normalizing terms are accessible for "reduct or immediate subterm".** -/
theorem acc_descStep_of_sn {t : Expr S} (h : StronglyNormalizing t) : Acc DescStep t := by
  suffices H : ∀ t : Expr S, StronglyNormalizing t →
      ∀ u, Relation.ReflTransGen ImmSub u t → Acc DescStep u from H t h t .refl
  intro t ht
  induction ht with
  | intro t _ ihT =>
      intro u hu
      induction u with
      | var n =>
          refine ⟨_, fun y hy => ?_⟩
          rcases hy with hy | hy
          · obtain ⟨t', ht', hs⟩ := sub_beta hu hy
            exact ihT t' ht' y hs
          · cases hy
      | sort s =>
          refine ⟨_, fun y hy => ?_⟩
          rcases hy with hy | hy
          · obtain ⟨t', ht', hs⟩ := sub_beta hu hy
            exact ihT t' ht' y hs
          · cases hy
      | app f a ihf iha =>
          refine ⟨_, fun y hy => ?_⟩
          rcases hy with hy | hy
          · obtain ⟨t', ht', hs⟩ := sub_beta hu hy
            exact ihT t' ht' y hs
          · cases hy with
            | app_left => exact ihf (Relation.ReflTransGen.head (.app_left _ _) hu)
            | app_right => exact iha (Relation.ReflTransGen.head (.app_right _ _) hu)
      | lam A b ihA ihb =>
          refine ⟨_, fun y hy => ?_⟩
          rcases hy with hy | hy
          · obtain ⟨t', ht', hs⟩ := sub_beta hu hy
            exact ihT t' ht' y hs
          · cases hy with
            | lam_domain => exact ihA (Relation.ReflTransGen.head (.lam_domain _ _) hu)
            | lam_body => exact ihb (Relation.ReflTransGen.head (.lam_body _ _) hu)
      | pi A B ihA ihB =>
          refine ⟨_, fun y hy => ?_⟩
          rcases hy with hy | hy
          · obtain ⟨t', ht', hs⟩ := sub_beta hu hy
            exact ihT t' ht' y hs
          · cases hy with
            | pi_domain => exact ihA (Relation.ReflTransGen.head (.pi_domain _ _) hu)
            | pi_body => exact ihB (Relation.ReflTransGen.head (.pi_body _ _) hu)

/-- The order of route (iii) is well founded below every strongly normalizing term. -/
theorem acc_desc_of_sn {t : Expr S} (h : StronglyNormalizing t) :
    Acc (Relation.TransGen DescStep) t :=
  (acc_descStep_of_sn h).transGen

theorem DescStep.rename {x y : Expr S} (h : DescStep x y) (ρ : Nat → Nat) :
    ∃ ρ', DescStep (x.rename ρ') (y.rename ρ) := by
  rcases h with h | h
  · exact ⟨ρ, .inl (h.rename ρ)⟩
  · cases h with
    | app_left f a => exact ⟨ρ, .inr (.app_left _ _)⟩
    | app_right f a => exact ⟨ρ, .inr (.app_right _ _)⟩
    | lam_domain A b => exact ⟨ρ, .inr (.lam_domain _ _)⟩
    | lam_body A b => exact ⟨liftRen ρ, .inr (.lam_body _ _)⟩
    | pi_domain A B => exact ⟨ρ, .inr (.pi_domain _ _)⟩
    | pi_body A B => exact ⟨liftRen ρ, .inr (.pi_body _ _)⟩

/-- `x` lies below `root` up to renaming. -/
def Below (x root : Expr S) : Prop := ∃ ρ, Relation.ReflTransGen DescStep (x.rename ρ) root

theorem Below.down {x y root : Expr S} (h : Below y root) (hxy : DescStep x y) : Below x root := by
  obtain ⟨ρ, hρ⟩ := h
  obtain ⟨ρ', h'⟩ := hxy.rename ρ
  exact ⟨ρ', Relation.ReflTransGen.head h' hρ⟩

theorem Below.unrename {x root : Expr S} {τ : Nat → Nat} (h : Below (x.rename τ) root) :
    Below x root := by
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨ρ ∘ τ, by rwa [← rename_comp]⟩

/-- A reduct of `x` followed by one more step is strictly below every `root` above `x`. -/
theorem Below.trans_reduct {x y z root : Expr S} (h : Below x root) (hxy : Reduces x y)
    (hyz : Beta y z) : ∃ ρ, Relation.TransGen DescStep (z.rename ρ) root := by
  obtain ⟨ρ, hρ⟩ := h
  have h0 : ∀ {x y z : Expr S}, Reduces x y → Beta y z → Relation.TransGen DescStep z x := by
    intro x y z hr hb
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => exact .single (.inl hb)
    | head hab _ ih => exact ih.tail (.inl hab)
  have h1 : Relation.TransGen DescStep (z.rename ρ) (x.rename ρ) :=
    h0 (hxy.rename ρ) (hyz.rename ρ)
  exact ⟨ρ, h1.trans_left hρ⟩

end Expr

/-- **Hereditary substitution into product premises**: substituting a canonical `N : A` (at depth
`Δ`) into a canonical product judgement `Π C E : s`, into a canonically valid target context,
gives after reduction a canonical product judgement.  This is the one recursive call of route
(iii) that is not at a smaller point of the order. -/
def HSubstPi (P : Specification Srt) : Prop :=
  ∀ {Γ : List (Expr Srt)} {N A : Expr Srt} {Δ Δ' : List (Expr Srt)} {C E : Expr Srt} {s : Srt},
    HasTypeNW P Γ N A → CtxSubstRed N Δ Δ' → ValidContextNW P (Δ' ++ Γ) →
    HasTypeNW P (Δ ++ A :: Γ) (.pi C E) (.sort s) →
    ∃ C' E', Reduces (C.subst (Expr.substAt N Δ.length)) C' ∧
      Reduces (E.subst (Expr.substAt N (Δ.length + 1))) E' ∧
      HasTypeNW P (Δ' ++ Γ) (.pi C' E') (.sort s)

/-- **Route (iii)**: outer well-founded induction on `root` (the substituted subject, up to
renaming, in the order "reduct or subterm"), inner induction on the canonical derivation. -/
theorem hsubst_route3_aux (f : CubeFeatures) (hpi : HSubstPi (cubeSpec f)) (root : Expr Srt)
    (hacc : Acc (Relation.TransGen Expr.DescStep) root) :
    ∀ {Γ : List (Expr Srt)} {N A : Expr Srt} {Θ : List (Expr Srt)} {M B : Expr Srt},
      HasTypeNW (cubeSpec f) Γ N A → HasTypeNW (cubeSpec f) Θ M B →
      ∀ Δ Δ' : List (Expr Srt), Θ = Δ ++ A :: Γ → CtxSubstRed N Δ Δ' →
      ValidContextNW (cubeSpec f) (Δ' ++ Γ) →
      Expr.Below (M.subst (Expr.substAt N Δ.length)) root →
      ∃ M' B', Reduces (M.subst (Expr.substAt N Δ.length)) M' ∧
        Reduces (B.subst (Expr.substAt N Δ.length)) B' ∧
        HasTypeNW (cubeSpec f) (Δ' ++ Γ) M' B' := by
  have hw : SystemWeaklyNormalizing (cubeSpec f) := fun Γ hΓ M hM =>
    weaklyNormalizing_of_stronglyNormalizing (cube_stronglyNormalizing _ Γ hΓ M hM)
  induction hacc with
  | intro root _ IHo =>
  intro Γ N A Θ M B hN h
  have ctxn : ∀ {Δ' : List (Expr Srt)} {M' B' : Expr Srt},
      HasTypeNW (cubeSpec f) (Δ' ++ Γ) M' B' → ∀ X ∈ Δ', Normal X :=
    fun h X hX => h.normal.2.2 X (List.mem_append_left _ hX)
  induction h with
  | ax _ => intro Δ _ heq; cases Δ <;> simp at heq
  | @var Θ₀ A₀ s hA₀ ih =>
      intro Δ Δ' heq hc hv _
      cases Δ with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          cases hc
          refine ⟨N, A₀, ?_, ?_, hN⟩
          · exact .refl
          · simp only [List.length_nil, Expr.substAt_zero, Expr.subst_lift_single]
            exact .refl
      | cons D Δ₀ =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          cases hc with
          | @cons _ Δ'₀ _ D' hc₀ hD =>
              cases hv with
              | cons hv₀ hD' =>
                  refine ⟨.var 0, D'.rename Nat.succ, ?_, ?_, .var hD'⟩
                  · simp only [List.length_cons, Expr.substAt_succ]
                    exact .refl
                  · simp only [List.length_cons, Expr.substAt_succ, Expr.rename_succ_subst_lift]
                    exact hD.rename _
  | @weaken Θ₀ M₀ B₀ A₀ s hM hA ihM ihA =>
      intro Δ Δ' heq hc hv hbelow
      cases Δ with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          cases hc
          refine ⟨M₀, B₀, ?_, ?_, hM⟩ <;>
            simp only [List.length_nil, Expr.substAt_zero, Expr.subst_lift_single] <;> exact .refl
      | cons D Δ₀ =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          cases hc with
          | @cons _ Δ'₀ _ D' hc₀ hD =>
              cases hv with
              | cons hv₀ hD' =>
                  have hb : Expr.Below (M₀.subst (Expr.substAt N Δ₀.length)) root := by
                    simp only [List.length_cons, Expr.substAt_succ,
                      Expr.rename_succ_subst_lift] at hbelow
                    exact hbelow.unrename
                  obtain ⟨M', B', hMr, hBr, hM'⟩ := ihM Δ₀ Δ'₀ rfl hc₀ hv₀ hb
                  refine ⟨M'.rename Nat.succ, B'.rename Nat.succ, ?_, ?_, .weaken hM' hD'⟩ <;>
                    simp only [List.length_cons, Expr.substAt_succ, Expr.rename_succ_subst_lift]
                  · exact hMr.rename _
                  · exact hBr.rename _
  | @product Θ C E s₁ s₂ s₃ hC hE hr ihC ihE =>
      intro Δ Δ' heq hc hv hbelow
      simp only [Expr.subst] at hbelow
      obtain ⟨C', T₁, hCr, hT₁, hC'⟩ :=
        ihC Δ Δ' heq hc hv (hbelow.down (.inr (.pi_domain _ _)))
      simp only [Expr.subst] at hT₁
      rw [Reduces.sort_eq hT₁] at hC'
      have hbE : Expr.Below (E.subst (Expr.substAt N (C :: Δ).length)) root := by
        rw [List.length_cons, Expr.substAt_succ]
        exact hbelow.down (.inr (.pi_body _ _))
      obtain ⟨E', T₂, hEr, hT₂, hE'⟩ :=
        ihE (C :: Δ) (C' :: Δ') (by rw [heq]; rfl) (.cons hc hCr) (.cons hv hC') hbE
      simp only [Expr.subst] at hT₂
      rw [Reduces.sort_eq hT₂] at hE'
      refine ⟨.pi C' E', .sort s₃, ?_, .refl, .product hC' hE' hr⟩
      simp only [Expr.subst, ← Expr.substAt_succ]
      simp only [List.length_cons] at hEr
      exact Reduces.pi hCr hEr
  | @abstraction Θ C b E s hb hP ihb ihP =>
      intro Δ Δ' heq hc hv hbelow
      rw [heq] at hP
      obtain ⟨C', E', hCr, hEr, hX⟩ := hpi hN hc hv hP
      obtain ⟨s₁, hC'⟩ := hX.product_domain _ _ rfl
      simp only [Expr.subst] at hbelow
      have hbb : Expr.Below (b.subst (Expr.substAt N (C :: Δ).length)) root := by
        rw [List.length_cons, Expr.substAt_succ]
        exact hbelow.down (.inr (.lam_body _ _))
      obtain ⟨b', E'', hbr, hEr', hb'⟩ :=
        ihb (C :: Δ) (C' :: Δ') (by rw [heq]; rfl) (.cons hc hCr) (.cons hv hC') hbb
      simp only [List.length_cons] at hbr hEr'
      obtain rfl : E'' = E' := Reduces.normal_unique hEr' hEr hb'.normal.2.1
        hX.normal.1.pi_body
      refine ⟨.lam C' b', .pi C' E'', ?_, ?_, .abstraction hb' hX⟩
      · simp only [Expr.subst, ← Expr.substAt_succ]
        exact Reduces.lam hCr hbr
      · simp only [Expr.subst, ← Expr.substAt_succ]
        exact Reduces.pi hCr hEr
  | @application Θ F a C D B₀ hF ha hr hB₀ happ ihF iha =>
      intro Δ Δ' heq hc hv hbelow
      have hbelow' := hbelow
      simp only [Expr.subst] at hbelow'
      obtain ⟨F', T', hFr, hTr, hF'⟩ :=
        ihF Δ Δ' heq hc hv (hbelow'.down (.inr (.app_left _ _)))
      simp only [Expr.subst] at hTr
      obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Reduces.pi_inv hTr
      obtain ⟨a', C', har, hCr, ha'⟩ :=
        iha Δ Δ' heq hc hv (hbelow'.down (.inr (.app_right _ _)))
      obtain rfl : C' = A₁ := Reduces.normal_unique hCr hA₁ ha'.normal.2.1
        hF'.normal.2.1.pi_domain
      set σ := Expr.substAt N Δ.length with hσdef
      have hTy : Reduces ((D.instantiate a).subst σ) (B₁.instantiate a') := by
        rw [← Expr.instantiate_subst]
        exact Reduces.instantiate hB₁ har
      have hB₀σ : Reduces ((D.instantiate a).subst σ) (B₀.subst σ) := hr.subst σ
      by_cases hlam : ∃ C₀ e, F' = .lam C₀ e
      · obtain ⟨C₀, e, rfl⟩ := hlam
        obtain ⟨E₀, s, heqT, he, _⟩ := hF'.lam_inv _ _ rfl
        obtain ⟨rfl, rfl⟩ := Expr.pi.inj heqT
        have hred : Reduces ((Expr.app F a).subst σ) (.app (.lam C' e) a') := by
          simp only [Expr.subst]
          exact Reduces.app hFr har
        obtain ⟨ρ, hlt⟩ := hbelow.trans_reduct hred (Beta.head C' e a')
        obtain ⟨e', E', her, hEr, he'⟩ :=
          IHo _ hlt ha' he ([]) ([]) rfl .nil ha'.valid ⟨ρ, .refl⟩
        simp only [List.length_nil, Expr.substAt_zero, List.nil_append] at her hEr he'
        refine ⟨e', E', ?_, ?_, he'⟩
        · exact (hred.tail (Beta.head C' e a')).trans her
        · exact Reduces.to_normal hB₀σ (hTy.trans hEr) he'.normal.2.1
      · simp only [not_exists] at hlam
        have happ' : Normal (.app F' a') :=
          Normal.app_of hF'.normal.1 ha'.normal.1 hlam
        have hT : HasType (cubeSpec f) (Δ' ++ Γ) (.app F' a') (B₁.instantiate a') :=
          .application hF'.toHasType ha'.toHasType
        obtain ⟨B'', hred, hnorm⟩ := hw _ hT.valid _ ⟨_, .inr hT⟩
        refine ⟨.app F' a', B'', ?_, ?_, .application hF' ha' hred hnorm happ'⟩
        · simp only [Expr.subst]
          exact Reduces.app hFr har
        · exact Reduces.to_normal hB₀σ (hTy.trans hred) hnorm

/-- **Route (iii) closes up to product premises**: in every corner of the cube, hereditary
substitution into product premises gives hereditary substitution on canonical derivations.  The
termination of the created redexes is bought from strong normalization
(`cube_stronglyNormalizing`). -/
theorem hsubstNW_of_hsubstPi (f : CubeFeatures) (hpi : HSubstPi (cubeSpec f)) :
    HSubstNW (cubeSpec f) := by
  intro Γ N A M B hN hM
  have hT : HasType (cubeSpec f) Γ (M.instantiate N) (B.instantiate N) := by
    show HasType _ _ (M.subst (Expr.single N)) (B.subst (Expr.single N))
    have := HasType.subst_at (Δ := []) hN.toHasType hM.toHasType
    simpa only [ctxSubstAt, List.nil_append, List.length_nil, Expr.substAt_zero] using this
  have hsn : StronglyNormalizing (M.instantiate N) :=
    cube_stronglyNormalizing f Γ hT.valid _ ⟨_, .inl hT⟩
  have hb : Expr.Below (M.subst (Expr.substAt N ([] : List (Expr Srt)).length))
      (M.instantiate N) := ⟨id, by rw [Expr.rename_id]; exact .refl⟩
  obtain ⟨M', B', h1, h2, h3⟩ :=
    hsubst_route3_aux f hpi _ (Expr.acc_desc_of_sn hsn) hN hM ([]) ([]) rfl .nil hN.valid hb
  exact ⟨M', B', h1, h2, h3⟩

/-- Expansion postponement in every corner of the cube, from hereditary substitution into
product premises. -/
theorem cube_expansionPostponement_of_hsubstPi (f : CubeFeatures)
    (hpi : HSubstPi (cubeSpec f)) :
    ProductNormalizationR (cubeSpec f) ∧ ExpansionPostponement (cubeSpec f) :=
  ⟨productNormalizationR_of_hsubst f (hsubstNW_of_hsubstPi f hpi),
    expansionPostponement_of_hsubst f (hsubstNW_of_hsubstPi f hpi)⟩

/-- Conversely, `HSubstNW` gives `HSubstPi` at depth `0` (sanity check of the hypothesis: it is
the depth-`0` product instance of `HSubstNW` when the context is empty). -/
theorem hsubstPi_nil_of_hsubstNW {P : Specification Srt} (hs : HSubstNW P)
    {Γ : List (Expr Srt)} {N A C E : Expr Srt} {s : Srt}
    (hN : HasTypeNW P Γ N A) (hP : HasTypeNW P (A :: Γ) (.pi C E) (.sort s)) :
    ∃ X, Reduces ((Expr.pi C E).instantiate N) X ∧ HasTypeNW P Γ X (.sort s) := by
  obtain ⟨X, T, hX, hT, h⟩ := hs hN hP
  have hT' : T = .sort s := Reduces.sort_eq hT
  subst hT'
  exact ⟨X, hX, h⟩

end PureTypeSystem
