import Start.PTSExpansionCoC
import Start.PTSExpansionPoll

/-!
# Series V, round 1, part C2: the specification-independent half of the coc route

The round-11 proof of `coc_expansionPostponement` is a chain

  `SortFundamental` (route (ii), the fundamental lemma) → `HSubstSort` → `HSubstPi`
  → `HSubstNW` (route (iii)) → `ProductNormalizationR` → `ExpansionPostponement`.

In the repository every link after the first is stated for `cubeSpec f` (or for a specification
over the cube's sort type `Srt`), and buys normalization from `cube_stronglyNormalizing`.  Here
the same links are restated and reproved for an arbitrary specification `P` over an arbitrary sort
type, with strong normalization as the only hypothesis (namespace `PureTypeSystem.SNGeneric`):

* `SNGeneric.NormNW`, `SortFundamental`, `HSubstSort`, `HSubstPi`, `HSubstNW` — the round-11
  definitions over any sort type (definitionally the old ones at `Srt`: `sortFundamental_iff`);
* `hsubst_route3_aux`, `hsubstNW_of_hsubstPi`, `hsubstPi_of_hsubstSort`,
  `hsubstSort_of_sortFundamental`, `normalizeNW_of_hsubst`, `productNormalizationR_of_hsubst`;
* **`expansionPostponement_of_sortFundamental`**: for every strongly normalizing `P`,
  `SortFundamental P → ExpansionPostponement P`.

So for a specification with a morphism into coc only route (ii) itself remains
(`PTSExpansionCoCMorphism.lean`).
-/

set_option autoImplicit false

namespace PureTypeSystem

namespace SNGeneric

variable {S : Type} {P : Specification S}

/-- The judgement `Γ ⊢ M : T` normalizes to a canonical judgement (any sort type). -/
def NormNW (P : Specification S) (Γ : List (Expr S)) (M T : Expr S) : Prop :=
  ∃ Γ' M' T', List.Forall₂ Reduces Γ Γ' ∧ Reduces M M' ∧ Reduces T T' ∧ HasTypeNW P Γ' M' T'

/-- The sort-typed fundamental lemma for a single substitution (any sort type). -/
def SortFundamental (P : Specification S) : Prop :=
  ∀ {Γ : List (Expr S)} {N A : Expr S} {Δ Δ' : List (Expr S)} {M : Expr S} {s : S},
    HasTypeNW P Γ N A → CtxSubstRed N Δ Δ' → ValidContextNW P (Δ' ++ Γ) →
    HasTypeNW P (Δ ++ A :: Γ) M (.sort s) →
    NormNW P (Δ' ++ Γ) (M.subst (Expr.substAt N Δ.length)) (.sort s)

/-- Hereditary substitution into sort-typed premises (any sort type). -/
def HSubstSort (P : Specification S) : Prop :=
  ∀ {Γ : List (Expr S)} {N A : Expr S} {Δ Δ' : List (Expr S)} {M : Expr S} {s : S},
    HasTypeNW P Γ N A → CtxSubstRed N Δ Δ' → ValidContextNW P (Δ' ++ Γ) →
    HasTypeNW P (Δ ++ A :: Γ) M (.sort s) →
    ∃ M', Reduces (M.subst (Expr.substAt N Δ.length)) M' ∧ HasTypeNW P (Δ' ++ Γ) M' (.sort s)

/-- Hereditary substitution into product premises (any sort type). -/
def HSubstPi (P : Specification S) : Prop :=
  ∀ {Γ : List (Expr S)} {N A : Expr S} {Δ Δ' : List (Expr S)} {C E : Expr S} {s : S},
    HasTypeNW P Γ N A → CtxSubstRed N Δ Δ' → ValidContextNW P (Δ' ++ Γ) →
    HasTypeNW P (Δ ++ A :: Γ) (.pi C E) (.sort s) →
    ∃ C' E', Reduces (C.subst (Expr.substAt N Δ.length)) C' ∧
      Reduces (E.subst (Expr.substAt N (Δ.length + 1))) E' ∧
      HasTypeNW P (Δ' ++ Γ) (.pi C' E') (.sort s)

/-- Hereditary substitution on canonical derivations (any sort type). -/
def HSubstNW (P : Specification S) : Prop :=
  ∀ {Γ : List (Expr S)} {N A M B : Expr S}, HasTypeNW P Γ N A → HasTypeNW P (A :: Γ) M B →
    ∃ M' B', Reduces (M.instantiate N) M' ∧ Reduces (B.instantiate N) B' ∧ HasTypeNW P Γ M' B'

/-- At the cube's sort type the generic definition is the round-11 one. -/
theorem sortFundamental_iff (Q : Specification LambdaPi.Srt) :
    SortFundamental Q ↔ RouteII.SortFundamental Q := Iff.rfl

theorem forall₂_reduces_refl' : ∀ Γ : List (Expr S), List.Forall₂ Reduces Γ Γ
  | [] => .nil
  | _ :: Γ => .cons .refl (forall₂_reduces_refl' Γ)

/-- The entries of a canonically valid context are normal (any sort type). -/
theorem normal_entries' {Γ : List (Expr S)} (h : ValidContextNW P Γ) : ∀ X ∈ Γ, Normal X := by
  induction h with
  | nil => simp
  | cons _ hA ih =>
      intro X hX
      rcases List.mem_cons.1 hX with rfl | hX
      · exact hA.normal.1
      · exact ih X hX

theorem hsubstSort_of_sortFundamental (h : SortFundamental P) : HSubstSort P := by
  intro Γ N A Δ Δ' M s hN hc hv hM
  obtain ⟨Γ'', M', T', hc', hM', hT', hNW⟩ := h hN hc hv hM
  rw [Reduces.sort_eq hT'] at hNW
  obtain rfl := forall₂_reduces_unique hc' (forall₂_reduces_refl' _) hNW.normal.2.2
    (normal_entries' hv)
  exact ⟨M', hM', hNW⟩

theorem hsubstPi_of_hsubstSort (h : HSubstSort P) : HSubstPi P := by
  intro Γ N A Δ Δ' C E s hN hc hv hP
  obtain ⟨M', hr, hM'⟩ := h hN hc hv hP
  simp only [Expr.subst] at hr
  obtain ⟨C', E', rfl, hC, hE⟩ := Reduces.pi_inv hr
  refine ⟨C', E', hC, ?_, hM'⟩
  first | exact hE | (rw [Expr.substAt_succ]; exact hE)

theorem hsubst_route3_aux (hsn : SystemStronglyNormalizing P) (hpi : HSubstPi P) (root : Expr S)
    (hacc : Acc (Relation.TransGen Expr.DescStep) root) :
    ∀ {Γ : List (Expr S)} {N A : Expr S} {Θ : List (Expr S)} {M B : Expr S},
      HasTypeNW (P) Γ N A → HasTypeNW (P) Θ M B →
      ∀ Δ Δ' : List (Expr S), Θ = Δ ++ A :: Γ → CtxSubstRed N Δ Δ' →
      ValidContextNW (P) (Δ' ++ Γ) →
      Expr.Below (M.subst (Expr.substAt N Δ.length)) root →
      ∃ M' B', Reduces (M.subst (Expr.substAt N Δ.length)) M' ∧
        Reduces (B.subst (Expr.substAt N Δ.length)) B' ∧
        HasTypeNW (P) (Δ' ++ Γ) M' B' := by
  have hw : SystemWeaklyNormalizing (P) := fun Γ hΓ M hM =>
    weaklyNormalizing_of_stronglyNormalizing (hsn Γ hΓ M hM)
  induction hacc with
  | intro root _ IHo =>
  intro Γ N A Θ M B hN h
  have ctxn : ∀ {Δ' : List (Expr S)} {M' B' : Expr S},
      HasTypeNW (P) (Δ' ++ Γ) M' B' → ∀ X ∈ Δ', Normal X :=
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
        have hT : HasType (P) (Δ' ++ Γ) (.app F' a') (B₁.instantiate a') :=
          .application hF'.toHasType ha'.toHasType
        obtain ⟨B'', hred, hnorm⟩ := hw _ hT.valid _ ⟨_, .inr hT⟩
        refine ⟨.app F' a', B'', ?_, ?_, .application hF' ha' hred hnorm happ'⟩
        · simp only [Expr.subst]
          exact Reduces.app hFr har
        · exact Reduces.to_normal hB₀σ (hTy.trans hred) hnorm


theorem hsubstNW_of_hsubstPi (hsn : SystemStronglyNormalizing P) (hpi : HSubstPi P) :
    HSubstNW P := by
  intro Γ N A M B hN hM
  have hT : HasType P Γ (M.instantiate N) (B.instantiate N) := by
    exact hM.toHasType.instantiate hN.toHasType
  have hsn' : StronglyNormalizing (M.instantiate N) := hsn Γ hT.valid _ ⟨_, .inl hT⟩
  have hb : Expr.Below (M.subst (Expr.substAt N ([] : List (Expr S)).length))
      (M.instantiate N) := ⟨id, by rw [Expr.rename_id]; exact .refl⟩
  obtain ⟨M', B', h1, h2, h3⟩ :=
    hsubst_route3_aux hsn hpi _ (Expr.acc_desc_of_sn hsn') hN hM ([]) ([]) rfl .nil hN.valid hb
  exact ⟨M', B', h1, h2, h3⟩

theorem normalizeNW_of_hsubst (hsn : SystemStronglyNormalizing P) (hs : HSubstNW P)
    {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeR (P) Γ M T) :
    ∃ Γ' M' T', List.Forall₂ Reduces Γ Γ' ∧ Reduces M M' ∧ Reduces T T' ∧
      HasTypeNW (P) Γ' M' T' := by
  have hw : SystemWeaklyNormalizing (P) := fun Γ hΓ M hM =>
    weaklyNormalizing_of_stronglyNormalizing (hsn Γ hΓ M hM)
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
            HasTypeNW (P) Γ₂ e' E' := hs ha' he
        obtain ⟨e', E', her, hEr, he'⟩ := hsub
        exact ⟨_, e', E', hc₂,
          ((Reduces.app hfr har).tail (Beta.head _ e a')).trans her, hTy.trans hEr, he'⟩
      · simp only [not_exists] at hlam
        have happ' : Normal (.app f' a') := Normal.app_of hf'.normal.1 ha'.normal.1 hlam
        have hT : HasType (P) Γ₂ (.app f' a') (B₁.instantiate a') :=
          .application hf'.toHasType ha'.toHasType
        obtain ⟨B'', hred, hnorm⟩ := hw _ hT.valid _ ⟨_, .inr hT⟩
        exact ⟨_, _, B'', hc₂, Reduces.app hfr har, hTy.trans hred,
          .application hf' ha' hred hnorm happ'⟩
  | reduction _ hAB ih =>
      obtain ⟨Γ', M', A', hc, hMr, hAr, hM'⟩ := ih
      exact ⟨Γ', M', A', hc, hMr,
        Reduces.to_normal (Relation.ReflTransGen.single hAB) hAr hM'.normal.2.1, hM'⟩

theorem productNormalizationR_of_hsubst (hsn : SystemStronglyNormalizing P) (hs : HSubstNW P) :
    ProductNormalizationR (P) := by
  intro Γ A B B' s hP hBB' hB'n
  obtain ⟨s₁, s₂, s₃, hA, hB, hr, hs'⟩ := hP.generation_pi A B rfl
  obtain ⟨Γ', M', T', hc, hM, hT, hNW⟩ := normalizeNW_of_hsubst hsn hs hB
  rw [Reduces.sort_eq hT] at hNW
  obtain rfl := Reduces.normal_unique hM hBB' hNW.normal.1 hB'n
  have hB' := hNW.toHasTypeR.ctx_expand (A :: Γ) hB.valid hc
  cases hs'
  exact .product hA hB' hr


/-! ### The base predicate of route (ii), over any sort type -/


theorem app_type_exists (hsn : SystemStronglyNormalizing P) {Γ : List (Expr S)} {F a A B : Expr S}
    (hF : HasTypeNW P Γ F (.pi A B)) (ha : HasTypeNW P Γ a A) :
    ∃ B', Reduces (B.instantiate a) B' ∧ Normal B' := by
  have hT : HasType P Γ (.app F a) (B.instantiate a) := .application hF.toHasType ha.toHasType
  exact weaklyNormalizing_of_stronglyNormalizing (hsn Γ hT.valid _ ⟨_, .inr hT⟩)

/-- Normalizability is invariant under reduction of the type (the canonical type is normal). -/
theorem NormNW.reduceType {Γ : List (Expr S)} {M T T₂ : Expr S}
    (h : NormNW P Γ M T) (hr : Reduces T T₂) : NormNW P Γ M T₂ := by
  obtain ⟨Γ', M', T', hc, hM, hT, hNW⟩ := h
  exact ⟨Γ', M', T', hc, hM, Reduces.to_normal hr hT hNW.normal.2.1, hNW⟩

theorem normal_pi_inv' {C E : Expr S} (h : Normal (.pi C E)) : Normal C ∧ Normal E :=
  ⟨fun _ hb => h _ (.pi_domain hb), fun _ hb => h _ (.pi_body hb)⟩


/-- **The abstraction case of the fundamental lemma, at the base predicate, with the product
premise handled by the predicate on the product's own derivation**: if the body and the product
normalize, so does the abstraction. -/
theorem NormNW.abstraction {Γ : List (Expr S)} {C E b : Expr S}
    {s : S} (hb : NormNW P (C :: Γ) b E) (hp : NormNW P Γ (.pi C E) (.sort s)) :
    NormNW P Γ (.lam C b) (.pi C E) := by
  obtain ⟨Γ₁, M₁, T₁, hc₁, hM₁, hT₁, hNW₁⟩ := hp
  rw [Reduces.sort_eq hT₁] at hNW₁
  obtain ⟨C', E', rfl, hC, hE⟩ := Reduces.pi_inv hM₁
  obtain ⟨Γ₂, b', E'', hc₂, hb', hE'', hNW₂⟩ := hb
  have hnP := normal_pi_inv' hNW₁.normal.1
  have hE_eq : E'' = E' :=
    (hNW₂.normal.2.1.reduces_eq (Reduces.to_normal hE'' hE hnP.2)).symm ▸ rfl
  have hΓ : Γ₂ = C' :: Γ₁ := by
    refine forall₂_reduces_unique hc₂ (.cons hC hc₁) hNW₂.normal.2.2 ?_
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact hnP.1
    · exact hNW₁.normal.2.2 X hX
  subst hE_eq hΓ
  exact ⟨Γ₁, .lam C' b', .pi C' E'', hc₁, Reduces.lam hC hb', Reduces.pi hC hE,
    .abstraction hNW₂ hNW₁⟩

/-- The product case of the fundamental lemma, at the base predicate. -/
theorem NormNW.product {Γ : List (Expr S)} {A B : Expr S}
    {s₁ s₂ s₃ : S} (hA : NormNW P Γ A (.sort s₁)) (hB : NormNW P (A :: Γ) B (.sort s₂))
    (hr : P.rule s₁ s₂ s₃) : NormNW P Γ (.pi A B) (.sort s₃) := by
  obtain ⟨Γ₁, A', T₁, hc₁, hA', hT₁, hNW₁⟩ := hA
  rw [Reduces.sort_eq hT₁] at hNW₁
  obtain ⟨Γ₂, B', T₂, hc₂, hB', hT₂, hNW₂⟩ := hB
  rw [Reduces.sort_eq hT₂] at hNW₂
  have hΓ : Γ₂ = A' :: Γ₁ := by
    refine forall₂_reduces_unique hc₂ (.cons hA' hc₁) hNW₂.normal.2.2 ?_
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact hNW₁.normal.1
    · exact hNW₁.normal.2.2 X hX
  subst hΓ
  exact ⟨Γ₁, .pi A' B', _, hc₁, Reduces.pi hA' hB', .refl, .product hNW₁ hNW₂ hr⟩


/-- **CR3, head-expansion form, for the base predicate**: normalizability of a judgement is
closed under expansion of the subject. -/
theorem NormNW.expand {Γ : List (Expr S)} {M M' T : Expr S}
    (hr : Reduces M M') (h : NormNW P Γ M' T) : NormNW P Γ M T := by
  obtain ⟨Γ', M'', T', hc, hM, hT, hNW⟩ := h
  exact ⟨Γ', M'', T', hc, hr.trans hM, hT, hNW⟩


/-- The judgement `Γ ⊢ M : T` normalizes to a canonical judgement with a neutral subject. -/
def NeNW (P : Specification S) (Γ : List (Expr S)) (M T : Expr S) : Prop :=
  ∃ Γ' M' T', List.Forall₂ Reduces Γ Γ' ∧ Reduces M M' ∧ Reduces T T' ∧
    HasTypeNW P Γ' M' T' ∧ Neutral M'

theorem NeNW.toNormNW {Γ : List (Expr S)} {M T : Expr S}
    (h : NeNW P Γ M T) : NormNW P Γ M T := by
  obtain ⟨Γ', M', T', hc, hM, hT, hNW, -⟩ := h
  exact ⟨Γ', M', T', hc, hM, hT, hNW⟩

/-- A variable which normalizes is a neutral which normalizes. -/
theorem NeNW.of_var {Γ : List (Expr S)} {x : ℕ} {T : Expr S}
    (h : NormNW P Γ (.var x) T) : NeNW P Γ (.var x) T := by
  obtain ⟨Γ', M', T', hc, hM, hT, hNW⟩ := h
  have hv : M' = .var x := ((Normal.var x).reduces_eq hM).symm
  subst hv
  exact ⟨Γ', _, T', hc, hM, hT, hNW, .var x⟩

/-- A neutral is never an abstraction. -/
theorem neutral_not_lam' {M : Expr S} (h : Neutral M) (A b : Expr S) : M ≠ .lam A b := by
  cases h <;> intro heq <;> cases heq

/-- A normal neutral applied to a normal argument is normal. -/
theorem normal_app_of_neutral' {F a : Expr S} (hF : Neutral F) (hFn : Normal F)
    (ha : Normal a) : Normal (.app F a) := by
  intro N hb
  cases hb with
  | head A b a => exact neutral_not_lam' hF A b rfl
  | app_left h => exact hFn _ h
  | app_right h => exact ha _ h

/-- **CR3 at neutral applications**, in every corner of the cube.  Only strong normalization
(for the normal form of `B[N]`) and uniqueness of normal forms are used; no canonical
derivation of the instantiated codomain is needed, because the application rule of
`HasTypeNW` does not ask for one. -/
theorem NeNW.app (hsn : SystemStronglyNormalizing P) {Γ : List (Expr S)} {F N A B : Expr S}
    (hF : NeNW (P) Γ F (.pi A B)) (hN : NormNW (P) Γ N A) :
    NeNW (P) Γ (.app F N) (B.instantiate N) := by
  obtain ⟨Γ₁, F', T₁, hc₁, hF', hT₁, hNW₁, hne⟩ := hF
  obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Reduces.pi_inv hT₁
  obtain ⟨Γ₂, N', A₂, hc₂, hN', hA₂, hNW₂⟩ := hN
  have hΓ : Γ₂ = Γ₁ :=
    forall₂_reduces_unique hc₂ hc₁ hNW₂.normal.2.2 hNW₁.normal.2.2
  subst hΓ
  have hnP := normal_pi_inv' hNW₁.normal.2.1
  have hA : A₂ = A₁ := Reduces.normal_unique hA₂ hA₁ hNW₂.normal.2.1 hnP.1
  subst hA
  obtain ⟨B', hB', hB'n⟩ := app_type_exists hsn hNW₁ hNW₂
  refine ⟨Γ₂, .app F' N', B', hc₂, Reduces.app hF' hN',
    (Reduces.instantiate hB₁ hN').trans hB', ?_, .app hne⟩
  exact .application hNW₁ hNW₂ hB' hB'n
    (normal_app_of_neutral' hne hNW₁.normal.1 hNW₂.normal.1)


/-- The base predicate is closed under conversion of the type. -/
theorem NormNW.convType {Γ : List (Expr S)} {M T T₂ : Expr S}
    (h : NormNW P Γ M T) (hc : Converts T T₂) : NormNW P Γ M T₂ := by
  obtain ⟨Γ', M', T', hcx, hM, hT, hNW⟩ := h
  obtain ⟨J, hTJ, hT₂J⟩ := Converts.join hc
  obtain ⟨K, hT'K, hJK⟩ := Reduces.confluent hT hTJ
  have hK : T' = K := hNW.normal.2.1.reduces_eq hT'K
  subst hK
  exact ⟨Γ', M', T', hcx, hM, hT₂J.trans hJK, hNW⟩

theorem NeNW.convType {Γ : List (Expr S)} {M T T₂ : Expr S}
    (h : NeNW P Γ M T) (hc : Converts T T₂) : NeNW P Γ M T₂ := by
  obtain ⟨Γ', M', T', hcx, hM, hT, hNW, hne⟩ := h
  obtain ⟨Γ'', M'', T'', h1, h2, h3, h4⟩ :=
    NormNW.convType (P := P) ⟨Γ', M', T', hcx, hM, hT, hNW⟩ hc
  have hM'' : M' = M'' := Reduces.normal_unique hM h2 hNW.normal.1 h4.normal.1
  subst hM''
  exact ⟨Γ'', M', T'', h1, h2, h3, h4, hne⟩


/-- The weakening renaming along a prefix (any sort type). -/
def wk (Γ₀ : List (Expr S)) : ℕ → ℕ := fun n => n + Γ₀.length

theorem neutral_rename' {M : Expr S} (h : Neutral M) (ρ : ℕ → ℕ) : Neutral (M.rename ρ) := by
  induction h with
  | var n => exact .var _
  | app _ ih => exact .app ih

theorem wk_nil' : wk ([] : List (Expr S)) = id := by funext n; simp [wk]

/-- The weakening renaming along a prefix is a declaration renaming. -/
theorem declRenaming_wk' (Γ : List (Expr S)) :
    ∀ (Γ₀ : List (Expr S)), TypingTree.DeclRenaming Γ (Γ₀ ++ Γ) (wk Γ₀)
  | [] => by
      intro n A hn
      rw [wk_nil', Expr.rename_id]
      exact hn
  | B :: Γ₀ => by
      intro n A hn
      have h := Lookup.succ B (declRenaming_wk' Γ Γ₀ n A hn)
      have he : wk (B :: Γ₀) = Nat.succ ∘ wk Γ₀ := by
        funext n; simp [wk, Function.comp]; omega
      rw [Expr.rename_comp, ← he] at h
      have hn' : wk Γ₀ n + 1 = wk (B :: Γ₀) n := by simp [wk]; omega
      rw [hn'] at h
      exact h

/-- Splitting a pointwise reduction of an appended context. -/
theorem forall₂_reduces_append_split' :
    ∀ (Γ₀ Γ Δ : List (Expr S)), List.Forall₂ Reduces (Γ₀ ++ Γ) Δ →
      ∃ Γ₀' Γ', Δ = Γ₀' ++ Γ' ∧ Γ₀'.length = Γ₀.length ∧ List.Forall₂ Reduces Γ Γ'
  | [], _, Δ, h => ⟨[], Δ, rfl, rfl, h⟩
  | _ :: Γ₀, Γ, _, h => by
      cases h with
      | @cons _ A' _ Δ' _ h =>
          obtain ⟨Γ₀', Γ', rfl, hl, h'⟩ := forall₂_reduces_append_split' Γ₀ Γ Δ' h
          exact ⟨A' :: Γ₀', Γ', rfl, by simp [hl], h'⟩

/-- **Weakening of neutral normalization** along a context prefix whose extension normalizes to
a canonical context. -/
theorem NeNW.weaken {Γ : List (Expr S)} {F T : Expr S}
    (h : NeNW P Γ F T) (Γ₀ : List (Expr S)) {Δ : List (Expr S)}
    (hc : List.Forall₂ Reduces (Γ₀ ++ Γ) Δ) (hv : ValidContextNW P Δ) :
    NeNW P (Γ₀ ++ Γ) (F.rename (wk Γ₀)) (T.rename (wk Γ₀)) := by
  obtain ⟨Γ', F', T', hc', hF, hT, hNW, hne⟩ := h
  obtain ⟨Γ₀', Γ₃, rfl, hl, h₃⟩ := forall₂_reduces_append_split' Γ₀ Γ Δ hc
  have hΓ : Γ₃ = Γ' := forall₂_reduces_unique h₃ hc'
    (fun X hX => normal_entries' hv X (List.mem_append_right _ hX)) hNW.normal.2.2
  subst hΓ
  have hwk : wk Γ₀ = wk Γ₀' := by funext n; simp [wk, hl]
  refine ⟨Γ₀' ++ Γ₃, F'.rename (wk Γ₀), T'.rename (wk Γ₀), hc, hF.rename _, hT.rename _, ?_,
    neutral_rename' hne _⟩
  rw [hwk]
  exact hNW.rename hv _ (declRenaming_wk' Γ₃ Γ₀')

/-- **CR3 at neutral applications in a context extension** (the Kripke form used by the
reflection lemmas). -/
theorem NeNW.app_wk (hsn : SystemStronglyNormalizing P) {Γ : List (Expr S)} {F T N A B : Expr S}
    (hF : NeNW (P) Γ F T) (Γ₀ : List (Expr S))
    (hT : Reduces (T.rename (wk Γ₀)) (.pi A B)) (hN : NormNW (P) (Γ₀ ++ Γ) N A) :
    NeNW (P) (Γ₀ ++ Γ) (.app (F.rename (wk Γ₀)) N) (B.instantiate N) := by
  obtain ⟨Δ, N', A', hc, hN', hA', hNW⟩ := hN
  have hw := hF.weaken Γ₀ hc hNW.valid
  exact NeNW.app hsn (hw.convType (Reduces.converts hT)) ⟨Δ, N', A', hc, hN', hA', hNW⟩

/-! ### The two-level relation: candidates with CR3, and type reducibility -/

/-- **Weakening of normalization** along a context prefix whose extension normalizes to a
canonical context (round 10). -/
theorem NormNW.weaken {Γ : List (Expr S)} {F T : Expr S}
    (h : NormNW P Γ F T) (Γ₀ : List (Expr S)) {Δ : List (Expr S)}
    (hc : List.Forall₂ Reduces (Γ₀ ++ Γ) Δ) (hv : ValidContextNW P Δ) :
    NormNW P (Γ₀ ++ Γ) (F.rename (wk Γ₀)) (T.rename (wk Γ₀)) := by
  obtain ⟨Γ', F', T', hc', hF, hT, hNW⟩ := h
  obtain ⟨Γ₀', Γ₃, rfl, hl, h₃⟩ := forall₂_reduces_append_split' Γ₀ Γ Δ hc
  have hΓ : Γ₃ = Γ' := forall₂_reduces_unique h₃ hc'
    (fun X hX => normal_entries' hv X (List.mem_append_right _ hX)) hNW.normal.2.2
  subst hΓ
  have hwk : wk Γ₀ = wk Γ₀' := by funext n; simp [wk, hl]
  refine ⟨Γ₀' ++ Γ₃, F'.rename (wk Γ₀), T'.rename (wk Γ₀), hc, hF.rename _, hT.rename _, ?_⟩
  rw [hwk]
  exact hNW.rename hv _ (declRenaming_wk' Γ₃ Γ₀')

/-- Composition of two weakening renamings (round 10). -/
theorem rename_wk_wk' (X : Expr S) (Γ₀ Γ₁ : List (Expr S)) :
    (X.rename (wk Γ₀)).rename (wk Γ₁) = X.rename (wk (Γ₁ ++ Γ₀)) := by
  rw [Expr.rename_comp]
  congr 1
  funext n
  simp only [wk, Function.comp, List.length_append]
  omega


/-- **Expansion postponement from the sort-typed fundamental lemma**, for every strongly
normalizing specification over any sort type. -/
theorem expansionPostponement_of_sortFundamental (hsn : SystemStronglyNormalizing P)
    (h : SortFundamental P) : ExpansionPostponement P :=
  expansionPostponement_of_productNormalizationR_sn hsn
    (productNormalizationR_of_hsubst hsn
      (hsubstNW_of_hsubstPi hsn (hsubstPi_of_hsubstSort (hsubstSort_of_sortFundamental h))))

/-- Sanity check: the generic chain re-derives expansion postponement for coc from the round-11
fundamental lemma. -/
theorem coc_expansionPostponement' : ExpansionPostponement (cubeSpec coc) :=
  expansionPostponement_of_sortFundamental (cube_stronglyNormalizing coc)
    RouteIICoC.sortFundamental_coc

end SNGeneric

end PureTypeSystem
