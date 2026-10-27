/-
**Martin-Löf type theory: the fundamental theorem, dependent products (formation)** —
milestone M30 (`M30-MLTT-FUND`).

* `TyR.pi_inv` — inversion of a reducible product type: its families and its interpretation;
* `PiTm.intro` — a pair of terms of a reducible product is related as soon as their weak head
  normal forms are related at every pair of related arguments (the generic equality of the
  normal forms follows by the extensionality rule `GenEq.eta`);
* `valid_piT` — **validity of `Π`** as a type, by the reducibility of the products of valid
  domains and codomains at every related substitution.
-/

import Start.MLTTFundBasic

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

variable {E : GenEq}

/-! ### Inversion -/

/-- The data of a reducible product. -/
structure PiData (E : GenEq) (l : ℕ) (Δ : Ctx) (F G : Tm) (I : Interp) : Prop where
  intro ::
  fam : ∃ (IF : Ctx → (ℕ → ℕ) → Interp) (IG : Ctx → (ℕ → ℕ) → Tm → Interp),
    WfTy Δ F ∧ WfTy (F :: Δ) G ∧ E.ty Δ (pi F G) (pi F G) ∧
    (∀ Δ' ρ, Wk Δ Δ' ρ → TyR E l Δ' (rename ρ F) (IF Δ' ρ)) ∧
    (∀ Δ' ρ a, Wk Δ Δ' ρ → (IF Δ' ρ).tmEq a a →
      TyR E l Δ' ((rename (upr ρ) G)[a]) (IG Δ' ρ a)) ∧
    (∀ Δ' ρ a b, Wk Δ Δ' ρ → (IF Δ' ρ).tmEq a a → (IF Δ' ρ).tmEq b b → (IF Δ' ρ).tmEq a b →
      (IG Δ' ρ a).tyEq ((rename (upr ρ) G)[b])) ∧
    (∀ B, I.tyEq B ↔ ∃ F' G', TyRedsT Δ B (pi F' G') ∧ E.ty Δ (pi F G) (pi F' G') ∧
      (∀ Δ' ρ, Wk Δ Δ' ρ → (IF Δ' ρ).tyEq (rename ρ F')) ∧
      (∀ Δ' ρ a, Wk Δ Δ' ρ → (IF Δ' ρ).tmEq a a →
        (IG Δ' ρ a).tyEq ((rename (upr ρ) G')[a]))) ∧
    (∀ t u, I.tmEq t u ↔ ∃ f g, TRedsT Δ t f (pi F G) ∧ TRedsT Δ u g (pi F G) ∧
      Whnf f ∧ Whnf g ∧ E.tm Δ f g (pi F G) ∧
      (∀ Δ' ρ a b, Wk Δ Δ' ρ → (IF Δ' ρ).tmEq a b →
        (IG Δ' ρ a).tmEq (app (rename ρ f) a) (app (rename ρ g) b)))

/-- **Inversion of a reducible product.** -/
theorem TyR.pi_inv {l : ℕ} {Δ : Ctx} {F G : Tm} {I : Interp} (h : TyR E l Δ (pi F G) I) :
    PiData E l Δ F G I := by
  rw [TyR.unfold] at h
  cases h with
  | univ hl D => exact absurd (D.red.of_whnf (Whnf.pi _ _)) (by simp)
  | nat D => exact absurd (D.red.of_whnf (Whnf.pi _ _)) (by simp)
  | empty D => exact absurd (D.red.of_whnf (Whnf.pi _ _)) (by simp)
  | ne D hN _ =>
      have e := D.red.of_whnf (Whnf.pi _ _)
      rw [e] at hN; cases hN
  | pi IF IG D hF hG hPi rF rG extG =>
      have e := D.red.of_whnf (Whnf.pi _ _)
      simp only [pi.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨IF, IG, hF, hG, hPi, fun Δ' ρ hρ => (rF Δ' ρ hρ).toTyR,
        fun Δ' ρ a hρ ha => (rG Δ' ρ a hρ ha).toTyR, extG, fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-! ### Related functions -/

/-- **Two functions are related when their normal forms are related at related arguments.** -/
theorem PiTm.intro {l : ℕ} {Δ : Ctx} {F G : Tm} {I : Interp} (h : TyR E l Δ (pi F G) I)
    {t u f g : Tm} (ht : TRedsT Δ t f (pi F G)) (hu : TRedsT Δ u g (pi F G)) (hf : Whnf f)
    (hg : Whnf g)
    (happ : ∀ (IF : Ctx → (ℕ → ℕ) → Interp) (IG : Ctx → (ℕ → ℕ) → Tm → Interp),
      (∀ Δ' ρ, Wk Δ Δ' ρ → TyR E l Δ' (rename ρ F) (IF Δ' ρ)) →
      (∀ Δ' ρ a, Wk Δ Δ' ρ → (IF Δ' ρ).tmEq a a →
        TyR E l Δ' ((rename (upr ρ) G)[a]) (IG Δ' ρ a)) →
      ∀ Δ' ρ a b, Wk Δ Δ' ρ → (IF Δ' ρ).tmEq a b →
        (IG Δ' ρ a).tmEq (app (rename ρ f) a) (app (rename ρ g) b)) :
    I.tmEq t u := by
  obtain ⟨IF, IG, hF, hG, hPi, rF, rG, extG, -, htm⟩ := h.pi_inv
  have happ' := happ IF IG rF rG
  refine (htm t u).mpr ⟨f, g, ht, hu, hf, hg, ?_, happ'⟩
  -- the generic equality of the normal forms, by extensionality
  have hFΔ : WfCtx (F :: Δ) := Der.cons ht.tyL.wf hF
  have hρ : Wk Δ (F :: Δ) Nat.succ := ⟨RenOk.shift Δ F, hFΔ⟩
  have hv : (IF (F :: Δ) Nat.succ).tmEq (var 0) (var 0) :=
    (rF _ _ hρ).var (Der.var hFΔ (Lookup.zero Δ F))
  have hrel := happ' _ _ (var 0) (var 0) hρ hv
  have hGv := rG _ _ (var 0) hρ ((TyR.good l (rF _ _ hρ)).left hv)
  obtain ⟨-, -, hE⟩ := hGv.escapeTm hrel
  rw [shift_inst_rename] at hE
  exact E.eta hF ht.tyR hu.tyR hf hg hE

/-! ### Validity of `Π` as a type -/

/-- The reducible product of a valid domain and codomain at a substitution related to itself,
and its reducible equality to the product at a related substitution. -/
theorem valid_piT_at {Γ : Ctx} {F G : Tm} (hΓ : ValidCtx E Γ) {i j : ℕ}
    (hFi : ∀ Δ σ σ', SubstR E Γ Δ σ σ' → ∃ I, TyR E i Δ (subst σ F) I ∧ I.tyEq (subst σ' F))
    (hGj : ∀ Δ σ σ', SubstR E (F :: Γ) Δ σ σ' →
      ∃ I, TyR E j Δ (subst σ G) I ∧ I.tyEq (subst σ' G))
    {Δ : Ctx} {σ σ' : ℕ → Tm} (hs : SubstR E Γ Δ σ σ') :
    ∃ I, TyR E (max i j) Δ (subst σ (pi F G)) I ∧ I.tyEq (subst σ' (pi F G)) := by
  have hF : ValidTy E Γ F := ⟨i, hFi⟩
  have hσ := hs.left hΓ
  have hσ' := hs.right hΓ
  have hΔ := hs.wfCtx
  set L := max i j
  set F₁ := subst σ F
  set G₁ := subst (up σ) G
  let IF : Ctx → (ℕ → ℕ) → Interp := fun Δ' ρ => TyInterp E L Δ' (rename ρ F₁)
  let IG : Ctx → (ℕ → ℕ) → Tm → Interp := fun Δ' ρ a =>
    TyInterp E L Δ' ((rename (upr ρ) G₁)[a])
  have eF : ∀ ρ : ℕ → ℕ, rename ρ F₁ = subst (fun n => rename ρ (σ n)) F := fun ρ =>
    rename_subst ρ σ F
  have eG : ∀ (ρ : ℕ → ℕ) (a : Tm),
      (rename (upr ρ) G₁)[a] = subst (scons a (fun n => rename ρ (σ n))) G := fun ρ a =>
    rename_subst_up_inst ρ σ a G
  -- the domain
  have rF : ∀ Δ' ρ, Wk Δ Δ' ρ → TyR E L Δ' (rename ρ F₁) (IF Δ' ρ) := by
    intro Δ' ρ hρ
    obtain ⟨I, hI, -⟩ := hFi Δ' _ _ (hσ.wk hρ)
    have hI' := TyInterp.spec ((eF ρ) ▸ (hI.lift (le_max_left i j)))
    exact hI'
  -- extending the substitution by related arguments
  have hcons : ∀ Δ' ρ a b, Wk Δ Δ' ρ → (IF Δ' ρ).tmEq a b →
      SubstR E (F :: Γ) Δ' (scons a (fun n => rename ρ (σ n))) (scons b (fun n => rename ρ (σ n))) := by
    intro Δ' ρ a b hρ hab
    refine ⟨hσ.wk hρ, L, IF Δ' ρ, ?_, hab⟩
    have := rF Δ' ρ hρ
    rw [eF ρ] at this
    exact this
  -- the codomain
  have rG : ∀ Δ' ρ a, Wk Δ Δ' ρ → (IF Δ' ρ).tmEq a a →
      TyR E L Δ' ((rename (upr ρ) G₁)[a]) (IG Δ' ρ a) := by
    intro Δ' ρ a hρ ha
    obtain ⟨I, hI, -⟩ := hGj Δ' _ _ (hcons Δ' ρ a a hρ ha)
    exact TyInterp.spec ((eG ρ a) ▸ (hI.lift (le_max_right i j)))
  have extG : ∀ Δ' ρ a b, Wk Δ Δ' ρ → (IF Δ' ρ).tmEq a a → (IF Δ' ρ).tmEq b b →
      (IF Δ' ρ).tmEq a b → (IG Δ' ρ a).tyEq ((rename (upr ρ) G₁)[b]) := by
    intro Δ' ρ a b hρ ha _ hab
    obtain ⟨I, hI, hIb⟩ := hGj Δ' _ _ (hcons Δ' ρ a b hρ hab)
    have hIG := rG Δ' ρ a hρ ha
    rw [eG ρ a] at hIG
    rw [eG ρ b]
    exact ((TyR.irrel (hI.lift (le_max_right i j)) hIG).1 _).mp hIb
  -- well-formedness and the generic reflexivity of the product
  obtain ⟨IF₀, hIF₀, hIF₀eq⟩ := hFi Δ σ σ' hs
  have hF₁ : WfTy Δ F₁ := hIF₀.wfTy
  have hΔF : WfCtx (F₁ :: Δ) := Der.cons hΔ hF₁
  have hup := SubstR.up hΓ hF hσ hΔF
  have hup' := SubstR.up hΓ hF hs hΔF
  obtain ⟨IG₀, hIG₀, hIG₀eq⟩ := hGj _ _ _ hup'
  have hG₁ : WfTy (F₁ :: Δ) G₁ := hIG₀.wfTy
  have hFF : E.ty Δ F₁ F₁ := hIF₀.escapeTyEq hIF₀.refl
  have hGG : E.ty (F₁ :: Δ) G₁ G₁ := hIG₀.escapeTyEq hIG₀.refl
  have hPi : E.ty Δ (pi F₁ G₁) (pi F₁ G₁) := E.pi_cong hF₁ hFF hGG
  have hR := (TyRAt.pi (E := E) (l := L) (lo := fun l' _ => TyR E l') IF IG
    (TyRedsT.refl (Der.piT hF₁ hG₁)) hF₁ hG₁ hPi
    (fun Δ' ρ hρ => by have := rF Δ' ρ hρ; rw [TyR.unfold] at this; exact this)
    (fun Δ' ρ a hρ ha => by have := rG Δ' ρ a hρ ha; rw [TyR.unfold] at this; exact this)
    extG).toTyR
  refine ⟨_, hR, ?_⟩
  -- the product at `σ'`
  obtain ⟨IF₁, hIF₁, -⟩ := hFi Δ σ' σ' hσ'
  have hF₂ : WfTy Δ (subst σ' F) := hIF₁.wfTy
  have hup₂ := SubstR.up hΓ hF hσ' (Der.cons hΔ hF₂)
  obtain ⟨IG₁, hIG₁, -⟩ := hGj _ _ _ hup₂
  have hG₂ : WfTy (subst σ' F :: Δ) (subst (up σ') G) := hIG₁.wfTy
  refine ⟨subst σ' F, subst (up σ') G, TyRedsT.refl (Der.piT hF₂ hG₂),
    E.pi_cong hF₁ (hIF₀.escapeTyEq hIF₀eq) (hIG₀.escapeTyEq hIG₀eq), ?_, ?_⟩
  · intro Δ' ρ hρ
    obtain ⟨I, hI, hIeq⟩ := hFi Δ' _ _ (hs.wk hρ)
    have hIF := rF Δ' ρ hρ
    rw [eF ρ] at hIF
    rw [rename_subst]
    exact ((TyR.irrel (hI.lift (le_max_left i j)) hIF).1 _).mp hIeq
  · intro Δ' ρ a hρ ha
    have hs₂ : SubstR E (F :: Γ) Δ' (scons a (fun n => rename ρ (σ n)))
        (scons a (fun n => rename ρ (σ' n))) := by
      refine ⟨hs.wk hρ, L, IF Δ' ρ, ?_, ha⟩
      have := rF Δ' ρ hρ
      rw [eF ρ] at this
      exact this
    obtain ⟨I, hI, hIeq⟩ := hGj Δ' _ _ hs₂
    have hIG := rG Δ' ρ a hρ ha
    rw [eG ρ a] at hIG
    rw [rename_subst_up_inst]
    exact ((TyR.irrel (hI.lift (le_max_right i j)) hIG).1 _).mp hIeq

/-- **Validity of the product type.** -/
theorem valid_piT {Γ : Ctx} {F G : Tm} (hΓ : ValidCtx E Γ) (hF : ValidTy E Γ F)
    (hG : ValidTy E (F :: Γ) G) : ValidTy E Γ (pi F G) := by
  obtain ⟨i, hFi⟩ := hF
  obtain ⟨j, hGj⟩ := hG
  exact ⟨max i j, fun Δ σ σ' hs => valid_piT_at hΓ hFi hGj hs⟩

end MLTT
