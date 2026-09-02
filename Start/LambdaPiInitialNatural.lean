/-
**The interpretation of `λΠ` is natural in the model, up to isomorphism.**

`Start/LambdaPiInitial.lean` builds, out of a model `M` with injective products, the comparison
morphism `LambdaPiInitial.mor : Cwa.Mor syntactic M.T` interpreting the syntax of `λΠ`.
`Start/LambdaPiInterpTransport.lean` proves that a morphism of models `H : ModelHom M N` carries
the interpretation relations of `M` to those of `N`.  This module puts the two together: the
triangle

  syntax → M → N     versus     syntax → N

commutes up to a canonical **invertible 2-cell** of `Start/CwaTwoCell.lean`.

* `LambdaPi.ModelHom.varVal_map_eq` — the image of a semantic context reads its variables exactly
  as the images of what they read;
* `LambdaPi.SubI.map` — the image of a morphism carrying a substitution carries it;
* `LambdaPiInitial.natApp` — the comparison of the two interpretations of a context, and
  `LambdaPiInitial.isIso_natApp` — it is an isomorphism;
* `LambdaPiInitial.transportTwoCell` — **the 2-cell** from the interpretation in `N` to the
  interpretation in `M` followed by `H`.
-/

import Start.CwaTwoCell
import Start.LambdaPiInterpTransport
import Start.LambdaPiInitialUniv

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w'

open CategoryTheory Limits

namespace LambdaPi

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {M : Model.{u, v, w} C} {N : Model.{u', v', w'} D}

/-- The image of a semantic context reads nothing where the source reads nothing. -/
theorem ModelHom.varVal_map_none (H : ModelHom M N) {Γ : C} (s : SemCtx M Γ) :
    ∀ n : ℕ, s.varVal n = none → (H.semCtx s).varVal n = none := by
  induction s with
  | nil => intro n _; cases n <;> rfl
  | @cons Γ s A ih =>
      intro n hp
      cases n with
      | zero => simp [SemCtx.varVal] at hp
      | succ m =>
          simp only [SemCtx.varVal, Option.map_eq_none_iff] at hp
          simp [SemCtx.varVal, ih m hp]

/-- **The image of a semantic context reads its de Bruijn variables as the images of what they
read in the source**, and reads nothing where the source reads nothing. -/
theorem ModelHom.varVal_map_eq (H : ModelHom M N) {Γ : C} (s : SemCtx M Γ) (n : ℕ) :
    (H.semCtx s).varVal n = (s.varVal n).map (H.valMap s) := by
  cases hp : s.varVal n with
  | some p => simpa using H.varVal_map s n p hp
  | none => simpa using H.varVal_map_none s n hp

/-- The image of a value substituted along a morphism of the source is the image of the value
substituted along the image of that morphism, read in the images of the semantic contexts. -/
theorem ModelHom.valMap_sub_semIso (H : ModelHom M N) {Γ' Δ' : C} (s : SemCtx M Γ')
    (r : SemCtx M Δ') (σ : Δ' ⟶ Γ') (p : TmVal M Γ') :
    Cwa.Val.sub ((H.semIso r).inv ≫ H.mor.fnc.map σ ≫ (H.semIso s).hom) (H.valMap s p)
      = H.valMap r (Cwa.Val.sub σ p) := by
  rw [valMap, valMap, H.mor.valMap_sub, N.co.val_sub_comp, N.co.val_sub_comp]
  congr 1
  simp

/-- **A morphism of models carries a morphism carrying a substitution to one carrying it.** -/
theorem SubI.map (H : ModelHom M N) {Γ' Δ' : C} {s : SemCtx M Γ'} {r : SemCtx M Δ'}
    {σ : Δ' ⟶ Γ'} {f : ℕ → Tm} (hσ : SubI s r σ f) :
    SubI (H.semCtx s) (H.semCtx r)
      ((H.semIso r).inv ≫ H.mor.fnc.map σ ≫ (H.semIso s).hom) f := by
  intro n q hq
  rw [H.varVal_map_eq s n] at hq
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
  exact TmI.cast_val (TmI.map H (hσ n p hp)) (H.valMap_sub_semIso s r σ p).symm

end LambdaPi

namespace LambdaPiInitial

open LambdaPi LambdaPiCat LambdaPiFull Cwa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {M : Model.{u, v, w} C} {N : Model.{u', v', w'} D}
  (hM : M.PiInj) (hN : N.PiInj) (H : ModelHom M N)

/-- **The interpretation of a context in `N` is the image of its interpretation in `M`.** -/
theorem ctxI_map (Γ : Ob) :
    (⟨obj hN Γ, sem hN Γ⟩ : (X : D) × SemCtx N X)
      = ⟨H.semObj (sem hM Γ), H.semCtx (sem hM Γ)⟩ :=
  CtxI.unique (functional_of_piInj hN) (sem_spec hN Γ) ((sem_spec hM Γ).map H)

/-- The two interpretations of a context have the same underlying object. -/
theorem objMap_eq (Γ : Ob) : obj hN Γ = H.semObj (sem hM Γ) :=
  congrArg Sigma.fst (ctxI_map hM hN H Γ)

/-- **The comparison of the two interpretations of a context**: the interpretation in `N` maps to
the image under `H` of the interpretation in `M`. -/
noncomputable def natApp (Γ : Ob) : obj hN Γ ⟶ H.mor.fnc.obj (obj hM Γ) :=
  eqToHom (objMap_eq hM hN H Γ) ≫ (H.semIso (sem hM Γ)).inv

/-- The comparison is an isomorphism. -/
theorem isIso_natApp (Γ : Ob) : IsIso (natApp hM hN H Γ) :=
  inferInstanceAs (IsIso (eqToHom (objMap_eq hM hN H Γ) ≫ (H.semIso (sem hM Γ)).inv))

/-- The comparison carries the identity substitution. -/
theorem subI_natApp (Γ : Ob) :
    SubI (H.semCtx (sem hM Γ)) (sem hN Γ) (natApp hM hN H Γ ≫ (H.semIso (sem hM Γ)).hom) ids := by
  have h := SubI.congr_tgt (ctxI_map hM hN H Γ) (SubI.id (sem hN Γ))
  have he : natApp hM hN H Γ ≫ (H.semIso (sem hM Γ)).hom
      = 𝟙 (obj hN Γ) ≫ eqToHom (congrArg Sigma.fst (ctxI_map hM hN H Γ)) := by
    simp [natApp]
  rw [he]
  exact h

/-- **The comparison is natural in the context.** -/
theorem natApp_naturality {Δ Γ : Ob} (σ : Δ ⟶ Γ) :
    homMap hN σ ≫ natApp hM hN H Γ = natApp hM hN H Δ ≫ H.mor.fnc.map (homMap hM σ) := by
  have hL : SubI (H.semCtx (sem hM Γ)) (sem hN Δ)
      ((homMap hN σ ≫ natApp hM hN H Γ) ≫ (H.semIso (sem hM Γ)).hom) σ.out.sub := by
    have h := SubI.congr_tgt (ctxI_map hM hN H Γ) (homMap_spec hN σ)
    have he : (homMap hN σ ≫ natApp hM hN H Γ) ≫ (H.semIso (sem hM Γ)).hom
        = homMap hN σ ≫ eqToHom (congrArg Sigma.fst (ctxI_map hM hN H Γ)) := by
      simp [natApp]
    rw [he]
    exact h
  have hR : SubI (H.semCtx (sem hM Γ)) (sem hN Δ)
      ((natApp hM hN H Δ ≫ H.mor.fnc.map (homMap hM σ)) ≫ (H.semIso (sem hM Γ)).hom)
      σ.out.sub := by
    have h := SubI.congr_src (ctxI_map hM hN H Δ).symm (SubI.map H (homMap_spec hM σ))
    have he : (natApp hM hN H Δ ≫ H.mor.fnc.map (homMap hM σ)) ≫ (H.semIso (sem hM Γ)).hom
        = eqToHom (congrArg Sigma.fst (ctxI_map hM hN H Δ).symm).symm
            ≫ (H.semIso (sem hM Δ)).inv ≫ H.mor.fnc.map (homMap hM σ)
              ≫ (H.semIso (sem hM Γ)).hom := by
      simp [natApp]
    rw [he]
    exact h
  have := SubI.unique hN ((sem_spec hM Γ).map H) hL hR
  exact (Iso.cancel_iso_hom_right _ _ (H.semIso (sem hM Γ))).mp this

/-- The comparison as a natural transformation. -/
noncomputable def natTrans : (functor hN) ⟶ (functor hM ⋙ H.mor.fnc) where
  app Γ := natApp hM hN H Γ
  naturality _ _ σ := natApp_naturality hM hN H σ

/-- **The comparison carries the interpretation of a type in `M` to its interpretation in `N`.** -/
theorem tySub_natApp (Γ : Ob) (A : TyQ Γ) :
    N.T.tySub (natApp hM hN H Γ) (H.mor.tyMap (tyMap hM A)) = tyMap hN A := by
  refine (tyMap_eq hN A (Conv.refl _) ?_).symm
  have h := TyI.congr_ctx (ctxI_map hM hN H Γ).symm (TyI.map H (tyMap_spec hM A))
  have heq : N.T.tySub (natApp hM hN H Γ) (H.mor.tyMap (tyMap hM A))
      = N.T.tySub (eqToHom (congrArg Sigma.fst (ctxI_map hM hN H Γ).symm).symm)
          (H.semTy (sem hM Γ) (tyMap hM A)) := by
    rw [ModelHom.semTy, ← N.T.tySub_comp]
    rfl
  rw [heq]
  exact h

/-- The comparison of extended contexts, stated for abstract identifications of semantic
contexts.  Once the identifications are substituted away, the two sides are the two descriptions
of the action of a morphism of models on an extended context. -/
private theorem extend_key (H : ModelHom M N) {X : C} (s : SemCtx M X) (A' : M.T.Ty X)
    {X₂ : C} {s₂ : SemCtx M X₂}
    (e₁ : (⟨X₂, s₂⟩ : (Z : C) × SemCtx M Z) = ⟨M.T.ext X A', s.cons A'⟩)
    {Y : D} {r : SemCtx N Y} {B' : N.T.Ty Y} {Y₂ : D} {r₂ : SemCtx N Y₂}
    (f₁ : (⟨Y₂, r₂⟩ : (Z : D) × SemCtx N Z) = ⟨N.T.ext Y B', r.cons B'⟩)
    (g₁ : (⟨Y, r⟩ : (Z : D) × SemCtx N Z) = ⟨H.semObj s, H.semCtx s⟩)
    (g₂ : (⟨Y₂, r₂⟩ : (Z : D) × SemCtx N Z) = ⟨H.semObj s₂, H.semCtx s₂⟩)
    (etype : N.T.tySub (eqToHom (congrArg Sigma.fst g₁) ≫ (H.semIso s).inv) (H.mor.tyMap A')
      = B') :
    eqToHom (congrArg Sigma.fst f₁)
        ≫ N.T.substCompare (eqToHom (congrArg Sigma.fst g₁) ≫ (H.semIso s).inv) etype
      = (eqToHom (congrArg Sigma.fst g₂) ≫ (H.semIso s₂).inv)
          ≫ H.mor.fnc.map (eqToHom (congrArg Sigma.fst e₁)) ≫ (H.mor.extIso A').hom := by
  obtain ⟨he1, he2⟩ := Sigma.mk.inj_iff.mp e₁
  subst he1
  cases eq_of_heq he2
  obtain ⟨hg1, hg2⟩ := Sigma.mk.inj_iff.mp g₁
  subst hg1
  cases eq_of_heq hg2
  obtain ⟨hf1, hf2⟩ := Sigma.mk.inj_iff.mp f₁
  subst hf1
  cases eq_of_heq hf2
  simp only [eqToHom_refl, Category.id_comp] at etype ⊢
  cases etype
  rw [show eqToHom (congrArg Sigma.fst g₂) = 𝟙 (H.semObj (s.cons A')) from eqToHom_refl _ _]
  simp [ModelHom.semTy]

/-- The comparison is compatible with the comparisons of extended contexts. -/
theorem extend_natApp (Γ : Ob) (A : TyQ Γ) :
    ((mor hN).extIso A).hom
        ≫ N.T.substCompare (natApp hM hN H Γ) (tySub_natApp hM hN H Γ A)
      = natApp hM hN H (extOb Γ A) ≫ (((mor hM).comp H.mor).extIso A).hom :=
  extend_key H (sem hM Γ) (tyMap hM A) (ctxI_ext hM A) (ctxI_ext hN A)
    (ctxI_map hM hN H Γ) (ctxI_map hM hN H (extOb Γ A)) (tySub_natApp hM hN H Γ A)

/-- **The interpretation of `λΠ` is natural in the model**: interpreting in `M` and then applying
a morphism of models `H : ModelHom M N` is isomorphic, as a morphism of categories with attributes
out of the syntax, to interpreting in `N` directly. -/
noncomputable def transportTwoCell : Cwa.TwoCell (mor hN) ((mor hM).comp H.mor) where
  nat := natTrans hM hN H
  tySub_app A := tySub_natApp hM hN H _ A
  extend_app A := extend_natApp hM hN H _ A

/-- The comparison is a natural isomorphism. -/
theorem isIso_natTrans : IsIso (natTrans hM hN H) := by
  have : ∀ Γ, IsIso ((natTrans hM hN H).app Γ) := fun Γ => isIso_natApp hM hN H Γ
  exact NatIso.isIso_of_isIso_app _

/-- **The 2-cell expressing the naturality of the interpretation is invertible.** -/
theorem isIso_transportTwoCell :
    @IsIso _ (Cwa.morCategory (T := syntactic) N.co) _ _ (transportTwoCell hM hN H) := by
  have : IsIso (transportTwoCell hM hN H).nat := isIso_natTrans hM hN H
  exact Cwa.TwoCell.isIso_of_isIso_nat N.co _

/-- **Interpreting in `M` and pushing forward along `H` is isomorphic to interpreting in `N`.** -/
noncomputable def transportIso :
    @Iso _ (Cwa.morCategory (T := syntactic) N.co) (mor hN) ((mor hM).comp H.mor) :=
  @asIso _ (Cwa.morCategory (T := syntactic) N.co) _ _ (transportTwoCell hM hN H)
    (isIso_transportTwoCell hM hN H)

end LambdaPiInitial
