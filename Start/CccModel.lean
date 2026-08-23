/-
Interpretation of the simply typed lambda calculus in an arbitrary cartesian closed category, and
soundness of βη-conversion.  Together with `Start/StlcCcc.lean` (the syntactic category of the
simply typed lambda calculus is itself cartesian closed) this is the Curry–Howard–Lambek
correspondence in both directions: the syntax of the simply typed lambda calculus *is* a
cartesian closed category, and *every* cartesian closed category is a model of it.

* `Stlc.tyObj`, `Stlc.ctxObj` — types as objects, contexts as iterated products;
* `Stlc.tmMor` — a term `Γ ⊢ t : A` as a morphism `⟦Γ⟧ ⟶ ⟦A⟧`;
* `Stlc.tmMor_sub` — the substitution lemma: substitution is composition;
* `Stlc.tmMor_conv` — **soundness**: convertible terms have equal interpretations;
* `Stlc.interpFunctor` — hence a functor from the syntactic category to any cartesian closed
  category, sending the type `A` to `⟦A⟧`;
* `Stlc.interpFunctor_obj_unit`, `Stlc.interpFunctor_obj_prod`, `Stlc.interpFunctor_obj_arrow`,
  `Stlc.interpFunctor_map_projFst`, `Stlc.interpFunctor_map_projSnd`,
  `Stlc.interpFunctor_map_pairHom`, `Stlc.interpFunctor_map_curryHom` — the functor preserves the
  cartesian closed structure: the terminal object, the products with their projections and
  pairing, and the exponentials with their currying.

What is *not* claimed here is freeness in the strict sense, i.e. that the interpretation functor
is the unique structure-preserving functor out of the syntactic category.
-/

import Start.StlcCcc

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe v u

namespace Stlc

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]

------------------------------------------------------------------------
-- The interpretation
------------------------------------------------------------------------

/-- Types as objects: the base type is interpreted by a chosen object `S`, the unit type by the
monoidal unit, products by the monoidal (i.e. cartesian) product, function types by the internal
hom. -/
@[reducible] def tyObj (S : C) : Ty → C
  | Ty.base => S
  | Ty.unit => 𝟙_ C
  | Ty.prod A B => tyObj S A ⊗ tyObj S B
  | Ty.arrow A B => tyObj S A ⟶[C] tyObj S B

/-- Contexts as iterated products, the variable `0` in the left factor. -/
@[reducible] def ctxObj (S : C) : Ctx → C
  | [] => 𝟙_ C
  | A :: Γ => tyObj S A ⊗ ctxObj S Γ

/-- A variable as a projection. -/
def varMor (S : C) : ∀ {Γ : Ctx} {A : Ty}, Var Γ A → (ctxObj S Γ ⟶ tyObj S A)
  | _, _, Var.zero => fst _ _
  | _, _, Var.succ v => snd _ _ ≫ varMor S v

/-- A term as a morphism from the interpretation of its context to the interpretation of its
type. -/
def tmMor (S : C) : ∀ {Γ : Ctx} {A : Ty}, Tm Γ A → (ctxObj S Γ ⟶ tyObj S A)
  | _, _, Tm.var v => varMor S v
  | _, _, Tm.app f a => lift (tmMor S a) (𝟙 _) ≫ uncurry (tmMor S f)
  | _, _, Tm.lam t => curry (tmMor S t)
  | _, _, Tm.star => toUnit _
  | _, _, Tm.pair a b => lift (tmMor S a) (tmMor S b)
  | _, _, Tm.fst t => tmMor S t ≫ fst _ _
  | _, _, Tm.snd t => tmMor S t ≫ snd _ _

/-- A renaming as a morphism between the interpretations of the contexts. -/
def renMor (S : C) : ∀ {Γ Δ : Ctx}, Ren Γ Δ → (ctxObj S Δ ⟶ ctxObj S Γ)
  | [], _, _ => toUnit _
  | _ :: _, _, r => lift (varMor S (r _ Var.zero)) (renMor S fun B v => r B v.succ)

/-- A substitution as a morphism between the interpretations of the contexts. -/
def subMor (S : C) : ∀ {Γ Δ : Ctx}, Sub Γ Δ → (ctxObj S Δ ⟶ ctxObj S Γ)
  | [], _, _ => toUnit _
  | _ :: _, _, σ => lift (tmMor S (σ _ Var.zero)) (subMor S fun B v => σ B v.succ)

------------------------------------------------------------------------
-- Renamings
------------------------------------------------------------------------

theorem varMor_renMor (S : C) : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {A : Ty} (v : Var Γ A),
    renMor S r ≫ varMor S v = varMor S (r A v)
  | _ :: _, _, r, _, Var.zero => by
      change lift (varMor S (r _ Var.zero)) _ ≫ fst _ _ = _
      rw [lift_fst]
  | _ :: _, _, r, _, Var.succ v => by
      change lift (varMor S (r _ Var.zero)) (renMor S fun B w => r B w.succ) ≫
        (snd _ _ ≫ varMor S v) = _
      rw [← Category.assoc, lift_snd]
      exact varMor_renMor S _ v

theorem renMor_succ (S : C) {B : Ty} : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ),
    renMor S (fun A v => Var.succ (B := B) (r A v))
      = snd (tyObj S B) (ctxObj S Δ) ≫ renMor S r
  | [], _, _ => toUnit_unique _ _
  | _ :: _, _, r => by
      change lift (varMor S (Var.succ (r _ Var.zero)))
        (renMor S fun A v => Var.succ (B := B) (r A v.succ)) = _
      rw [renMor_succ S fun A v => r A v.succ]
      change lift (snd _ _ ≫ varMor S (r _ Var.zero)) _ = _
      rw [← comp_lift]
      rfl

theorem renMor_id (S : C) : ∀ Γ : Ctx, renMor S (Ren.id Γ) = 𝟙 (ctxObj S Γ)
  | [] => toUnit_unique _ _
  | A :: Γ => by
      change lift (varMor S (Var.zero (Γ := Γ) (A := A)))
        (renMor S fun B v => Var.succ (B := A) (Ren.id Γ B v)) = _
      rw [renMor_succ S (Ren.id Γ), renMor_id S Γ, Category.comp_id]
      exact lift_fst_snd

theorem renMor_lift (S : C) {Γ Δ : Ctx} (r : Ren Γ Δ) (B : Ty) :
    renMor S (r.lift B) = tyObj S B ◁ renMor S r := by
  refine hom_ext _ _ ?_ ?_
  · change lift (varMor S (Var.zero (Γ := Δ) (A := B))) _ ≫ fst _ _ = _
    rw [lift_fst, whiskerLeft_fst]
    rfl
  · change lift (varMor S (Var.zero (Γ := Δ) (A := B)))
      (renMor S fun A v => (r.lift B) A v.succ) ≫ snd _ _ = _
    rw [lift_snd, whiskerLeft_snd]
    exact renMor_succ S r

theorem tmMor_ren (S : C) : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {A : Ty} (t : Tm Γ A),
    tmMor S (ren r t) = renMor S r ≫ tmMor S t
  | _, _, r, _, Tm.var v => (varMor_renMor S r v).symm
  | _, _, r, _, Tm.app f a => by
      change lift (tmMor S (ren r a)) (𝟙 _) ≫ uncurry (tmMor S (ren r f)) = _
      rw [tmMor_ren S r a, tmMor_ren S r f, uncurry_natural_left]
      change _ = renMor S r ≫ lift (tmMor S a) (𝟙 _) ≫ uncurry (tmMor S f)
      rw [← Category.assoc, ← Category.assoc, comp_lift]
      congr 1
      refine hom_ext _ _ ?_ ?_
      · rw [Category.assoc, whiskerLeft_fst, lift_fst, lift_fst]
      · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd, lift_snd,
          Category.id_comp, Category.comp_id]
  | _, _, r, _, Tm.lam t => by
      change curry (tmMor S (ren (r.lift _) t)) = _
      rw [tmMor_ren S (r.lift _) t, renMor_lift, curry_natural_left]
      rfl
  | _, _, _, _, Tm.star => toUnit_unique _ _
  | _, _, r, _, Tm.pair a b => by
      change lift (tmMor S (ren r a)) (tmMor S (ren r b)) = _
      rw [tmMor_ren S r a, tmMor_ren S r b, ← comp_lift]
      rfl
  | _, _, r, _, Tm.fst t => by
      change tmMor S (ren r t) ≫ fst _ _ = _
      rw [tmMor_ren S r t, Category.assoc]
      rfl
  | _, _, r, _, Tm.snd t => by
      change tmMor S (ren r t) ≫ snd _ _ = _
      rw [tmMor_ren S r t, Category.assoc]
      rfl

theorem tmMor_wk (S : C) {Γ : Ctx} {A : Ty} (B : Ty) (t : Tm Γ A) :
    tmMor S (wk B t) = snd (tyObj S B) (ctxObj S Γ) ≫ tmMor S t := by
  change tmMor S (ren (Ren.wk B) t) = _
  rw [tmMor_ren]
  congr 1
  change renMor S (fun A v => Var.succ (B := B) (Ren.id Γ A v)) = _
  rw [renMor_succ S (Ren.id Γ), renMor_id, Category.comp_id]

------------------------------------------------------------------------
-- Substitutions
------------------------------------------------------------------------

theorem tmMor_subMor (S : C) : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ) {A : Ty} (v : Var Γ A),
    subMor S σ ≫ varMor S v = tmMor S (σ A v)
  | _ :: _, _, σ, _, Var.zero => by
      change lift (tmMor S (σ _ Var.zero)) _ ≫ fst _ _ = _
      rw [lift_fst]
  | _ :: _, _, σ, _, Var.succ v => by
      change lift (tmMor S (σ _ Var.zero)) (subMor S fun B w => σ B w.succ) ≫
        (snd _ _ ≫ varMor S v) = _
      rw [← Category.assoc, lift_snd]
      exact tmMor_subMor S _ v

theorem subMor_wk (S : C) {B : Ty} : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ),
    subMor S (fun A v => wk B (σ A v)) = snd (tyObj S B) (ctxObj S Δ) ≫ subMor S σ
  | [], _, _ => toUnit_unique _ _
  | _ :: _, _, σ => by
      change lift (tmMor S (wk B (σ _ Var.zero)))
        (subMor S fun A v => wk B (σ A v.succ)) = _
      rw [tmMor_wk, subMor_wk S fun A v => σ A v.succ, ← comp_lift]
      rfl

theorem subMor_lift (S : C) {Γ Δ : Ctx} (σ : Sub Γ Δ) (B : Ty) :
    subMor S (σ.lift B) = tyObj S B ◁ subMor S σ := by
  refine hom_ext _ _ ?_ ?_
  · change lift (tmMor S (Tm.var (Var.zero (Γ := Δ) (A := B)))) _ ≫ fst _ _ = _
    rw [lift_fst, whiskerLeft_fst]
    rfl
  · change lift (tmMor S (Tm.var (Var.zero (Γ := Δ) (A := B))))
      (subMor S fun A v => (σ.lift B) A v.succ) ≫ snd _ _ = _
    rw [lift_snd, whiskerLeft_snd]
    exact subMor_wk S σ

theorem tmMor_sub (S : C) : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ) {A : Ty} (t : Tm Γ A),
    tmMor S (sub σ t) = subMor S σ ≫ tmMor S t
  | _, _, σ, _, Tm.var v => (tmMor_subMor S σ v).symm
  | _, _, σ, _, Tm.app f a => by
      change lift (tmMor S (sub σ a)) (𝟙 _) ≫ uncurry (tmMor S (sub σ f)) = _
      rw [tmMor_sub S σ a, tmMor_sub S σ f, uncurry_natural_left]
      change _ = subMor S σ ≫ lift (tmMor S a) (𝟙 _) ≫ uncurry (tmMor S f)
      rw [← Category.assoc, ← Category.assoc, comp_lift]
      congr 1
      refine hom_ext _ _ ?_ ?_
      · rw [Category.assoc, whiskerLeft_fst, lift_fst, lift_fst]
      · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd, lift_snd,
          Category.id_comp, Category.comp_id]
  | _, _, σ, _, Tm.lam t => by
      change curry (tmMor S (sub (σ.lift _) t)) = _
      rw [tmMor_sub S (σ.lift _) t, subMor_lift, curry_natural_left]
      rfl
  | _, _, _, _, Tm.star => toUnit_unique _ _
  | _, _, σ, _, Tm.pair a b => by
      change lift (tmMor S (sub σ a)) (tmMor S (sub σ b)) = _
      rw [tmMor_sub S σ a, tmMor_sub S σ b, ← comp_lift]
      rfl
  | _, _, σ, _, Tm.fst t => by
      change tmMor S (sub σ t) ≫ fst _ _ = _
      rw [tmMor_sub S σ t, Category.assoc]
      rfl
  | _, _, σ, _, Tm.snd t => by
      change tmMor S (sub σ t) ≫ snd _ _ = _
      rw [tmMor_sub S σ t, Category.assoc]
      rfl

theorem subMor_id (S : C) : ∀ Γ : Ctx, subMor S (Sub.id Γ) = 𝟙 (ctxObj S Γ)
  | [] => toUnit_unique _ _
  | A :: Γ => by
      change lift (tmMor S (Tm.var (Var.zero (Γ := Γ) (A := A))))
        (subMor S fun B v => Tm.var (Var.succ (B := A) v)) = _
      have h : (fun (B : Ty) (v : Var Γ B) => Tm.var (Var.succ (B := A) v))
          = fun B v => wk A (Sub.id Γ B v) := rfl
      rw [h, subMor_wk S (Sub.id Γ), subMor_id S Γ, Category.comp_id]
      exact lift_fst_snd

theorem subMor_single (S : C) {Γ : Ctx} {A : Ty} (s : Tm Γ A) :
    subMor S (Sub.single s) = lift (tmMor S s) (𝟙 (ctxObj S Γ)) := by
  change lift (tmMor S s) (subMor S (Sub.id Γ)) = _
  rw [subMor_id]

theorem tmMor_inst (S : C) {Γ : Ctx} {A B : Ty} (t : Tm (A :: Γ) B) (s : Tm Γ A) :
    tmMor S (inst t s) = lift (tmMor S s) (𝟙 _) ≫ tmMor S t := by
  change tmMor S (sub (Sub.single s) t) = _
  rw [tmMor_sub, subMor_single]

------------------------------------------------------------------------
-- Soundness of conversion
------------------------------------------------------------------------

omit [MonoidalClosed C] in
theorem lift_fst_id_comp_whiskerLeft_snd (X Y : C) :
    lift (fst X Y) (𝟙 (X ⊗ Y)) ≫ (X ◁ snd X Y) = 𝟙 (X ⊗ Y) := by
  refine hom_ext _ _ ?_ ?_
  · rw [Category.assoc, whiskerLeft_fst, lift_fst, Category.id_comp]
  · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd, Category.id_comp]

/-- **Soundness**: βη-convertible terms have the same interpretation in every cartesian closed
category. -/
theorem tmMor_conv (S : C) : ∀ {Γ : Ctx} {A : Ty} {t u : Tm Γ A}, Conv t u →
    tmMor S t = tmMor S u := by
  intro Γ A t u h
  induction h with
  | refl t => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | app _ _ ih₁ ih₂ => simp only [tmMor, ih₁, ih₂]
  | lam _ ih => simp only [tmMor, ih]
  | pair _ _ ih₁ ih₂ => simp only [tmMor, ih₁, ih₂]
  | fst _ ih => simp only [tmMor, ih]
  | snd _ ih => simp only [tmMor, ih]
  | beta t s =>
      simp only [tmMor, MonoidalClosed.uncurry_curry]
      rw [tmMor_inst]
  | eta t =>
      simp only [tmMor, varMor, tmMor_wk, uncurry_natural_left]
      rw [← Category.assoc, lift_fst_id_comp_whiskerLeft_snd, Category.id_comp,
        MonoidalClosed.curry_uncurry]
  | fst_pair a b => simp only [tmMor, lift_fst]
  | snd_pair a b => simp only [tmMor, lift_snd]
  | pair_eta t =>
      simp only [tmMor]
      rw [← comp_lift, lift_fst_snd, Category.comp_id]
  | unit_eta t => exact toUnit_unique _ _

------------------------------------------------------------------------
-- The interpretation functor
------------------------------------------------------------------------

/-- The interpretation of a one-variable term as a morphism `⟦A⟧ ⟶ ⟦B⟧`, using that the
interpretation of the context `[A]` is `⟦A⟧ ⊗ 𝟙_ C`. -/
def interpTm (S : C) {A B : Ty} (t : Tm [A] B) : tyObj S A ⟶ tyObj S B :=
  (ρ_ (tyObj S A)).inv ≫ tmMor S t

omit [MonoidalClosed C] in
theorem rightUnitor_inv_fst (X : C) : (ρ_ X).inv ≫ fst X (𝟙_ C) = 𝟙 X := by
  rw [← cancel_epi (ρ_ X).hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    Category.comp_id]
  exact (rightUnitor_hom X).symm

theorem interpTm_congr (S : C) {A B : Ty} {t u : Tm [A] B} (h : Conv t u) :
    interpTm S t = interpTm S u := by
  rw [interpTm, interpTm, tmMor_conv S h]

theorem interpTm_id (S : C) (A : Ty) :
    interpTm S (Tm.var (Var.zero (Γ := []) (A := A))) = 𝟙 (tyObj S A) := by
  simp only [interpTm, tmMor, varMor]
  exact rightUnitor_inv_fst _

theorem interpTm_cmp (S : C) {A B D : Ty} (g : Tm [B] D) (f : Tm [A] B) :
    interpTm S (cmp g f) = interpTm S f ≫ interpTm S g := by
  have hsub : (ρ_ (tyObj S A)).inv ≫ subMor S (one f)
      = ((ρ_ (tyObj S A)).inv ≫ tmMor S f) ≫ (ρ_ (tyObj S B)).inv := by
    refine hom_ext _ _ ?_ ?_
    · change ((ρ_ (tyObj S A)).inv ≫ lift (tmMor S f) (toUnit (tyObj S A ⊗ 𝟙_ C))) ≫
        fst (tyObj S B) (𝟙_ C) = _
      rw [Category.assoc, lift_fst, Category.assoc, rightUnitor_inv_fst, Category.comp_id]
    · exact toUnit_unique _ _
  change (ρ_ (tyObj S A)).inv ≫ tmMor S (sub (one f) g) = interpTm S f ≫ interpTm S g
  rw [tmMor_sub, ← Category.assoc, hsub]
  simp only [interpTm, Category.assoc]

/-- **The interpretation functor**: any cartesian closed category `C` with a chosen interpretation
`S` of the base type is a model of the simply typed lambda calculus, i.e. receives a functor from
the syntactic category which sends types to their interpretations and terms to their
denotations. -/
def interpFunctor (S : C) : Ty ⥤ C where
  obj A := tyObj S A
  map {A B} f := Quotient.liftOn f (fun (t : Tm [A] B) => interpTm S t)
    (fun _ _ h => interpTm_congr S h)
  map_id A := interpTm_id S A
  map_comp {A B D} f g := by
    induction f using Hom.ind with
    | _ f =>
      induction g using Hom.ind with
      | _ g => exact interpTm_cmp S g f

@[simp] theorem interpFunctor_obj (S : C) (A : Ty) : (interpFunctor S).obj A = tyObj S A := rfl

@[simp] theorem interpFunctor_map_hom (S : C) {A B : Ty} (t : Tm [A] B) :
    (interpFunctor S).map (hom t) = interpTm S t := rfl

------------------------------------------------------------------------
-- The interpretation functor preserves the cartesian closed structure
------------------------------------------------------------------------

/-- The interpretation of the unit type is the terminal object, on the nose. -/
theorem interpFunctor_obj_unit (S : C) : (interpFunctor S).obj Ty.unit = 𝟙_ C := rfl

/-- The interpretation of a product type is the product of the interpretations, on the nose. -/
theorem interpFunctor_obj_prod (S : C) (A B : Ty) :
    (interpFunctor S).obj (Ty.prod A B) = (interpFunctor S).obj A ⊗ (interpFunctor S).obj B := rfl

/-- The interpretation of a function type is the internal hom of the interpretations, on the
nose. -/
theorem interpFunctor_obj_arrow (S : C) (A B : Ty) :
    (interpFunctor S).obj (Ty.arrow A B)
      = ((interpFunctor S).obj A ⟶[C] (interpFunctor S).obj B) := rfl

theorem interpFunctor_map_projFst (S : C) (A B : Ty) :
    (interpFunctor S).map (projFst A B) = fst (tyObj S A) (tyObj S B) := by
  change (ρ_ (tyObj S A ⊗ tyObj S B)).inv ≫ fst _ _ ≫ fst _ _ = _
  rw [← Category.assoc, rightUnitor_inv_fst, Category.id_comp]

theorem interpFunctor_map_projSnd (S : C) (A B : Ty) :
    (interpFunctor S).map (projSnd A B) = snd (tyObj S A) (tyObj S B) := by
  change (ρ_ (tyObj S A ⊗ tyObj S B)).inv ≫ fst _ _ ≫ snd _ _ = _
  rw [← Category.assoc, rightUnitor_inv_fst, Category.id_comp]

/-- The interpretation functor preserves pairing. -/
theorem interpFunctor_map_pairHom (S : C) {D A B : Ty} (f : D ⟶ A) (g : D ⟶ B) :
    (interpFunctor S).map (pairHom f g)
      = lift ((interpFunctor S).map f) ((interpFunctor S).map g) := by
  induction f using Hom.ind with
  | _ f =>
    induction g using Hom.ind with
    | _ g =>
      change (ρ_ (tyObj S D)).inv ≫ lift (tmMor S f) (tmMor S g) = _
      rw [comp_lift]
      rfl

theorem whiskerLeft_rightUnitor_inv_comp_subMor_pairVar (S : C) (X Y : Ty) :
    (tyObj S X ◁ (ρ_ (tyObj S Y)).inv) ≫ subMor S (one (pairVar X Y))
      = (ρ_ (tyObj S X ⊗ tyObj S Y)).inv := by
  refine hom_ext _ _ ?_ ?_
  · change ((tyObj S X ◁ (ρ_ (tyObj S Y)).inv) ≫
      lift (lift (fst _ _) (snd _ _ ≫ fst _ _)) (toUnit _)) ≫ fst _ _ = _
    rw [Category.assoc, lift_fst, rightUnitor_inv_fst]
    refine hom_ext _ _ ?_ ?_
    · rw [Category.assoc, lift_fst, whiskerLeft_fst, Category.id_comp]
    · rw [Category.assoc, lift_snd, ← Category.assoc, whiskerLeft_snd, Category.assoc,
        rightUnitor_inv_fst, Category.comp_id, Category.id_comp]
  · exact toUnit_unique _ _

/-- The interpretation functor preserves currying, so it preserves the exponentials. -/
theorem interpFunctor_map_curryHom (S : C) {X Y Z : Ty} (f : Ty.prod X Y ⟶ Z) :
    (interpFunctor S).map (curryHom (X := X) f) = curry ((interpFunctor S).map f) := by
  induction f using Hom.ind with
  | _ f =>
    change (ρ_ (tyObj S Y)).inv ≫ curry (tmMor S (sub (one (pairVar X Y)) f)) = _
    rw [tmMor_sub, ← curry_natural_left, ← Category.assoc,
      whiskerLeft_rightUnitor_inv_comp_subMor_pairVar]
    rfl

end Stlc
