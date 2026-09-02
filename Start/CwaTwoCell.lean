/-
**2-cells between morphisms of categories with attributes.**

`Start/CwaMor.lean` defines a morphism of categories with attributes and `Start/CwaCat.lean`
assembles the models into a *1-category*.  That is too coarse for the comparison theorems one
wants about models of a dependent type theory: an interpretation of the syntax in a model is
canonical only *up to isomorphism*, so a statement such as "the interpretation is unique" can only
be expressed once one can compare two morphisms by a 2-cell.

This module supplies the missing dimension.  A **2-cell** between two morphisms `F, G : T ⟶ S` is
a natural transformation `F.fnc ⟶ G.fnc` of the functors on contexts which is compatible with the
two remaining pieces of data: substituting along the component carries the type `G.tyMap A` to
`F.tyMap A`, and the comparison isomorphisms of extended contexts commute with the component.  The
second law is stated with `Cwa.substCompare`, the canonical map out of an extended context whose
type is a substituted one; that packaging is what makes the laws compose.

Note that 2-cells require of the target model a coherence law: the identity 2-cell needs
`extend (𝟙 _)` to be the transport along `tySub_id`, and the vertical composite needs `extend` of a
composite to be the composite of the `extend`s.  These are exactly the two equations of
`Cwa.ExtCoherent` (see `Start/CwaSubFunctorial.lean`), which the strictified and the syntactic
models both satisfy; they are *not* consequences of the pullback axiom.

Main definitions:

* `Cwa.substCompare` — the canonical map `S.ext Δ A ⟶ S.ext Γ B` attached to `σ : Δ ⟶ Γ` and an
  identification `S.tySub σ B = A`;
* `Cwa.TwoCell F G` — a 2-cell between two morphisms of categories with attributes;
* `Cwa.TwoCell.id`, `Cwa.TwoCell.vcomp` — the identity 2-cell and vertical composition;
* `Cwa.morCategory` — **the morphisms `T ⟶ S` and the 2-cells between them form a category**;
* `Cwa.TwoCell.whiskerLeft`, `Cwa.TwoCell.whiskerRight` — whiskering by a morphism.

Main results:

* `Cwa.substCompare_comp`, `Cwa.substCompare_id` — the canonical maps compose;
* `Cwa.TwoCell.ext` — a 2-cell is determined by its natural transformation;
* `Cwa.TwoCell.whisker_exchange` — **the interchange law**;
* `Cwa.TwoCell.isIso_of_isIso_nat` — a 2-cell whose natural transformation is invertible is
  invertible, so 2-cells with invertible components are exactly the pseudo-natural isomorphisms.
-/

import Start.CwaCat
import Start.CwaSubFunctorial

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w' u'' v'' w''

open CategoryTheory

namespace Cwa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  {T : Cwa.{u, v, w} C} {S : Cwa.{u', v', w'} D} {R : Cwa.{u'', v'', w''} E}

/-! ### The canonical map out of an extended context -/

/-- The canonical map from a context extended by a type identified with a substituted one to the
context extended by the type it is substituted from.  This is `Cwa.extend` with the identification
of types folded into it, which is the shape in which it composes. -/
def substCompare (S : Cwa.{u', v', w'} D) {Δ Γ : D} (σ : Δ ⟶ Γ) {B : S.Ty Γ} {A : S.Ty Δ}
    (e : S.tySub σ B = A) : S.ext Δ A ⟶ S.ext Γ B :=
  eqToHom (congrArg (S.ext Δ) e.symm) ≫ S.extend σ B

@[simp] theorem substCompare_rfl {Δ Γ : D} (σ : Δ ⟶ Γ) (B : S.Ty Γ) :
    S.substCompare σ (rfl : S.tySub σ B = S.tySub σ B) = S.extend σ B := by
  simp [substCompare]

/-- The canonical map depends only on the substitution. -/
theorem substCompare_congr {Δ Γ : D} {σ σ' : Δ ⟶ Γ} (h : σ = σ') {B : S.Ty Γ} {A : S.Ty Δ}
    (e : S.tySub σ B = A) (e' : S.tySub σ' B = A) :
    S.substCompare σ e = S.substCompare σ' e' := by
  subst h
  rfl

/-- The canonical map lies over the substitution. -/
@[reassoc] theorem substCompare_disp {Δ Γ : D} (σ : Δ ⟶ Γ) {B : S.Ty Γ} {A : S.Ty Δ}
    (e : S.tySub σ B = A) :
    S.substCompare σ e ≫ S.disp B = S.disp A ≫ σ := by
  subst e
  simpa [substCompare] using (S.isPullback σ B).w

/-- The canonical map of an identity substitution is the transport along the identification. -/
theorem substCompare_id (coh : ExtCoherent S) {Γ : D} {B A : S.Ty Γ} (e : S.tySub (𝟙 Γ) B = A) :
    S.substCompare (𝟙 Γ) e
      = eqToHom (congrArg (S.ext Γ) (((S.tySub_id B).symm.trans e).symm)) := by
  subst e
  simp [substCompare, coh.extend_id]

/-- **The canonical maps compose.** -/
theorem substCompare_comp (coh : ExtCoherent S) {Θ Δ Γ : D} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    {B : S.Ty Γ} {A : S.Ty Δ} {A' : S.Ty Θ} (e : S.tySub σ B = A) (e' : S.tySub τ A = A') :
    S.substCompare τ e' ≫ S.substCompare σ e
      = S.substCompare (τ ≫ σ) (by rw [S.tySub_comp, e, e']) := by
  subst e
  subst e'
  simp [substCompare, coh.extend_comp σ τ B]

/-- A morphism of models carries the canonical maps to the canonical maps. -/
theorem extIso_substCompare (H : Mor S R) {Δ Γ : D} (σ : Δ ⟶ Γ) {B : S.Ty Γ} {A : S.Ty Δ}
    (e : S.tySub σ B = A) :
    (H.extIso A).hom ≫ R.substCompare (H.fnc.map σ)
        (show R.tySub (H.fnc.map σ) (H.tyMap B) = H.tyMap A from
          (H.tyMap_sub σ B).symm.trans (congrArg H.tyMap e))
      = H.fnc.map (S.substCompare σ e) ≫ (H.extIso B).hom := by
  subst e
  simpa [substCompare] using (H.extIso_extend σ B).symm

/-! ### 2-cells -/

/-- A **2-cell** between two morphisms of categories with attributes: a natural transformation of
the functors on contexts along which the action on types and the comparison of extended contexts
agree. -/
structure TwoCell (F G : Mor T S) where
  /-- The natural transformation of the functors on contexts. -/
  nat : F.fnc ⟶ G.fnc
  /-- Substituting along the component carries the type assigned by `G` to the one assigned
  by `F`. -/
  tySub_app : ∀ {Γ : C} (A : T.Ty Γ), S.tySub (nat.app Γ) (G.tyMap A) = F.tyMap A
  /-- The comparisons of extended contexts commute with the component. -/
  extend_app : ∀ {Γ : C} (A : T.Ty Γ),
      (F.extIso A).hom ≫ S.substCompare (nat.app Γ) (tySub_app A)
        = nat.app (T.ext Γ A) ≫ (G.extIso A).hom

namespace TwoCell

variable {F G H : Mor T S}

/-- **A 2-cell is determined by its natural transformation**; the remaining fields are
propositions. -/
@[ext] theorem ext {θ ψ : TwoCell F G} (h : θ.nat = ψ.nat) : θ = ψ := by
  cases θ
  cases ψ
  subst h
  rfl

/-- The identity 2-cell. -/
def id (coh : ExtCoherent S) (F : Mor T S) : TwoCell F F where
  nat := 𝟙 F.fnc
  tySub_app A := by simpa using S.tySub_id (F.tyMap A)
  extend_app := fun {Γ} A => by
    change (F.extIso A).hom ≫ S.substCompare (𝟙 (F.fnc.obj Γ)) _
        = 𝟙 (F.fnc.obj (T.ext Γ A)) ≫ (F.extIso A).hom
    rw [substCompare_id coh]
    simp

@[simp] theorem id_nat (coh : ExtCoherent S) (F : Mor T S) : (TwoCell.id coh F).nat = 𝟙 F.fnc :=
  rfl

/-- Vertical composition of 2-cells. -/
def vcomp (coh : ExtCoherent S) (θ : TwoCell F G) (ψ : TwoCell G H) : TwoCell F H where
  nat := θ.nat ≫ ψ.nat
  tySub_app A := by
    have h : S.tySub (θ.nat.app _ ≫ ψ.nat.app _) (H.tyMap A)
        = S.tySub (θ.nat.app _) (S.tySub (ψ.nat.app _) (H.tyMap A)) :=
      S.tySub_comp _ _ _
    rw [NatTrans.comp_app, h, ψ.tySub_app A, θ.tySub_app A]
  extend_app A := by
    have hcomp := substCompare_comp coh (ψ.nat.app _) (θ.nat.app _) (ψ.tySub_app A) (θ.tySub_app A)
    change (F.extIso A).hom ≫ S.substCompare (θ.nat.app _ ≫ ψ.nat.app _) _
        = (θ.nat.app (T.ext _ A) ≫ ψ.nat.app (T.ext _ A)) ≫ (H.extIso A).hom
    rw [← hcomp, ← Category.assoc, θ.extend_app A, Category.assoc, ψ.extend_app A,
      Category.assoc]

@[simp] theorem vcomp_nat (coh : ExtCoherent S) (θ : TwoCell F G) (ψ : TwoCell G H) :
    (θ.vcomp coh ψ).nat = θ.nat ≫ ψ.nat := rfl

end TwoCell

/-- **The morphisms between two categories with attributes form a category**, the 2-cells being
its morphisms. -/
@[instance_reducible]
def morCategory (coh : ExtCoherent S) : Category.{max u v'} (Mor T S) where
  Hom F G := TwoCell F G
  id F := TwoCell.id coh F
  comp θ ψ := θ.vcomp coh ψ
  id_comp θ := by ext; simp
  comp_id θ := by ext; simp
  assoc θ ψ ξ := by ext; simp

namespace TwoCell

/-- The natural transformation of a 2-cell coming from an equality of morphisms is the transport
of the underlying functors. -/
@[simp] theorem nat_eqToHom (coh : ExtCoherent S) {F G : Mor T S} (h : F = G) :
    (@eqToHom (Mor T S) (morCategory (T := T) coh).toCategoryStruct F G h).nat
      = eqToHom (congrArg Mor.fnc h) := by
  cases h
  rfl

/-- The component of the inverse of an invertible natural transformation cancels the component. -/
private theorem inv_app_hom {F G : Mor T S} (θ : TwoCell F G) [IsIso θ.nat] (Γ : C) :
    (CategoryTheory.inv θ.nat).app Γ ≫ θ.nat.app Γ = 𝟙 (G.fnc.obj Γ) := by
  rw [← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app]

private theorem hom_app_inv {F G : Mor T S} (θ : TwoCell F G) [IsIso θ.nat] (Γ : C) :
    θ.nat.app Γ ≫ (CategoryTheory.inv θ.nat).app Γ = 𝟙 (F.fnc.obj Γ) := by
  rw [← NatTrans.comp_app, IsIso.hom_inv_id, NatTrans.id_app]

/-- The action on types of the inverse of an invertible 2-cell. -/
theorem inv_tySub {F G : Mor T S} (θ : TwoCell F G) [IsIso θ.nat] {Γ : C} (A : T.Ty Γ) :
    S.tySub ((CategoryTheory.inv θ.nat).app Γ) (F.tyMap A) = G.tyMap A := by
  calc S.tySub ((CategoryTheory.inv θ.nat).app Γ) (F.tyMap A)
      = S.tySub ((CategoryTheory.inv θ.nat).app Γ) (S.tySub (θ.nat.app Γ) (G.tyMap A)) := by
        rw [θ.tySub_app A]
    _ = S.tySub ((CategoryTheory.inv θ.nat).app Γ ≫ θ.nat.app Γ) (G.tyMap A) :=
        (S.tySub_comp _ _ _).symm
    _ = G.tyMap A := by rw [inv_app_hom θ Γ, S.tySub_id]

/-- A 2-cell whose natural transformation is invertible has an inverse 2-cell. -/
noncomputable def inv (coh : ExtCoherent S) {F G : Mor T S} (θ : TwoCell F G) [IsIso θ.nat] :
    TwoCell G F where
  nat := CategoryTheory.inv θ.nat
  tySub_app A := inv_tySub θ A
  extend_app A := by
    have hkey : S.substCompare (θ.nat.app _) (θ.tySub_app A)
          ≫ S.substCompare ((CategoryTheory.inv θ.nat).app _) (inv_tySub θ A)
        = 𝟙 (S.ext (F.fnc.obj _) (F.tyMap A)) := by
      rw [substCompare_comp coh,
        substCompare_congr (S := S) (hom_app_inv θ _) _
          (show S.tySub (𝟙 (F.fnc.obj _)) (F.tyMap A) = F.tyMap A from S.tySub_id _),
        substCompare_id coh]
      simp
    have hnat : (CategoryTheory.inv θ.nat).app (T.ext _ A) ≫ θ.nat.app (T.ext _ A)
        = 𝟙 (G.fnc.obj (T.ext _ A)) := inv_app_hom θ _
    have hθ := θ.extend_app A
    calc (G.extIso A).hom ≫ S.substCompare ((CategoryTheory.inv θ.nat).app _) (inv_tySub θ A)
        = ((CategoryTheory.inv θ.nat).app (T.ext _ A) ≫ θ.nat.app (T.ext _ A)) ≫ (G.extIso A).hom
            ≫ S.substCompare ((CategoryTheory.inv θ.nat).app _) (inv_tySub θ A) := by
          rw [hnat, Category.id_comp]
      _ = (CategoryTheory.inv θ.nat).app (T.ext _ A) ≫ ((F.extIso A).hom
            ≫ S.substCompare (θ.nat.app _) (θ.tySub_app A))
            ≫ S.substCompare ((CategoryTheory.inv θ.nat).app _) (inv_tySub θ A) := by
          rw [hθ]
          simp only [Category.assoc]
      _ = (CategoryTheory.inv θ.nat).app (T.ext _ A) ≫ (F.extIso A).hom := by
          rw [Category.assoc, hkey, Category.comp_id]

/-- **A 2-cell whose natural transformation is invertible is invertible.** -/
theorem isIso_of_isIso_nat (coh : ExtCoherent S) {F G : Mor T S} (θ : TwoCell F G)
    [IsIso θ.nat] :
    @IsIso _ (morCategory (T := T) coh) F G θ := by
  let := morCategory (T := T) coh
  refine ⟨θ.inv coh, ?_, ?_⟩
  · change θ.vcomp coh (θ.inv coh) = TwoCell.id coh F
    refine TwoCell.ext ?_
    change θ.nat ≫ CategoryTheory.inv θ.nat = 𝟙 F.fnc
    simp
  · change (θ.inv coh).vcomp coh θ = TwoCell.id coh G
    refine TwoCell.ext ?_
    change CategoryTheory.inv θ.nat ≫ θ.nat = 𝟙 G.fnc
    simp

/-! ### A 2-cell is determined by its components on the base contexts -/

variable {F G : Mor T S}

/-- **The component of a 2-cell at an extended context is determined by its component at the base
context.** -/
theorem app_ext (θ : TwoCell F G) {Γ : C} (A : T.Ty Γ) :
    θ.nat.app (T.ext Γ A)
      = (F.extIso A).hom ≫ S.substCompare (θ.nat.app Γ) (θ.tySub_app A) ≫ (G.extIso A).inv := by
  refine (?_ : _ = θ.nat.app (T.ext Γ A)).symm
  rw [← Category.assoc, Iso.comp_inv_eq]
  exact θ.extend_app A

/-- Two 2-cells agreeing at a context agree at every extension of it. -/
theorem app_ext_congr {θ ψ : TwoCell F G} {Γ : C} (A : T.Ty Γ) (h : θ.nat.app Γ = ψ.nat.app Γ) :
    θ.nat.app (T.ext Γ A) = ψ.nat.app (T.ext Γ A) := by
  rw [app_ext, app_ext, substCompare_congr (S := S) h (θ.tySub_app A) (ψ.tySub_app A)]

/-- Two 2-cells agreeing at a context agree at every object isomorphic to an extension of it. -/
theorem app_eq_of_iso {θ ψ : TwoCell F G} {X Γ : C} (A : T.Ty Γ) (i : X ≅ T.ext Γ A)
    (h : θ.nat.app Γ = ψ.nat.app Γ) : θ.nat.app X = ψ.nat.app X := by
  have hθ := θ.nat.naturality i.hom
  have hψ := ψ.nat.naturality i.hom
  have hcancel : ∀ u v : F.fnc.obj X ⟶ G.fnc.obj X,
      u ≫ G.fnc.map i.hom = v ≫ G.fnc.map i.hom → u = v := by
    intro u v huv
    have := congrArg (fun x => x ≫ G.fnc.map i.inv) huv
    simpa [Category.assoc, ← G.fnc.map_comp] using this
  refine hcancel _ _ ?_
  rw [← hθ, ← hψ, app_ext_congr A h]

/-! ### Whiskering -/

/-- Whiskering a 2-cell on the left by a morphism. -/
def whiskerLeft (F : Mor T S) {G H : Mor S R} (θ : TwoCell G H) :
    TwoCell (F.comp G) (F.comp H) where
  nat := Functor.whiskerLeft F.fnc θ.nat
  tySub_app A := θ.tySub_app (F.tyMap A)
  extend_app A := by
    have hθ := θ.extend_app (F.tyMap A)
    have hnat := θ.nat.naturality (F.extIso A).hom
    change (G.fnc.map (F.extIso A).hom ≫ (G.extIso (F.tyMap A)).hom)
        ≫ R.substCompare (θ.nat.app (F.fnc.obj _)) (θ.tySub_app (F.tyMap A))
      = θ.nat.app (F.fnc.obj (T.ext _ A)) ≫ H.fnc.map (F.extIso A).hom ≫
          (H.extIso (F.tyMap A)).hom
    rw [Category.assoc, hθ, ← Category.assoc, hnat, Category.assoc]

@[simp] theorem whiskerLeft_nat (F : Mor T S) {G H : Mor S R} (θ : TwoCell G H) :
    (TwoCell.whiskerLeft F θ).nat = Functor.whiskerLeft F.fnc θ.nat := rfl

/-- Whiskering a 2-cell on the right by a morphism. -/
def whiskerRight {F G : Mor T S} (θ : TwoCell F G) (H : Mor S R) :
    TwoCell (F.comp H) (G.comp H) where
  nat := Functor.whiskerRight θ.nat H.fnc
  tySub_app A :=
    (H.tyMap_sub (θ.nat.app _) (G.tyMap A)).symm.trans (congrArg H.tyMap (θ.tySub_app A))
  extend_app A := by
    have hθ := θ.extend_app A
    have hH := extIso_substCompare H (θ.nat.app _) (θ.tySub_app A)
    change (H.fnc.map (F.extIso A).hom ≫ (H.extIso (F.tyMap A)).hom)
        ≫ R.substCompare (H.fnc.map (θ.nat.app _)) _
      = H.fnc.map (θ.nat.app (T.ext _ A)) ≫ H.fnc.map (G.extIso A).hom ≫
          (H.extIso (G.tyMap A)).hom
    rw [Category.assoc, hH, ← Category.assoc, ← H.fnc.map_comp, hθ, H.fnc.map_comp,
      Category.assoc]

@[simp] theorem whiskerRight_nat {F G : Mor T S} (θ : TwoCell F G) (H : Mor S R) :
    (TwoCell.whiskerRight θ H).nat = Functor.whiskerRight θ.nat H.fnc := rfl

/-- **The interchange law** for whiskering. -/
theorem whisker_exchange (coh : ExtCoherent R) {F G : Mor T S} {H K : Mor S R}
    (θ : TwoCell F G) (ψ : TwoCell H K) :
    (TwoCell.whiskerLeft F ψ).vcomp coh (TwoCell.whiskerRight θ K)
      = (TwoCell.whiskerRight θ H).vcomp coh (TwoCell.whiskerLeft G ψ) := by
  refine TwoCell.ext ?_
  simp only [vcomp_nat, whiskerLeft_nat, whiskerRight_nat]
  exact Functor.whiskerLeft_comp_whiskerRight θ.nat ψ.nat

end TwoCell

end Cwa
