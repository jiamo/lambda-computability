/-
**Whiskering of lax 2-cells by a morphism of models.**

`Start/CwaLaxTwoCell.lean` defines the lax 2-cells and their vertical composition, and
`Start/CwaLaxCategory.lean` proves that the vertical structure is a category.  This module supplies
the horizontal structure: a lax 2-cell can be whiskered by a morphism of categories with attributes
on either side.

Whiskering on the left is immediate — the comparison of `F ⋆ θ` at `A` is the comparison of `θ` at
`F.tyMap A`.  Whiskering on the right has to transport the comparison of `θ` through the morphism
`H`: the image `H.fnc.map (θ.cmp Γ A)` is a map between images of extended contexts, which the
comparison isomorphisms `H.extIso` and the compatibility `H.tyMap_sub` turn into a map of extended
contexts over the base.  Both whiskerings are functorial in the 2-cell.

Main definitions:

* `Cwa.LaxTwoCell.whiskerLeft`, `Cwa.LaxTwoCell.whiskerRight` — whiskering a lax 2-cell by a
  morphism of models.

Main results:

* `Cwa.morMap_subOver` — a morphism of models carries the substituted map of extended contexts to
  the substituted map;
* `Cwa.LaxTwoCell.whiskerLeft_id`, `Cwa.LaxTwoCell.whiskerLeft_vcomp` — whiskering on the left is
  functorial in the 2-cell;
* `Cwa.LaxTwoCell.whiskerRight_id`, `Cwa.LaxTwoCell.whiskerRight_vcomp` — whiskering on the right
  is functorial in the 2-cell.

The interchange law is not proved *here*, and at the time this module was written it was expected
to fail, on the ground that it would ask the comparison of one lax 2-cell to be natural in the
component of the other, which is not part of the data.  That expectation was wrong: the comparison
of a lax 2-cell is *determined* by its natural transformation (`Start/CwaLaxRigid.lean`), and the
interchange law does hold in full generality — `Cwa.LaxTwoCell.whisker_exchange` in
`Start/CwaLaxInterchange.lean`, whence the bicategory `Start/CwaLaxBicat.lean`.
-/

import Start.CwaLaxCategory

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w' u'' v'' w''

open CategoryTheory

namespace Cwa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  {T : Cwa.{u, v, w} C} {S : Cwa.{u', v', w'} D} {R : Cwa.{u'', v'', w''} E}

/-- A transport along an equality of an object with itself cancels on the left.  (`eqToHom_refl`
matches only a proof that is syntactically `rfl`.) -/
private theorem eqToHom_self_comp {X Y : E} (e : X = X) (f : X ⟶ Y) : eqToHom e ≫ f = f := by
  have he : e = rfl := rfl
  rw [he, eqToHom_refl, Category.id_comp]

/-- A chain of three transports is the transport with the same ends. -/
private theorem eqToHom_three_eq_one {X₁ X₂ X₃ X₄ : E} (p : X₁ = X₂) (q : X₂ = X₃)
    (r : X₃ = X₄) (s : X₁ = X₄) :
    (eqToHom p ≫ eqToHom q) ≫ eqToHom r = eqToHom s := by
  cases p
  cases q
  cases r
  have hs : s = rfl := rfl
  rw [hs]
  simp

/-- Two chains of transports with the same ends, around the same two morphisms, agree. -/
private theorem eqToHom_around_two {W X₀ X₁ Y₀ Y₁ Y₂ Y₃ Y₄ Z₁ : E} (f : W ⟶ X₀) (p : X₀ = X₁)
    (g : X₁ ⟶ Y₀) (q : Y₀ = Y₁) (r : Y₁ = Y₂) (s : Y₂ = Y₃) (t : Y₃ = Y₄) (p' : X₀ = X₁)
    (w : Y₀ = Z₁) (x : Z₁ = Y₄) :
    f ≫ eqToHom p ≫ g ≫ eqToHom q ≫ eqToHom r ≫ eqToHom s ≫ eqToHom t
      = f ≫ eqToHom p' ≫ g ≫ eqToHom w ≫ eqToHom x := by
  cases p
  cases q
  cases r
  cases s
  cases t
  cases w
  have hp : p' = rfl := rfl
  have hx : x = rfl := rfl
  rw [hp, hx]
  simp

/-! ### The image of a map of extended contexts over the base -/

/-- The image under a morphism of models of a map of extended contexts over a context, read as a
map of extended contexts over the image context. -/
noncomputable def morOver (H : Mor S R) {Γ : D} {A B : S.Ty Γ} (u : S.ext Γ A ⟶ S.ext Γ B) :
    R.ext (H.fnc.obj Γ) (H.tyMap A) ⟶ R.ext (H.fnc.obj Γ) (H.tyMap B) :=
  (H.extIso A).inv ≫ H.fnc.map u ≫ (H.extIso B).hom

/-- The image of a map over the base lies over the base. -/
@[reassoc] theorem morOver_disp (H : Mor S R) {Γ : D} {A B : S.Ty Γ}
    (u : S.ext Γ A ⟶ S.ext Γ B) (hu : u ≫ S.disp B = S.disp A) :
    morOver H u ≫ R.disp (H.tyMap B) = R.disp (H.tyMap A) := by
  rw [morOver, Category.assoc, Category.assoc, H.extIso_disp, ← H.fnc.map_comp, hu,
    ← H.extIso_disp A, Iso.inv_hom_id_assoc]

/-- The image of an identity is the identity. -/
@[simp] theorem morOver_id (H : Mor S R) {Γ : D} (A : S.Ty Γ) :
    morOver H (𝟙 (S.ext Γ A)) = 𝟙 (R.ext (H.fnc.obj Γ) (H.tyMap A)) := by
  simp [morOver]

/-- The image of a composite is the composite of the images. -/
theorem morOver_comp (H : Mor S R) {Γ : D} {A B X : S.Ty Γ} (u : S.ext Γ A ⟶ S.ext Γ B)
    (v : S.ext Γ B ⟶ S.ext Γ X) :
    morOver H (u ≫ v) = morOver H u ≫ morOver H v := by
  simp [morOver]

/-- The image of a transport is the transport. -/
theorem morOver_eqToHom (H : Mor S R) {Γ : D} {A B : S.Ty Γ} (e : A = B) :
    morOver H (eqToHom (congrArg (S.ext Γ) e))
      = eqToHom (congrArg (R.ext (H.fnc.obj Γ)) (congrArg H.tyMap e)) := by
  cases e
  simp [morOver]

/-- **A morphism of models carries the substituted map of extended contexts to the substituted
map**, up to the transports identifying the image of a substituted type. -/
theorem morMap_subOver (H : Mor S R) {Δ Γ : D} (σ : Δ ⟶ Γ) {A B : S.Ty Γ}
    (u : S.ext Γ A ⟶ S.ext Γ B) (hu : u ≫ S.disp B = S.disp A) :
    eqToHom (congrArg (R.ext (H.fnc.obj Δ)) (H.tyMap_sub σ A).symm)
        ≫ morOver H (S.subOver σ u hu)
        ≫ eqToHom (congrArg (R.ext (H.fnc.obj Δ)) (H.tyMap_sub σ B))
      = R.subOver (H.fnc.map σ) (morOver H u) (morOver_disp H u hu) := by
  have hkey : eqToHom (congrArg (R.ext (H.fnc.obj Δ)) (H.tyMap_sub σ A).symm)
      ≫ (H.extIso (S.tySub σ A)).inv ≫ H.fnc.map (S.extend σ A)
      = R.extend (H.fnc.map σ) (H.tyMap A) ≫ (H.extIso A).inv := by
    rw [Iso.eq_comp_inv]
    simp only [Category.assoc]
    rw [H.extIso_extend σ A, Iso.inv_hom_id_assoc, ← Category.assoc, eqToHom_trans,
      eqToHom_self_comp]
  refine (R.isPullback (H.fnc.map σ) (H.tyMap B)).hom_ext ?_ ?_
  · rw [subOver_extend, morOver, morOver]
    simp only [Category.assoc]
    rw [← H.extIso_extend σ B, ← Functor.map_comp_assoc, subOver_extend,
      Functor.map_comp_assoc, ← Category.assoc ((H.extIso (S.tySub σ A)).inv),
      ← Category.assoc (eqToHom _), hkey]
    simp only [Category.assoc]
  · rw [subOver_disp, Category.assoc, Category.assoc,
      eqToHom_ext_disp (T := R) (H.tyMap_sub σ B),
      morOver_disp H _ (subOver_disp σ u hu),
      eqToHom_ext_disp (T := R) (H.tyMap_sub σ A).symm]

/-- A transport, a morphism and a transport back on either side cancel. -/
private theorem eqToHom_cancel_around {X₁ X₂ X₃ X₄ : E} (p : X₁ = X₂) (q : X₂ = X₁)
    (f : X₁ ⟶ X₃) (r : X₃ = X₄) (s : X₄ = X₃) :
    eqToHom p ≫ (eqToHom q ≫ f ≫ eqToHom r) ≫ eqToHom s = f := by
  cases p
  cases r
  have hq : q = rfl := rfl
  have hs : s = rfl := rfl
  rw [hq, hs]
  simp

/-- **The image of a substituted map of extended contexts** is the substituted map of the image,
up to the transports identifying the image of a substituted type. -/
theorem morOver_subOver (H : Mor S R) {Δ Γ : D} (σ : Δ ⟶ Γ) {A B : S.Ty Γ}
    (u : S.ext Γ A ⟶ S.ext Γ B) (hu : u ≫ S.disp B = S.disp A) :
    morOver H (S.subOver σ u hu)
      = eqToHom (congrArg (R.ext (H.fnc.obj Δ)) (H.tyMap_sub σ A))
        ≫ R.subOver (H.fnc.map σ) (morOver H u) (morOver_disp H u hu)
        ≫ eqToHom (congrArg (R.ext (H.fnc.obj Δ)) (H.tyMap_sub σ B).symm) := by
  rw [← morMap_subOver H σ u hu]
  exact (eqToHom_cancel_around _ _ _ _ _).symm

namespace LaxTwoCell

/-! ### Whiskering -/

/-- **Whiskering a lax 2-cell on the left** by a morphism of models. -/
def whiskerLeft (F : Mor T S) {G H : Mor S R} (θ : LaxTwoCell G H) :
    LaxTwoCell (F.comp G) (F.comp H) where
  nat := Functor.whiskerLeft F.fnc θ.nat
  cmp Γ A := θ.cmp (F.fnc.obj Γ) (F.tyMap A)
  cmp_disp Γ A := θ.cmp_disp (F.fnc.obj Γ) (F.tyMap A)
  extend_app Γ A := by
    have hθ := θ.extend_app (F.fnc.obj Γ) (F.tyMap A)
    have hnat := θ.nat.naturality (F.extIso A).hom
    change (G.fnc.map (F.extIso A).hom ≫ (G.extIso (F.tyMap A)).hom)
        ≫ θ.cmp (F.fnc.obj Γ) (F.tyMap A)
          ≫ R.extend (θ.nat.app (F.fnc.obj Γ)) (H.tyMap (F.tyMap A))
      = θ.nat.app (F.fnc.obj (T.ext Γ A)) ≫ H.fnc.map (F.extIso A).hom
          ≫ (H.extIso (F.tyMap A)).hom
    rw [Category.assoc, hθ, ← Category.assoc, hnat, Category.assoc]

@[simp] theorem whiskerLeft_nat (F : Mor T S) {G H : Mor S R} (θ : LaxTwoCell G H) :
    (whiskerLeft F θ).nat = Functor.whiskerLeft F.fnc θ.nat := rfl

/-- **Whiskering a lax 2-cell on the right** by a morphism of models. -/
noncomputable def whiskerRight {F G : Mor T S} (θ : LaxTwoCell F G) (H : Mor S R) :
    LaxTwoCell (F.comp H) (G.comp H) where
  nat := Functor.whiskerRight θ.nat H.fnc
  cmp Γ A :=
    morOver H (θ.cmp Γ A)
      ≫ eqToHom (congrArg (R.ext (H.fnc.obj (F.fnc.obj Γ)))
          (H.tyMap_sub (θ.nat.app Γ) (G.tyMap A)))
  cmp_disp Γ A := by
    change (morOver H (θ.cmp Γ A) ≫ eqToHom (congrArg (R.ext (H.fnc.obj (F.fnc.obj Γ)))
          (H.tyMap_sub (θ.nat.app Γ) (G.tyMap A))))
        ≫ R.disp (R.tySub (H.fnc.map (θ.nat.app Γ)) (H.tyMap (G.tyMap A)))
      = R.disp (H.tyMap (F.tyMap A))
    rw [Category.assoc, eqToHom_ext_disp (T := R) (H.tyMap_sub (θ.nat.app Γ) (G.tyMap A)),
      morOver_disp H _ (θ.cmp_disp Γ A)]
  extend_app Γ A := by
    have hext := H.extIso_extend (θ.nat.app Γ) (G.tyMap A)
    have hθ := θ.extend_app Γ A
    change (H.fnc.map (F.extIso A).hom ≫ (H.extIso (F.tyMap A)).hom)
        ≫ (morOver H (θ.cmp Γ A) ≫ eqToHom (congrArg (R.ext (H.fnc.obj (F.fnc.obj Γ)))
            (H.tyMap_sub (θ.nat.app Γ) (G.tyMap A))))
          ≫ R.extend (H.fnc.map (θ.nat.app Γ)) (H.tyMap (G.tyMap A))
      = H.fnc.map (θ.nat.app (T.ext Γ A)) ≫ H.fnc.map (G.extIso A).hom
          ≫ (H.extIso (G.tyMap A)).hom
    rw [morOver]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc, ← hext, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      Category.assoc, hθ, Functor.map_comp_assoc]

@[simp] theorem whiskerRight_nat {F G : Mor T S} (θ : LaxTwoCell F G) (H : Mor S R) :
    (whiskerRight θ H).nat = Functor.whiskerRight θ.nat H.fnc := rfl

/-- The comparison of a right whiskering. -/
theorem whiskerRight_cmp {F G : Mor T S} (θ : LaxTwoCell F G) (H : Mor S R) (Γ : C)
    (A : T.Ty Γ) :
    (whiskerRight θ H).cmp Γ A
      = morOver H (θ.cmp Γ A)
        ≫ eqToHom (congrArg (R.ext (H.fnc.obj (F.fnc.obj Γ)))
            (show H.tyMap (S.tySub (θ.nat.app Γ) (G.tyMap A))
                = R.tySub ((whiskerRight θ H).nat.app Γ) ((G.comp H).tyMap A) from
              H.tyMap_sub (θ.nat.app Γ) (G.tyMap A))) :=
  rfl

/-! ### Whiskering is functorial in the 2-cell -/

/-- Whiskering the identity on the left gives the identity. -/
theorem whiskerLeft_id (coh : ExtCoherent R) (F : Mor T S) (G : Mor S R) :
    whiskerLeft F (LaxTwoCell.id coh G) = LaxTwoCell.id coh (F.comp G) := rfl

/-- **Whiskering on the left preserves vertical composition.** -/
theorem whiskerLeft_vcomp (coh : ExtCoherent R) (F : Mor T S) {G H K : Mor S R}
    (θ : LaxTwoCell G H) (ψ : LaxTwoCell H K) :
    whiskerLeft F (θ.vcomp coh ψ) = (whiskerLeft F θ).vcomp coh (whiskerLeft F ψ) := rfl

/-- Whiskering the identity on the right gives the identity. -/
theorem whiskerRight_id (coh : ExtCoherent R) (cohS : ExtCoherent S) (F : Mor T S)
    (H : Mor S R) :
    whiskerRight (LaxTwoCell.id cohS F) H = LaxTwoCell.id coh (F.comp H) := by
  refine ext_of_cmp (by ext X; simp) ?_
  intro Γ A
  rw [whiskerRight_cmp, LaxTwoCell.id_cmp,
    morOver_eqToHom H
      (show F.tyMap A = S.tySub ((LaxTwoCell.id cohS F).nat.app Γ) (F.tyMap A) from
        (S.tySub_id (F.tyMap A)).symm),
    LaxTwoCell.id_cmp]
  exact eqToHom_three_eq_one _ _ _ _

/-- **Whiskering on the right preserves vertical composition.** -/
theorem whiskerRight_vcomp (coh : ExtCoherent R) (cohS : ExtCoherent S) {F G K : Mor T S}
    (θ : LaxTwoCell F G) (ψ : LaxTwoCell G K) (H : Mor S R) :
    whiskerRight (θ.vcomp cohS ψ) H = (whiskerRight θ H).vcomp coh (whiskerRight ψ H) := by
  refine ext_of_cmp (by ext X; simp) ?_
  intro Γ A
  have e₂ : S.tySub (θ.nat.app Γ) (S.tySub (ψ.nat.app Γ) (K.tyMap A))
      = S.tySub ((θ.vcomp cohS ψ).nat.app Γ) (K.tyMap A) :=
    (S.tySub_comp (ψ.nat.app Γ) (θ.nat.app Γ) (K.tyMap A)).symm
  have e₃ : H.tyMap (S.tySub (ψ.nat.app Γ) (K.tyMap A))
      = R.tySub ((whiskerRight ψ H).nat.app Γ) ((K.comp H).tyMap A) :=
    H.tyMap_sub (ψ.nat.app Γ) (K.tyMap A)
  rw [whiskerRight_cmp, LaxTwoCell.vcomp_cmp, morOver_comp, morOver_comp,
    morOver_eqToHom H e₂, morOver_subOver, LaxTwoCell.vcomp_cmp,
    subOver_congr _ _ (whiskerRight_cmp ψ H Γ A), subOver_comp, subOver_eqToHom _ e₃,
    whiskerRight_cmp]
  · simp only [Category.assoc]
    exact eqToHom_around_two _ _ _ _ _ _ _ _ _ _
  · exact eqToHom_ext_disp (T := R) e₃

end LaxTwoCell

end Cwa
