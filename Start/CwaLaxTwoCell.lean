/-
**Lax 2-cells between morphisms of categories with attributes.**

`Start/CwaTwoCell.lean` compares two morphisms `F, G : T ⟶ S` of categories with attributes by a
2-cell: a natural transformation of the functors on contexts along which the action on types agrees
*on the nose*, `S.tySub (nat.app Γ) (G.tyMap A) = F.tyMap A`.  That equality is a strong demand.
`Start/CwaStrictRigid.lean` shows how strong: between the morphisms of models induced by two
pullback-preserving functors it forces the functors to agree on objects, so that a natural
transformation of pullback-preserving functors induces, in general, *no* 2-cell at all
(`Cwa.isEmpty_twoCell_id_coyoneda`) — strictification cannot be 2-functorial for these 2-cells.

This module supplies the weakening that repairs it.  A **lax 2-cell** replaces the equality of
types by a *map over the base*: a morphism of the extended contexts

  `cmp Γ A : S.ext (F.fnc.obj Γ) (F.tyMap A) ⟶`
  `S.ext (F.fnc.obj Γ) (S.tySub (nat.app Γ) (G.tyMap A))`

commuting with the display maps, subject to the same coherence law as before, with the transport
along the equality replaced by `cmp`.  A strict 2-cell is a lax one whose comparison is the
transport (`Cwa.TwoCell.toLax`), and lax 2-cells have identities and vertical composition.

Main definitions:

* `Cwa.subOver` — a map of extended contexts over a context is substituted along a morphism, by
  the universal property of the extension square;
* `Cwa.LaxTwoCell F G` — a lax 2-cell;
* `Cwa.TwoCell.toLax`, `Cwa.LaxTwoCell.id`, `Cwa.LaxTwoCell.vcomp` — strict 2-cells are lax, and
  lax 2-cells compose vertically.

Main results:

* `Cwa.subOver_extend`, `Cwa.subOver_disp` — the two equations defining the substituted map;
* `Cwa.LaxTwoCell.ext_of_nat_eq` — a lax 2-cell is determined by its natural transformation and
  its comparison.
-/

import Start.CwaTwoCell

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w'

open CategoryTheory

namespace Cwa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {T : Cwa.{u, v, w} C} {S : Cwa.{u', v', w'} D}

/-! ### Substituting a map of extended contexts -/

/-- **A map of extended contexts over a context is substituted along a morphism.**  Given
`u : S.ext Γ A ⟶ S.ext Γ B` lying over `Γ`, the extension square of `B` lifts `u` to a map over
`Δ` between the substituted extended contexts. -/
noncomputable def subOver (S : Cwa.{u', v', w'} D) {Δ Γ : D} (σ : Δ ⟶ Γ) {A B : S.Ty Γ}
    (u : S.ext Γ A ⟶ S.ext Γ B) (hu : u ≫ S.disp B = S.disp A) :
    S.ext Δ (S.tySub σ A) ⟶ S.ext Δ (S.tySub σ B) :=
  (S.isPullback σ B).lift (S.extend σ A ≫ u) (S.disp (S.tySub σ A))
    (by rw [Category.assoc, hu]; exact (S.isPullback σ A).w)

@[reassoc] theorem subOver_extend {Δ Γ : D} (σ : Δ ⟶ Γ) {A B : S.Ty Γ}
    (u : S.ext Γ A ⟶ S.ext Γ B) (hu : u ≫ S.disp B = S.disp A) :
    S.subOver σ u hu ≫ S.extend σ B = S.extend σ A ≫ u :=
  (S.isPullback σ B).lift_fst _ _ _

@[reassoc] theorem subOver_disp {Δ Γ : D} (σ : Δ ⟶ Γ) {A B : S.Ty Γ}
    (u : S.ext Γ A ⟶ S.ext Γ B) (hu : u ≫ S.disp B = S.disp A) :
    S.subOver σ u hu ≫ S.disp (S.tySub σ B) = S.disp (S.tySub σ A) :=
  (S.isPullback σ B).lift_snd _ _ _

/-! ### Lax 2-cells -/

/-- A **lax 2-cell** between two morphisms of categories with attributes: a natural transformation
of the functors on contexts together with, for every type, a map of extended contexts over the
base comparing the type assigned by `F` with the substituted type assigned by `G`, satisfying the
coherence law of a 2-cell.  A strict 2-cell is the special case where that map is the transport
along an equality of types. -/
structure LaxTwoCell (F G : Mor T S) where
  /-- The natural transformation of the functors on contexts. -/
  nat : F.fnc ⟶ G.fnc
  /-- The comparison of the type assigned by `F` with the substituted type assigned by `G`. -/
  cmp : ∀ (Γ : C) (A : T.Ty Γ),
      S.ext (F.fnc.obj Γ) (F.tyMap A) ⟶ S.ext (F.fnc.obj Γ) (S.tySub (nat.app Γ) (G.tyMap A))
  /-- The comparison lies over the base. -/
  cmp_disp : ∀ (Γ : C) (A : T.Ty Γ),
      cmp Γ A ≫ S.disp (S.tySub (nat.app Γ) (G.tyMap A)) = S.disp (F.tyMap A)
  /-- The comparisons of extended contexts commute with the component. -/
  extend_app : ∀ (Γ : C) (A : T.Ty Γ),
      (F.extIso A).hom ≫ cmp Γ A ≫ S.extend (nat.app Γ) (G.tyMap A)
        = nat.app (T.ext Γ A) ≫ (G.extIso A).hom

namespace LaxTwoCell

variable {F G H : Mor T S}

/-- **A lax 2-cell is determined by its natural transformation and its comparison.** -/
theorem ext_of_nat_eq {θ ψ : LaxTwoCell F G} (h : θ.nat = ψ.nat) (h' : HEq θ.cmp ψ.cmp) :
    θ = ψ := by
  cases θ
  cases ψ
  cases h
  cases h'
  rfl

end LaxTwoCell

/-- **A 2-cell is a lax 2-cell** whose comparison is the transport along the equality of types. -/
def TwoCell.toLax {F G : Mor T S} (θ : TwoCell F G) : LaxTwoCell F G where
  nat := θ.nat
  cmp Γ A := eqToHom (congrArg (S.ext (F.fnc.obj Γ)) (θ.tySub_app A).symm)
  cmp_disp _ A := eqToHom_ext_disp (θ.tySub_app A).symm
  extend_app _ A := θ.extend_app A

@[simp] theorem TwoCell.toLax_nat {F G : Mor T S} (θ : TwoCell F G) : θ.toLax.nat = θ.nat := rfl

namespace LaxTwoCell

variable {F G H : Mor T S}

/-- The identity lax 2-cell. -/
noncomputable def id (coh : ExtCoherent S) (F : Mor T S) : LaxTwoCell F F :=
  (TwoCell.id coh F).toLax

@[simp] theorem id_nat (coh : ExtCoherent S) (F : Mor T S) :
    (LaxTwoCell.id coh F).nat = 𝟙 F.fnc := rfl

/-- **Vertical composition of lax 2-cells**: the comparison of the composite is the comparison of
the first followed by the comparison of the second, substituted along the first component. -/
noncomputable def vcomp (coh : ExtCoherent S) (θ : LaxTwoCell F G) (ψ : LaxTwoCell G H) :
    LaxTwoCell F H where
  nat := θ.nat ≫ ψ.nat
  cmp Γ A :=
    θ.cmp Γ A ≫ S.subOver (θ.nat.app Γ) (ψ.cmp Γ A) (ψ.cmp_disp Γ A)
      ≫ eqToHom (congrArg (S.ext (F.fnc.obj Γ))
          (show S.tySub (θ.nat.app Γ) (S.tySub (ψ.nat.app Γ) (H.tyMap A))
              = S.tySub ((θ.nat ≫ ψ.nat).app Γ) (H.tyMap A) from
            (S.tySub_comp (ψ.nat.app Γ) (θ.nat.app Γ) (H.tyMap A)).symm))
  cmp_disp Γ A := by
    have he : S.tySub (θ.nat.app Γ) (S.tySub (ψ.nat.app Γ) (H.tyMap A))
        = S.tySub ((θ.nat ≫ ψ.nat).app Γ) (H.tyMap A) :=
      (S.tySub_comp (ψ.nat.app Γ) (θ.nat.app Γ) (H.tyMap A)).symm
    rw [Category.assoc, Category.assoc, eqToHom_ext_disp he, subOver_disp, θ.cmp_disp]
  extend_app Γ A := by
    have hext : S.extend ((θ.nat ≫ ψ.nat).app Γ) (H.tyMap A)
        = eqToHom (congrArg (S.ext (F.fnc.obj Γ))
            (show S.tySub ((θ.nat ≫ ψ.nat).app Γ) (H.tyMap A)
                = S.tySub (θ.nat.app Γ) (S.tySub (ψ.nat.app Γ) (H.tyMap A)) from
              S.tySub_comp (ψ.nat.app Γ) (θ.nat.app Γ) (H.tyMap A)))
          ≫ S.extend (θ.nat.app Γ) (S.tySub (ψ.nat.app Γ) (H.tyMap A))
            ≫ S.extend (ψ.nat.app Γ) (H.tyMap A) :=
      coh.extend_comp (ψ.nat.app Γ) (θ.nat.app Γ) (H.tyMap A)
    rw [hext, Category.assoc, Category.assoc, ← Category.assoc (eqToHom _) (eqToHom _),
      eqToHom_trans, eqToHom_refl, Category.id_comp, subOver_extend_assoc,
      ← Category.assoc (θ.cmp Γ A), ← Category.assoc (F.extIso A).hom, θ.extend_app Γ A,
      Category.assoc, ψ.extend_app Γ A, NatTrans.comp_app, Category.assoc]

@[simp] theorem vcomp_nat (coh : ExtCoherent S) (θ : LaxTwoCell F G) (ψ : LaxTwoCell G H) :
    (θ.vcomp coh ψ).nat = θ.nat ≫ ψ.nat := rfl

end LaxTwoCell

end Cwa
