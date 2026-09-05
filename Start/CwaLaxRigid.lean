/-
**A lax 2-cell is exactly a natural transformation of the functors on contexts.**

`Start/CwaLaxTwoCell.lean` defines a lax 2-cell as a natural transformation `nat` of the functors
on contexts *together with* a comparison `cmp` of extended contexts over the base, and
`Start/CwaLaxWhisker.lean` records as its boundary that the interchange law between the two
whiskerings cannot be stated, because nothing forces the comparison of one 2-cell to be natural in
the component of another.

This module removes the boundary, by showing that the comparison is not data at all: it is
*uniquely determined* by the natural transformation.  Indeed `cmp Γ A` is a map into
`S.ext (F.fnc.obj Γ) (S.tySub (nat.app Γ) (G.tyMap A))`, which is a pullback, and the two laws of a
lax 2-cell prescribe both of its projections — `extend_app` prescribes the composite with
`S.extend`, and `cmp_disp` the composite with the display map.  Hence:

* `Cwa.LaxTwoCell.ext_of_nat` — two lax 2-cells with the same natural transformation are equal;
* `Cwa.LaxTwoCell.ofNat` — *every* natural transformation of the functors on contexts underlies a
  lax 2-cell, the required commuting square being naturality itself;
* `Cwa.LaxTwoCell.equivNatTrans` — **the lax 2-cells `F ⟶ G` are exactly the natural
  transformations `F.fnc ⟶ G.fnc`**.

So a lax 2-cell carries no information beyond its components, which is what makes the horizontal
and vertical structures interact: everything about a lax 2-cell can be checked on the natural
transformation alone (`Start/CwaLaxInterchange.lean`).

Main results:

* `Cwa.LaxTwoCell.cmp_extend` — the comparison composed with the extension map;
* `Cwa.LaxTwoCell.cmp_eq` — the comparison is the map into the pullback prescribed by the laws;
* `Cwa.LaxTwoCell.ext_of_nat`, `Cwa.LaxTwoCell.equivNatTrans` — the classification.
-/

import Start.CwaLaxCategory

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w'

open CategoryTheory

namespace Cwa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {T : Cwa.{u, v, w} C} {S : Cwa.{u', v', w'} D}

namespace LaxTwoCell

variable {F G : Mor T S}

/-- **The comparison of a lax 2-cell, followed by the extension map**, is the component of the
natural transformation read through the comparison isomorphisms of the two morphisms.  This is
the law `extend_app` with the isomorphism `F.extIso A` cancelled. -/
@[reassoc] theorem cmp_extend (θ : LaxTwoCell F G) (Γ : C) (A : T.Ty Γ) :
    θ.cmp Γ A ≫ S.extend (θ.nat.app Γ) (G.tyMap A)
      = (F.extIso A).inv ≫ θ.nat.app (T.ext Γ A) ≫ (G.extIso A).hom := by
  rw [← θ.extend_app Γ A, Iso.inv_hom_id_assoc]

/-- The square that the component of a natural transformation makes with the display maps: this is
the commuting condition needed to lift it into the pullback defining an extended context. -/
theorem nat_disp_square (F G : Mor T S) (n : F.fnc ⟶ G.fnc) (Γ : C) (A : T.Ty Γ) :
    ((F.extIso A).inv ≫ n.app (T.ext Γ A) ≫ (G.extIso A).hom) ≫ S.disp (G.tyMap A)
      = S.disp (F.tyMap A) ≫ n.app Γ := by
  rw [Category.assoc, Category.assoc, G.extIso_disp, ← n.naturality (T.disp A),
    ← Category.assoc, ← F.extIso_disp A, Iso.inv_hom_id_assoc]

/-- **The comparison of a lax 2-cell is determined by its natural transformation**: it is the map
into the pullback whose projections are prescribed by the two laws. -/
theorem cmp_eq (θ : LaxTwoCell F G) (Γ : C) (A : T.Ty Γ) :
    θ.cmp Γ A
      = (S.isPullback (θ.nat.app Γ) (G.tyMap A)).lift
          ((F.extIso A).inv ≫ θ.nat.app (T.ext Γ A) ≫ (G.extIso A).hom) (S.disp (F.tyMap A))
          (nat_disp_square F G θ.nat Γ A) := by
  refine (S.isPullback (θ.nat.app Γ) (G.tyMap A)).hom_ext ?_ ?_
  · rw [cmp_extend, (S.isPullback (θ.nat.app Γ) (G.tyMap A)).lift_fst]
  · rw [θ.cmp_disp, (S.isPullback (θ.nat.app Γ) (G.tyMap A)).lift_snd]

/-- **A lax 2-cell is determined by its natural transformation.** -/
theorem ext_of_nat {θ ψ : LaxTwoCell F G} (h : θ.nat = ψ.nat) : θ = ψ := by
  obtain ⟨n, c, hd, he⟩ := θ
  obtain ⟨n', c', hd', he'⟩ := ψ
  simp only at h
  subst h
  have hc : c = c' := by
    funext Γ A
    exact (cmp_eq ⟨n, c, hd, he⟩ Γ A).trans (cmp_eq ⟨n, c', hd', he'⟩ Γ A).symm
  subst hc
  rfl

/-- **Every natural transformation of the functors on contexts underlies a lax 2-cell.**  The
comparison is the map into the pullback given by the component at the extended context; the square
it has to satisfy is naturality with respect to the display map. -/
noncomputable def ofNat (F G : Mor T S) (n : F.fnc ⟶ G.fnc) : LaxTwoCell F G where
  nat := n
  cmp Γ A :=
    (S.isPullback (n.app Γ) (G.tyMap A)).lift
      ((F.extIso A).inv ≫ n.app (T.ext Γ A) ≫ (G.extIso A).hom) (S.disp (F.tyMap A))
      (nat_disp_square F G n Γ A)
  cmp_disp Γ A := (S.isPullback (n.app Γ) (G.tyMap A)).lift_snd _ _ _
  extend_app Γ A := by
    rw [(S.isPullback (n.app Γ) (G.tyMap A)).lift_fst, Iso.hom_inv_id_assoc]

@[simp] theorem ofNat_nat (F G : Mor T S) (n : F.fnc ⟶ G.fnc) : (ofNat F G n).nat = n := rfl

@[simp] theorem ofNat_self (θ : LaxTwoCell F G) : ofNat F G θ.nat = θ := ext_of_nat rfl

/-- **The lax 2-cells between two morphisms of models are exactly the natural transformations of
the underlying functors on contexts.** -/
noncomputable def equivNatTrans (F G : Mor T S) : LaxTwoCell F G ≃ (F.fnc ⟶ G.fnc) where
  toFun θ := θ.nat
  invFun n := ofNat F G n
  left_inv θ := ofNat_self θ
  right_inv _ := rfl

/-- Hence there is a lax 2-cell exactly when there is a natural transformation. -/
theorem nonempty_iff_nonempty_natTrans (F G : Mor T S) :
    Nonempty (LaxTwoCell F G) ↔ Nonempty (F.fnc ⟶ G.fnc) :=
  ⟨fun ⟨θ⟩ => ⟨θ.nat⟩, fun ⟨n⟩ => ⟨ofNat F G n⟩⟩

/-- And there is at most one lax 2-cell exactly when there is at most one natural
transformation. -/
theorem subsingleton_iff_subsingleton_natTrans (F G : Mor T S) :
    Subsingleton (LaxTwoCell F G) ↔ Subsingleton (F.fnc ⟶ G.fnc) :=
  (equivNatTrans F G).subsingleton_congr

end LaxTwoCell

end Cwa
