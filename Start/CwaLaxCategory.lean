/-
**The lax 2-cells between morphisms of categories with attributes form a category.**

`Start/CwaLaxTwoCell.lean` introduces the lax 2-cells — a natural transformation of the functors on
contexts together with a comparison of extended contexts *over the base*, in place of the equality
of types demanded by a strict 2-cell — with an identity and a vertical composite.  It does not
check the laws.  This module does: vertical composition of lax 2-cells is associative and unital,
so the morphisms `T ⟶ S` and the lax 2-cells between them form a category
(`Cwa.laxMorCategory`), and the inclusion of the strict 2-cells into the lax ones is a functor
(`Cwa.laxInclusion`).

The proofs run through the calculus of the substituted map `Cwa.subOver`: it is functorial
(`Cwa.subOver_id`, `Cwa.subOver_comp`) and carries a transport to a transport
(`Cwa.subOver_eqToHom`).

Main definitions:

* `Cwa.laxMorCategory` — **the category of morphisms and lax 2-cells**;
* `Cwa.laxInclusion` — the functor from the category of strict 2-cells to it.

Main results:

* `Cwa.subOver_id`, `Cwa.subOver_comp`, `Cwa.subOver_eqToHom` — functoriality of the substituted
  map of extended contexts;
* `Cwa.LaxTwoCell.ext_of_cmp` — a lax 2-cell is determined by its natural transformation and its
  comparison, up to the transport along the equality of the two natural transformations;
* `Cwa.LaxTwoCell.id_vcomp`, `Cwa.LaxTwoCell.vcomp_id`, `Cwa.LaxTwoCell.vcomp_assoc` — the
  category laws;
* `Cwa.TwoCell.toLax_id`, `Cwa.TwoCell.toLax_vcomp`, `Cwa.TwoCell.toLax_injective` — the inclusion
  of the strict 2-cells preserves identities and vertical composition, and is injective.
-/

import Start.CwaLaxTwoCell

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w'

open CategoryTheory

namespace Cwa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {T : Cwa.{u, v, w} C} {S : Cwa.{u', v', w'} D}

/-- Two chains of transports with the same ends, around the same morphisms, agree.  This is the
shape in which the transports of a triple vertical composite cancel. -/
private theorem eqToHom_chain_eq {V W X₀ X₁ X₂ X₃ X₄ X₅ X₆ : D} (f₁ : V ⟶ W) (f₂ : W ⟶ X₀)
    (p : X₀ = X₁) (q : X₁ = X₀) (g : X₀ ⟶ X₂) (r : X₂ = X₃) (s : X₃ = X₄) (t : X₄ = X₅)
    (u : X₂ = X₆) (v : X₆ = X₅) :
    f₁ ≫ f₂ ≫ eqToHom p ≫ eqToHom q ≫ g ≫ eqToHom r ≫ eqToHom s ≫ eqToHom t
      = f₁ ≫ f₂ ≫ g ≫ eqToHom u ≫ eqToHom v := by
  cases p
  cases r
  cases s
  cases t
  cases u
  have hq : q = rfl := rfl
  have hv : v = rfl := rfl
  rw [hq, hv]
  simp

/-- Two chains of transports with the same ends agree. -/
private theorem eqToHom_chain_eq_chain {X₀ X₁ X₂ Y₁ Y₂ : D} (p : X₀ = X₁) (q : X₁ = X₂)
    (r : X₀ = Y₁) (s : Y₁ = Y₂) (t : Y₂ = X₂) :
    eqToHom p ≫ eqToHom q = eqToHom r ≫ eqToHom s ≫ eqToHom t := by
  cases p
  cases q
  cases r
  cases s
  have ht : t = rfl := rfl
  rw [ht]
  simp

/-! ### Functoriality of the substituted map of extended contexts -/

/-- **The substituted map of an identity is the identity.** -/
theorem subOver_id {Δ Γ : D} (σ : Δ ⟶ Γ) (A : S.Ty Γ) :
    S.subOver σ (𝟙 (S.ext Γ A)) (Category.id_comp _) = 𝟙 (S.ext Δ (S.tySub σ A)) := by
  refine (S.isPullback σ A).hom_ext ?_ ?_
  · rw [subOver_extend, Category.comp_id, Category.id_comp]
  · rw [subOver_disp, Category.id_comp]

/-- **The substituted map of a composite is the composite of the substituted maps.** -/
theorem subOver_comp {Δ Γ : D} (σ : Δ ⟶ Γ) {A B E : S.Ty Γ}
    (u : S.ext Γ A ⟶ S.ext Γ B) (hu : u ≫ S.disp B = S.disp A)
    (v : S.ext Γ B ⟶ S.ext Γ E) (hv : v ≫ S.disp E = S.disp B) :
    S.subOver σ (u ≫ v) (by rw [Category.assoc, hv, hu]) =
      S.subOver σ u hu ≫ S.subOver σ v hv := by
  refine (S.isPullback σ E).hom_ext ?_ ?_
  · simp only [subOver_extend, Category.assoc, subOver_extend_assoc]
  · rw [subOver_disp, Category.assoc, subOver_disp, subOver_disp]

/-- **The substituted map of a transport is the transport.** -/
theorem subOver_eqToHom {Δ Γ : D} (σ : Δ ⟶ Γ) {A B : S.Ty Γ} (e : A = B) :
    S.subOver σ (eqToHom (congrArg (S.ext Γ) e)) (eqToHom_ext_disp e)
      = eqToHom (congrArg (S.ext Δ) (congrArg (S.tySub σ) e)) := by
  cases e
  simpa using subOver_id σ A

/-- **Substituting along the identity** acts by the transports along `tySub_id`. -/
theorem subOver_id_sub (coh : ExtCoherent S) {Γ : D} {A B : S.Ty Γ}
    (u : S.ext Γ A ⟶ S.ext Γ B) (hu : u ≫ S.disp B = S.disp A) :
    S.subOver (𝟙 Γ) u hu
      = eqToHom (congrArg (S.ext Γ) (S.tySub_id A)) ≫ u
          ≫ eqToHom (congrArg (S.ext Γ) (S.tySub_id B).symm) := by
  refine (S.isPullback (𝟙 Γ) B).hom_ext ?_ ?_
  · rw [subOver_extend, coh.extend_id, coh.extend_id]
    simp
  · rw [subOver_disp, Category.assoc, Category.assoc,
      eqToHom_ext_disp (T := S) (S.tySub_id B).symm, hu,
      eqToHom_ext_disp (T := S) (S.tySub_id A)]

/-- **Substituting along a composite** is substituting twice, up to the transports along
`tySub_comp`. -/
theorem subOver_subOver (coh : ExtCoherent S) {Θ Δ Γ : D} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    {A B : S.Ty Γ} (u : S.ext Γ A ⟶ S.ext Γ B) (hu : u ≫ S.disp B = S.disp A) :
    S.subOver (τ ≫ σ) u hu
      = eqToHom (congrArg (S.ext Θ) (S.tySub_comp σ τ A))
        ≫ S.subOver τ (S.subOver σ u hu) (subOver_disp σ u hu)
        ≫ eqToHom (congrArg (S.ext Θ) (S.tySub_comp σ τ B).symm) := by
  refine (S.isPullback (τ ≫ σ) B).hom_ext ?_ ?_
  · rw [subOver_extend, coh.extend_comp σ τ B, coh.extend_comp σ τ A]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      subOver_extend_assoc, subOver_extend]
  · rw [subOver_disp, Category.assoc, Category.assoc,
      eqToHom_ext_disp (T := S) (S.tySub_comp σ τ B).symm, subOver_disp,
      eqToHom_ext_disp (T := S) (S.tySub_comp σ τ A)]

/-- **Substituting along a morphism equal to the identity** acts by the transports along
`tySub_id`. -/
theorem subOver_eq_of_eq_id (coh : ExtCoherent S) {Γ : D} {σ : Γ ⟶ Γ} (hσ : σ = 𝟙 Γ)
    {A B : S.Ty Γ} (u : S.ext Γ A ⟶ S.ext Γ B) (hu : u ≫ S.disp B = S.disp A) :
    S.subOver σ u hu
      = eqToHom (congrArg (S.ext Γ) (show S.tySub σ A = A by rw [hσ]; exact S.tySub_id A)) ≫ u
          ≫ eqToHom (congrArg (S.ext Γ) (show B = S.tySub σ B by rw [hσ]; exact
              (S.tySub_id B).symm)) := by
  subst hσ
  exact subOver_id_sub coh u hu

/-- **Substituting a map that is a transport** gives the transport. -/
theorem subOver_eq_eqToHom {Δ Γ : D} (σ : Δ ⟶ Γ) {A B : S.Ty Γ} (u : S.ext Γ A ⟶ S.ext Γ B)
    (hu : u ≫ S.disp B = S.disp A) (e : A = B) (hue : u = eqToHom (congrArg (S.ext Γ) e)) :
    S.subOver σ u hu = eqToHom (congrArg (S.ext Δ) (congrArg (S.tySub σ) e)) := by
  subst hue
  exact subOver_eqToHom σ e

/-- The substituted map only depends on the map. -/
theorem subOver_congr {Δ Γ : D} (σ : Δ ⟶ Γ) {A B : S.Ty Γ} {u u' : S.ext Γ A ⟶ S.ext Γ B}
    (hu : u ≫ S.disp B = S.disp A) (h : u = u') :
    S.subOver σ u hu = S.subOver σ u' (h ▸ hu) := by
  subst h
  rfl

/-- **Substituting along a morphism equal to a composite** is substituting twice, up to the
transports along `tySub_comp`. -/
theorem subOver_eq_of_eq_comp (coh : ExtCoherent S) {Θ Δ Γ : D} {σ : Δ ⟶ Γ} {τ : Θ ⟶ Δ}
    {ρ : Θ ⟶ Γ} (hρ : ρ = τ ≫ σ) {A B : S.Ty Γ} (u : S.ext Γ A ⟶ S.ext Γ B)
    (hu : u ≫ S.disp B = S.disp A) :
    S.subOver ρ u hu
      = eqToHom (congrArg (S.ext Θ)
            (show S.tySub ρ A = S.tySub τ (S.tySub σ A) by rw [hρ]; exact S.tySub_comp σ τ A))
        ≫ S.subOver τ (S.subOver σ u hu) (subOver_disp σ u hu)
        ≫ eqToHom (congrArg (S.ext Θ)
            (show S.tySub τ (S.tySub σ B) = S.tySub ρ B by
              rw [hρ]; exact (S.tySub_comp σ τ B).symm)) := by
  subst hρ
  exact subOver_subOver coh σ τ u hu

/-! ### Cancelling transports

A composite of transports whose two ends agree is the identity.  These are `eqToHom_trans` and
`eqToHom_refl` packaged so that they apply to a chain in one step; the packaged form is what is
needed below, where the proofs of the equalities are not syntactically `rfl`. -/

/-- A chain of transports around a morphism, returning to its two ends, is the morphism. -/
private theorem eqToHom_cancel_left_right {X Y Z W V : D} (p : X = Y) (q : Y = X) (f : X ⟶ Z)
    (r : Z = W) (s : W = V) (t : V = Z) :
    eqToHom p ≫ eqToHom q ≫ f ≫ eqToHom r ≫ eqToHom s ≫ eqToHom t = f := by
  cases p
  cases r
  cases s
  have hq : q = rfl := rfl
  have ht : t = rfl := rfl
  rw [hq, ht]
  simp

/-- A chain of transports after a morphism, returning to its target, is the morphism. -/
private theorem comp_eqToHom_cancel {X Y Z W : D} (f : X ⟶ Y) (p : Y = Z) (q : Z = W)
    (r : W = Y) : f ≫ eqToHom p ≫ eqToHom q ≫ eqToHom r = f := by
  cases p
  cases q
  have hr : r = rfl := rfl
  rw [hr]
  simp

/-! ### The category laws for lax 2-cells -/

namespace LaxTwoCell

variable {F G H K : Mor T S}

/-- **A lax 2-cell is determined by its natural transformation and its comparison**, the latter
compared after the transport along the equality of the natural transformations. -/
theorem ext_of_cmp {θ ψ : LaxTwoCell F G} (h : θ.nat = ψ.nat)
    (h' : ∀ (Γ : C) (A : T.Ty Γ),
      θ.cmp Γ A ≫ eqToHom (congrArg (S.ext (F.fnc.obj Γ)) (by rw [h])) = ψ.cmp Γ A) :
    θ = ψ := by
  obtain ⟨n₁, c₁, d₁, e₁⟩ := θ
  obtain ⟨n₂, c₂, d₂, e₂⟩ := ψ
  cases h
  have hc : c₁ = c₂ := by
    funext Γ A
    simpa using h' Γ A
  cases hc
  rfl

/-- The comparison of a vertical composite. -/
theorem vcomp_cmp (coh : ExtCoherent S) (θ : LaxTwoCell F G) (ψ : LaxTwoCell G H) (Γ : C)
    (A : T.Ty Γ) :
    (θ.vcomp coh ψ).cmp Γ A
      = θ.cmp Γ A ≫ S.subOver (θ.nat.app Γ) (ψ.cmp Γ A) (ψ.cmp_disp Γ A)
          ≫ eqToHom (congrArg (S.ext (F.fnc.obj Γ))
              (show S.tySub (θ.nat.app Γ) (S.tySub (ψ.nat.app Γ) (H.tyMap A))
                  = S.tySub ((θ.vcomp coh ψ).nat.app Γ) (H.tyMap A) from
                (S.tySub_comp (ψ.nat.app Γ) (θ.nat.app Γ) (H.tyMap A)).symm)) :=
  rfl

/-- The comparison of the identity lax 2-cell is the transport along `tySub_id`. -/
theorem id_cmp (coh : ExtCoherent S) (F : Mor T S) (Γ : C) (A : T.Ty Γ) :
    (LaxTwoCell.id coh F).cmp Γ A
      = eqToHom (congrArg (S.ext (F.fnc.obj Γ))
          (show F.tyMap A = S.tySub ((LaxTwoCell.id coh F).nat.app Γ) (F.tyMap A) from
            (S.tySub_id (F.tyMap A)).symm)) :=
  rfl

/-- **Vertical composition with the identity on the left.** -/
theorem id_vcomp (coh : ExtCoherent S) (θ : LaxTwoCell F G) :
    (LaxTwoCell.id coh F).vcomp coh θ = θ := by
  refine ext_of_cmp (Category.id_comp _) ?_
  intro Γ A
  rw [vcomp_cmp, subOver_eq_of_eq_id coh
    (σ := (LaxTwoCell.id coh F).nat.app Γ) rfl, id_cmp]
  simp only [Category.assoc]
  exact eqToHom_cancel_left_right _ _ _ _ _ _

/-- **Vertical composition with the identity on the right.** -/
theorem vcomp_id (coh : ExtCoherent S) (θ : LaxTwoCell F G) :
    θ.vcomp coh (LaxTwoCell.id coh G) = θ := by
  refine ext_of_cmp (Category.comp_id _) ?_
  intro Γ A
  rw [vcomp_cmp, subOver_eq_eqToHom _ _ _
    (show G.tyMap A = S.tySub ((LaxTwoCell.id coh G).nat.app Γ) (G.tyMap A) from
      (S.tySub_id (G.tyMap A)).symm) (id_cmp coh G Γ A)]
  simp only [Category.assoc]
  exact comp_eqToHom_cancel _ _ _ _

/-- **Vertical composition of lax 2-cells is associative.** -/
theorem vcomp_assoc (coh : ExtCoherent S) (θ : LaxTwoCell F G) (ψ : LaxTwoCell G H)
    (ξ : LaxTwoCell H K) :
    (θ.vcomp coh ψ).vcomp coh ξ = θ.vcomp coh (ψ.vcomp coh ξ) := by
  refine ext_of_cmp (Category.assoc _ _ _) ?_
  intro Γ A
  have e₀ : S.tySub (ψ.nat.app Γ) (S.tySub (ξ.nat.app Γ) (K.tyMap A))
      = S.tySub ((ψ.vcomp coh ξ).nat.app Γ) (K.tyMap A) :=
    (S.tySub_comp (ξ.nat.app Γ) (ψ.nat.app Γ) (K.tyMap A)).symm
  rw [vcomp_cmp, vcomp_cmp, vcomp_cmp,
    subOver_congr (θ.nat.app Γ) _ (vcomp_cmp coh ψ ξ Γ A), subOver_comp, subOver_comp,
    subOver_eqToHom (θ.nat.app Γ) e₀,
    subOver_eq_of_eq_comp coh (ρ := (θ.vcomp coh ψ).nat.app Γ) rfl]
  · simp only [Category.assoc]
    exact eqToHom_chain_eq _ _ _ _ _ _ _ _ _ _
  all_goals first
    | exact ψ.cmp_disp Γ A
    | exact eqToHom_ext_disp (T := S) e₀
    | exact subOver_disp _ _ _
    | rw [Category.assoc, eqToHom_ext_disp (T := S) e₀, subOver_disp]

end LaxTwoCell

namespace TwoCell

variable {F G H : Mor T S}

/-- The identity 2-cell is the identity lax 2-cell. -/
theorem toLax_id (coh : ExtCoherent S) (F : Mor T S) :
    (TwoCell.id coh F).toLax = LaxTwoCell.id coh F := rfl

/-- The comparison of the lax 2-cell of a strict one is the transport along its action on
types. -/
theorem toLax_cmp (θ : TwoCell F G) (Γ : C) (A : T.Ty Γ) :
    θ.toLax.cmp Γ A
      = eqToHom (congrArg (S.ext (F.fnc.obj Γ))
          (show F.tyMap A = S.tySub (θ.toLax.nat.app Γ) (G.tyMap A) from
            (θ.tySub_app A).symm)) :=
  rfl

/-- **The inclusion of the strict 2-cells into the lax ones preserves vertical composition.** -/
theorem toLax_vcomp (coh : ExtCoherent S) (θ : TwoCell F G) (ψ : TwoCell G H) :
    (θ.vcomp coh ψ).toLax = θ.toLax.vcomp coh ψ.toLax := by
  refine LaxTwoCell.ext_of_cmp rfl ?_
  intro Γ A
  rw [LaxTwoCell.vcomp_cmp, subOver_eq_eqToHom _ _ _
    (show G.tyMap A = S.tySub (ψ.toLax.nat.app Γ) (H.tyMap A) from (ψ.tySub_app A).symm)
    (toLax_cmp ψ Γ A), toLax_cmp θ Γ A, toLax_cmp (θ.vcomp coh ψ) Γ A]
  exact eqToHom_chain_eq_chain _ _ _ _ _

/-- **A strict 2-cell is determined by the lax 2-cell it becomes**: the inclusion is faithful. -/
theorem toLax_injective : Function.Injective (TwoCell.toLax (T := T) (S := S) (F := F) (G := G)) :=
  fun _ _ h => TwoCell.ext (congrArg LaxTwoCell.nat h)

end TwoCell

/-- **The morphisms between two categories with attributes and the lax 2-cells between them form a
category.** -/
@[instance_reducible]
noncomputable def laxMorCategory (coh : ExtCoherent S) : Category.{max u v' w} (Mor T S) where
  Hom F G := LaxTwoCell F G
  id F := LaxTwoCell.id coh F
  comp θ ψ := θ.vcomp coh ψ
  id_comp θ := LaxTwoCell.id_vcomp coh θ
  comp_id θ := LaxTwoCell.vcomp_id coh θ
  assoc θ ψ ξ := LaxTwoCell.vcomp_assoc coh θ ψ ξ

/-- **The inclusion of the strict 2-cells into the lax ones is a functor.** -/
noncomputable def laxInclusion (coh : ExtCoherent S) :
    @Functor (Mor T S) (morCategory (T := T) coh) (Mor T S) (laxMorCategory (T := T) coh) :=
  letI := morCategory (T := T) coh
  letI := laxMorCategory (T := T) coh
  { obj := fun F => F
    map := fun θ => TwoCell.toLax θ
    map_id := fun F => TwoCell.toLax_id coh F
    map_comp := fun θ ψ => TwoCell.toLax_vcomp coh θ ψ }

end Cwa
