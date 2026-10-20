/-
**Stability of the groupoid Π-type under substitution** (task `M23-GROUPOID-PI`).

* `GrpdModel.fibI_extend` — the inclusion of a fibre commutes with reindexing:
  `fibI (σ ⋙ A) δ ⋙ extend σ A = fibI A (σ.obj δ)`;
* `GrpdModel.trans_reindex` — transport of sections of `e ⋙ B` is transport of sections of `B`
  along the whiskered transformation;
* `GrpdModel.trans_hcongr` — transport is `HEq`-congruent in all its arguments;
* `GrpdModel.PiF_sub` — **Beck–Chevalley for Π**: `σ ⋙ PiF A B = PiF (σ ⋙ A) (extend σ A ⋙ B)`.
-/

import Start.GrpdPi

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace GrpdModel

section Extend

variable {Δ Γ : Type u} [Groupoid.{u} Δ] [Groupoid.{u} Γ] (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd.{u, u})

/-- **The inclusion of a fibre commutes with reindexing.** -/
theorem fibI_extend (δ : Δ) : fibI (σ ⋙ A) δ ⋙ extend σ A = fibI A (σ.obj δ) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b φ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine GHom.hext (σ.map_id δ) ?_
  exact (eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _).symm

end Extend

section Trans

variable {X Y E E' : Type u} [Category.{u} X] [Category.{u} Y] [Category.{u} E] [Category.{u} E']

/-- Transport of sections of `e ⋙ B` is transport of sections of `B` along the whiskered
transformation. -/
theorem trans_reindex (B : E ⥤ Grpd.{u, u}) (e : E' ⥤ E) (K : X ⥤ Y) (i : Y ⥤ E') (j : X ⥤ E')
    (θ : K ⋙ i ⟶ j) :
    trans (e ⋙ B) K i j θ = trans B K (i ⋙ e) (j ⋙ e) (Functor.whiskerRight θ e) := by
  have hobj : ∀ s : Sect (i ⋙ e ⋙ B),
      (trans (e ⋙ B) K i j θ).obj s = (trans B K (i ⋙ e) (j ⋙ e) (Functor.whiskerRight θ e)).obj s := by
    intro s
    refine Sect.hext rfl ?_
    intro x y f
    show HEq ((transObj (e ⋙ B) K i j θ s).map f)
      ((transObj B K (i ⋙ e) (j ⋙ e) (Functor.whiskerRight θ e) s).map f)
    rw [transObj_map, transObj_map]
    exact (eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _).symm
  refine CategoryTheory.Functor.ext hobj ?_
  intro s t α
  refine Sect.hom_ext fun x => ?_
  simp only [Sect.comp_app, Sect.eqToHom_app, trans_app]
  simp

/-- Transport is `HEq`-congruent in all its arguments. -/
theorem trans_hcongr (B : E ⥤ Grpd.{u, u}) {K K' : X ⥤ Y} {i i' : Y ⥤ E} {j j' : X ⥤ E}
    (θ : K ⋙ i ⟶ j) (θ' : K' ⋙ i' ⟶ j') (hK : K = K') (hi : i = i') (hj : j = j')
    (hθ : ∀ x, HEq (θ.app x) (θ'.app x)) :
    HEq (trans B K i j θ) (trans B K' i' j' θ') := by
  subst hK hi hj
  have : θ = θ' := NatTrans.ext (funext fun x => eq_of_heq (hθ x))
  subst this
  rfl

end Trans

section PiSub

variable {Δ Γ : Type u} [Groupoid.{u} Δ] [Groupoid.{u} Γ] (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd.{u, u})
  (B : GObj A ⥤ Grpd.{u, u})

theorem map_groupoidInv {δ δ' : Δ} (g : δ ⟶ δ') :
    σ.map (Groupoid.inv g) = Groupoid.inv (σ.map g) := by
  rw [Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, Functor.map_inv]

/-- **Beck–Chevalley for the groupoid Π-type.** -/
theorem PiF_sub : σ ⋙ PiF A B = PiF (σ ⋙ A) (extend σ A ⋙ B) := by
  have hobj : ∀ δ : Δ, (σ ⋙ PiF A B).obj δ = (PiF (σ ⋙ A) (extend σ A ⋙ B)).obj δ := by
    intro δ
    show Grpd.of (Sect (fibI A (σ.obj δ) ⋙ B)) =
      Grpd.of (Sect ((fibI (σ ⋙ A) δ ⋙ extend σ A) ⋙ B))
    rw [fibI_extend]
  refine CategoryTheory.Functor.hext hobj ?_
  intro δ δ' g
  show HEq (piMap A B (σ.map g)) (piMap (σ ⋙ A) (extend σ A ⋙ B) g)
  unfold piMap
  rw [trans_reindex]
  refine trans_hcongr B _ _ ?_ (fibI_extend σ A δ).symm (fibI_extend σ A δ').symm ?_
  · show A.map (Groupoid.inv (σ.map g)) = A.map (σ.map (Groupoid.inv g))
    rw [map_groupoidInv]
  · intro a
    have hp : (A.map (Groupoid.inv (σ.map g))).obj a = (A.map (σ.map (Groupoid.inv g))).obj a := by
      rw [map_groupoidInv]
    refine GHom.hext' (p := ⟨σ.obj δ, (A.map (Groupoid.inv (σ.map g))).obj a⟩)
      (p' := ⟨σ.obj δ, (A.map (σ.map (Groupoid.inv g))).obj a⟩)
      (GObj.ext' rfl (heq_of_eq hp)) rfl HEq.rfl ?_
    dsimp only [piTheta, Functor.whiskerRight_app, extend]
    exact eqToHom_heq_eqToHom _ _ (congrArg (A.map (σ.map g)).obj hp) rfl

end PiSub

end GrpdModel
