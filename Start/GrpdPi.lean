/-
**The Π-type of the groupoid model** (task `M23-GROUPOID-PI`).

For a groupoid `Γ`, a type `A : Γ ⥤ Grpd` and a family `B : ∫ A ⥤ Grpd`, the dependent product
`PiF A B : Γ ⥤ Grpd` sends `γ` to the groupoid `Sect (fibI A γ ⋙ B)` of sections of `B` over the
fibre `A γ` (`Start/GrpdSect.lean`), and a morphism `g : γ ⟶ γ'` to transport
(`GrpdModel.trans`) along the natural transformation `piTheta`, whose component at `a : A γ'` is
the morphism `(γ, A(g⁻¹) a) ⟶ (γ', a)` of `∫ A` over `g`.

* `fibI A γ : A γ ⥤ ∫ A` — the inclusion of a fibre;
* `piTheta A g : A(g⁻¹) ⋙ fibI A γ ⟶ fibI A γ'` — the comparison of two fibres along `g`;
* `PiF A B : Γ ⥤ Grpd` — **the Π-groupoid and its functoriality** (`map_id` and `map_comp` hold
  strictly, through `trans_id`, `trans_comp` and `trans_congr`).
-/

import Start.GrpdSect

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace GrpdModel

section Fibre

variable {Γ : Type u} [Groupoid.{u} Γ] (A : Γ ⥤ Grpd.{u, u})

/-- The inclusion of the fibre of `A` at `γ` into the Grothendieck construction. -/
def fibI (γ : Γ) : A.obj γ ⥤ GObj A where
  obj a := ⟨γ, a⟩
  map φ := ⟨𝟙 γ, eqToHom (map_id_obj _ _) ≫ φ⟩
  map_id a := GHom.hext rfl (by simp)
  map_comp φ ψ := by
    refine GHom.ext' (Category.comp_id _).symm ?_
    simp only [comp_fib, Category.assoc, map_id_map (A := A)]
    simp

@[simp] theorem fibI_obj (γ : Γ) (a : A.obj γ) : (fibI A γ).obj a = ⟨γ, a⟩ := rfl

@[simp] theorem fibI_map (γ : Γ) {a b : A.obj γ} (φ : a ⟶ b) :
    (fibI A γ).map φ = ⟨𝟙 γ, eqToHom (map_id_obj _ _) ≫ φ⟩ := rfl

/-- The fibre comparison morphism: `(γ, A(g⁻¹) a) ⟶ (γ', a)` over `g : γ ⟶ γ'`. -/
def piTheta {γ γ' : Γ} (g : γ ⟶ γ') : A.map (Groupoid.inv g) ⋙ fibI A γ ⟶ fibI A γ' where
  app a := ⟨g, eqToHom ((map_comp_obj _ _ _).symm.trans
    (by rw [Groupoid.inv_comp, map_id_obj]; rfl))⟩
  naturality {a b} φ := by
    refine GHom.ext' (by simp) ?_
    have key : (A.map g).map ((A.map (Groupoid.inv g)).map φ) =
        eqToHom (map_comp_obj (A := A) (Groupoid.inv g) g a).symm ≫
          (A.map (Groupoid.inv g ≫ g)).map φ ≫
            eqToHom (map_comp_obj (A := A) (Groupoid.inv g) g b) := map_map _ _ _
    simp only [comp_fib, Functor.comp_map, fibI_map, Functor.map_comp, eqToHom_map,
      Category.assoc]
    rw [key, map_congr_map (Groupoid.inv_comp g) φ, map_id_map (A := A) γ' φ]
    simp

end Fibre

section Pi

variable {Γ : Type u} [Groupoid.{u} Γ] (A : Γ ⥤ Grpd.{u, u}) (B : GObj A ⥤ Grpd.{u, u})

/-- The action of `Π A B` on a morphism of the base: transport of sections. -/
def piMap {γ γ' : Γ} (g : γ ⟶ γ') :
    Sect (fibI A γ ⋙ B) ⥤ Sect (fibI A γ' ⋙ B) :=
  trans B (A.map (Groupoid.inv g)) (fibI A γ) (fibI A γ') (piTheta A g)

/-- **The dependent product in the groupoid model**: `Π A B` at `γ` is the groupoid of sections
of `B` over the fibre `A γ`, and a morphism of the base acts by transport. -/
def PiF : Γ ⥤ Grpd.{u, u} where
  obj γ := Grpd.of (Sect (fibI A γ ⋙ B))
  map g := piMap A B g
  map_id γ := by
    have hobj : ∀ a : A.obj γ, (A.map (Groupoid.inv (𝟙 γ))).obj a = a := by
      intro a
      rw [Groupoid.inv_eq_inv, IsIso.inv_id]
      exact map_id_obj γ a
    have hK : A.map (Groupoid.inv (𝟙 γ)) = 𝟭 (A.obj γ) := by
      rw [Groupoid.inv_eq_inv, IsIso.inv_id]
      exact A.map_id γ
    refine Eq.trans (trans_congr B (K := A.map (Groupoid.inv (𝟙 γ))) (K' := 𝟭 (A.obj γ))
      (piTheta A (𝟙 γ)) (𝟙 (fibI A γ)) hK ?_) (trans_id B (fibI A γ))
    intro a
    refine GHom.hext' (p := ⟨γ, (A.map (Groupoid.inv (𝟙 γ))).obj a⟩) (p' := ⟨γ, a⟩)
      (GObj.ext' rfl (heq_of_eq (hobj a))) rfl HEq.rfl ?_
    exact eqToHom_heq_eqToHom
      ((map_comp_obj (A := A) (Groupoid.inv (𝟙 γ)) (𝟙 γ) a).symm.trans
        (by rw [Groupoid.inv_comp, map_id_obj]; rfl))
      (map_id_obj (A := A) γ a) (congrArg (A.map (𝟙 γ)).obj (hobj a)) rfl
  map_comp {γ γ' γ''} g h := by
    have hK : A.map (Groupoid.inv (g ≫ h)) =
        A.map (Groupoid.inv h) ⋙ A.map (Groupoid.inv g) := by
      rw [Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, IsIso.inv_comp]
      exact A.map_comp (CategoryTheory.inv h) (CategoryTheory.inv g)
    refine Eq.trans (trans_congr B (piTheta A (g ≫ h))
      (Functor.whiskerLeft (A.map (Groupoid.inv h)) (piTheta A g) ≫ piTheta A h) hK ?_)
      (trans_comp B (A.map (Groupoid.inv g)) (A.map (Groupoid.inv h)) (fibI A γ) (fibI A γ')
        (fibI A γ'') (piTheta A g) (piTheta A h)).symm
    intro a
    have hobj : (A.map (Groupoid.inv (g ≫ h))).obj a =
        (A.map (Groupoid.inv g)).obj ((A.map (Groupoid.inv h)).obj a) := by
      rw [hK]; rfl
    have hp2 : (A.map (g ≫ h)).obj
        ((A.map (Groupoid.inv g)).obj ((A.map (Groupoid.inv h)).obj a)) = a := by
      rw [← hobj]
      exact (map_comp_obj _ _ _).symm.trans (by rw [Groupoid.inv_comp, map_id_obj])
    refine GHom.hext' (p := ⟨γ, (A.map (Groupoid.inv (g ≫ h))).obj a⟩)
      (p' := ⟨γ, (A.map (Groupoid.inv g)).obj ((A.map (Groupoid.inv h)).obj a)⟩)
      (GObj.ext' rfl (heq_of_eq hobj)) rfl HEq.rfl ?_
    have hr : ((Functor.whiskerLeft (A.map (Groupoid.inv h)) (piTheta A g) ≫
        piTheta A h).app a).fib = eqToHom hp2 := by
      simp [piTheta, eqToHom_map]
    rw [hr]
    exact eqToHom_heq_eqToHom
      ((map_comp_obj (A := A) (Groupoid.inv (g ≫ h)) (g ≫ h) a).symm.trans
        (by rw [Groupoid.inv_comp, map_id_obj]; rfl))
      hp2 (congrArg (A.map (g ≫ h)).obj hobj) rfl

end Pi

end GrpdModel
