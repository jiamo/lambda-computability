/-
**Towards Σ-types in the groupoid model** — task `M23-GROUPOID-SIGMA` (round 8, part D).

For a groupoid `Γ`, a type `A : Γ ⥤ Grpd` and a family `B : ∫ A ⥤ Grpd`, the dependent sum
`Σ A B` sends `γ` to the Grothendieck construction `∫ (fibI A γ ⋙ B)` of `B` restricted to the
fibre `A γ`.  Its action on a morphism `g : γ ⟶ γ'` is the composite of the two Grothendieck
functorialities (Mathlib's `Grothendieck.map` and `Grothendieck.pre`, here for this library's
`GObj`): change of base along `A g : A γ ⥤ A γ'`, and the fibre transformation
`fibI A γ ⟶ A g ⋙ fibI A γ'` whose component at `a` is `(g, 𝟙) : (γ, a) ⟶ (γ', A g a)`.

* `GrpdModel.sigMap K F G θ B` — **the generic Grothendieck functoriality**: for `K : C ⥤ D`,
  `F : C ⥤ X`, `G : D ⥤ X` and `θ : F ⟶ K ⋙ G`, a functor `∫ (F ⋙ B) ⥤ ∫ (G ⋙ B)` sending
  `(c, b)` to `(K c, B(θ_c) b)`, with its functor laws;
* `GrpdModel.sigTheta A g` — the fibre transformation along `g`;
* `GrpdModel.sigObj`, `GrpdModel.sigMapG` — the object part and the morphism part of the functor
  `SigF A B : Γ ⥤ Grpd`.

Open: the functor laws of `SigF` (`map_id` and `map_comp`, equalities of functors between
Grothendieck constructions up to the `eqToHom` coherences of `A.map_comp`), then the pairing
isomorphism `∫ B ≅ ∫ (SigF A B)` over `Γ` and `GrpdModel.grpdSigmaStruct`.
-/

import Start.GrpdPi

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace GrpdModel

section SigMap

variable {C D X : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} X]
variable (K : C ⥤ D) (F : C ⥤ X) (G : D ⥤ X) (θ : F ⟶ K ⋙ G) (B : X ⥤ Grpd.{u, u})

theorem sigMap_obj_eq {c c' : C} (f : c ⟶ c') (b : B.obj (F.obj c)) :
    ((G ⋙ B).map (K.map f)).obj ((B.map (θ.app c)).obj b) =
      (B.map (θ.app c')).obj (((F ⋙ B).map f).obj b) := by
  simp only [Functor.comp_map]
  rw [← map_comp_obj (A := B), ← map_comp_obj (A := B)]
  have := θ.naturality f
  simp only [Functor.comp_map] at this
  rw [this]

theorem sigMap_key {c c' : C} (g : c ⟶ c') {x y : B.obj (F.obj c)} (φ : x ⟶ y) :
    (B.map (θ.app c')).map ((B.map (F.map g)).map φ) =
      eqToHom (sigMap_obj_eq K F G θ B g x).symm ≫
        (B.map (G.map (K.map g))).map ((B.map (θ.app c)).map φ) ≫
          eqToHom (sigMap_obj_eq K F G θ B g y) := by
  have hn : F.map g ≫ θ.app c' = θ.app c ≫ G.map (K.map g) := θ.naturality g
  rw [map_map (A := B), map_map (A := B), map_congr_map (A := B) hn]
  simp

/-- **The generic Grothendieck functoriality**: change of base along `K` and of the fibre
functor along `θ`. -/
def sigMap : GObj (F ⋙ B) ⥤ GObj (G ⋙ B) where
  obj p := ⟨K.obj p.base, (B.map (θ.app p.base)).obj p.fib⟩
  map {p q} f := ⟨K.map f.base, eqToHom (sigMap_obj_eq K F G θ B f.base p.fib) ≫
    (B.map (θ.app q.base)).map f.fib⟩
  map_id p := by
    refine GHom.hext (K.map_id _) ?_
    simp only [id_fib, eqToHom_map, eqToHom_trans]
    exact eqToHom_heq_eqToHom _ _ (by simp) rfl
  map_comp {p q r} f g := by
    refine GHom.ext' (K.map_comp _ _) ?_
    simp only [comp_fib, Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc]
    simp only [Functor.comp_map] at *
    rw [sigMap_key K F G θ B g.base f.fib]
    simp

end SigMap

section SigF

variable {Γ : Type u} [Groupoid.{u} Γ] (A : Γ ⥤ Grpd.{u, u}) (B : GObj A ⥤ Grpd.{u, u})

/-- The fibre transformation along `g : γ ⟶ γ'`: its component at `a` is the morphism
`(g, 𝟙) : (γ, a) ⟶ (γ', A g a)` of `∫ A`. -/
def sigTheta {γ γ' : Γ} (g : γ ⟶ γ') : fibI A γ ⟶ A.map g ⋙ fibI A γ' where
  app a := ⟨g, 𝟙 _⟩
  naturality {a b} φ := by
    refine GHom.ext' (by simp) ?_
    simp only [comp_fib, Functor.comp_map, fibI_map, Functor.map_comp, eqToHom_map,
      Category.comp_id]
    simp

/-- The object part of `Σ A B`: the Grothendieck construction of `B` over the fibre `A γ`. -/
def sigObj (γ : Γ) : Grpd.{u, u} := Grpd.of (GObj (fibI A γ ⋙ B))

/-- The morphism part of `Σ A B`: the generic Grothendieck functoriality along `A g` and
`sigTheta A g`. -/
def sigMapG {γ γ' : Γ} (g : γ ⟶ γ') : sigObj A B γ ⟶ sigObj A B γ' :=
  sigMap (A.map g) (fibI A γ) (fibI A γ') (sigTheta A g) B

/-- The base component of `sigMapG` is `A g`. -/
theorem sigMapG_disp {γ γ' : Γ} (g : γ ⟶ γ') :
    (sigMapG A B g : GObj (fibI A γ ⋙ B) ⥤ GObj (fibI A γ' ⋙ B)) ⋙ disp (fibI A γ' ⋙ B) =
      disp (fibI A γ ⋙ B) ⋙ A.map g := rfl

end SigF

end GrpdModel
