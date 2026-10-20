/-
**The functor laws of `Σ A B` in the groupoid model** — task `M23-GROUPOID-SIGMA` (round 9,
part D), continuing `Start/GrpdSigma.lean`.

* `GrpdModel.sigTheta_id` — the fibre transformation along `𝟙 γ` is an `eqToHom`;
* `GrpdModel.sigTheta_comp` — the fibre transformation along `g ≫ g'` is the composite of the
  two, up to the `eqToHom` coherence of `A.map_comp`;
* `GrpdModel.map_eqToHom_obj_heq`, `GrpdModel.map_eqToHom_map_heq`,
  `GrpdModel.map_comp_eq_obj_heq`, `GrpdModel.map_comp_eq_map_heq` — transport lemmas for the
  family `B` along such morphisms;
* `GrpdModel.sigMapG_id` and `GrpdModel.sigMapG_comp` — **the functor laws** of the morphism part
  of `Σ A B`;
* `GrpdModel.SigF A B : Γ ⥤ Grpd` — **the dependent sum as a functor**.
-/

import Start.GrpdSigma

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace GrpdModel

section Transport

variable {C : Type u} [Category.{u} C] (B : C ⥤ Grpd.{u, u})

theorem grpd_eqToHom_obj_heq {X Y : Grpd.{u, u}} (e : X = Y) (x : X) :
    HEq ((eqToHom e).obj x) x := by
  subst e; rfl

/-- The family `B` along a morphism which is an `eqToHom`, on objects. -/
theorem map_eqToHom_obj_heq {P Q : C} (m : P ⟶ Q) (h : P = Q) (hm : m = eqToHom h)
    (x : B.obj P) : HEq ((B.map m).obj x) x := by
  subst h; subst hm
  rw [eqToHom_refl, B.map_id]
  rfl

/-- The family `B` along a morphism which is an `eqToHom`, on morphisms. -/
theorem map_eqToHom_map_heq {P Q : C} (m : P ⟶ Q) (h : P = Q) (hm : m = eqToHom h)
    {x y : B.obj P} (φ : x ⟶ y) : HEq ((B.map m).map φ) φ := by
  subst h; subst hm
  rw [eqToHom_refl, B.map_id]
  rfl

/-- The family `B` along two morphisms equal up to an `eqToHom` of the target, on objects. -/
theorem map_comp_eq_obj_heq {P Q Q' : C} (m₁ : P ⟶ Q) (m₂ : P ⟶ Q') (h : Q = Q')
    (hm : m₁ ≫ eqToHom h = m₂) (x : B.obj P) : HEq ((B.map m₁).obj x) ((B.map m₂).obj x) := by
  subst h; subst hm
  simp

/-- The family `B` along two morphisms equal up to an `eqToHom` of the target, on morphisms. -/
theorem map_comp_eq_map_heq {P Q Q' : C} (m₁ : P ⟶ Q) (m₂ : P ⟶ Q') (h : Q = Q')
    (hm : m₁ ≫ eqToHom h = m₂) {x y : B.obj P} (φ : x ⟶ y) :
    HEq ((B.map m₁).map φ) ((B.map m₂).map φ) := by
  subst h; subst hm
  rw [eqToHom_refl, Category.comp_id]

theorem grpd_map_eqToHom_comp_heq {X Y : Grpd.{u, u}} (F : X ⟶ Y) {x x' y : X} (h : x = x')
    (φ : x' ⟶ y) : HEq (F.map (eqToHom h ≫ φ)) (F.map φ) := by
  subst h
  simp

end Transport

section SigF

variable {Γ : Type u} [Groupoid.{u} Γ] (A : Γ ⥤ Grpd.{u, u}) (B : GObj A ⥤ Grpd.{u, u})

theorem eqToHom_fib_heq {p q : GObj A} (h : p = q) : HEq (GHom.fib (eqToHom h)) (𝟙 q.fib) := by
  subst h
  simp only [eqToHom_refl, id_fib]
  exact eqToHom_heq_id_cod _ _ _

/-- The fibre transformation along `𝟙 γ` is an `eqToHom`. -/
theorem sigTheta_id (γ : Γ) (a : A.obj γ) :
    (sigTheta A (𝟙 γ)).app a =
      eqToHom (GObj.ext' rfl (heq_of_eq (map_id_obj γ a).symm) :
        (⟨γ, a⟩ : GObj A) = ⟨γ, (A.map (𝟙 γ)).obj a⟩) := by
  refine GHom.hext ?_ ?_
  · rw [eqToHom_base]; rfl
  · exact (eqToHom_fib_heq A _).symm

/-- The fibre transformation along `g ≫ g'` is the composite, up to `A.map_comp`. -/
theorem sigTheta_comp {γ γ' γ'' : Γ} (g : γ ⟶ γ') (g' : γ' ⟶ γ'') (a : A.obj γ) :
    (sigTheta A (g ≫ g')).app a ≫
        eqToHom (GObj.ext' rfl (heq_of_eq (map_comp_obj g g' a)) :
          (⟨γ'', (A.map (g ≫ g')).obj a⟩ : GObj A) = ⟨γ'', (A.map g').obj ((A.map g).obj a)⟩) =
      (sigTheta A g).app a ≫ (sigTheta A g').app ((A.map g).obj a) := by
  refine GHom.hext ?_ ?_
  · simp only [comp_base, eqToHom_base]
    simp [sigTheta]
  · simp only [comp_fib, sigTheta]
    refine (eqToHom_comp_heq _ _).trans ?_
    refine HEq.trans ?_ (eqToHom_comp_heq _ _).symm
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    exact eqToHom_fib_heq A _

/-- **The identity law of `Σ A B`.** -/
theorem sigMapG_id (γ : Γ) : sigMapG A B (𝟙 γ) = 𝟙 (sigObj A B γ) := by
  refine functor_ext ?_ (fun p => ?_) (fun {p q} f => ?_)
  · show disp (fibI A γ ⋙ B) ⋙ A.map (𝟙 γ) = 𝟭 _ ⋙ disp (fibI A γ ⋙ B)
    rw [A.map_id]
    rfl
  · exact map_eqToHom_obj_heq B _ _ (sigTheta_id A γ p.base) _
  · show HEq (eqToHom _ ≫ (B.map ((sigTheta A (𝟙 γ)).app q.base)).map f.fib) f.fib
    refine (eqToHom_comp_heq _ _).trans ?_
    exact map_eqToHom_map_heq B _ _ (sigTheta_id A γ q.base) _

/-- **The composition law of `Σ A B`.** -/
theorem sigMapG_comp {γ γ' γ'' : Γ} (g : γ ⟶ γ') (g' : γ' ⟶ γ'') :
    sigMapG A B (g ≫ g') = sigMapG A B g ≫ sigMapG A B g' := by
  refine functor_ext ?_ (fun p => ?_) (fun {p q} f => ?_)
  · show disp (fibI A γ ⋙ B) ⋙ A.map (g ≫ g') =
      (disp (fibI A γ ⋙ B) ⋙ A.map g) ⋙ A.map g'
    rw [A.map_comp]
    rfl
  · show HEq ((B.map ((sigTheta A (g ≫ g')).app p.base)).obj p.fib)
      ((B.map ((sigTheta A g').app ((A.map g).obj p.base))).obj
        ((B.map ((sigTheta A g).app p.base)).obj p.fib))
    refine (map_comp_eq_obj_heq B _ _ _ (sigTheta_comp A g g' p.base) _).trans ?_
    rw [B.map_comp]
    rfl
  · show HEq (eqToHom _ ≫ (B.map ((sigTheta A (g ≫ g')).app q.base)).map f.fib)
      (eqToHom _ ≫ (B.map ((sigTheta A g').app ((A.map g).obj q.base))).map
        (eqToHom _ ≫ (B.map ((sigTheta A g).app q.base)).map f.fib))
    refine (eqToHom_comp_heq _ _).trans ?_
    refine HEq.trans ?_ (eqToHom_comp_heq _ _).symm
    refine (map_comp_eq_map_heq B _ _ _ (sigTheta_comp A g g' q.base) _).trans ?_
    rw [B.map_comp]
    exact (grpd_map_eqToHom_comp_heq (B.map ((sigTheta A g').app ((A.map g).obj q.base))) _
      ((B.map ((sigTheta A g).app q.base)).map f.fib)).symm

/-- **The dependent sum `Σ A B` as a functor `Γ ⥤ Grpd`.** -/
def SigF : Γ ⥤ Grpd.{u, u} where
  obj := sigObj A B
  map := sigMapG A B
  map_id := sigMapG_id A B
  map_comp := sigMapG_comp A B

@[simp] theorem SigF_obj (γ : Γ) : (SigF A B).obj γ = sigObj A B γ := rfl

@[simp] theorem SigF_map {γ γ' : Γ} (g : γ ⟶ γ') : (SigF A B).map g = sigMapG A B g := rfl

end SigF

end GrpdModel
