/-
**Abstraction for the groupoid Π-type** (task `M23-GROUPOID-PI`, round 5, partial).

* `GrpdModel.Sect.restrict i τ` — restriction of a section of `B : E ⥤ Grpd` along `i : Y ⥤ E`;
* `GrpdModel.tmEquivSect` — **terms of the groupoid model are sections**:
  `grpdCwa.Tm X F ≃ Sect F` (a term is a functor `X ⥤ ∫ F` lying strictly over `𝟭 X`);
* `GrpdModel.curryMap τ g` — for a section `τ` of `B` over `∫ A` and `g : γ ⟶ γ'`, the morphism
  `(PiF A B).map g (τ|γ) ⟶ τ|γ'` of the groupoid `Sect (fibI A γ' ⋙ B)` whose component at `a` is
  `τ.map (piTheta A g a)`.  **The naturality of the section family `γ ↦ τ|γ` is this morphism, not
  an equation**: `(PiF A B).map g (τ|γ)` and `τ|γ'` are in general different objects (their values
  at `a` are `B(θ_a)(τ(γ, A(g⁻¹) a))` and `τ(γ', a)`), related by the isomorphism `τ.map θ_a`.
* `GrpdModel.curry` — **currying of sections**, `Sect B → Sect (PiF A B)`, with `map_id` and
  `map_comp`;
* `GrpdModel.grpdLam` — **abstraction**, `grpdCwa.Tm (ext Γ A) B → grpdCwa.Tm Γ (PiF A B)`.

Open (first missing construction): application, i.e. the inverse `Sect (PiF A B) → Sect B`; its
`map_comp` law is the evaluation functor's functoriality (see the evidence note).
-/

import Start.GrpdPiSub
import Start.CwaGroupoid

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace GrpdModel

section SectLemmas

variable {X : Type u} [Category.{u} X] {F : X ⥤ Grpd.{u, u}}

theorem Sect.map_hcongr (τ : Sect F) {x y x' y' : X} (hx : x = x') (hy : y = y') {f : x ⟶ y}
    {f' : x' ⟶ y'} (h : HEq f f') : HEq (τ.map f) (τ.map f') := by
  subst hx hy
  cases h
  rfl

theorem Sect.map_eqToHom_heq (τ : Sect F) {x y : X} (h : x = y) :
    HEq (τ.map (eqToHom h)) (𝟙 (τ.obj y)) := by
  subst h
  rw [eqToHom_refl, τ.map_id]
  exact (eqToHom_heq_id_cod _ _ _)

theorem Sect.cast_obj_heq {F₁ F₂ : X ⥤ Grpd.{u, u}} (h : F₁ = F₂) (σ : Sect F₁) (x : X) :
    HEq ((cast (congrArg Sect h) σ : Sect F₂).obj x) (σ.obj x) := by
  subst h; rfl

theorem Sect.cast_map_heq {F₁ F₂ : X ⥤ Grpd.{u, u}} (h : F₁ = F₂) (σ : Sect F₁) {x y : X}
    (f : x ⟶ y) : HEq ((cast (congrArg Sect h) σ : Sect F₂).map f) (σ.map f) := by
  subst h; rfl

end SectLemmas

section Restrict

variable {Y E : Type u} [Category.{u} Y] [Category.{u} E] {B : E ⥤ Grpd.{u, u}}

/-- Restriction of a section along a functor. -/
def Sect.restrict (i : Y ⥤ E) (τ : Sect B) : Sect (i ⋙ B) where
  obj y := τ.obj (i.obj y)
  map f := τ.map (i.map f)
  map_id y := by
    refine eq_of_heq ((τ.map_hcongr rfl rfl (heq_of_eq (i.map_id y))).trans ?_)
    rw [τ.map_id]
    exact eqToHom_heq_eqToHom _ _
      (congrArg (fun m => (B.map m).obj (τ.obj (i.obj y))) (i.map_id y).symm) rfl
  map_comp f g := by
    refine eq_of_heq ((τ.map_hcongr rfl rfl (heq_of_eq (i.map_comp f g))).trans ?_)
    rw [τ.map_comp]
    exact (eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _).symm

@[simp] theorem Sect.restrict_obj (i : Y ⥤ E) (τ : Sect B) (y : Y) :
    (Sect.restrict i τ).obj y = τ.obj (i.obj y) := rfl

@[simp] theorem Sect.restrict_map (i : Y ⥤ E) (τ : Sect B) {y y' : Y} (f : y ⟶ y') :
    (Sect.restrict i τ).map f = τ.map (i.map f) := rfl

end Restrict

section TmSect

/-- The section determined by a term of the groupoid model. -/
def sectOfTm {X : Grpd.{u, u}} {F : X ⥤ Grpd.{u, u}} (s : grpdCwa.Tm X F) : Sect F :=
  cast (congrArg Sect (congrArg (· ⋙ F) s.2)) (Sect.ofOver s.1)

/-- The term determined by a section. -/
def tmOfSect {X : Grpd.{u, u}} {F : X ⥤ Grpd.{u, u}} (σ : Sect F) : grpdCwa.Tm X F :=
  ⟨σ.toFunctor, rfl⟩

/-- **Terms of the groupoid model are sections.** -/
def tmEquivSect (X : Grpd.{u, u}) (F : X ⥤ Grpd.{u, u}) : grpdCwa.Tm X F ≃ Sect F where
  toFun := sectOfTm
  invFun := tmOfSect
  left_inv s := by
    apply Subtype.ext
    show (sectOfTm s).toFunctor = s.1
    refine functor_ext ?_ ?_ ?_
    · exact s.2.symm
    · intro x
      exact Sect.cast_obj_heq (congrArg (· ⋙ F) s.2) _ x
    · intro x y m
      exact Sect.cast_map_heq (congrArg (· ⋙ F) s.2) _ m
  right_inv σ := by
    have h : (σ.toFunctor ⋙ disp F) ⋙ F = F := rfl
    refine Sect.hext (funext fun x => eq_of_heq (Sect.cast_obj_heq h _ x)) ?_
    intro x y f
    exact Sect.cast_map_heq h _ f

end TmSect

section Curry

variable {Γ : Type u} [Groupoid.{u} Γ] (A : Γ ⥤ Grpd.{u, u}) (B : GObj A ⥤ Grpd.{u, u})

/-- The fibre of a section of `B` at `γ`: its restriction to the fibre `A γ`. -/
abbrev curryObj (τ : Sect B) (γ : Γ) : Sect (fibI A γ ⋙ B) := Sect.restrict (fibI A γ) τ

/-- **The naturality morphism of the section family `γ ↦ τ|γ`**: its component at `a` is
`τ.map (piTheta A g a)`. -/
def curryMap (τ : Sect B) {γ γ' : Γ} (g : γ ⟶ γ') :
    (piMap A B g).obj (curryObj A B τ γ) ⟶ curryObj A B τ γ' where
  app a := τ.map ((piTheta A g).app a)
  nat {a b} φ := by
    show (transObj B _ _ _ (piTheta A g) (curryObj A B τ γ)).map φ ≫ τ.map ((piTheta A g).app b) =
      (B.map ((fibI A γ').map φ)).map (τ.map ((piTheta A g).app a)) ≫ τ.map ((fibI A γ').map φ)
    rw [transObj_map]
    have hn := (piTheta A g).naturality φ
    have h1 : HEq (eqToHom (transport_eq B (S := A.map (Groupoid.inv g) ⋙
          (curryObj A B τ γ).toFunctor ⋙ extend (fibI A γ) B) (piTheta A g) φ) ≫
        (B.map ((piTheta A g).app b)).map
          ((curryObj A B τ γ).map ((A.map (Groupoid.inv g)).map φ)) ≫
        τ.map ((piTheta A g).app b))
        (τ.map (((A.map (Groupoid.inv g)) ⋙ fibI A γ).map φ ≫ (piTheta A g).app b)) := by
      rw [τ.map_comp]
      exact (eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _).symm
    have h2 : HEq ((B.map ((fibI A γ').map φ)).map (τ.map ((piTheta A g).app a)) ≫
        τ.map ((fibI A γ').map φ))
        (τ.map ((piTheta A g).app a ≫ (fibI A γ').map φ)) := by
      rw [τ.map_comp]
      exact (eqToHom_comp_heq _ _).symm
    rw [Category.assoc]
    exact eq_of_heq (h1.trans ((τ.map_hcongr rfl rfl (heq_of_eq hn)).trans h2.symm))

@[simp] theorem curryMap_app (τ : Sect B) {γ γ' : Γ} (g : γ ⟶ γ') (a : A.obj γ') :
    (curryMap A B τ g).app a = τ.map ((piTheta A g).app a) := rfl

theorem piTheta_id_heq (γ : Γ) (a : A.obj γ) :
    HEq ((piTheta A (𝟙 γ)).app a) (𝟙 ((fibI A γ).obj a)) := by
  have hobj : (A.map (Groupoid.inv (𝟙 γ))).obj a = a := by
    rw [Groupoid.inv_eq_inv, IsIso.inv_id]
    exact map_id_obj γ a
  refine GHom.hext' (p := ⟨γ, (A.map (Groupoid.inv (𝟙 γ))).obj a⟩) (p' := ⟨γ, a⟩)
    (GObj.ext' rfl (heq_of_eq hobj)) rfl HEq.rfl ?_
  exact eqToHom_heq_eqToHom
    ((map_comp_obj (A := A) (Groupoid.inv (𝟙 γ)) (𝟙 γ) a).symm.trans
      (by rw [Groupoid.inv_comp, map_id_obj]; rfl))
    (map_id_obj (A := A) γ a) (congrArg (A.map (𝟙 γ)).obj hobj) rfl

theorem piTheta_comp_heq {γ γ' γ'' : Γ} (g : γ ⟶ γ') (h : γ' ⟶ γ'') (a : A.obj γ'') :
    HEq ((piTheta A (g ≫ h)).app a)
      ((piTheta A g).app ((A.map (Groupoid.inv h)).obj a) ≫ (piTheta A h).app a) := by
  have hK : A.map (Groupoid.inv (g ≫ h)) =
      A.map (Groupoid.inv h) ⋙ A.map (Groupoid.inv g) := by
    rw [Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, IsIso.inv_comp]
    exact A.map_comp (CategoryTheory.inv h) (CategoryTheory.inv g)
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
  have hr : ((piTheta A g).app ((A.map (Groupoid.inv h)).obj a) ≫ (piTheta A h).app a).fib =
      eqToHom hp2 := by
    simp [piTheta, eqToHom_map]
  rw [hr]
  exact eqToHom_heq_eqToHom
    ((map_comp_obj (A := A) (Groupoid.inv (g ≫ h)) (g ≫ h) a).symm.trans
      (by rw [Groupoid.inv_comp, map_id_obj]; rfl))
    hp2 (congrArg (A.map (g ≫ h)).obj hobj) rfl

/-- **Currying of sections**: a section of `B` over `∫ A` gives a section of `Π A B` over `Γ`. -/
def curry (τ : Sect B) : Sect (PiF A B) where
  obj γ := curryObj A B τ γ
  map g := curryMap A B τ g
  map_id γ := by
    refine Sect.hom_ext fun a => ?_
    rw [Sect.eqToHom_app]
    refine eq_of_heq ((τ.map_hcongr ?_ rfl (piTheta_id_heq A γ a)).trans ?_)
    · show (⟨γ, (A.map (Groupoid.inv (𝟙 γ))).obj a⟩ : GObj A) = ⟨γ, a⟩
      refine GObj.ext' rfl (heq_of_eq ?_)
      rw [Groupoid.inv_eq_inv, IsIso.inv_id]
      exact map_id_obj γ a
    · rw [τ.map_id]
      exact (eqToHom_heq_id_cod _ _ _).trans (eqToHom_heq_id_cod _ _ _).symm
  map_comp {γ γ' γ''} g h := by
    refine Sect.hom_ext fun a => ?_
    erw [Sect.comp_app, Sect.comp_app]
    rw [Sect.eqToHom_app]
    refine eq_of_heq ((τ.map_hcongr ?_ rfl (piTheta_comp_heq A g h a)).trans ?_)
    · show (⟨γ, (A.map (Groupoid.inv (g ≫ h))).obj a⟩ : GObj A) =
        ⟨γ, (A.map (Groupoid.inv g)).obj ((A.map (Groupoid.inv h)).obj a)⟩
      refine GObj.ext' rfl (heq_of_eq ?_)
      rw [Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, IsIso.inv_comp,
        Functor.map_comp]
      rfl
    · rw [τ.map_comp]
      exact (eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _).symm

end Curry

section Lam

variable {Γ : Grpd.{u, u}} (A : grpdCwa.Ty Γ) (B : grpdCwa.Ty (grpdCwa.ext Γ A))

/-- **Abstraction in the groupoid model.** -/
def grpdLam (b : grpdCwa.Tm (grpdCwa.ext Γ A) B) : grpdCwa.Tm Γ (PiF A B) :=
  (tmEquivSect Γ (PiF A B)).symm (curry A B ((tmEquivSect _ B) b))

end Lam

end GrpdModel
