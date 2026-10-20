/-
**The Grothendieck construction for groupoid-valued functors** (support for `M23-GROUPOID-MODEL`).

For a category `Γ` and a functor `A : Γ ⥤ Grpd`, `GrpdModel.GObj A` is the Grothendieck
construction `∫ A`: objects are pairs `⟨γ, a⟩` with `a : A γ`, morphisms `⟨γ, a⟩ ⟶ ⟨γ', a'⟩` are
pairs of `f : γ ⟶ γ'` and `φ : A(f) a ⟶ a'`.

* `GObj.category`, `GObj.groupoid` — the category structure, and the groupoid structure when the
  base is a groupoid;
* `GrpdModel.disp A : GObj A ⥤ Γ` — the projection;
* `GrpdModel.extend σ A : GObj (σ ⋙ A) ⥤ GObj A` — reindexing along `σ`; it is strictly
  functorial in `σ` (`extend_comp`, by `rfl`);
* `GrpdModel.functor_ext` — two functors into `GObj A` are equal as soon as their projections
  agree and their fibre components agree up to `HEq`.
-/

import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Whiskering

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

open CategoryTheory

namespace GrpdModel

section Groth

variable {Γ : Type u} [Category.{u} Γ]

/-- Objects of the Grothendieck construction `∫ A`. -/
structure GObj (A : Γ ⥤ Grpd.{u, u}) where
  /-- The base object. -/
  base : Γ
  /-- The fibre object. -/
  fib : A.obj base

/-- Morphisms of the Grothendieck construction `∫ A`. -/
structure GHom {A : Γ ⥤ Grpd.{u, u}} (p q : GObj A) where
  /-- The base morphism. -/
  base : p.base ⟶ q.base
  /-- The fibre morphism. -/
  fib : (A.map base).obj p.fib ⟶ q.fib

variable {A : Γ ⥤ Grpd.{u, u}}

theorem map_id_obj (γ : Γ) (a : A.obj γ) : (A.map (𝟙 γ)).obj a = a :=
  Functor.congr_obj (A.map_id γ) a

theorem map_comp_obj {γ γ' γ'' : Γ} (f : γ ⟶ γ') (g : γ' ⟶ γ'') (a : A.obj γ) :
    (A.map (f ≫ g)).obj a = (A.map g).obj ((A.map f).obj a) :=
  Functor.congr_obj (A.map_comp f g) a

theorem map_id_map (γ : Γ) {a b : A.obj γ} (φ : a ⟶ b) :
    (A.map (𝟙 γ)).map φ = eqToHom (map_id_obj γ a) ≫ φ ≫ eqToHom (map_id_obj γ b).symm :=
  Functor.congr_hom (A.map_id γ) φ

theorem map_comp_map {γ γ' γ'' : Γ} (f : γ ⟶ γ') (g : γ' ⟶ γ'') {a b : A.obj γ} (φ : a ⟶ b) :
    (A.map (f ≫ g)).map φ = eqToHom (map_comp_obj f g a) ≫ (A.map g).map ((A.map f).map φ) ≫
      eqToHom (map_comp_obj f g b).symm :=
  Functor.congr_hom (A.map_comp f g) φ

theorem GHom.hext {p q : GObj A} {f g : GHom p q} (hb : f.base = g.base) (hf : HEq f.fib g.fib) :
    f = g := by
  cases f; cases g
  cases hb
  cases hf
  rfl

theorem GHom.ext' {p q : GObj A} {f g : GHom p q} (hb : f.base = g.base)
    (hf : f.fib = eqToHom (by rw [hb]) ≫ g.fib) : f = g := by
  apply GHom.hext hb
  rw [hf]
  exact eqToHom_comp_heq _ _

instance GObj.category : Category.{u} (GObj A) where
  Hom := GHom
  id p := ⟨𝟙 p.base, eqToHom (map_id_obj _ _)⟩
  comp f g := ⟨f.base ≫ g.base, eqToHom (map_comp_obj _ _ _) ≫ (A.map g.base).map f.fib ≫ g.fib⟩
  id_comp f := by
    apply GHom.hext (Category.id_comp _)
    simp only [eqToHom_map]
    rw [← Category.assoc, eqToHom_trans]
    exact eqToHom_comp_heq _ _
  comp_id f := by
    apply GHom.hext (Category.comp_id _)
    simp only [map_id_map, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [← Category.assoc, eqToHom_trans]
    exact eqToHom_comp_heq _ _
  assoc f g h := by
    apply GHom.ext' (Category.assoc _ _ _)
    simp [map_comp_map, eqToHom_map]

@[simp] theorem id_base (p : GObj A) : GHom.base (𝟙 p) = 𝟙 p.base := rfl
@[simp] theorem id_fib (p : GObj A) : GHom.fib (𝟙 p) = eqToHom (map_id_obj _ _) := rfl
@[simp] theorem comp_base {p q r : GObj A} (f : p ⟶ q) (g : q ⟶ r) :
    GHom.base (f ≫ g) = f.base ≫ g.base := rfl
@[simp] theorem comp_fib {p q r : GObj A} (f : p ⟶ q) (g : q ⟶ r) :
    GHom.fib (f ≫ g) = eqToHom (map_comp_obj _ _ _) ≫ (A.map g.base).map f.fib ≫ g.fib := rfl

theorem GObj.ext' {p q : GObj A} (hb : p.base = q.base) (hf : HEq p.fib q.fib) : p = q := by
  cases p; cases q
  cases hb
  cases hf
  rfl

theorem eqToHom_base {p q : GObj A} (h : p = q) :
    GHom.base (eqToHom h) = eqToHom (congrArg GObj.base h) := by
  subst h; rfl

theorem map_map {γ γ' γ'' : Γ} (f : γ ⟶ γ') (g : γ' ⟶ γ'') {a b : A.obj γ} (φ : a ⟶ b) :
    (A.map g).map ((A.map f).map φ) = eqToHom (map_comp_obj f g a).symm ≫
      (A.map (f ≫ g)).map φ ≫ eqToHom (map_comp_obj f g b) := by
  simp [map_comp_map]

theorem map_congr_map {γ γ' : Γ} {f f' : γ ⟶ γ'} (h : f = f') {a b : A.obj γ} (φ : a ⟶ b) :
    (A.map f).map φ = eqToHom (by rw [h]) ≫ (A.map f').map φ ≫ eqToHom (by rw [h]) := by
  subst h; simp

/-- Morphisms of `∫ A` between possibly different objects are `HEq` when their components are. -/
theorem GHom.hext' {p q p' q' : GObj A} (hp : p = p') (hq : q = q') {f : p ⟶ q} {g : p' ⟶ q'}
    (hb : HEq f.base g.base) (hf : HEq f.fib g.fib) : HEq f g := by
  subst hp hq
  exact heq_of_eq (GHom.hext (eq_of_heq hb) hf)

end Groth

section Grpd

variable {Γ : Type u} [Groupoid.{u} Γ] {A : Γ ⥤ Grpd.{u, u}}

/-- The inverse of a morphism of `∫ A` over a groupoid. -/
def GHom.inv {p q : GObj A} (f : p ⟶ q) : q ⟶ p :=
  ⟨Groupoid.inv f.base, (A.map (Groupoid.inv f.base)).map (Groupoid.inv f.fib) ≫
    eqToHom ((map_comp_obj _ _ _).symm.trans (by rw [Groupoid.comp_inv, map_id_obj]))⟩

/-- **The Grothendieck construction of a groupoid-valued functor on a groupoid is a groupoid.** -/
instance GObj.groupoid : Groupoid.{u} (GObj A) where
  inv f := GHom.inv f
  inv_comp f := by
    apply GHom.ext' (Groupoid.inv_comp _)
    simp only [comp_fib, GHom.inv, Functor.map_comp, eqToHom_map, id_fib, map_map,
      map_congr_map (Groupoid.inv_comp f.base), map_id_map]
    simp
    exact (eqToHom_trans _ _).symm
  comp_inv f := by
    apply GHom.ext' (Groupoid.comp_inv _)
    simp only [comp_fib, GHom.inv, id_fib]
    simp
    exact (eqToHom_trans _ _).symm

end Grpd

section Functors

variable {X : Type u} [Category.{u} X] {Γ : Type u} [Category.{u} Γ]

theorem eqToHom_heq_eqToHom {C : Type*} [Category C] {a b a' b' : C} (h : a = b) (h' : a' = b')
    (ha : a = a') (hb : b = b') : HEq (eqToHom h) (eqToHom h') := by
  subst ha hb; rfl

/-- The projection `∫ A ⥤ Γ`. -/
def disp (A : Γ ⥤ Grpd.{u, u}) : GObj A ⥤ Γ where
  obj p := p.base
  map f := f.base

/-- Reindexing `∫ (σ ⋙ A) ⥤ ∫ A` along `σ : Δ ⥤ Γ`. -/
def extend (σ : X ⥤ Γ) (A : Γ ⥤ Grpd.{u, u}) : GObj (σ ⋙ A) ⥤ GObj A where
  obj p := ⟨σ.obj p.base, p.fib⟩
  map f := ⟨σ.map f.base, f.fib⟩
  map_id p := GHom.hext (σ.map_id _) (by
    simp only [id_fib]; exact eqToHom_heq_eqToHom _ _ (by simp) rfl)
  map_comp f g := GHom.ext' (σ.map_comp _ _) (by simp)

theorem extend_disp (σ : X ⥤ Γ) (A : Γ ⥤ Grpd.{u, u}) :
    extend σ A ⋙ disp A = disp (σ ⋙ A) ⋙ σ := rfl

theorem extend_comp {Y : Type u} [Category.{u} Y] (τ : Y ⥤ X) (σ : X ⥤ Γ)
    (A : Γ ⥤ Grpd.{u, u}) : extend τ (σ ⋙ A) ⋙ extend σ A = extend (τ ⋙ σ) A := rfl

/-- **Functor extensionality for functors into `∫ A`.** -/
theorem functor_ext {A : Γ ⥤ Grpd.{u, u}} {F G : X ⥤ GObj A} (hb : F ⋙ disp A = G ⋙ disp A)
    (ho : ∀ x, HEq (F.obj x).fib (G.obj x).fib)
    (hm : ∀ {x y : X} (m : x ⟶ y), HEq (F.map m).fib (G.map m).fib) : F = G := by
  have hobj : ∀ x, F.obj x = G.obj x := fun x => GObj.ext' (Functor.congr_obj hb x) (ho x)
  exact Functor.hext hobj fun x y m =>
    GHom.hext' (hobj x) (hobj y) (Functor.hcongr_hom hb m) (hm m)

/-- The canonical section of `∫ (F ⋙ disp A ⋙ A)` determined by a functor `F : X ⥤ ∫ A`. -/
def secOf {A : Γ ⥤ Grpd.{u, u}} (F : X ⥤ GObj A) : X ⥤ GObj ((F ⋙ disp A) ⋙ A) where
  obj x := ⟨x, (F.obj x).fib⟩
  map m := ⟨m, (F.map m).fib⟩
  map_id x := by
    refine GHom.hext rfl ?_
    refine (congr_arg_heq GHom.fib (F.map_id x)).trans ?_
    simp only [id_fib]
    exact eqToHom_heq_eqToHom _ _ (by simp [disp]) rfl
  map_comp m n := by
    refine GHom.hext rfl ?_
    refine (congr_arg_heq GHom.fib (F.map_comp m n)).trans ?_
    exact (eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _).symm

/-- Reindexing along an equality of families. -/
def reindex {B B' : X ⥤ Grpd.{u, u}} (h : B = B') : GObj B ⥤ GObj B' := h ▸ 𝟭 (GObj B)

theorem secOf_reindex_disp {A : Γ ⥤ Grpd.{u, u}} (F : X ⥤ GObj A) (B' : X ⥤ Grpd.{u, u})
    (h : (F ⋙ disp A) ⋙ A = B') : (secOf F ⋙ reindex h) ⋙ disp B' = 𝟭 X := by
  subst h; rfl

theorem secOf_reindex_extend {A : Γ ⥤ Grpd.{u, u}} (F : X ⥤ GObj A) (G : X ⥤ Γ)
    (h : F ⋙ disp A = G) :
    (secOf F ⋙ reindex (congrArg (· ⋙ A) h)) ⋙ extend G A = F := by
  subst h; rfl

end Functors

section Pullback

variable {W : Type u} [Category.{u} W] {Δ : Type u} [Category.{u} Δ] {Γ : Type u} [Category.{u} Γ]

/-- The pullback lift for the square `extend σ A`, `disp`, `disp`, `σ`. -/
def liftG (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd.{u, u}) (F : W ⥤ GObj A) (G : W ⥤ Δ)
    (h : F ⋙ disp A = G ⋙ σ) : W ⥤ GObj (σ ⋙ A) :=
  (secOf F ⋙ reindex (congrArg (· ⋙ A) h)) ⋙ extend G (σ ⋙ A)

theorem liftG_fst (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd.{u, u}) (F : W ⥤ GObj A) (G : W ⥤ Δ)
    (h : F ⋙ disp A = G ⋙ σ) : liftG σ A F G h ⋙ extend σ A = F :=
  secOf_reindex_extend F (G ⋙ σ) h

theorem liftG_snd (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd.{u, u}) (F : W ⥤ GObj A) (G : W ⥤ Δ)
    (h : F ⋙ disp A = G ⋙ σ) : liftG σ A F G h ⋙ disp (σ ⋙ A) = G := by
  change ((secOf F ⋙ reindex (congrArg (· ⋙ A) h)) ⋙ disp ((G ⋙ σ) ⋙ A)) ⋙ G = G
  rw [secOf_reindex_disp]
  rfl

theorem liftG_congr (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd.{u, u}) {F F' : W ⥤ GObj A} {G G' : W ⥤ Δ}
    (h : F ⋙ disp A = G ⋙ σ) (h' : F' ⋙ disp A = G' ⋙ σ) (hF : F = F') (hG : G = G') :
    liftG σ A F G h = liftG σ A F' G' h' := by
  subst hF hG; rfl

theorem liftG_self (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd.{u, u}) (m : W ⥤ GObj (σ ⋙ A)) :
    m = liftG σ A (m ⋙ extend σ A) (m ⋙ disp (σ ⋙ A)) rfl := rfl

theorem liftG_uniq (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd.{u, u}) (F : W ⥤ GObj A) (G : W ⥤ Δ)
    (h : F ⋙ disp A = G ⋙ σ) (m : W ⥤ GObj (σ ⋙ A)) (h₁ : m ⋙ extend σ A = F)
    (h₂ : m ⋙ disp (σ ⋙ A) = G) : m = liftG σ A F G h :=
  (liftG_self σ A m).trans (liftG_congr σ A _ _ h₁ h₂)

end Pullback

end GrpdModel
