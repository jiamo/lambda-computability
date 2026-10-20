/-
**Groupoids of sections** (support for `M23-GROUPOID-PI`).

For a functor `F : X ⥤ Grpd`, `GrpdModel.Sect F` is the groupoid of sections of `F`: an object
assigns to every `x` an object `s x : F x` and to every `f : x ⟶ y` a morphism
`F(f)(s x) ⟶ s y`, functorially; a morphism is a family of fibre morphisms, natural in `x`.
It is the groupoid of sections over `X` of the Grothendieck construction `∫ F` with vertical
natural transformations as morphisms (`Sect.toFunctor`, `Sect.ofOver`).

* `Sect.groupoid` — the groupoid structure;
* `GrpdModel.trans K i j θ : Sect (i ⋙ B) ⥤ Sect (j ⋙ B)` — transport of sections of a family
  `B : E ⥤ Grpd` along a natural transformation `θ : K ⋙ i ⟶ j`; it is strictly functorial in
  `(K, θ)`: `trans_comp`, `trans_id`, `trans_congr`.
-/

import Start.GrpdIdTypes

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace GrpdModel

section Sect

variable {X : Type u} [Category.{u} X]

/-- Sections of a groupoid-valued functor. -/
structure Sect (F : X ⥤ Grpd.{u, u}) where
  /-- The value at an object. -/
  obj : ∀ x, F.obj x
  /-- The value at a morphism. -/
  map : ∀ {x y : X} (f : x ⟶ y), (F.map f).obj (obj x) ⟶ obj y
  map_id : ∀ x, map (𝟙 x) = eqToHom (map_id_obj x (obj x))
  map_comp : ∀ {x y z : X} (f : x ⟶ y) (g : y ⟶ z),
    map (f ≫ g) = eqToHom (map_comp_obj f g (obj x)) ≫ (F.map g).map (map f) ≫ map g

variable {F : X ⥤ Grpd.{u, u}}

theorem Sect.hext {s t : Sect F} (ho : s.obj = t.obj)
    (hm : ∀ {x y : X} (f : x ⟶ y), HEq (s.map f) (t.map f)) : s = t := by
  cases s with | mk so sm _ _ =>
  cases t with | mk so' sm' _ _ =>
  cases ho
  have : @sm = @sm' := by
    funext x y f
    exact eq_of_heq (hm f)
  subst this
  rfl

/-- Morphisms of sections: natural families of fibre morphisms. -/
structure SectHom (s t : Sect F) where
  /-- The component at an object. -/
  app : ∀ x, s.obj x ⟶ t.obj x
  nat : ∀ {x y : X} (f : x ⟶ y), s.map f ≫ app y = (F.map f).map (app x) ≫ t.map f

@[ext] theorem SectHom.ext' {s t : Sect F} {α β : SectHom s t} (h : ∀ x, α.app x = β.app x) :
    α = β := by
  cases α; cases β
  congr
  funext x
  exact h x

instance Sect.category : Category.{u} (Sect F) where
  Hom := SectHom
  id s := ⟨fun x => 𝟙 _, fun f => by simp⟩
  comp α β := ⟨fun x => α.app x ≫ β.app x, fun f => by
    rw [Functor.map_comp, Category.assoc, ← β.nat, ← Category.assoc, α.nat, Category.assoc]⟩
  id_comp _ := SectHom.ext' fun _ => Category.id_comp _
  comp_id _ := SectHom.ext' fun _ => Category.comp_id _
  assoc _ _ _ := SectHom.ext' fun _ => Category.assoc _ _ _

@[simp] theorem Sect.id_app (s : Sect F) (x : X) : SectHom.app (𝟙 s) x = 𝟙 _ := rfl
@[simp] theorem Sect.comp_app {s t r : Sect F} (α : s ⟶ t) (β : t ⟶ r) (x : X) :
    SectHom.app (α ≫ β) x = α.app x ≫ β.app x := rfl

theorem Sect.hom_ext {s t : Sect F} {α β : s ⟶ t} (h : ∀ x, α.app x = β.app x) : α = β :=
  SectHom.ext' h

theorem Sect.eqToHom_app {s t : Sect F} (h : s = t) (x : X) :
    SectHom.app (eqToHom h) x = eqToHom (by rw [h]) := by
  subst h; rfl

theorem SectHom.hext' {s t s' t' : Sect F} (hs : s = s') (ht : t = t') {α : s ⟶ t}
    {β : s' ⟶ t'} (h : ∀ x, HEq (α.app x) (β.app x)) : HEq α β := by
  subst hs ht
  exact heq_of_eq (Sect.hom_ext fun x => eq_of_heq (h x))

/-- The inverse of a morphism of sections. -/
def SectHom.inv {s t : Sect F} (α : s ⟶ t) : t ⟶ s where
  app x := Groupoid.inv (α.app x)
  nat {x y} f := by
    have h : (F.map f).map (α.app x) ≫ t.map f = s.map f ≫ α.app y := (α.nat f).symm
    have hmap : (F.map f).map (Groupoid.inv (α.app x)) =
        CategoryTheory.inv ((F.map f).map (α.app x)) := by
      simp [Groupoid.inv_eq_inv]
    rw [hmap, Groupoid.inv_eq_inv, IsIso.eq_inv_comp, ← Category.assoc, h, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]

/-- **Sections of a groupoid-valued functor form a groupoid.** -/
instance Sect.groupoid : Groupoid.{u} (Sect F) where
  inv α := SectHom.inv α
  inv_comp α := Sect.hom_ext fun x => Groupoid.inv_comp (α.app x)
  comp_inv α := Sect.hom_ext fun x => Groupoid.comp_inv (α.app x)

/-- A section, as a functor into the Grothendieck construction lying strictly over `𝟭`. -/
def Sect.toFunctor (s : Sect F) : X ⥤ GObj F where
  obj x := ⟨x, s.obj x⟩
  map f := ⟨f, s.map f⟩
  map_id x := GHom.hext rfl (heq_of_eq (s.map_id x))
  map_comp f g := GHom.hext rfl (heq_of_eq (s.map_comp f g))

@[simp] theorem Sect.toFunctor_disp (s : Sect F) : s.toFunctor ⋙ disp F = 𝟭 X := rfl

end Sect

section OfOver

variable {X : Type u} [Category.{u} X] {E : Type u} [Category.{u} E] {B : E ⥤ Grpd.{u, u}}

/-- The section of `(G ⋙ disp B) ⋙ B` determined by a functor `G : X ⥤ ∫ B`. -/
def Sect.ofOver (G : X ⥤ GObj B) : Sect ((G ⋙ disp B) ⋙ B) where
  obj x := (G.obj x).fib
  map f := (G.map f).fib
  map_id x := by
    have h := congr_arg_heq GHom.fib (G.map_id x)
    refine eq_of_heq (h.trans ?_)
    simp only [id_fib]
    exact eqToHom_heq_eqToHom _ _
      (congrArg (fun m => (B.map m).obj (G.obj x).fib)
        (show 𝟙 (G.obj x).base = (G.map (𝟙 x)).base by rw [G.map_id, id_base])) rfl
  map_comp f g := by
    have h := congr_arg_heq GHom.fib (G.map_comp f g)
    refine eq_of_heq (h.trans ?_)
    simp only [comp_fib]
    exact (eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _).symm

end OfOver

section Trans

variable {X Y E : Type u} [Category.{u} X] [Category.{u} Y] [Category.{u} E]
  (B : E ⥤ Grpd.{u, u})

/-- The functor `X ⥤ ∫ B` obtained by transporting a section along `θ`. -/
def transF (K : X ⥤ Y) (i : Y ⥤ E) (j : X ⥤ E) (θ : K ⋙ i ⟶ j) (s : Sect (i ⋙ B)) :
    X ⥤ GObj B :=
  transportAlong B (K ⋙ s.toFunctor ⋙ extend i B) j θ

/-- Transport of a section along `θ : K ⋙ i ⟶ j`, on objects. -/
def transObj (K : X ⥤ Y) (i : Y ⥤ E) (j : X ⥤ E) (θ : K ⋙ i ⟶ j) (s : Sect (i ⋙ B)) :
    Sect (j ⋙ B) :=
  Sect.ofOver (transF B K i j θ s)

theorem transObj_obj (K : X ⥤ Y) (i : Y ⥤ E) (j : X ⥤ E) (θ : K ⋙ i ⟶ j) (s : Sect (i ⋙ B))
    (x : X) : (transObj B K i j θ s).obj x = (B.map (θ.app x)).obj (s.obj (K.obj x)) := rfl

theorem transObj_map (K : X ⥤ Y) (i : Y ⥤ E) (j : X ⥤ E) (θ : K ⋙ i ⟶ j) (s : Sect (i ⋙ B))
    {x y : X} (f : x ⟶ y) : (transObj B K i j θ s).map f =
      eqToHom (transport_eq B (S := K ⋙ s.toFunctor ⋙ extend i B) θ f) ≫
        (B.map (θ.app y)).map (s.map (K.map f)) := rfl

/-- Transport of a section along `θ`, on morphisms. -/
def transHom (K : X ⥤ Y) (i : Y ⥤ E) (j : X ⥤ E) (θ : K ⋙ i ⟶ j) {s t : Sect (i ⋙ B)}
    (α : s ⟶ t) : transObj B K i j θ s ⟶ transObj B K i j θ t where
  app x := (B.map (θ.app x)).map (α.app (K.obj x))
  nat {x y} f := by
    rw [transObj_map, transObj_map]
    have h := α.nat (K.map f)
    have nat : i.map (K.map f) ≫ θ.app y = θ.app x ≫ j.map f := θ.naturality f
    simp only [Category.assoc]
    rw [← Functor.map_comp, h, Functor.map_comp]
    change _ = ((j ⋙ B).map f).map _ ≫ _
    simp only [Functor.comp_map, Functor.comp_obj, map_map, map_congr_map nat, Category.assoc,
      eqToHom_trans_assoc]

/-- **Transport of sections along `θ : K ⋙ i ⟶ j`**, a functor between section groupoids. -/
def trans (K : X ⥤ Y) (i : Y ⥤ E) (j : X ⥤ E) (θ : K ⋙ i ⟶ j) :
    Sect (i ⋙ B) ⥤ Sect (j ⋙ B) where
  obj := transObj B K i j θ
  map := transHom B K i j θ
  map_id _s := Sect.hom_ext fun x => (B.map (θ.app x)).map_id _
  map_comp _α _β := Sect.hom_ext fun x => (B.map (θ.app x)).map_comp _ _

theorem trans_obj_eq (K : X ⥤ Y) (i : Y ⥤ E) (j : X ⥤ E) (θ : K ⋙ i ⟶ j) (s : Sect (i ⋙ B)) :
    (trans B K i j θ).obj s = transObj B K i j θ s := rfl

theorem trans_obj_obj (K : X ⥤ Y) (i : Y ⥤ E) (j : X ⥤ E) (θ : K ⋙ i ⟶ j) (s : Sect (i ⋙ B))
    (x : X) : ((trans B K i j θ).obj s).obj x = (B.map (θ.app x)).obj (s.obj (K.obj x)) := rfl

theorem trans_app (K : X ⥤ Y) (i : Y ⥤ E) (j : X ⥤ E) (θ : K ⋙ i ⟶ j) {s t : Sect (i ⋙ B)}
    (α : s ⟶ t) (x : X) :
    SectHom.app ((trans B K i j θ).map α) x = (B.map (θ.app x)).map (α.app (K.obj x)) := rfl

/-- Transport along the identity is the identity. -/
theorem trans_id (i : X ⥤ E) : trans B (𝟭 X) i i (𝟙 i) = 𝟭 (Sect (i ⋙ B)) := by
  have hobj : ∀ s : Sect (i ⋙ B), (trans B (𝟭 X) i i (𝟙 i)).obj s = s := by
    intro s
    refine Sect.hext (funext fun x => map_id_obj (A := B) (i.obj x) (s.obj x)) ?_
    intro x y f
    show HEq ((transObj B (𝟭 X) i i (𝟙 i) s).map f) _
    rw [transObj_map]
    refine (eqToHom_comp_heq _ _).trans ?_
    simp only [NatTrans.id_app, Functor.id_map, Functor.id_obj]
    refine HEq.trans (heq_of_eq (Functor.congr_hom (B.map_id (i.obj y)) (s.map f))) ?_
    exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)
  refine CategoryTheory.Functor.ext hobj ?_
  intro s t α
  refine Sect.hom_ext fun x => ?_
  rw [trans_app]
  simp only [Sect.comp_app, Sect.eqToHom_app, Functor.id_map, Functor.id_obj, NatTrans.id_app]
  rw [Functor.congr_hom (B.map_id (i.obj x)) (α.app x)]
  rfl

end Trans

section TransComp

variable {X Y Z E : Type u} [Category.{u} X] [Category.{u} Y] [Category.{u} Z] [Category.{u} E]
  (B : E ⥤ Grpd.{u, u})

/-- Transport is functorial: transporting twice is transporting along the composite. -/
theorem trans_comp (K₁ : X ⥤ Y) (K₂ : Z ⥤ X) (i : Y ⥤ E) (j : X ⥤ E) (k : Z ⥤ E)
    (θ₁ : K₁ ⋙ i ⟶ j) (θ₂ : K₂ ⋙ j ⟶ k) :
    trans B K₁ i j θ₁ ⋙ trans B K₂ j k θ₂ =
      trans B (K₂ ⋙ K₁) i k (Functor.whiskerLeft K₂ θ₁ ≫ θ₂) := by
  have hobj : ∀ s : Sect (i ⋙ B),
      (trans B K₁ i j θ₁ ⋙ trans B K₂ j k θ₂).obj s =
        (trans B (K₂ ⋙ K₁) i k (Functor.whiskerLeft K₂ θ₁ ≫ θ₂)).obj s := by
    intro s
    refine Sect.hext (funext fun z => (map_comp_obj (A := B) _ _ _).symm) ?_
    intro x y f
    show HEq ((transObj B K₂ j k θ₂ (transObj B K₁ i j θ₁ s)).map f)
      ((transObj B (K₂ ⋙ K₁) i k (Functor.whiskerLeft K₂ θ₁ ≫ θ₂) s).map f)
    rw [transObj_map, transObj_map, transObj_map]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_map, Functor.map_comp,
      eqToHom_map]
    rw [Functor.congr_hom (B.map_comp (θ₁.app (K₂.obj y)) (θ₂.app y))
      (s.map (K₁.map (K₂.map f)))]
    refine (eqToHom_comp_heq _ _).trans (HEq.symm ?_)
    refine (eqToHom_comp_heq _ _).trans ?_
    refine (eqToHom_comp_heq _ _).trans ?_
    exact (comp_eqToHom_heq
        ((B.map (θ₁.app (K₂.obj y)) ≫ B.map (θ₂.app y)).map (s.map (K₁.map (K₂.map f)))) _).trans
      (eqToHom_comp_heq ((B.map (θ₂.app y)).map
        ((B.map (θ₁.app (K₂.obj y))).map (s.map (K₁.map (K₂.map f))))) _).symm
  refine CategoryTheory.Functor.ext hobj ?_
  intro s t α
  refine Sect.hom_ext fun z => ?_
  simp only [Functor.comp_map, trans_app, Sect.comp_app, Sect.eqToHom_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.comp_obj]
  rw [Functor.congr_hom (B.map_comp (θ₁.app (K₂.obj z)) (θ₂.app z)) (α.app (K₁.obj (K₂.obj z)))]
  simp
  rfl

end TransComp

section TransCongr

variable {X Y E : Type u} [Category.{u} X] [Category.{u} Y] [Category.{u} E]
  (B : E ⥤ Grpd.{u, u})

theorem trans_congr {K K' : X ⥤ Y} {i : Y ⥤ E} {j : X ⥤ E} (θ : K ⋙ i ⟶ j) (θ' : K' ⋙ i ⟶ j)
    (hK : K = K') (hθ : ∀ x, HEq (θ.app x) (θ'.app x)) :
    trans B K i j θ = trans B K' i j θ' := by
  subst hK
  have : θ = θ' := NatTrans.ext (funext fun x => eq_of_heq (hθ x))
  subst this
  rfl

end TransCongr

end GrpdModel
