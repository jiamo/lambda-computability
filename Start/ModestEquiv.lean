/-
**Partial equivalence relations are the same thing as modest assemblies.**

`Start/PER.lean` presents a PER `R` over a partial combinatory algebra as an assembly
`R.toAsm`, and proves that assembly modest; `Start/Modest.lean` goes the other way at the level of
objects, turning a modest assembly into a PER.  This module upgrades that dictionary to an
**equivalence of categories**.

PERs are made into a category by taking as morphisms the *tracked* functions between the quotient
sets: a function `R.Quot → S.Quot` is tracked when a single element of the algebra sends every
element of the domain of `R` to a representative of the value.  That is the intrinsic notion, and
`Realizability.PER.tracked_iff` identifies it with being tracked as a map of assemblies, so the
comparison functor into the modest assemblies is fully faithful.  Essential surjectivity is the
content of `Realizability.Assembly.perIso`: a modest assembly is isomorphic to the assembly of the
PER it presents, the isomorphism being tracked by the identity combinator in both directions
because the two objects have *the same realizers*.

Main definitions:

* `Realizability.PER.Tracked`, `Realizability.PER.Hom` — tracked functions between the quotients
  of two PERs, and the resulting category `Realizability.PER.instCategory` of PERs;
* `Realizability.ModestCat` — the full subcategory of the modest assemblies;
* `Realizability.PER.toModest` — the comparison functor;
* `Realizability.Assembly.toPERIso` — the assembly of the PER of a modest assembly, compared with
  the assembly itself.

Main results:

* `Realizability.PER.tracked_iff` — tracked as a map of PERs is tracked as a map of assemblies;
* `Realizability.PER.toModestFullyFaithful` — the comparison functor is fully faithful;
* `Realizability.perEquivModest` — **the category of PERs is equivalent to the category of modest
  assemblies**;
* `Realizability.PER.arrowIso` — under that equivalence the arrow PER `R ⇒ S` is the exponential
  `S ^ R` of the two assemblies.
-/

import Start.Modest

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

open CategoryTheory

namespace Realizability

variable {A : Type u} [PCA A]

/-! ### Tracked functions between partial equivalence relations -/

namespace PER

/-- A function between the quotients of two PERs is **tracked** when one element of the algebra
computes it on representatives: applied to any element of the domain of `R` it converges to a
representative of the value. -/
def Tracked (R S : PER A) (f : R.Quot → S.Quot) : Prop :=
  ∃ r : A, ∀ (a : A) (ha : R.dom a),
    ∃ v ∈ PCA.app r a, ∃ hv : S.dom v, S.cls v hv = f (R.cls a ha)

theorem realizes_toAsm {R : PER A} {a : A} {x : R.Quot} :
    R.toAsm.realizes a x ↔ ∃ h : R.dom a, R.cls a h = x := Iff.rfl

/-- **Tracked as a map of PERs is the same as tracked as a map of the assemblies they present.** -/
theorem tracked_iff {R S : PER A} (f : R.Quot → S.Quot) :
    Tracked R S f ↔ Assembly.Tracked R.toAsm S.toAsm f := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rintro a x ⟨ha, rfl⟩
    exact hr a ha
  · rintro ⟨r, hr⟩
    exact ⟨r, fun a ha => hr a (R.cls a ha) ⟨ha, rfl⟩⟩

/-- A **morphism of PERs**: a tracked function between the quotients. -/
structure Hom (R S : PER A) where
  /-- The underlying function on the quotients. -/
  toFun : R.Quot → S.Quot
  /-- Some element of the algebra computes it on representatives. -/
  tracked : Tracked R S toFun

@[ext] theorem Hom.ext {R S : PER A} {f g : Hom R S} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

noncomputable instance instCategoryStruct : CategoryStruct (PER A) where
  Hom R S := Hom R S
  id R := ⟨_root_.id, (tracked_iff _).2 (Assembly.tracked_id R.toAsm)⟩
  comp f g := ⟨g.toFun ∘ f.toFun,
    (tracked_iff _).2 (((tracked_iff _).1 f.tracked).comp ((tracked_iff _).1 g.tracked))⟩

@[simp] theorem id_toFun (R : PER A) : (𝟙 R : Hom R R).toFun = _root_.id := rfl

@[simp] theorem comp_toFun {R S T : PER A} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

noncomputable instance instCategory : Category (PER A) where
  id_comp _ := Hom.ext rfl
  comp_id _ := Hom.ext rfl
  assoc _ _ _ := Hom.ext rfl

end PER

/-! ### The category of modest assemblies -/

/-- Modesty as a property of assemblies. -/
def modestProperty (A : Type u) [PCA A] : ObjectProperty (Assembly.{u, u} A) :=
  fun X => X.Modest

/-- **The category of modest assemblies**: the full subcategory of `Asm(A)` on the assemblies
whose realizers determine their elements. -/
abbrev ModestCat (A : Type u) [PCA A] : Type (u + 1) := (modestProperty A).FullSubcategory

/-! ### A modest assembly is the assembly of a PER -/

namespace Assembly

variable {X : Assembly.{u, u} A}

/-- A chosen realizer of an element of an assembly. -/
noncomputable def chosenRealizer (X : Assembly.{u, u} A) (x : X.carrier) : A :=
  (X.exists_realizer x).choose

theorem chosenRealizer_realizes (X : Assembly.{u, u} A) (x : X.carrier) :
    X.realizes (X.chosenRealizer x) x :=
  (X.exists_realizer x).choose_spec

/-- The element of a modest assembly realized by an element of the algebra in the domain of the
PER: modesty makes it unique. -/
noncomputable def elemOf (hX : X.Modest) {a : A} (ha : (toPER hX).dom a) : X.carrier :=
  ((dom_toPER hX a).1 ha).choose

theorem realizes_elemOf (hX : X.Modest) {a : A} (ha : (toPER hX).dom a) :
    X.realizes a (elemOf hX ha) :=
  ((dom_toPER hX a).1 ha).choose_spec

theorem elemOf_eq (hX : X.Modest) {a : A} (ha : (toPER hX).dom a) {x : X.carrier}
    (hx : X.realizes a x) : elemOf hX ha = x :=
  hX a _ _ (realizes_elemOf hX ha) hx

/-- The function from the quotient of the PER of a modest assembly to the assembly. -/
noncomputable def ofPERQuot (hX : X.Modest) : (toPER hX).Quot → X.carrier :=
  Quotient.lift (s := (toPER hX).setoid) (fun p => elemOf hX p.2) <| by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨x, hax, hbx⟩
    change elemOf hX ha = elemOf hX hb
    rw [elemOf_eq hX ha hax, elemOf_eq hX hb hbx]

@[simp] theorem ofPERQuot_cls (hX : X.Modest) {a : A} (ha : (toPER hX).dom a) :
    ofPERQuot hX ((toPER hX).cls a ha) = elemOf hX ha := rfl

/-- The PER of a modest assembly has the elements of the assembly as its equivalence classes:
the two objects have the same realizers, so the identity combinator tracks both directions. -/
noncomputable def toPERIso (hX : X.Modest) : (toPER hX).toAsm ≅ X where
  hom :=
    { toFun := ofPERQuot hX
      tracked := by
        refine ⟨PCA.i A, ?_⟩
        rintro a z ⟨ha, rfl⟩
        exact ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, realizes_elemOf hX ha⟩ }
  inv :=
    { toFun := fun x => (toPER hX).cls (X.chosenRealizer x)
        ⟨x, chosenRealizer_realizes X x, chosenRealizer_realizes X x⟩
      tracked := by
        refine ⟨PCA.i A, fun a x hx => ?_⟩
        refine ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, ⟨x, hx, hx⟩, ?_⟩
        exact ((toPER hX).cls_eq_cls _ _).2 ⟨x, hx, chosenRealizer_realizes X x⟩ }
  hom_inv_id := by
    refine hom_ext ?_
    refine PER.quot_ind (fun a ha => ?_)
    change (toPER hX).cls (X.chosenRealizer (elemOf hX ha)) _ = (toPER hX).cls a ha
    exact ((toPER hX).cls_eq_cls _ _).2
      ⟨elemOf hX ha, chosenRealizer_realizes X _, realizes_elemOf hX ha⟩
  inv_hom_id := by
    refine hom_ext fun x => ?_
    change elemOf hX (⟨x, chosenRealizer_realizes X x, chosenRealizer_realizes X x⟩ :
        (toPER hX).dom (X.chosenRealizer x)) = x
    exact elemOf_eq hX _ (chosenRealizer_realizes X x)

end Assembly

/-! ### The equivalence -/

namespace PER

/-- **The comparison functor**: a PER is sent to the modest assembly it presents. -/
noncomputable def toModest : PER A ⥤ ModestCat A where
  obj R := ⟨R.toAsm, R.modest_toAsm⟩
  map f := ObjectProperty.homMk ⟨f.toFun, (tracked_iff _).1 f.tracked⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The comparison functor is fully faithful**: a tracked map of assemblies between the
assemblies of two PERs is exactly a tracked map of the PERs. -/
noncomputable def toModestFullyFaithful : (toModest (A := A)).FullyFaithful where
  preimage {_ _} g := ⟨g.hom.toFun, (tracked_iff _).2 g.hom.tracked⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

noncomputable instance : (toModest (A := A)).Full := toModestFullyFaithful.full

noncomputable instance : (toModest (A := A)).Faithful := toModestFullyFaithful.faithful

/-- Every modest assembly is isomorphic to the assembly of a PER. -/
instance : (toModest (A := A)).EssSurj where
  mem_essImage X :=
    ⟨Assembly.toPER X.2, ⟨ObjectProperty.isoMk (P := modestProperty A) (Assembly.toPERIso X.2)⟩⟩

noncomputable instance : (toModest (A := A)).IsEquivalence where

end PER

/-- **Partial equivalence relations are the same thing as modest assemblies.** -/
noncomputable def perEquivModest (A : Type u) [PCA A] : PER A ≌ ModestCat A :=
  (PER.toModest (A := A)).asEquivalence

/-! ### The arrow PER is the exponential -/

namespace PER

open Assembly

variable {R S : PER A}

/-- The value at `a` of an element of the domain of the arrow PER: some element of the algebra
that `r` returns on `a`. -/
noncomputable def arrowApp {r : A} (hr : (arrow R S).dom r) {a : A} (ha : R.dom a) : A :=
  (hr a a ha).choose

theorem arrowApp_mem {r : A} (hr : (arrow R S).dom r) {a : A} (ha : R.dom a) :
    arrowApp hr ha ∈ PCA.app r a :=
  (hr a a ha).choose_spec.1

/-- Two elements returned on related arguments are related. -/
theorem arrowApp_rel {r r' : A} (hrr' : (arrow R S).rel r r') (hr : (arrow R S).dom r)
    (hr' : (arrow R S).dom r') {a b : A} (ha : R.dom a) (hb : R.dom b) (hab : R.rel a b) :
    S.rel (arrowApp hr ha) (arrowApp hr' hb) := by
  obtain ⟨u, hu, v, hv, huv⟩ := hrr' a b hab
  rwa [Part.mem_unique (arrowApp_mem hr ha) hu, Part.mem_unique (arrowApp_mem hr' hb) hv]

theorem arrowApp_dom {r : A} (hr : (arrow R S).dom r) {a : A} (ha : R.dom a) :
    S.dom (arrowApp hr ha) :=
  arrowApp_rel hr hr hr ha ha ha

/-- The function on the quotients computed by an element of the domain of the arrow PER. -/
noncomputable def arrowFun {r : A} (hr : (arrow R S).dom r) : R.Quot → S.Quot :=
  Quotient.lift (s := R.setoid) (fun p => S.cls (arrowApp hr p.2) (arrowApp_dom hr p.2)) <| by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    exact (S.cls_eq_cls _ _).2 (arrowApp_rel hr hr hr ha hb hab)

@[simp] theorem arrowFun_cls {r : A} (hr : (arrow R S).dom r) {a : A} (ha : R.dom a) :
    arrowFun hr (R.cls a ha) = S.cls (arrowApp hr ha) (arrowApp_dom hr ha) := rfl

/-- An element of the domain of the arrow PER tracks the function it computes. -/
theorem realizesFun_arrowFun {r : A} (hr : (arrow R S).dom r) :
    Assembly.RealizesFun R.toAsm S.toAsm r (arrowFun hr) := by
  rintro a x ⟨ha, rfl⟩
  exact ⟨arrowApp hr ha, arrowApp_mem hr ha, arrowApp_dom hr ha, rfl⟩

/-- **Two elements of the algebra tracking the same function are related by the arrow PER.** -/
theorem rel_of_realizesFun {r r' : A} {f : R.Quot → S.Quot}
    (hr : Assembly.RealizesFun R.toAsm S.toAsm r f)
    (hr' : Assembly.RealizesFun R.toAsm S.toAsm r' f) : (arrow R S).rel r r' := by
  intro a b hab
  have ha : R.dom a := dom_left hab
  have hb : R.dom b := dom_right hab
  obtain ⟨u, hu, hud, hucls⟩ := hr a (R.cls a ha) ⟨ha, rfl⟩
  obtain ⟨v, hv, hvd, hvcls⟩ := hr' b (R.cls b hb) ⟨hb, rfl⟩
  refine ⟨u, hu, v, hv, (S.cls_eq_cls hud hvd).1 ?_⟩
  rw [hucls, hvcls, (R.cls_eq_cls ha hb).2 hab]

/-- The function computed by a tracker is the function it tracks. -/
theorem arrowFun_eq_of_realizesFun {r : A} {f : R.Quot → S.Quot}
    (hr : Assembly.RealizesFun R.toAsm S.toAsm r f) (hrd : (arrow R S).dom r) :
    arrowFun hrd = f := by
  funext x
  refine quot_ind (motive := fun x => arrowFun hrd x = f x) ?_ x
  intro a ha
  obtain ⟨u, hu, hud, hucls⟩ := hr a (R.cls a ha) ⟨ha, rfl⟩
  rw [arrowFun_cls, ← hucls]
  exact (S.cls_eq_cls _ _).2 (by
    rw [Part.mem_unique (arrowApp_mem hrd ha) hu]
    exact hud)

/-- **The arrow PER presents the exponential of the two assemblies.**  A class of the arrow PER is
the function computed by any of its representatives, and conversely a tracked function is the
class of any of its trackers; both directions preserve realizers, so both are tracked by the
identity combinator. -/
noncomputable def arrowIso (R S : PER A) :
    (arrow R S).toAsm ≅ expAsm R.toAsm S.toAsm where
  hom :=
    { toFun := Quotient.lift (s := (arrow R S).setoid)
        (fun p => ⟨arrowFun p.2, p.1, realizesFun_arrowFun p.2⟩) (by
          rintro ⟨r, hr⟩ ⟨r', hr'⟩ hrr'
          refine Subtype.ext (funext fun x => ?_)
          refine quot_ind (motive := fun x => arrowFun hr x = arrowFun hr' x) ?_ x
          intro a ha
          exact (S.cls_eq_cls _ _).2 (arrowApp_rel hrr' hr hr' ha ha ha))
      tracked := by
        refine ⟨PCA.i A, ?_⟩
        rintro p z ⟨hp, rfl⟩
        exact ⟨p, by rw [PCA.i_app]; exact Part.mem_some _, realizesFun_arrowFun hp⟩ }
  inv :=
    { toFun := fun f => (arrow R S).cls f.2.choose
        (rel_of_realizesFun f.2.choose_spec f.2.choose_spec)
      tracked := by
        refine ⟨PCA.i A, fun p f hp => ?_⟩
        refine ⟨p, by rw [PCA.i_app]; exact Part.mem_some _,
          rel_of_realizesFun hp hp, ?_⟩
        exact ((arrow R S).cls_eq_cls _ _).2 (rel_of_realizesFun hp f.2.choose_spec) }
  hom_inv_id := by
    refine hom_ext ?_
    refine quot_ind (fun r hr => ?_)
    refine ((arrow R S).cls_eq_cls _ _).2 ?_
    have h : Assembly.Tracked R.toAsm S.toAsm (arrowFun hr) := ⟨r, realizesFun_arrowFun hr⟩
    exact rel_of_realizesFun h.choose_spec (realizesFun_arrowFun hr)
  inv_hom_id := by
    refine hom_ext fun f => ?_
    exact Subtype.ext (arrowFun_eq_of_realizesFun f.2.choose_spec _)

end PER

end Realizability
