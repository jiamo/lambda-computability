/-
**The modest sets, and hence the PERs, are finitely complete and finitely cocomplete.**

`Start/ModestCcc.lean` shows that the terminal object, the binary products and the exponentials of
`Asm(A)` restrict to the full subcategory `Realizability.ModestCat A` of the modest assemblies,
making it cartesian closed.  This module completes the picture with the remaining finite (co)limits
of `Start/AssemblyLimits.lean` and `Start/AssemblyColimits.lean`:

* a sub-assembly of a modest assembly is modest, so equalizers stay in the subcategory and the
  modest assemblies have all finite limits;
* the initial assembly is modest, vacuously;
* a coequalizer of a modest assembly is modest — a realizer of two classes realizes a
  representative of each, and modesty of the ambient assembly identifies the two representatives;
* a coproduct of modest assemblies is modest **as soon as the algebra has more than one element**,
  which is exactly what makes the two boolean tags `k` and `k i` distinguishable
  (`Realizability.PCA.k_ne_kI`); over a one-element algebra every assembly is modest anyway, but
  the tags carry no information.

Main results:

* `Realizability.PCA.k_ne_kI` — in a partial combinatory algebra with more than one element the
  two boolean combinators differ;
* `Realizability.Assembly.Modest.sub`, `.coeq`, `.coprod`,
  `Realizability.Assembly.modest_emptyAsm` — the stability results;
* `Realizability.Modest.instHasFiniteLimits` — the modest assemblies have all finite limits;
* `Realizability.Modest.instHasFiniteColimits` — **the modest assemblies have all finite
  colimits**;
* `Realizability.PER.instHasFiniteLimits`, `Realizability.PER.instHasFiniteColimits` — hence so do
  the PERs, along the equivalence of `Start/ModestEquiv.lean`.
-/

import Start.AssemblyColimits
import Start.ModestCcc

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Realizability

variable {A : Type u} [PCA A]

/-! ### The two boolean tags are distinguishable -/

namespace PCA

/-- **In a partial combinatory algebra with more than one element the two boolean combinators
differ**: if `k` and `k i` were equal, then `a = k a b = (k i) a b = b` for all `a` and `b`. -/
theorem k_ne_kI [Nontrivial A] : (PCA.k : A) ≠ PCA.kI A := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  have h₁ := PCA.k_app_app (A := A) a b
  rw [h, PCA.kI_app] at h₁
  exact hab (Part.some_inj.1 h₁).symm

end PCA

namespace Assembly

/-! ### Modesty is stable under the remaining finite (co)limits -/

/-- A sub-assembly of a modest assembly is modest. -/
theorem Modest.sub {X : Assembly.{u, u} A} (hX : X.Modest) (P : X.carrier → Prop) :
    (subAsm X P).Modest :=
  fun a x y hx hy => Subtype.ext (hX a x.1 y.1 hx hy)

/-- The equalizer of two morphisms with modest domain is modest. -/
theorem Modest.eq {X Y : Assembly.{u, u} A} (hX : X.Modest) (f g : X ⟶ Y) :
    (eqAsm f g).Modest :=
  Modest.sub hX _

/-- The initial assembly is modest: it has no elements. -/
theorem modest_emptyAsm : (emptyAsm.{u, u} A).Modest :=
  fun _ x _ _ _ => x.elim

/-- A coequalizer of a modest assembly is modest: a realizer of two classes realizes a
representative of each, and modesty identifies those representatives. -/
theorem Modest.coeq {X Y : Assembly.{u, u} A} (f g : X ⟶ Y) (hY : Y.Modest) :
    (coeqAsm f g).Modest := by
  rintro a q q' ⟨y, rfl, hy⟩ ⟨y', rfl, hy'⟩
  exact congrArg _ (hY a y y' hy hy')

/-- **A coproduct of modest assemblies is modest** over an algebra with more than one element: the
tag of a realizer says which summand its element lies in, and the payload determines the element
there. -/
theorem Modest.coprod [Nontrivial A] {X Y : Assembly.{u, u} A} (hX : X.Modest) (hY : Y.Modest) :
    (coprodAsm X Y).Modest := by
  intro p z z' hz hz'
  cases z with
  | inl x =>
    cases z' with
    | inl x' =>
      obtain ⟨a, ha, rfl⟩ := hz
      obtain ⟨a', ha', hp⟩ := hz'
      obtain rfl := (pairEl_inj hp).2
      exact congrArg Sum.inl (hX a x x' ha ha')
    | inr y' =>
      obtain ⟨a, _, rfl⟩ := hz
      obtain ⟨b, _, hp⟩ := hz'
      exact absurd (pairEl_inj hp).1 PCA.k_ne_kI
  | inr y =>
    cases z' with
    | inl x' =>
      obtain ⟨b, _, rfl⟩ := hz
      obtain ⟨a', _, hp⟩ := hz'
      exact absurd (pairEl_inj hp).1.symm PCA.k_ne_kI
    | inr y' =>
      obtain ⟨b, hb, rfl⟩ := hz
      obtain ⟨b', hb', hp⟩ := hz'
      obtain rfl := (pairEl_inj hp).2
      exact congrArg Sum.inr (hY b y y' hb hb')

end Assembly

/-! ### Finite limits and colimits of modest assemblies -/

namespace Modest

open Assembly

/-- The equalizer of two morphisms of modest assemblies. -/
def eqModest {X Y : ModestCat A} (f g : X ⟶ Y) : ModestCat A :=
  ⟨eqAsm f.hom g.hom, Modest.eq X.2 f.hom g.hom⟩

/-- The equalizing sub-assembly as a fork in the subcategory. -/
noncomputable def eqForkModest {X Y : ModestCat A} (f g : X ⟶ Y) : Fork f g :=
  Fork.ofι (P := eqModest f g) (ObjectProperty.homMk (eqIncl f.hom g.hom))
    (ObjectProperty.hom_ext _ (eqIncl_comp f.hom g.hom))

/-- The equalizer of two morphisms of modest assemblies is their equalizer in the
subcategory. -/
noncomputable def eqForkModestIsLimit {X Y : ModestCat A} (f g : X ⟶ Y) :
    IsLimit (eqForkModest f g) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨ObjectProperty.homMk (subLift (P := fun x => f.hom.toFun x = g.hom.toFun x) s.ι.hom
        (fun z => congrArg (fun k : s.pt ⟶ Y => k.hom.toFun z) s.condition)),
      ObjectProperty.hom_ext _ (hom_ext fun _ => rfl),
      fun hm => ObjectProperty.hom_ext _ (hom_ext fun z =>
        Subtype.ext (congrArg (fun k : s.pt ⟶ X => k.hom.toFun z) hm))⟩

instance hasLimit_parallelPair {X Y : ModestCat A} (f g : X ⟶ Y) : HasLimit (parallelPair f g) :=
  ⟨⟨⟨eqForkModest f g, eqForkModestIsLimit f g⟩⟩⟩

instance instHasEqualizers : HasEqualizers (ModestCat A) :=
  hasEqualizers_of_hasLimit_parallelPair _

/-- **The modest assemblies have all finite limits.** -/
instance instHasFiniteLimits : HasFiniteLimits (ModestCat A) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- The initial modest assembly. -/
def emptyModest (A : Type u) [PCA A] : ModestCat A :=
  ⟨emptyAsm A, modest_emptyAsm⟩

/-- The empty assembly is initial among the modest ones. -/
noncomputable def isInitialEmptyModest : IsInitial (emptyModest A) :=
  IsInitial.ofUniqueHom (fun X => ObjectProperty.homMk (fromEmpty X.obj))
    (fun _ _ => ObjectProperty.hom_ext _ (hom_ext fun x => x.elim))

instance : HasInitial (ModestCat A) :=
  IsInitial.hasInitial isInitialEmptyModest

/-- The coequalizer of two morphisms of modest assemblies. -/
def coeqModest {X Y : ModestCat A} (f g : X ⟶ Y) : ModestCat A :=
  ⟨coeqAsm f.hom g.hom, Modest.coeq f.hom g.hom Y.2⟩

/-- The quotient assembly as a cofork in the subcategory. -/
noncomputable def coeqCoforkModest {X Y : ModestCat A} (f g : X ⟶ Y) : Cofork f g :=
  Cofork.ofπ (P := coeqModest f g) (ObjectProperty.homMk (coeqProj f.hom g.hom))
    (ObjectProperty.hom_ext _ (coeqProj_comp f.hom g.hom))

/-- The coequalizer of two morphisms of modest assemblies is their coequalizer in the
subcategory. -/
noncomputable def coeqCoforkModestIsColimit {X Y : ModestCat A} (f g : X ⟶ Y) :
    IsColimit (coeqCoforkModest f g) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨ObjectProperty.homMk (coeqDesc s.π.hom (congrArg (fun k : X ⟶ s.pt => k.hom) s.condition)),
      ObjectProperty.hom_ext _ (hom_ext fun _ => rfl),
      fun {m} hm => ObjectProperty.hom_ext _ (hom_ext fun q => by
        induction q using Quot.ind with
        | _ y => exact congrArg (fun k : Y ⟶ s.pt => k.hom.toFun y) hm)⟩

instance hasColimit_parallelPair {X Y : ModestCat A} (f g : X ⟶ Y) :
    HasColimit (parallelPair f g) :=
  ⟨⟨⟨coeqCoforkModest f g, coeqCoforkModestIsColimit f g⟩⟩⟩

instance instHasCoequalizers : HasCoequalizers (ModestCat A) :=
  hasCoequalizers_of_hasColimit_parallelPair _

section Nontrivial

variable [Nontrivial A]

/-- The coproduct of two modest assemblies. -/
def coprodModest (X Y : ModestCat A) : ModestCat A :=
  ⟨coprodAsm X.obj Y.obj, Modest.coprod X.2 Y.2⟩

/-- The coproduct assembly as a cofan in the subcategory. -/
noncomputable def coprodCofanModest (X Y : ModestCat A) : BinaryCofan X Y :=
  BinaryCofan.mk (P := coprodModest X Y) (ObjectProperty.homMk (coprodInl X.obj Y.obj))
    (ObjectProperty.homMk (coprodInr X.obj Y.obj))

/-- The coproduct of two modest assemblies is their coproduct in the subcategory. -/
noncomputable def coprodCofanModestIsColimit (X Y : ModestCat A) :
    IsColimit (coprodCofanModest X Y) :=
  BinaryCofan.isColimitMk
    (fun s => ObjectProperty.homMk (coprodDesc (BinaryCofan.inl s).hom (BinaryCofan.inr s).hom))
    (fun _ => ObjectProperty.hom_ext _ (hom_ext fun _ => rfl))
    (fun _ => ObjectProperty.hom_ext _ (hom_ext fun _ => rfl))
    (fun s m h₁ h₂ => ObjectProperty.hom_ext _ (hom_ext fun z => by
      cases z with
      | inl x => exact congrArg (fun k : X ⟶ s.pt => k.hom.toFun x) h₁
      | inr y => exact congrArg (fun k : Y ⟶ s.pt => k.hom.toFun y) h₂))

instance (X Y : ModestCat A) : HasBinaryCoproduct X Y :=
  ⟨⟨⟨coprodCofanModest X Y, coprodCofanModestIsColimit X Y⟩⟩⟩

instance instHasBinaryCoproducts : HasBinaryCoproducts (ModestCat A) :=
  hasBinaryCoproducts_of_hasColimit_pair _

instance instHasFiniteCoproducts : HasFiniteCoproducts (ModestCat A) :=
  hasFiniteCoproducts_of_has_binary_and_initial

/-- **The modest assemblies have all finite colimits** over an algebra with more than one
element. -/
instance instHasFiniteColimits : HasFiniteColimits (ModestCat A) :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

end Nontrivial

end Modest

/-! ### The same structure on the PERs -/

namespace PER

/-- The PERs have all finite limits, being equivalent to the modest assemblies. -/
instance instHasFiniteLimits : HasFiniteLimits (PER A) where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (perEquivModest A).functor

/-- **The PERs have all finite colimits** over an algebra with more than one element. -/
instance instHasFiniteColimits [Nontrivial A] : HasFiniteColimits (PER A) where
  out _ := Adjunction.hasColimitsOfShape_of_equivalence (perEquivModest A).functor

end PER

end Realizability
