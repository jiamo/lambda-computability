/-
**The modest sets form a cartesian closed category.**

`Start/Modest.lean` proves that modesty is stable under the terminal object, binary products and
exponentials of `Asm(A)`, and `Start/ModestEquiv.lean` identifies the modest assemblies with the
PERs.  This module draws the categorical consequence: the full subcategory
`Realizability.ModestCat A` of the modest assemblies is **cartesian closed**, with the same
terminal object, products and exponentials as `Asm(A)` — the inclusion is full, so a cone whose
point happens to be modest is a limit in the subcategory exactly when it is one in `Asm(A)`.

Because the modest assemblies are the PERs, the same structure lives on the category of PERs; the
exponential is the arrow PER of `Start/PER.lean` (`Realizability.PER.arrowIso`).

Main definitions:

* `Realizability.Modest.unitModest`, `Realizability.Modest.prodModest`,
  `Realizability.Modest.expModest` — the terminal modest assembly, the product and the
  exponential;
* `Realizability.Modest.instCartesianMonoidalCategory` — the finite products as a cartesian
  monoidal structure;
* `Realizability.Modest.curryEquivModest` — currying as a bijection.

Main results:

* `Realizability.Assembly.Modest.of_iso` — modesty is invariant under isomorphism of assemblies;
* `Realizability.Modest.isTerminalUnitModest`, `Realizability.Modest.prodFanModestIsLimit` — the
  terminal object and the binary products of the subcategory;
* `Realizability.Modest.instMonoidalClosed` — **the category of modest assemblies is cartesian
  closed**;
* `Realizability.PER.instMonoidalClosed` — hence so is the category of PERs.
-/

import Start.ModestEquiv

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace Realizability

variable {A : Type u} [PCA A]

/-! ### Modesty is invariant under isomorphism -/

namespace Assembly

/-- **Modesty is invariant under isomorphism.**  A realizer of two elements of `X` is carried by a
tracker of `e.hom` to a single realizer of their two images, which modesty of `Y` identifies. -/
theorem Modest.of_iso {X Y : Assembly.{u, v} A} (e : X ≅ Y) (hY : Y.Modest) : X.Modest := by
  intro a x x' hx hx'
  obtain ⟨r, hr⟩ := e.hom.tracked
  obtain ⟨v, hv, hvx⟩ := hr a x hx
  obtain ⟨w, hw, hwx⟩ := hr a x' hx'
  rw [← Part.mem_unique hv hw] at hwx
  have himg : e.hom.toFun x = e.hom.toFun x' := hY v _ _ hvx hwx
  have hcancel : ∀ z : X.carrier, e.inv.toFun (e.hom.toFun z) = z := fun z =>
    congrArg (fun f : X ⟶ X => f.toFun z) e.hom_inv_id
  rw [← hcancel x, ← hcancel x', himg]

end Assembly

/-! ### Finite products of modest assemblies -/

namespace Modest

open Assembly

/-- The terminal modest assembly. -/
def unitModest (A : Type u) [PCA A] : ModestCat A :=
  ⟨unitAsm A, modest_unitAsm⟩

/-- The terminal assembly is terminal among the modest ones. -/
noncomputable def isTerminalUnitModest : IsTerminal (unitModest A) :=
  IsTerminal.ofUniqueHom (fun X => ObjectProperty.homMk (toUnit X.obj))
    (fun _ _ => ObjectProperty.hom_ext _ (hom_ext fun _ => rfl))

/-- The product of two modest assemblies. -/
def prodModest (X Y : ModestCat A) : ModestCat A :=
  ⟨prodAsm X.obj Y.obj, Modest.prod X.2 Y.2⟩

/-- The product assembly as a fan in the subcategory. -/
noncomputable def prodFanModest (X Y : ModestCat A) : BinaryFan X Y :=
  BinaryFan.mk (P := prodModest X Y) (ObjectProperty.homMk (prodFst X.obj Y.obj))
    (ObjectProperty.homMk (prodSnd X.obj Y.obj))

/-- The product of two modest assemblies is their product in the subcategory. -/
noncomputable def prodFanModestIsLimit (X Y : ModestCat A) : IsLimit (prodFanModest X Y) :=
  BinaryFan.isLimitMk
    (fun s => ObjectProperty.homMk (prodLift (BinaryFan.fst s).hom (BinaryFan.snd s).hom))
    (fun _ => ObjectProperty.hom_ext _ (hom_ext fun _ => rfl))
    (fun _ => ObjectProperty.hom_ext _ (hom_ext fun _ => rfl))
    (fun s m h₁ h₂ => ObjectProperty.hom_ext _ (hom_ext fun z => by
      have e₁ : (m.hom.toFun z).1 = (BinaryFan.fst s).hom.toFun z := by rw [← h₁]; rfl
      have e₂ : (m.hom.toFun z).2 = (BinaryFan.snd s).hom.toFun z := by rw [← h₂]; rfl
      exact Prod.ext e₁ e₂))

/-- The modest assemblies are cartesian monoidal, with the product assembly as product. -/
noncomputable instance instCartesianMonoidalCategory :
    CartesianMonoidalCategory (ModestCat A) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    ⟨asEmptyCone (unitModest A), isTerminalUnitModest⟩
    (fun X Y => ⟨prodFanModest X Y, prodFanModestIsLimit X Y⟩)

theorem tensorObj_obj (X Y : ModestCat A) : (X ⊗ Y).obj = prodAsm X.obj Y.obj := rfl

theorem fst_hom (X Y : ModestCat A) :
    (CartesianMonoidalCategory.fst X Y).hom = prodFst X.obj Y.obj := rfl

theorem snd_hom (X Y : ModestCat A) :
    (CartesianMonoidalCategory.snd X Y).hom = prodSnd X.obj Y.obj := rfl

/-- Whiskering acts on underlying functions as one expects. -/
theorem whiskerLeft_toFun (X : ModestCat A) {Y Y' : ModestCat A} (f : Y ⟶ Y')
    (p : (X ⊗ Y).obj.carrier) : (X ◁ f).hom.toFun p = (p.1, f.hom.toFun p.2) := by
  have h₁ := congrArg (fun φ : (X ⊗ Y) ⟶ X => φ.hom.toFun p)
    (CartesianMonoidalCategory.whiskerLeft_fst X f)
  have h₂ := congrArg (fun φ : (X ⊗ Y) ⟶ Y' => φ.hom.toFun p)
    (CartesianMonoidalCategory.whiskerLeft_snd X f)
  simp only [ObjectProperty.FullSubcategory.comp_hom, fst_hom, snd_hom, prodFst_toFun] at h₁ h₂
  exact Prod.ext h₁ h₂

/-! ### Exponentials -/

/-- The exponential of two modest assemblies. -/
def expModest (X Y : ModestCat A) : ModestCat A :=
  ⟨expAsm X.obj Y.obj, Modest.exp Y.2⟩

/-- The functor `X ⇒ -` on modest assemblies. -/
noncomputable def expFunctorModest (X : ModestCat A) : ModestCat A ⥤ ModestCat A where
  obj Y := expModest X Y
  map g := ObjectProperty.homMk (expMap X.obj g.hom)
  map_id _ := ObjectProperty.hom_ext _ (hom_ext fun _ => Subtype.ext rfl)
  map_comp _ _ := ObjectProperty.hom_ext _ (hom_ext fun _ => Subtype.ext rfl)

/-- Currying is a bijection `(X × Y ⟶ Z) ≃ (Y ⟶ X ⇒ Z)` for modest assemblies. -/
noncomputable def curryEquivModest (X Y Z : ModestCat A) :
    ((X ⊗ Y) ⟶ Z) ≃ (Y ⟶ expModest X Z) where
  toFun h := ObjectProperty.homMk (curryAsm h.hom)
  invFun g := ObjectProperty.homMk (uncurryAsm g.hom)
  left_inv _ := ObjectProperty.hom_ext _ (hom_ext fun _ => rfl)
  right_inv _ := ObjectProperty.hom_ext _ (hom_ext fun _ => Subtype.ext rfl)

/-- **Every modest assembly is exponentiable in the subcategory**: `X × - ⊣ X ⇒ -`. -/
noncomputable instance instClosedModest (X : ModestCat A) : Closed X where
  rightAdj := expFunctorModest X
  adj := Adjunction.mkOfHomEquiv
    { homEquiv := fun Y Z => curryEquivModest X Y Z
      homEquiv_naturality_left_symm := by
        intro Y' Y Z f g
        refine ObjectProperty.hom_ext _ (hom_ext fun p => ?_)
        change (g.hom.toFun (f.hom.toFun p.2)).1 p.1 = _
        change _ = (uncurryAsm g.hom).toFun ((X ◁ f).hom.toFun p)
        rw [whiskerLeft_toFun]
        rfl
      homEquiv_naturality_right := by
        intro Y Z Z' f g
        exact ObjectProperty.hom_ext _ (hom_ext fun _ => Subtype.ext rfl) }

/-- **The category of modest assemblies over a partial combinatory algebra is cartesian
closed.** -/
noncomputable instance instMonoidalClosed : MonoidalClosed (ModestCat A) where
  closed X := instClosedModest X

instance : HasTerminal (ModestCat A) := IsTerminal.hasTerminal isTerminalUnitModest

instance (X Y : ModestCat A) : HasBinaryProduct X Y :=
  ⟨⟨⟨prodFanModest X Y, prodFanModestIsLimit X Y⟩⟩⟩

instance : HasBinaryProducts (ModestCat A) := hasBinaryProducts_of_hasLimit_pair _

instance : HasFiniteProducts (ModestCat A) := hasFiniteProducts_of_has_binary_and_terminal

end Modest

/-! ### The same structure on the PERs -/

namespace PER

instance hasFiniteProducts : HasFiniteProducts (PER A) where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (perEquivModest A).functor

/-- **The exponential of the modest assemblies of two PERs is the arrow PER**: the comparison
functor of `Start/ModestEquiv.lean` carries `R ⇒ S` to `X ⇒ Y`. -/
noncomputable def toModestArrowIso (R S : PER A) :
    toModest.obj (arrow R S) ≅ Modest.expModest (toModest.obj R) (toModest.obj S) :=
  ObjectProperty.isoMk (P := modestProperty A) (arrowIso R S)

/-- The PERs are cartesian monoidal. -/
noncomputable instance instCartesianMonoidalCategory : CartesianMonoidalCategory (PER A) :=
  .ofHasFiniteProducts

/-- **The category of PERs over a partial combinatory algebra is cartesian closed**, being
equivalent to the modest assemblies. -/
noncomputable instance instMonoidalClosed : MonoidalClosed (PER A) :=
  cartesianClosedOfEquiv (perEquivModest A).symm

end PER

end Realizability
