/-
The category of assemblies over a partial combinatory algebra.

An **assembly** over a PCA `A` is a set together with a relation "`a` realizes `x`" such that
every element has at least one realizer; a morphism of assemblies is a function which is
*tracked* by an element of `A`, i.e. computed uniformly by an element of the algebra.  Assemblies
are the basic objects of realizability: they are the "sets with computational content" out of
which the effective topos is built.

This file constructs the category `Asm(A)` and its finite products.

* `Realizability.Assembly` — assemblies over `A`;
* `Realizability.AsmHom` — tracked maps, and `Realizability.Assembly.instCategory`;
* `Realizability.Assembly.unitAsm`, `.isTerminalUnitAsm` — the terminal assembly;
* `Realizability.Assembly.prodAsm`, `.binaryFanIsLimit` — binary products, realized by Church
  pairs;
* the resulting `HasTerminal` and `HasBinaryProducts` instances.

Cartesian closedness is `Start/AssemblyCcc.lean`.
-/

import Start.PCA
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

/-- An **assembly** over a PCA `A`: a set with a relation of realizability for which every
element is realized. -/
structure Assembly (A : Type u) [PCA A] where
  /-- The underlying set. -/
  carrier : Type v
  /-- `realizes a x` reads "`a` realizes `x`". -/
  realizes : A → carrier → Prop
  /-- Every element has a realizer. -/
  exists_realizer : ∀ x : carrier, ∃ a, realizes a x

namespace Assembly

variable {A : Type u} [PCA A]

/-- `RealizesFun X Y r f` says that the element `r` computes `f` on realizers: applied to a
realizer of `x` it converges to a realizer of `f x`. -/
def RealizesFun (X Y : Assembly.{u, v} A) (r : A) (f : X.carrier → Y.carrier) : Prop :=
  ∀ (a : A) (x : X.carrier), X.realizes a x → ∃ v ∈ PCA.app r a, Y.realizes v (f x)

/-- A function between assemblies is **tracked** when some element of the algebra computes it. -/
def Tracked (X Y : Assembly.{u, v} A) (f : X.carrier → Y.carrier) : Prop :=
  ∃ r : A, RealizesFun X Y r f

/-- The identity is tracked, by `i`. -/
theorem tracked_id (X : Assembly.{u, v} A) : Tracked X X _root_.id :=
  ⟨PCA.i A, fun a x hx => ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, hx⟩⟩

/-- Tracked functions are closed under composition. -/
theorem Tracked.comp {X Y Z : Assembly.{u, v} A} {f : X.carrier → Y.carrier}
    {g : Y.carrier → Z.carrier} (hf : Tracked X Y f) (hg : Tracked Y Z g) :
    Tracked X Z (g ∘ f) := by
  obtain ⟨r, hr⟩ := hf
  obtain ⟨t, ht⟩ := hg
  refine ⟨PCA.comp t r, fun a x hx => ?_⟩
  obtain ⟨u, hu, hux⟩ := hr a x hx
  obtain ⟨w, hw, hwx⟩ := ht u (f x) hux
  refine ⟨w, ?_, hwx⟩
  have hmem : w ∈ Part.some t ⬝ (Part.some r ⬝ Part.some a) := by
    rw [papp_some_some, papp_some_left]
    exact Part.mem_bind_iff.2 ⟨u, hu, hw⟩
  have := PCA.comp_app t r a w hmem
  rwa [papp_some_some] at this

/-- A **morphism of assemblies**: a function tracked by an element of the algebra. -/
structure AsmHom (X Y : Assembly.{u, v} A) where
  /-- The underlying function. -/
  toFun : X.carrier → Y.carrier
  /-- Some element of the algebra computes `toFun` on realizers. -/
  tracked : Tracked X Y toFun

@[ext] theorem AsmHom.ext {X Y : Assembly.{u, v} A} {f g : AsmHom X Y}
    (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

/-- The identity morphism. -/
noncomputable def AsmHom.id (X : Assembly.{u, v} A) : AsmHom X X where
  toFun := _root_.id
  tracked := tracked_id X

/-- Composition of morphisms. -/
noncomputable def AsmHom.comp {X Y Z : Assembly.{u, v} A} (f : AsmHom X Y) (g : AsmHom Y Z) :
    AsmHom X Z where
  toFun := g.toFun ∘ f.toFun
  tracked := f.tracked.comp g.tracked

noncomputable instance instCategoryStruct : CategoryStruct (Assembly.{u, v} A) where
  Hom X Y := AsmHom X Y
  id X := AsmHom.id X
  comp f g := AsmHom.comp f g

@[simp] theorem id_toFun (X : Assembly.{u, v} A) : (𝟙 X : AsmHom X X).toFun = _root_.id := rfl

@[simp] theorem comp_toFun {X Y Z : Assembly.{u, v} A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

noncomputable instance instCategory : Category (Assembly.{u, v} A) where
  id_comp _ := AsmHom.ext rfl
  comp_id _ := AsmHom.ext rfl
  assoc _ _ _ := AsmHom.ext rfl

theorem hom_ext {X Y : Assembly.{u, v} A} {f g : X ⟶ Y}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g :=
  AsmHom.ext (funext h)

/-- An assembly is **modest** when realizers determine elements: no element of the algebra
realizes two distinct elements.  Modest assemblies are the ones presented by partial equivalence
relations (`Start/PER.lean`). -/
def Modest (X : Assembly.{u, v} A) : Prop :=
  ∀ (a : A) (x y : X.carrier), X.realizes a x → X.realizes a y → x = y

/-! ### The terminal assembly -/

/-- The terminal assembly: one element, realized by everything. -/
def unitAsm (A : Type u) [PCA A] : Assembly.{u, v} A where
  carrier := PUnit
  realizes _ _ := True
  exists_realizer _ := ⟨PCA.k, trivial⟩

/-- The unique morphism to the terminal assembly, tracked by `k`. -/
noncomputable def toUnit (X : Assembly.{u, v} A) : X ⟶ unitAsm A where
  toFun _ := PUnit.unit
  tracked := ⟨PCA.k, fun a _ _ =>
    ⟨(PCA.app (PCA.k : A) a).get (PCA.k_dom a), Part.get_mem _, trivial⟩⟩

/-- The terminal assembly is terminal. -/
noncomputable def isTerminalUnitAsm : IsTerminal (unitAsm.{u, v} A) :=
  IsTerminal.ofUniqueHom toUnit fun _ _ => hom_ext fun _ => rfl

instance : HasTerminal (Assembly.{u, v} A) :=
  IsTerminal.hasTerminal isTerminalUnitAsm

/-! ### Binary products -/

/-- The product of two assemblies: the product set, realized by Church pairs of realizers. -/
def prodAsm (X Y : Assembly.{u, v} A) : Assembly.{u, v} A where
  carrier := X.carrier × Y.carrier
  realizes p z := ∃ a b, X.realizes a z.1 ∧ Y.realizes b z.2 ∧ p = PCA.pairEl a b
  exists_realizer z := by
    obtain ⟨a, ha⟩ := X.exists_realizer z.1
    obtain ⟨b, hb⟩ := Y.exists_realizer z.2
    exact ⟨PCA.pairEl a b, a, b, ha, hb, rfl⟩

/-- The first projection, tracked by `λp. p k`. -/
noncomputable def prodFst (X Y : Assembly.{u, v} A) : prodAsm X Y ⟶ X where
  toFun := Prod.fst
  tracked := by
    refine ⟨PCA.fstComb A, fun p z hz => ?_⟩
    obtain ⟨a, b, ha, _, rfl⟩ := hz
    refine ⟨a, ?_, ha⟩
    have := PCA.fstComb_pairEl (A := A) a b
    rw [papp_some_some] at this
    rw [this]
    exact Part.mem_some _

/-- The second projection, tracked by `λp. p (k i)`. -/
noncomputable def prodSnd (X Y : Assembly.{u, v} A) : prodAsm X Y ⟶ Y where
  toFun := Prod.snd
  tracked := by
    refine ⟨PCA.sndComb A, fun p z hz => ?_⟩
    obtain ⟨a, b, _, hb, rfl⟩ := hz
    refine ⟨b, ?_, hb⟩
    have := PCA.sndComb_pairEl (A := A) a b
    rw [papp_some_some] at this
    rw [this]
    exact Part.mem_some _

/-- The pairing of two morphisms, tracked by `λz. pair (r z) (t z)`. -/
noncomputable def prodLift {Z X Y : Assembly.{u, v} A} (f : Z ⟶ X) (g : Z ⟶ Y) :
    Z ⟶ prodAsm X Y where
  toFun z := (f.toFun z, g.toFun z)
  tracked := by
    obtain ⟨r, hr⟩ := f.tracked
    obtain ⟨t, ht⟩ := g.tracked
    refine ⟨PCA.lam 0 (Expr.app (Expr.app (Expr.const (PCA.pairComb A))
      (Expr.app (Expr.const r) (Expr.var 0)))
      (Expr.app (Expr.const t) (Expr.var 0))) (PCA.env0 A), fun a z hz => ?_⟩
    obtain ⟨u, hu, hux⟩ := hr a z hz
    obtain ⟨w, hw, hwx⟩ := ht a z hz
    refine ⟨PCA.pairEl u w, ?_, u, w, hux, hwx, rfl⟩
    have hle := PCA.lam_app 0 (Expr.app (Expr.app (Expr.const (PCA.pairComb A))
      (Expr.app (Expr.const r) (Expr.var 0)))
      (Expr.app (Expr.const t) (Expr.var 0))) (PCA.env0 A) a
    refine hle _ ?_
    have hmono : (Part.some (PCA.pairComb A) ⬝ Part.some u) ⬝ Part.some w
        ≤ (Part.some (PCA.pairComb A) ⬝ (Part.some r ⬝ Part.some a))
          ⬝ (Part.some t ⬝ Part.some a) := by
      refine papp_mono (papp_mono le_rfl ?_) ?_
      · rw [papp_some_some]
        exact fun _ h => by rwa [Part.mem_some_iff.1 h]
      · rw [papp_some_some]
        exact fun _ h => by rwa [Part.mem_some_iff.1 h]
    have : PCA.pairEl u w ∈ (Part.some (PCA.pairComb A) ⬝ (Part.some r ⬝ Part.some a))
        ⬝ (Part.some t ⬝ Part.some a) := by
      refine hmono _ ?_
      rw [PCA.pairComb_app]
      exact Part.mem_some _
    simpa [Expr.eval] using this

@[simp] theorem prodFst_toFun (X Y : Assembly.{u, v} A) : (prodFst X Y).toFun = Prod.fst := rfl

@[simp] theorem prodSnd_toFun (X Y : Assembly.{u, v} A) : (prodSnd X Y).toFun = Prod.snd := rfl

@[simp] theorem prodLift_toFun {Z X Y : Assembly.{u, v} A} (f : Z ⟶ X) (g : Z ⟶ Y) (z : Z.carrier) :
    (prodLift f g).toFun z = (f.toFun z, g.toFun z) := rfl

/-- The binary fan given by the product assembly. -/
noncomputable def prodFan (X Y : Assembly.{u, v} A) : BinaryFan X Y :=
  BinaryFan.mk (prodFst X Y) (prodSnd X Y)

/-- The product assembly really is a product. -/
noncomputable def prodFanIsLimit (X Y : Assembly.{u, v} A) : IsLimit (prodFan X Y) :=
  BinaryFan.isLimitMk (fun s => prodLift (BinaryFan.fst s) (BinaryFan.snd s))
    (fun _ => hom_ext fun _ => rfl) (fun _ => hom_ext fun _ => rfl)
    (fun s m h₁ h₂ => hom_ext fun z => by
      have e₁ : (m.toFun z).1 = (BinaryFan.fst s).toFun z := by rw [← h₁]; rfl
      have e₂ : (m.toFun z).2 = (BinaryFan.snd s).toFun z := by rw [← h₂]; rfl
      exact Prod.ext e₁ e₂)

instance (X Y : Assembly.{u, v} A) : HasBinaryProduct X Y :=
  ⟨⟨⟨prodFan X Y, prodFanIsLimit X Y⟩⟩⟩

instance : HasBinaryProducts (Assembly.{u, v} A) :=
  hasBinaryProducts_of_hasLimit_pair _

end Assembly

end Realizability
