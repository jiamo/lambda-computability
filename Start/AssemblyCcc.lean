/-
**The category of assemblies over a PCA is cartesian closed.**

The exponential `X ⇒ Y` is the set of *tracked* maps `X → Y`, an element `r` of the algebra
realizing such a map when `r` tracks it.  Currying and uncurrying are then witnessed by explicit
combinators built with combinatory completeness (`Start/PCA.lean`):

* `Realizability.Assembly.cartesianMonoidal` — the finite products of `Start/Assembly.lean` as a
  `CartesianMonoidalCategory` structure;
* `Realizability.Assembly.expAsm`, `.expFunctor` — the exponential and its functoriality;
* `Realizability.Assembly.curryEquiv` — the bijection `(X × Y ⟶ Z) ≃ (Y ⟶ X ⇒ Z)`;
* `Realizability.Assembly.instClosed`, `.monoidalClosed` — the adjunction `X × - ⊣ X ⇒ -`, i.e.
  **`Asm(A)` is cartesian closed**.

Since the simply typed λ-calculus is interpreted in any cartesian closed category
(`Start/CccModel.lean`), this gives a realizability model of it over any PCA — over Kleene's `K₁`
(`Start/PCAKleene.lean`) this is recursive realizability.
-/

import Start.Assembly
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

namespace Assembly

open CategoryTheory CategoryTheory.Limits MonoidalCategory

variable {A : Type u} [PCA A]

/-! ### The cartesian monoidal structure -/

/-- The terminal assembly as a limit cone. -/
noncomputable def terminalCone : LimitCone (Functor.empty.{0} (Assembly.{u, v} A)) where
  cone := asEmptyCone (unitAsm A)
  isLimit := isTerminalUnitAsm

/-- The product assembly as a limit cone. -/
noncomputable def prodCone (X Y : Assembly.{u, v} A) : LimitCone (pair X Y) where
  cone := prodFan X Y
  isLimit := prodFanIsLimit X Y

/-- `Asm(A)` is cartesian monoidal, with the product assembly as monoidal product. -/
noncomputable instance cartesianMonoidal :
    CartesianMonoidalCategory (Assembly.{u, v} A) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts terminalCone (fun X Y => prodCone X Y)

theorem tensorObj_eq (X Y : Assembly.{u, v} A) : (X ⊗ Y) = prodAsm X Y := rfl

theorem fst_eq (X Y : Assembly.{u, v} A) :
    CartesianMonoidalCategory.fst X Y = prodFst X Y := rfl

theorem snd_eq (X Y : Assembly.{u, v} A) :
    CartesianMonoidalCategory.snd X Y = prodSnd X Y := rfl

/-- Whiskering acts on underlying functions as one expects. -/
theorem whiskerLeft_toFun (X : Assembly.{u, v} A) {Y Y' : Assembly.{u, v} A} (f : Y ⟶ Y')
    (p : (X ⊗ Y).carrier) : (X ◁ f).toFun p = (p.1, f.toFun p.2) := by
  have h₁ := congrArg (fun φ => AsmHom.toFun φ p)
    (CartesianMonoidalCategory.whiskerLeft_fst X f)
  have h₂ := congrArg (fun φ => AsmHom.toFun φ p)
    (CartesianMonoidalCategory.whiskerLeft_snd X f)
  simp only [fst_eq, snd_eq, prodFst_toFun] at h₁ h₂
  exact Prod.ext h₁ h₂

/-! ### The exponential -/

/-- The **exponential assembly** `X ⇒ Y`: the tracked maps from `X` to `Y`, realized by their
trackers. -/
def expAsm (X Y : Assembly.{u, v} A) : Assembly.{u, v} A where
  carrier := {f : X.carrier → Y.carrier // Tracked X Y f}
  realizes r f := RealizesFun X Y r f.1
  exists_realizer f := f.2

/-- The expression `t (w a)`, with the realizer `w` of a function at variable `0` and the
argument `a` at variable `1`: post-composition with `t`. -/
def postCompBody (t : A) : Expr A :=
  Expr.app (Expr.const t) (Expr.app (Expr.var 0) (Expr.var 1))

theorem postCompBody_eval (t w a : A) :
    (postCompBody t).eval (Function.update (Function.update (PCA.env0 A) 0 w) 1 a)
      = Part.some t ⬝ PCA.app w a := by
  have h0 : Function.update (Function.update (PCA.env0 A) 0 w) 1 a 0 = w := by simp
  have h1 : Function.update (Function.update (PCA.env0 A) 0 w) 1 a 1 = a := by simp
  simp only [postCompBody, Expr.eval_app, Expr.eval_const, Expr.eval_var, h0, h1,
    papp_some_some]

/-- The functorial action of `X ⇒ -`: post-composition. -/
noncomputable def expMap (X : Assembly.{u, v} A) {Y Z : Assembly.{u, v} A} (g : Y ⟶ Z) :
    expAsm X Y ⟶ expAsm X Z where
  toFun f := ⟨g.toFun ∘ f.1, f.2.comp g.tracked⟩
  tracked := by
    obtain ⟨t, ht⟩ := g.tracked
    refine ⟨PCA.lam2 (postCompBody t), fun w f hw => ?_⟩
    refine ⟨PCA.lam 1 (postCompBody t) (Function.update (PCA.env0 A) 0 w), ?_, ?_⟩
    · have := PCA.lam2_app (postCompBody t) w
      rw [papp_some_some] at this
      rw [this]
      exact Part.mem_some _
    · intro a x hx
      obtain ⟨u, hu, hux⟩ := hw a x hx
      obtain ⟨z, hz, hzx⟩ := ht u (f.1 x) hux
      refine ⟨z, ?_, hzx⟩
      have hle := PCA.lam2_app_app (postCompBody t) w a
      rw [postCompBody_eval, PCA.lam2_app, papp_some_some] at hle
      exact hle _ (mem_papp (Part.mem_some _) hu hz)

/-- The exponential functor `X ⇒ -`. -/
noncomputable def expFunctor (X : Assembly.{u, v} A) :
    Assembly.{u, v} A ⥤ Assembly.{u, v} A where
  obj Y := expAsm X Y
  map g := expMap X g
  map_id _ := hom_ext fun _ => Subtype.ext rfl
  map_comp _ _ := hom_ext fun _ => Subtype.ext rfl

/-! ### Currying -/

/-- The expression `r (pair a b)`, with the realizer `b` of the second component at variable `0`
and the realizer `a` of the first at variable `1`. -/
noncomputable def curryBody (r : A) : Expr A :=
  Expr.app (Expr.const r)
    (Expr.app (Expr.app (Expr.const (PCA.pairComb A)) (Expr.var 1)) (Expr.var 0))

theorem curryBody_eval (r b a : A) :
    (curryBody r).eval (Function.update (Function.update (PCA.env0 A) 0 b) 1 a)
      = PCA.app r (PCA.pairEl a b) := by
  have h0 : Function.update (Function.update (PCA.env0 A) 0 b) 1 a 0 = b := by simp
  have h1 : Function.update (Function.update (PCA.env0 A) 0 b) 1 a 1 = a := by simp
  simp only [curryBody, Expr.eval_app, Expr.eval_const, Expr.eval_var, h0, h1]
  rw [PCA.pairComb_app, papp_some_some]

/-- The inner tracking datum of a curried morphism. -/
theorem curry_realizesFun {X Y Z : Assembly.{u, v} A} (h : (X ⊗ Y) ⟶ Z) {r : A}
    (hr : RealizesFun (X ⊗ Y) Z r h.toFun) (b : A) (y : Y.carrier) (hb : Y.realizes b y) :
    RealizesFun X Z (PCA.lam 1 (curryBody r) (Function.update (PCA.env0 A) 0 b))
      (fun x => h.toFun (x, y)) := by
  intro a x hx
  obtain ⟨z, hz, hzx⟩ := hr (PCA.pairEl a b) (x, y) ⟨a, b, hx, hb, rfl⟩
  refine ⟨z, ?_, hzx⟩
  have hle := PCA.lam2_app_app (curryBody r) b a
  rw [curryBody_eval, PCA.lam2_app, papp_some_some] at hle
  exact hle _ hz

/-- **Currying** a morphism out of a product. -/
noncomputable def curryAsm {X Y Z : Assembly.{u, v} A} (h : (X ⊗ Y) ⟶ Z) : Y ⟶ expAsm X Z where
  toFun y := ⟨fun x => h.toFun (x, y), by
    obtain ⟨r, hr⟩ := h.tracked
    obtain ⟨b, hb⟩ := Y.exists_realizer y
    exact ⟨_, curry_realizesFun h hr b y hb⟩⟩
  tracked := by
    obtain ⟨r, hr⟩ := h.tracked
    refine ⟨PCA.lam2 (curryBody r), fun b y hb => ?_⟩
    refine ⟨PCA.lam 1 (curryBody r) (Function.update (PCA.env0 A) 0 b), ?_,
      curry_realizesFun h hr b y hb⟩
    have := PCA.lam2_app (curryBody r) b
    rw [papp_some_some] at this
    rw [this]
    exact Part.mem_some _

/-- The expression `t (snd p) (fst p)`, with the realizer `p` of a pair at variable `0`. -/
noncomputable def uncurryBody (t : A) : Expr A :=
  Expr.app (Expr.app (Expr.const t) (Expr.app (Expr.const (PCA.sndComb A)) (Expr.var 0)))
    (Expr.app (Expr.const (PCA.fstComb A)) (Expr.var 0))

theorem uncurryBody_eval (t a b : A) :
    (uncurryBody t).eval (Function.update (PCA.env0 A) 0 (PCA.pairEl a b))
      = PCA.app t b ⬝ Part.some a := by
  have h0 : Function.update (PCA.env0 A) 0 (PCA.pairEl a b) 0 = PCA.pairEl a b := by simp
  simp only [uncurryBody, Expr.eval_app, Expr.eval_const, Expr.eval_var, h0]
  rw [PCA.sndComb_pairEl, PCA.fstComb_pairEl, papp_some_some]

/-- **Uncurrying** a morphism into an exponential. -/
noncomputable def uncurryAsm {X Y Z : Assembly.{u, v} A} (g : Y ⟶ expAsm X Z) : (X ⊗ Y) ⟶ Z where
  toFun p := (g.toFun p.2).1 p.1
  tracked := by
    obtain ⟨t, ht⟩ := g.tracked
    refine ⟨PCA.lam1 (uncurryBody t), fun p q hq => ?_⟩
    obtain ⟨a, b, ha, hb, rfl⟩ := hq
    obtain ⟨w, hw, hwy⟩ := ht b q.2 hb
    obtain ⟨z, hz, hzx⟩ := hwy a q.1 ha
    refine ⟨z, ?_, hzx⟩
    have hle := PCA.lam1_app (uncurryBody t) (PCA.pairEl a b)
    rw [uncurryBody_eval, papp_some_some] at hle
    exact hle _ (mem_papp hw (Part.mem_some _) hz)

/-- Currying is a bijection `(X × Y ⟶ Z) ≃ (Y ⟶ X ⇒ Z)`. -/
noncomputable def curryEquiv (X Y Z : Assembly.{u, v} A) :
    ((X ⊗ Y) ⟶ Z) ≃ (Y ⟶ expAsm X Z) where
  toFun := curryAsm
  invFun := uncurryAsm
  left_inv _ := hom_ext fun _ => rfl
  right_inv _ := hom_ext fun _ => Subtype.ext rfl

/-! ### The adjunction -/

/-- **Every assembly is exponentiable**: `X × - ⊣ X ⇒ -`. -/
noncomputable instance instClosed (X : Assembly.{u, v} A) : Closed X where
  rightAdj := expFunctor X
  adj := Adjunction.mkOfHomEquiv
    { homEquiv := fun Y Z => curryEquiv X Y Z
      homEquiv_naturality_left_symm := by
        intro Y' Y Z f g
        refine hom_ext fun p => ?_
        change (g.toFun (f.toFun p.2)).1 p.1 = _
        rw [comp_toFun]
        change _ = (uncurryAsm g).toFun ((X ◁ f).toFun p)
        rw [whiskerLeft_toFun]
        rfl
      homEquiv_naturality_right := by
        intro Y Z Z' f g
        exact hom_ext fun _ => Subtype.ext rfl }

/-- **The category of assemblies over a partial combinatory algebra is cartesian closed.** -/
noncomputable instance monoidalClosed : MonoidalClosed (Assembly.{u, v} A) where
  closed X := instClosed X

end Assembly

end Realizability
