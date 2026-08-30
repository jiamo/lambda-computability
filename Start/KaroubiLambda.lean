/-
The Karoubi envelope of a λ-model: **every λ-model is a cartesian closed category with a
reflexive object.**

This is the converse half of the Scott–Koymans correspondence.  Given a λ-model `M`
(`Start/LambdaModel.lean`), its **retracts** are the elements `a` with `a ∘ a = a`, and a
morphism `a ⟶ b` is an element `f` with `b ∘ f ∘ a = f`; composition is composition of elements.
This is the Karoubi (idempotent splitting) envelope of the applicative structure.

* `Lambda.LambdaModel.Ret`, `Lambda.LambdaModel.karoubiCategory` — the category of retracts;
* `Lambda.LambdaModel.topRet`, `Lambda.LambdaModel.prodRet` — a terminal object and binary
  products, hence `Lambda.LambdaModel.karoubiCartesianMonoidal`;
* `Lambda.LambdaModel.expRet`, `Lambda.LambdaModel.karoubiClosed`,
  `Lambda.LambdaModel.karoubiMonoidalClosed` — exponentials: the category is cartesian closed;
* `Lambda.LambdaModel.dRet`, `Lambda.LambdaModel.reflexive_dRet` — the object `D = λz. z` is
  **reflexive**: its function space `D ⇒ D` is a retract of it.

Everything is proved pointwise: a morphism is a λ-value, and two λ-values with the same
applicative behaviour are equal (`Lambda.LambdaModel.lamVal_ext`), so every equation between
morphisms reduces to a computation with the combinators of `Start/LambdaModelComb.lean`.
-/

import Start.LambdaModelComb
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Lambda

namespace LambdaModel

noncomputable section

open CategoryTheory Limits MonoidalCategory

variable {M : LambdaModel.{u}}

/-- A **retract** of a λ-model: an idempotent for composition. -/
structure Ret (M : LambdaModel.{u}) where
  /-- The underlying element. -/
  elt : M.Carrier
  /-- Idempotency. -/
  idem : M.compE elt elt = elt

namespace Ret

theorem isLamVal (a : Ret M) : M.IsLamVal a.elt := a.idem ▸ M.isLamVal_compE _ _

@[simp] theorem app_app (a : Ret M) (x : M.Carrier) :
    M.app a.elt (M.app a.elt x) = M.app a.elt x := by
  conv_rhs => rw [← a.idem]
  rw [M.app_compE]

end Ret

/-- A morphism of retracts: an element absorbed by the source and the target. -/
def RetHom (a b : Ret M) : Type u := {f : M.Carrier // M.compE b.elt (M.compE f a.elt) = f}

namespace RetHom

theorem isLamVal {a b : Ret M} (f : RetHom a b) : M.IsLamVal f.1 :=
  f.2 ▸ M.isLamVal_compE _ _

/-- A morphism is absorbed by its target. -/
theorem comp_left {a b : Ret M} (f : RetHom a b) : M.compE b.elt f.1 = f.1 := by
  conv_lhs => rw [← f.2]
  rw [← M.compE_assoc, b.idem, f.2]

/-- A morphism is absorbed by its source. -/
theorem comp_right {a b : Ret M} (f : RetHom a b) : M.compE f.1 a.elt = f.1 := by
  conv_lhs => rw [← f.2]
  rw [M.compE_assoc, M.compE_assoc, a.idem, f.2]

theorem app_left {a b : Ret M} (f : RetHom a b) (z : M.Carrier) :
    M.app b.elt (M.app f.1 z) = M.app f.1 z := by
  conv_rhs => rw [← comp_left f]
  rw [M.app_compE]

theorem app_right {a b : Ret M} (f : RetHom a b) (z : M.Carrier) :
    M.app f.1 (M.app a.elt z) = M.app f.1 z := by
  conv_rhs => rw [← comp_right f]
  rw [M.app_compE]

/-- Any element becomes a morphism after composing with the two retracts. -/
def mk' (a b : Ret M) (m : M.Carrier) : RetHom a b :=
  ⟨M.compE b.elt (M.compE m a.elt), M.compE_congr fun d => by
    simp only [M.app_compE, Ret.app_app]⟩

theorem app_mk' (a b : Ret M) (m z : M.Carrier) :
    M.app (mk' a b m).1 z = M.app b.elt (M.app m (M.app a.elt z)) := by
  rw [mk']
  simp only [M.app_compE]

theorem comp_mem {a b c : Ret M} (f : RetHom a b) (g : RetHom b c) :
    M.compE c.elt (M.compE (M.compE g.1 f.1) a.elt) = M.compE g.1 f.1 :=
  M.lamVal_ext (M.isLamVal_compE _ _) (M.isLamVal_compE _ _) fun d => by
    simp only [M.app_compE, app_left g, app_right f]

end RetHom

/-- **The Karoubi envelope of a λ-model**: retracts and the elements they absorb. -/
instance karoubiCategory : Category (Ret M) where
  Hom a b := RetHom a b
  id a := ⟨a.elt, by rw [a.idem, a.idem]⟩
  comp f g := ⟨M.compE g.1 f.1, RetHom.comp_mem f g⟩
  id_comp f := Subtype.ext (RetHom.comp_right f)
  comp_id f := Subtype.ext (RetHom.comp_left f)
  assoc f g h := Subtype.ext (M.compE_assoc _ _ _).symm

@[simp] theorem karoubi_id_elt (a : Ret M) : (𝟙 a : a ⟶ a).1 = a.elt := rfl

@[simp] theorem karoubi_comp_elt {a b c : Ret M} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).1 = M.compE g.1 f.1 := rfl

@[simp] theorem app_comp {a b c : Ret M} (f : a ⟶ b) (g : b ⟶ c) (d : M.Carrier) :
    M.app (f ≫ g).1 d = M.app g.1 (M.app f.1 d) := by
  rw [karoubi_comp_elt, M.app_compE]

/-- **Morphisms are equal when they act the same way.** -/
theorem hom_ext {a b : Ret M} {f g : a ⟶ b} (h : ∀ d, M.app f.1 d = M.app g.1 d) : f = g :=
  Subtype.ext (M.lamVal_ext (RetHom.isLamVal f) (RetHom.isLamVal g) h)

@[simp] theorem app_hom_left {a b : Ret M} (f : a ⟶ b) (z : M.Carrier) :
    M.app b.elt (M.app f.1 z) = M.app f.1 z := RetHom.app_left f z

@[simp] theorem app_hom_right {a b : Ret M} (f : a ⟶ b) (z : M.Carrier) :
    M.app f.1 (M.app a.elt z) = M.app f.1 z := RetHom.app_right f z

@[simp] theorem app_mk' (a b : Ret M) (m z : M.Carrier) :
    M.app (RetHom.mk' a b m).1 z = M.app b.elt (M.app m (M.app a.elt z)) :=
  RetHom.app_mk' a b m z

/-! ### The terminal object -/

/-- The terminal retract, the constant function `λz. I`. -/
def topRet (M : LambdaModel.{u}) : Ret M :=
  ⟨M.topE, M.lamVal_ext (M.isLamVal_compE _ _) M.isLamVal_topE fun d => by
    rw [M.app_compE, M.app_topE, M.app_topE]⟩

@[simp] theorem topRet_elt : (topRet M).elt = M.topE := rfl

/-- Every morphism into the terminal retract is the constant `λz. I`. -/
theorem eq_topE_of_hom_topRet {a : Ret M} (f : a ⟶ topRet M) : f.1 = M.topE := by
  refine M.lamVal_ext (RetHom.isLamVal f) M.isLamVal_topE fun d => ?_
  calc M.app f.1 d = M.app (topRet M).elt (M.app f.1 d) := (app_hom_left f d).symm
    _ = M.idE := M.app_topE _
    _ = M.app M.topE d := (M.app_topE d).symm

/-- The retract `λz. I` is terminal. -/
def isTerminalTopRet : IsTerminal (topRet M) :=
  IsTerminal.ofUniqueHom (fun a => RetHom.mk' a (topRet M) M.topE)
    (fun _ f => hom_ext fun d => by
      rw [eq_topE_of_hom_topRet f, app_mk']
      exact (M.app_topE d).trans (M.app_topE _).symm)

/-- The chosen terminal cone. -/
def terminalCone (M : LambdaModel.{u}) : LimitCone (Functor.empty.{0} (Ret M)) where
  cone := asEmptyCone (topRet M)
  isLimit := isTerminalTopRet

/-! ### Binary products -/

/-- The product of two retracts. -/
def prodRet (a b : Ret M) : Ret M :=
  ⟨M.prodE a.elt b.elt, M.lamVal_ext (M.isLamVal_compE _ _) (M.isLamVal_prodE _ _) fun p => by
    rw [M.app_compE, M.app_prodE, M.app_prodE, M.fstE_pairE, M.sndE_pairE, a.app_app,
      b.app_app]⟩

@[simp] theorem app_prodRet (a b : Ret M) (p : M.Carrier) :
    M.app (prodRet a b).elt p = M.pairE (M.app a.elt (M.fstE p)) (M.app b.elt (M.sndE p)) :=
  M.app_prodE _ _ _

/-- The first projection, as an element. -/
def fstCombE (M : LambdaModel.{u}) : M.Carrier :=
  M.interp (Lambda.lam (Lambda.app (Lambda.var 0) (Lambda.var 1))) (modelCons M.kE M.env0)

/-- The second projection, as an element. -/
def sndCombE (M : LambdaModel.{u}) : M.Carrier :=
  M.interp (Lambda.lam (Lambda.app (Lambda.var 0) (Lambda.var 1))) (modelCons M.kSE M.env0)

@[simp] theorem app_fstCombE (p : M.Carrier) : M.app (fstCombE M) p = M.fstE p := by
  rw [fstCombE, M.interp_beta]
  simp only [M.interp_app, M.interp_var, modelCons_zero, modelCons_succ, fstE]

@[simp] theorem app_sndCombE (p : M.Carrier) : M.app (sndCombE M) p = M.sndE p := by
  rw [sndCombE, M.interp_beta]
  simp only [M.interp_app, M.interp_var, modelCons_zero, modelCons_succ, sndE]

/-- The first projection of a product of retracts. -/
def projFst (a b : Ret M) : prodRet a b ⟶ a := RetHom.mk' _ _ (fstCombE M)

/-- The second projection of a product of retracts. -/
def projSnd (a b : Ret M) : prodRet a b ⟶ b := RetHom.mk' _ _ (sndCombE M)

@[simp] theorem app_projFst (a b : Ret M) (p : M.Carrier) :
    M.app (projFst a b).1 p = M.app a.elt (M.fstE p) := by
  rw [projFst, app_mk', app_fstCombE, app_prodRet, M.fstE_pairE, Ret.app_app]

@[simp] theorem app_projSnd (a b : Ret M) (p : M.Carrier) :
    M.app (projSnd a b).1 p = M.app b.elt (M.sndE p) := by
  rw [projSnd, app_mk', app_sndCombE, app_prodRet, M.sndE_pairE, Ret.app_app]

/-- The pairing of two morphisms. -/
def pairMor {c a b : Ret M} (f : c ⟶ a) (g : c ⟶ b) : c ⟶ prodRet a b :=
  RetHom.mk' _ _ (M.pairMorE f.1 g.1)

@[simp] theorem app_pairMor {c a b : Ret M} (f : c ⟶ a) (g : c ⟶ b) (z : M.Carrier) :
    M.app (pairMor f g).1 z = M.pairE (M.app f.1 z) (M.app g.1 z) := by
  rw [pairMor, app_mk', M.app_pairMorE, app_prodRet, M.fstE_pairE, M.sndE_pairE]
  simp only [app_hom_right, app_hom_left]

theorem pairMor_projFst {c a b : Ret M} (f : c ⟶ a) (g : c ⟶ b) :
    pairMor f g ≫ projFst a b = f := by
  refine hom_ext fun d => ?_
  simp only [app_comp, app_pairMor, app_projFst, M.fstE_pairE, app_hom_left]

theorem pairMor_projSnd {c a b : Ret M} (f : c ⟶ a) (g : c ⟶ b) :
    pairMor f g ≫ projSnd a b = g := by
  refine hom_ext fun d => ?_
  simp only [app_comp, app_pairMor, app_projSnd, M.sndE_pairE, app_hom_left]

theorem pairMor_unique {c a b : Ret M} (f : c ⟶ a) (g : c ⟶ b) (m : c ⟶ prodRet a b)
    (h₁ : m ≫ projFst a b = f) (h₂ : m ≫ projSnd a b = g) : m = pairMor f g := by
  subst h₁; subst h₂
  refine hom_ext fun d => ?_
  conv_lhs => rw [← app_hom_left m d]
  simp only [app_pairMor, app_comp, app_projFst, app_projSnd, app_prodRet]

/-- The chosen binary product cone. -/
def prodCone (a b : Ret M) : LimitCone (Limits.pair a b) where
  cone := BinaryFan.mk (projFst a b) (projSnd a b)
  isLimit :=
    BinaryFan.IsLimit.mk _ (fun f g => pairMor f g) (fun f g => pairMor_projFst f g)
      (fun f g => pairMor_projSnd f g) (fun f g m h₁ h₂ => pairMor_unique f g m h₁ h₂)

/-- The Karoubi envelope has finite products. -/
instance karoubiCartesianMonoidal : CartesianMonoidalCategory (Ret M) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts (terminalCone M) (fun a b => prodCone a b)


/-! ### Exponentials -/

theorem tensorObj_eq (a b : Ret M) : (a ⊗ b : Ret M) = prodRet a b := rfl

theorem fst_eq (a b : Ret M) : CartesianMonoidalCategory.fst a b = projFst a b := rfl

theorem snd_eq (a b : Ret M) : CartesianMonoidalCategory.snd a b = projSnd a b := rfl

/-- The function-space retract. -/
def expRet (a b : Ret M) : Ret M :=
  ⟨M.expE a.elt b.elt, M.lamVal_ext (M.isLamVal_compE _ _) (M.isLamVal_expE _ _) fun f => by
    rw [M.app_compE, M.app_expE, M.app_expE]
    exact M.compE_congr fun d => by simp only [M.app_compE, Ret.app_app]⟩

@[simp] theorem expRet_elt (a b : Ret M) : (expRet a b).elt = M.expE a.elt b.elt := rfl

@[simp] theorem app_app_expRet (a b : Ret M) (f d : M.Carrier) :
    M.app (M.app (expRet a b).elt f) d = M.app b.elt (M.app f (M.app a.elt d)) := by
  rw [expRet_elt, M.app_expE, M.app_compE, M.app_compE]

theorem isLamVal_app_expRet (a b : Ret M) (f : M.Carrier) :
    M.IsLamVal (M.app (expRet a b).elt f) := by
  rw [expRet_elt, M.app_expE]
  exact M.isLamVal_compE _ _

/-- A morphism into a function-space retract is determined by its values in two arguments. -/
theorem hom_expRet_ext {c a b : Ret M} {m n : c ⟶ expRet a b}
    (h : ∀ z d, M.app (M.app m.1 z) d = M.app (M.app n.1 z) d) : m = n := by
  refine hom_ext fun z => ?_
  refine M.lamVal_ext ?_ ?_ (h z)
  · rw [← app_hom_left m z]; exact isLamVal_app_expRet a b _
  · rw [← app_hom_left n z]; exact isLamVal_app_expRet a b _

/-- Post-composition, as a morphism of function-space retracts. -/
def expMap (a : Ret M) {b c : Ret M} (g : b ⟶ c) : expRet a b ⟶ expRet a c :=
  RetHom.mk' _ _ (M.postCompE g.1)

@[simp] theorem app_app_expMap (a : Ret M) {b c : Ret M} (g : b ⟶ c) (f d : M.Carrier) :
    M.app (M.app (expMap a g).1 f) d = M.app g.1 (M.app b.elt (M.app f (M.app a.elt d))) := by
  rw [expMap, app_mk', M.app_postCompE]
  simp only [app_app_expRet, M.app_compE, Ret.app_app, app_hom_left, app_hom_right]

/-- The right adjoint of the product with `a`. -/
def expFunctor (a : Ret M) : Ret M ⥤ Ret M where
  obj b := expRet a b
  map g := expMap a g
  map_id b := hom_expRet_ext fun z d => by
    simp only [app_app_expMap, karoubi_id_elt, Ret.app_app, app_app_expRet]
  map_comp g h := hom_expRet_ext fun z d => by
    simp only [app_app_expMap, app_comp, Ret.app_app, app_hom_left, app_hom_right]

/-- Currying, as a map of morphisms. -/
def curryMor {a c b : Ret M} (h : prodRet a c ⟶ b) : c ⟶ expRet a b :=
  RetHom.mk' _ _ (M.curryE h.1)

/-- Uncurrying, as a map of morphisms. -/
def uncurryMor {a c b : Ret M} (g : c ⟶ expRet a b) : prodRet a c ⟶ b :=
  RetHom.mk' _ _ (M.uncurryE g.1)

/-- The value of a morphism into a function-space retract already lies in the function
space: it absorbs the source retract on its argument and the target retract on its result. -/
theorem app_app_hom_expRet {c a b : Ret M} (g : c ⟶ expRet a b) (z d : M.Carrier) :
    M.app (M.app g.1 z) d = M.app b.elt (M.app (M.app g.1 z) (M.app a.elt d)) := by
  conv_lhs => rw [← app_hom_left g z]
  rw [app_app_expRet]

/-- The argument of such a value may be pre-processed by the source retract. -/
@[simp] theorem app_arg_hom_expRet {c a b : Ret M} (g : c ⟶ expRet a b) (z d : M.Carrier) :
    M.app (M.app g.1 z) (M.app a.elt d) = M.app (M.app g.1 z) d := by
  rw [app_app_hom_expRet g z (M.app a.elt d), Ret.app_app, ← app_app_hom_expRet]

/-- The result of such a value is absorbed by the target retract. -/
@[simp] theorem app_res_hom_expRet {c a b : Ret M} (g : c ⟶ expRet a b) (z d : M.Carrier) :
    M.app b.elt (M.app (M.app g.1 z) d) = M.app (M.app g.1 z) d := by
  conv_lhs => rw [← app_arg_hom_expRet g z d]
  rw [← app_app_hom_expRet]

@[simp] theorem app_app_curryMor {a c b : Ret M} (h : prodRet a c ⟶ b) (z d : M.Carrier) :
    M.app (M.app (curryMor h).1 z) d
      = M.app h.1 (M.pairE (M.app a.elt d) (M.app c.elt z)) := by
  rw [curryMor, app_mk']
  simp only [app_app_expRet, M.app_app_curryE, app_hom_left]

@[simp] theorem app_uncurryMor {a c b : Ret M} (g : c ⟶ expRet a b) (p : M.Carrier) :
    M.app (uncurryMor g).1 p
      = M.app (M.app g.1 (M.app c.elt (M.sndE p))) (M.app a.elt (M.fstE p)) := by
  rw [uncurryMor, app_mk']
  simp only [M.app_uncurryE, app_prodRet, M.fstE_pairE, M.sndE_pairE,
    app_hom_right, app_arg_hom_expRet, app_res_hom_expRet]

/-- Currying is a bijection. -/
def curryEquiv (a c b : Ret M) : (prodRet a c ⟶ b) ≃ (c ⟶ expRet a b) where
  toFun := curryMor
  invFun := uncurryMor
  left_inv h := by
    refine hom_ext fun p => ?_
    rw [app_uncurryMor]
    simp only [app_app_curryMor, Ret.app_app]
    rw [← app_prodRet, app_hom_right]
  right_inv g := by
    refine hom_expRet_ext fun z d => ?_
    rw [app_app_curryMor, app_uncurryMor]
    simp only [M.fstE_pairE, M.sndE_pairE, Ret.app_app, app_hom_right,
      app_arg_hom_expRet]

theorem whiskerLeft_eq (a : Ret M) {c c' : Ret M} (f : c ⟶ c') :
    (a ◁ f : a ⊗ c ⟶ a ⊗ c') = pairMor (projFst a c) (projSnd a c ≫ f) := by
  refine pairMor_unique _ _ _ ?_ ?_
  · rw [← fst_eq]; exact CartesianMonoidalCategory.whiskerLeft_fst a f
  · rw [← snd_eq]; exact CartesianMonoidalCategory.whiskerLeft_snd a f

@[simp] theorem app_whiskerLeft (a : Ret M) {c c' : Ret M} (f : c ⟶ c') (p : M.Carrier) :
    M.app (a ◁ f : a ⊗ c ⟶ a ⊗ c').1 p
      = M.pairE (M.app a.elt (M.fstE p)) (M.app f.1 (M.sndE p)) := by
  rw [whiskerLeft_eq, app_pairMor, app_projFst, app_comp, app_projSnd, app_hom_right]

/-- Uncurrying is natural in the context. -/
theorem uncurryMor_naturality_left {a c' c b : Ret M} (f : c' ⟶ c) (g : c ⟶ expRet a b) :
    uncurryMor (f ≫ g) = (a ◁ f : a ⊗ c' ⟶ a ⊗ c) ≫ uncurryMor g := by
  refine hom_ext fun p => ?_
  have hcomp : M.app ((a ◁ f : a ⊗ c' ⟶ a ⊗ c) ≫ uncurryMor g).1 p
      = M.app (uncurryMor g).1 (M.app (a ◁ f : a ⊗ c' ⟶ a ⊗ c).1 p) := app_comp _ _ p
  rw [hcomp, app_uncurryMor, app_uncurryMor, app_whiskerLeft]
  simp only [app_comp, M.fstE_pairE, M.sndE_pairE, Ret.app_app, app_hom_left, app_hom_right]

/-- Currying is natural in the result type. -/
theorem curryMor_naturality_right {a c b b' : Ret M} (h : prodRet a c ⟶ b) (g : b ⟶ b') :
    curryMor (h ≫ g) = curryMor h ≫ expMap a g := by
  refine hom_expRet_ext fun z d => ?_
  simp only [app_comp, app_app_expMap, app_app_curryMor, Ret.app_app, app_hom_left]

/-- **Every retract is exponentiable**: the Karoubi envelope of a λ-model is cartesian
closed. -/
instance karoubiClosed (a : Ret M) : Closed a where
  rightAdj := expFunctor a
  adj := Adjunction.mkOfHomEquiv
    { homEquiv := fun c b => curryEquiv a c b
      homEquiv_naturality_left_symm := fun f g => uncurryMor_naturality_left f g
      homEquiv_naturality_right := fun h g => curryMor_naturality_right h g }

/-- **The Karoubi envelope of a λ-model is a cartesian closed category.** -/
instance karoubiMonoidalClosed : MonoidalClosed (Ret M) where
  closed a := karoubiClosed a

/-! ### The reflexive object -/

/-- The retract `D = λz. z`: the whole model, as an object of its Karoubi envelope. -/
def dRet (M : LambdaModel.{u}) : Ret M :=
  ⟨M.idE, M.lamVal_ext (M.isLamVal_compE _ _) M.isLamVal_idE fun d => by
    rw [M.app_compE, M.app_idE, M.app_idE]⟩

@[simp] theorem dRet_elt : (dRet M).elt = M.idE := rfl

/-- The morphism `D ⇒ D ⟶ D` given by `λf x. f x`. -/
def dLam (M : LambdaModel.{u}) : expRet (dRet M) (dRet M) ⟶ dRet M :=
  RetHom.mk' _ _ M.idE

/-- The morphism `D ⟶ D ⇒ D` given by `λf x. f x`. -/
def dApp (M : LambdaModel.{u}) : dRet M ⟶ expRet (dRet M) (dRet M) :=
  RetHom.mk' _ _ M.idE

/-- **`D` is a reflexive object**: the function space `D ⇒ D` is a retract of `D` in the Karoubi
envelope, which is a cartesian closed category. -/
theorem reflexive_dRet : dLam M ≫ dApp M = 𝟙 (expRet (dRet M) (dRet M)) := by
  refine hom_expRet_ext fun z d => ?_
  simp only [app_comp, dLam, dApp, app_mk', dRet_elt, M.app_idE, karoubi_id_elt,
    app_app_expRet, Ret.app_app]

end

end LambdaModel

end Lambda
