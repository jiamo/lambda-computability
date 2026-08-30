/-
The combinatory calculus inside a λ-model.

`Start/LambdaModel.lean` defines a λ-model abstractly.  This file develops, inside an arbitrary
λ-model `M`, the elements and equations needed to build a cartesian closed category out of it
(the Karoubi envelope, `Start/KaroubiLambda.lean`).

The organising notion is that of a **λ-value** (`Lambda.LambdaModel.IsLamVal`): an element which
is the value of an abstraction.  The Meyer–Scott axiom says exactly that two λ-values with the
same applicative behaviour are equal (`Lambda.LambdaModel.lamVal_ext`), and this is the only tool
used afterwards: each combinator below is introduced with the equation computing its application,
and every identity between combinators is proved by comparing applications.

* `idE`, `kE`, `kSE`, `constE` — the identity, the two projections and the constant functions;
* `compE` — composition, `x ∘ y = λz. x (y z)`, associative (`compE_assoc`) and unital on
  λ-values;
* `pairE`, `fstE`, `sndE`, `pairMorE` — Church pairs and the pairing of two functions;
* `prodE`, `projFstE`, `projSndE` — the product of two retracts and its projections;
* `expE`, `curryE`, `uncurryE` — the function space of two retracts, currying and uncurrying;
* `topE` — the constant `λz. I`, the terminal retract.
-/

import Start.LambdaModel

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Lambda

namespace LambdaModel

noncomputable section

variable (M : LambdaModel.{u})

/-! ### λ-values and their extensionality -/

/-- An element of the model is a **λ-value** when it is the value of an abstraction. -/
def IsLamVal (u : M.Carrier) : Prop :=
  ∃ (t : Lambda) (ρ : ℕ → M.Carrier), u = M.interp (Lambda.lam t) ρ

theorem isLamVal_interp_lam (t : Lambda) (ρ : ℕ → M.Carrier) :
    M.IsLamVal (M.interp (Lambda.lam t) ρ) := ⟨t, ρ, rfl⟩

/-- **Extensionality for λ-values** — the Meyer–Scott axiom in the form used throughout: two
values of abstractions with the same applicative behaviour are equal. -/
theorem lamVal_ext {u v : M.Carrier} (hu : M.IsLamVal u) (hv : M.IsLamVal v)
    (h : ∀ d, M.app u d = M.app v d) : u = v := by
  obtain ⟨t, ρ, rfl⟩ := hu
  obtain ⟨t', ρ', rfl⟩ := hv
  refine M.interp_lam_ext t t' ρ ρ' fun d => ?_
  rw [← M.interp_beta, ← M.interp_beta]
  exact h d

/-! ### The basic combinators -/

/-- The identity `λz. z`. -/
def idE : M.Carrier := M.interp (Lambda.lam (Lambda.var 0)) M.env0

/-- The first projection combinator `λx y. x`. -/
def kE : M.Carrier := M.interp (Lambda.lam (Lambda.lam (Lambda.var 1))) M.env0

/-- The second projection combinator `λx y. y`. -/
def kSE : M.Carrier := M.interp (Lambda.lam (Lambda.lam (Lambda.var 0))) M.env0

/-- Composition `x ∘ y = λz. x (y z)`. -/
def compE (x y : M.Carrier) : M.Carrier :=
  M.interp (Lambda.lam (Lambda.app (Lambda.var 2) (Lambda.app (Lambda.var 1) (Lambda.var 0))))
    (modelCons y (modelCons x M.env0))

/-- The constant function `λz. x`. -/
def constE (x : M.Carrier) : M.Carrier :=
  M.interp (Lambda.lam (Lambda.var 1)) (modelCons x M.env0)

/-- The Church pair `λz. z x y`. -/
def pairE (x y : M.Carrier) : M.Carrier :=
  M.interp (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 0) (Lambda.var 2)) (Lambda.var 1)))
    (modelCons y (modelCons x M.env0))

/-- The first component of a Church pair. -/
def fstE (p : M.Carrier) : M.Carrier := M.app p M.kE

/-- The second component of a Church pair. -/
def sndE (p : M.Carrier) : M.Carrier := M.app p M.kSE

@[simp] theorem app_idE (d : M.Carrier) : M.app M.idE d = d := by
  rw [idE, M.interp_beta, M.interp_var]
  rfl

@[simp] theorem app_app_kE (x y : M.Carrier) : M.app (M.app M.kE x) y = x := by
  rw [kE, M.interp_beta, M.interp_beta, M.interp_var]
  rfl

@[simp] theorem app_app_kSE (x y : M.Carrier) : M.app (M.app M.kSE x) y = y := by
  rw [kSE, M.interp_beta, M.interp_beta, M.interp_var]
  rfl

@[simp] theorem app_compE (x y d : M.Carrier) :
    M.app (M.compE x y) d = M.app x (M.app y d) := by
  rw [compE, M.interp_beta]
  simp only [M.interp_app, M.interp_var, modelCons_zero, modelCons_succ]

@[simp] theorem app_constE (x d : M.Carrier) : M.app (M.constE x) d = x := by
  rw [constE, M.interp_beta, M.interp_var]
  rfl

@[simp] theorem app_pairE (x y z : M.Carrier) :
    M.app (M.pairE x y) z = M.app (M.app z x) y := by
  rw [pairE, M.interp_beta]
  simp only [M.interp_app, M.interp_var, modelCons_zero, modelCons_succ]

@[simp] theorem fstE_pairE (x y : M.Carrier) : M.fstE (M.pairE x y) = x := by
  rw [fstE, app_pairE, app_app_kE]

@[simp] theorem sndE_pairE (x y : M.Carrier) : M.sndE (M.pairE x y) = y := by
  rw [sndE, app_pairE, app_app_kSE]

theorem isLamVal_idE : M.IsLamVal M.idE := isLamVal_interp_lam M _ _
theorem isLamVal_kE : M.IsLamVal M.kE := isLamVal_interp_lam M _ _
theorem isLamVal_kSE : M.IsLamVal M.kSE := isLamVal_interp_lam M _ _
theorem isLamVal_compE (x y : M.Carrier) : M.IsLamVal (M.compE x y) := isLamVal_interp_lam M _ _
theorem isLamVal_constE (x : M.Carrier) : M.IsLamVal (M.constE x) := isLamVal_interp_lam M _ _
theorem isLamVal_pairE (x y : M.Carrier) : M.IsLamVal (M.pairE x y) := isLamVal_interp_lam M _ _

/-! ### The algebra of composition -/

theorem compE_congr {x y x' y' : M.Carrier}
    (h : ∀ d, M.app x (M.app y d) = M.app x' (M.app y' d)) : M.compE x y = M.compE x' y' :=
  M.lamVal_ext (M.isLamVal_compE x y) (M.isLamVal_compE x' y') fun d => by
    rw [app_compE, app_compE]; exact h d

/-- Composition is associative. -/
theorem compE_assoc (x y z : M.Carrier) :
    M.compE (M.compE x y) z = M.compE x (M.compE y z) :=
  M.compE_congr fun d => by simp only [app_compE]

/-- The identity is a left unit for composition on λ-values. -/
theorem compE_idE_left {x : M.Carrier} (hx : M.IsLamVal x) : M.compE M.idE x = x :=
  M.lamVal_ext (M.isLamVal_compE _ _) hx fun d => by simp only [app_compE, app_idE]

/-- The identity is a right unit for composition on λ-values. -/
theorem compE_idE_right {x : M.Carrier} (hx : M.IsLamVal x) : M.compE x M.idE = x :=
  M.lamVal_ext (M.isLamVal_compE _ _) hx fun d => by simp only [app_compE, app_idE]

/-- Composing with a constant function. -/
theorem compE_constE (x y : M.Carrier) : M.compE (M.constE x) y = M.constE x :=
  M.lamVal_ext (M.isLamVal_compE _ _) (M.isLamVal_constE x) fun d => by
    simp only [app_compE, app_constE]

/-! ### Products of retracts -/

/-- The product retract `λp. ⟨a (fst p), b (snd p)⟩`. -/
def prodE (a b : M.Carrier) : M.Carrier :=
  M.interp
    (Lambda.lam (Lambda.lam
      (Lambda.app
        (Lambda.app (Lambda.var 0) (Lambda.app (Lambda.var 5) (Lambda.app (Lambda.var 1)
          (Lambda.var 3))))
        (Lambda.app (Lambda.var 4) (Lambda.app (Lambda.var 1) (Lambda.var 2))))))
    (modelCons M.kSE (modelCons M.kE (modelCons b (modelCons a M.env0))))

theorem isLamVal_prodE (a b : M.Carrier) : M.IsLamVal (M.prodE a b) := isLamVal_interp_lam M _ _

@[simp] theorem app_prodE (a b p : M.Carrier) :
    M.app (M.prodE a b) p = M.pairE (M.app a (M.fstE p)) (M.app b (M.sndE p)) := by
  rw [prodE, M.interp_beta]
  refine M.lamVal_ext (isLamVal_interp_lam M _ _) (M.isLamVal_pairE _ _) fun z => ?_
  rw [M.interp_beta, app_pairE]
  simp only [M.interp_app, M.interp_var, modelCons_zero, modelCons_succ, fstE, sndE]

/-- The first projection out of a product retract, `λp. a (fst p)`. -/
def projFstE (a : M.Carrier) : M.Carrier :=
  M.interp (Lambda.lam (Lambda.app (Lambda.var 2) (Lambda.app (Lambda.var 0) (Lambda.var 1))))
    (modelCons M.kE (modelCons a M.env0))

/-- The second projection out of a product retract, `λp. b (snd p)`. -/
def projSndE (b : M.Carrier) : M.Carrier :=
  M.interp (Lambda.lam (Lambda.app (Lambda.var 2) (Lambda.app (Lambda.var 0) (Lambda.var 1))))
    (modelCons M.kSE (modelCons b M.env0))

theorem isLamVal_projFstE (a : M.Carrier) : M.IsLamVal (M.projFstE a) := isLamVal_interp_lam M _ _
theorem isLamVal_projSndE (b : M.Carrier) : M.IsLamVal (M.projSndE b) := isLamVal_interp_lam M _ _

@[simp] theorem app_projFstE (a p : M.Carrier) :
    M.app (M.projFstE a) p = M.app a (M.fstE p) := by
  rw [projFstE, M.interp_beta]
  simp only [M.interp_app, M.interp_var, modelCons_zero, modelCons_succ, fstE]

@[simp] theorem app_projSndE (b p : M.Carrier) :
    M.app (M.projSndE b) p = M.app b (M.sndE p) := by
  rw [projSndE, M.interp_beta]
  simp only [M.interp_app, M.interp_var, modelCons_zero, modelCons_succ, sndE]

/-- The pairing of two functions, `λz. ⟨f z, g z⟩`. -/
def pairMorE (f g : M.Carrier) : M.Carrier :=
  M.interp
    (Lambda.lam (Lambda.lam
      (Lambda.app (Lambda.app (Lambda.var 0) (Lambda.app (Lambda.var 3) (Lambda.var 1)))
        (Lambda.app (Lambda.var 2) (Lambda.var 1)))))
    (modelCons g (modelCons f M.env0))

theorem isLamVal_pairMorE (f g : M.Carrier) : M.IsLamVal (M.pairMorE f g) :=
  isLamVal_interp_lam M _ _

@[simp] theorem app_pairMorE (f g z : M.Carrier) :
    M.app (M.pairMorE f g) z = M.pairE (M.app f z) (M.app g z) := by
  rw [pairMorE, M.interp_beta]
  refine M.lamVal_ext (isLamVal_interp_lam M _ _) (M.isLamVal_pairE _ _) fun w => ?_
  rw [M.interp_beta, app_pairE]
  simp only [M.interp_app, M.interp_var, modelCons_zero, modelCons_succ]

/-! ### Function spaces of retracts -/

/-- The function-space retract `λf. b ∘ f ∘ a`. -/
def expE (a b : M.Carrier) : M.Carrier :=
  M.interp
    (Lambda.lam (Lambda.lam
      (Lambda.app (Lambda.var 2) (Lambda.app (Lambda.var 1) (Lambda.app (Lambda.var 3)
        (Lambda.var 0))))))
    (modelCons b (modelCons a M.env0))

theorem isLamVal_expE (a b : M.Carrier) : M.IsLamVal (M.expE a b) := isLamVal_interp_lam M _ _

@[simp] theorem app_expE (a b f : M.Carrier) :
    M.app (M.expE a b) f = M.compE b (M.compE f a) := by
  rw [expE, M.interp_beta]
  refine M.lamVal_ext (isLamVal_interp_lam M _ _) (M.isLamVal_compE _ _) fun x => ?_
  rw [M.interp_beta, app_compE, app_compE]
  simp only [M.interp_app, M.interp_var, modelCons_zero, modelCons_succ]

/-- Currying: from `λp. h ⟨x, z⟩` to `λz x. h ⟨x, z⟩`. -/
def curryE (h : M.Carrier) : M.Carrier :=
  M.interp
    (Lambda.lam (Lambda.lam
      (Lambda.app (Lambda.var 2)
        (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 0) (Lambda.var 1)) (Lambda.var 2))))))
    (modelCons h M.env0)

theorem isLamVal_curryE (h : M.Carrier) : M.IsLamVal (M.curryE h) := isLamVal_interp_lam M _ _

theorem isLamVal_app_curryE (h z : M.Carrier) : M.IsLamVal (M.app (M.curryE h) z) := by
  rw [curryE, M.interp_beta]
  exact isLamVal_interp_lam M _ _

@[simp] theorem app_app_curryE (h z x : M.Carrier) :
    M.app (M.app (M.curryE h) z) x = M.app h (M.pairE x z) := by
  rw [curryE, M.interp_beta, M.interp_beta]
  simp only [M.interp_app, M.interp_var, modelCons_zero, modelCons_succ]
  congr 1
  refine M.lamVal_ext (isLamVal_interp_lam M _ _) (M.isLamVal_pairE _ _) fun w => ?_
  rw [M.interp_beta, app_pairE]
  simp only [M.interp_app, M.interp_var, modelCons_zero, modelCons_succ]

/-- Uncurrying: from `λz x. g z x` to `λp. g (snd p) (fst p)`. -/
def uncurryE (g : M.Carrier) : M.Carrier :=
  M.interp
    (Lambda.lam
      (Lambda.app (Lambda.app (Lambda.var 3) (Lambda.app (Lambda.var 0) (Lambda.var 1)))
        (Lambda.app (Lambda.var 0) (Lambda.var 2))))
    (modelCons M.kSE (modelCons M.kE (modelCons g M.env0)))

theorem isLamVal_uncurryE (g : M.Carrier) : M.IsLamVal (M.uncurryE g) := isLamVal_interp_lam M _ _

@[simp] theorem app_uncurryE (g p : M.Carrier) :
    M.app (M.uncurryE g) p = M.app (M.app g (M.sndE p)) (M.fstE p) := by
  rw [uncurryE, M.interp_beta]
  simp only [M.interp_app, M.interp_var, modelCons_zero, modelCons_succ, fstE, sndE]

/-- Post-composition `λf. g ∘ f`. -/
def postCompE (g : M.Carrier) : M.Carrier :=
  M.interp
    (Lambda.lam (Lambda.lam
      (Lambda.app (Lambda.var 2) (Lambda.app (Lambda.var 1) (Lambda.var 0)))))
    (modelCons g M.env0)

theorem isLamVal_postCompE (g : M.Carrier) : M.IsLamVal (M.postCompE g) :=
  isLamVal_interp_lam M _ _

@[simp] theorem app_postCompE (g f : M.Carrier) :
    M.app (M.postCompE g) f = M.compE g f := by
  rw [postCompE, M.interp_beta]
  refine M.lamVal_ext (isLamVal_interp_lam M _ _) (M.isLamVal_compE _ _) fun x => ?_
  rw [M.interp_beta, app_compE]
  simp only [M.interp_app, M.interp_var, modelCons_zero, modelCons_succ]

/-! ### The terminal retract -/

/-- The constant function `λz. I`, the terminal retract. -/
def topE : M.Carrier := M.constE M.idE

theorem isLamVal_topE : M.IsLamVal M.topE := M.isLamVal_constE _

@[simp] theorem app_topE (d : M.Carrier) : M.app M.topE d = M.idE := M.app_constE _ _

end

end LambdaModel

end Lambda
