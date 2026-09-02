/-
Partial combinatory algebras.

A **partial combinatory algebra** (PCA) is the algebraic structure underlying realizability:
a set `A` with a *partial* binary application `a ⬝ b` and two elements `k`, `s` satisfying the
combinatory axioms in their partial form.  Every model of the untyped λ-calculus is a PCA with
a total application (`Start/PCALambdaModel.lean`), and Kleene's first algebra `K₁` — the natural
numbers with Turing application — is the PCA of computability theory
(`Start/PCAKleene.lean`).

The content of this file is **combinatory completeness**: every applicative expression built from
variables and constants can be abstracted over a variable, so that a PCA has "λ-abstraction" for
its own expressions even though it has no binder.

* `Realizability.PCA` — the class: `app : A → A → Part A`, `k`, `s`, with `k a b = a`,
  `s a b ↓` and `s a b c ⊒ (a c) (b c)`;
* `Realizability.papp` (notation `x ⬝ y`) — application extended to partial elements;
* `Realizability.Expr`, `Expr.eval` — applicative expressions and their partial value;
* `Realizability.Expr.abst`, `Realizability.PCA.lam` — the abstraction operator, with
  `Realizability.abst_dom` (an abstraction is always defined) and
  `Realizability.lam_app` (**combinatory completeness**: `(λ n. e) a ⊒ e[a/n]`);
* `Realizability.PCA.i`, `.kI`, `.comp`, `.pairEl`, `.fstComb`, `.sndComb` — the identity, the
  second projection, composition and Church pairing, with their computation rules.

The inequalities are the usual ones of partial algebra: `x ≤ y` in `Part` means that if `x` is
defined then so is `y`, with the same value.  Abstraction only satisfies `e[a/n] ≤ (λ n. e) a`,
which is all that holds in a general PCA.
-/

import Mathlib.Data.Part
import Mathlib.Logic.Function.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Realizability

/-- A **partial combinatory algebra**: a set with a partial application and combinators `k`, `s`.

`k_app` says `k a b = a` (in particular `k a` is defined, which is `k_dom`), `s_dom` says that
`s a b` is always defined, and `s_app` says that `s a b c` is defined and equal to `(a c) (b c)`
*whenever the latter is defined* — the standard partial form of the `s` axiom. -/
class PCA (A : Type u) where
  /-- The partial application of the algebra. -/
  app : A → A → Part A
  /-- The combinator `k`. -/
  k : A
  /-- The combinator `s`. -/
  s : A
  /-- `k a` is always defined. -/
  k_dom : ∀ a : A, (app k a).Dom
  /-- `k a b = a`. -/
  k_app : ∀ a b : A, ((app k a).bind fun f => app f b) = Part.some a
  /-- `s a b` is always defined. -/
  s_dom : ∀ a b : A, ((app s a).bind fun f => app f b).Dom
  /-- `s a b c ⊒ (a c) (b c)`. -/
  s_app : ∀ a b c : A,
    ((app a c).bind fun u => (app b c).bind fun v => app u v)
      ≤ (((app s a).bind fun f => app f b).bind fun g => app g c)

/-- Application extended to partial elements: `x ⬝ y` is defined when both `x` and `y` are and
their values apply. -/
def papp {A : Type u} [PCA A] (x y : Part A) : Part A :=
  x.bind fun a => y.bind fun b => PCA.app a b

@[inherit_doc] scoped infixl:70 " ⬝ " => Realizability.papp

variable {A : Type u} [PCA A]

@[simp] theorem papp_some_some (a b : A) : Part.some a ⬝ Part.some b = PCA.app a b := by
  simp [papp]

theorem papp_some_left (a : A) (y : Part A) : Part.some a ⬝ y = y.bind fun b => PCA.app a b := by
  simp [papp]

theorem papp_some_right (x : Part A) (b : A) : x ⬝ Part.some b = x.bind fun a => PCA.app a b := by
  simp [papp]

theorem some_le_of_mem {α : Type u} {x : Part α} {u : α} (h : u ∈ x) : Part.some u ≤ x :=
    fun _ hv => by
  rwa [Part.mem_some_iff.1 hv]

theorem mem_papp {x y : Part A} {u b z : A} (hu : u ∈ x) (hb : b ∈ y) (hz : z ∈ PCA.app u b) :
    z ∈ x ⬝ y := by
  simp only [papp, Part.mem_bind_iff]
  exact ⟨u, hu, b, hb, hz⟩

theorem papp_mono {x x' y y' : Part A} (hx : x ≤ x') (hy : y ≤ y') : x ⬝ y ≤ x' ⬝ y' := by
  intro v hv
  simp only [papp, Part.mem_bind_iff] at hv ⊢
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  exact ⟨a, hx _ ha, b, hy _ hb, hab⟩

/-! ### The axioms, restated with `⬝` -/

theorem k_papp (a b : A) : (Part.some (PCA.k : A) ⬝ Part.some a) ⬝ Part.some b = Part.some a := by
  simpa [papp_some_right] using PCA.k_app a b

theorem s_papp_dom (a b : A) :
    ((Part.some (PCA.s : A) ⬝ Part.some a) ⬝ Part.some b).Dom := by
  simpa [papp_some_right] using PCA.s_dom a b

theorem s_papp (a b c : A) :
    (Part.some a ⬝ Part.some c) ⬝ (Part.some b ⬝ Part.some c)
      ≤ ((Part.some (PCA.s : A) ⬝ Part.some a) ⬝ Part.some b) ⬝ Part.some c := by
  simpa [papp, Part.bind_some] using PCA.s_app a b c

/-! ### The identity combinator -/

namespace PCA

/-- The identity combinator `i = s k k`. -/
noncomputable def i (A : Type u) [PCA A] : A :=
  (((PCA.app (PCA.s : A) PCA.k).bind fun f => PCA.app f PCA.k)).get (PCA.s_dom _ _)

theorem some_i : Part.some (i A) = (Part.some (s : A) ⬝ Part.some (k : A)) ⬝ Part.some (k : A) := by
  rw [papp_some_right, papp_some_some]
  exact Part.some_get _

@[simp] theorem i_app (a : A) : PCA.app (i A) a = Part.some a := by
  obtain ⟨u, hu⟩ : ∃ u : A, PCA.app (k : A) a = Part.some u :=
    ⟨_, (Part.some_get (PCA.k_dom a)).symm⟩
  have hk : PCA.app u u = Part.some a := by
    have h := PCA.k_app a u
    rwa [hu, Part.bind_some] at h
  have hs := s_papp (k : A) (k : A) a
  rw [← some_i] at hs
  have hmem : a ∈ (Part.some (k : A) ⬝ Part.some a) ⬝ (Part.some (k : A) ⬝ Part.some a) := by
    rw [papp_some_some, hu, papp_some_some, hk]
    exact Part.mem_some _
  have hfin := hs a hmem
  rw [papp_some_some] at hfin
  exact Part.eq_some_iff.2 hfin

@[simp] theorem i_papp (a : A) : Part.some (i A) ⬝ Part.some a = Part.some a := by
  simp

end PCA

/-! ### Applicative expressions -/

/-- An applicative expression over a PCA: variables, constants and application. -/
inductive Expr (A : Type u) : Type u
  /-- A variable. -/
  | var : ℕ → Expr A
  /-- A constant of the algebra. -/
  | const : A → Expr A
  /-- Application. -/
  | app : Expr A → Expr A → Expr A
  deriving Inhabited

namespace Expr

/-- The value of an expression in an environment: a partial element of the algebra. -/
def eval : Expr A → (ℕ → A) → Part A
  | Expr.var n, ρ => Part.some (ρ n)
  | Expr.const a, _ => Part.some a
  | Expr.app e₁ e₂, ρ => (e₁.eval ρ) ⬝ (e₂.eval ρ)

@[simp] theorem eval_var (n : ℕ) (ρ : ℕ → A) : (Expr.var n : Expr A).eval ρ = Part.some (ρ n) :=
  rfl

@[simp] theorem eval_const (a : A) (ρ : ℕ → A) : (Expr.const a : Expr A).eval ρ = Part.some a :=
  rfl

@[simp] theorem eval_app (e₁ e₂ : Expr A) (ρ : ℕ → A) :
    (Expr.app e₁ e₂).eval ρ = (e₁.eval ρ) ⬝ (e₂.eval ρ) := rfl

/-- **Abstraction** of an expression over a variable: the bracket abstraction `λ* n. e`. -/
noncomputable def abst (n : ℕ) : Expr A → Expr A
  | Expr.var m => if m = n then Expr.const (PCA.i A) else Expr.app (Expr.const PCA.k) (Expr.var m)
  | Expr.const a => Expr.app (Expr.const PCA.k) (Expr.const a)
  | Expr.app e₁ e₂ => Expr.app (Expr.app (Expr.const PCA.s) (e₁.abst n)) (e₂.abst n)

end Expr

/-- An abstraction is always defined. -/
theorem abst_dom (n : ℕ) (e : Expr A) (ρ : ℕ → A) : ((e.abst n).eval ρ).Dom := by
  induction e with
  | var m =>
      by_cases h : m = n
      · simp only [Expr.abst, if_pos h, Expr.eval_const]
        trivial
      · simp only [Expr.abst, if_neg h, Expr.eval_app, Expr.eval_const, Expr.eval_var,
          papp_some_some]
        exact PCA.k_dom _
  | const a =>
      simp only [Expr.abst, Expr.eval_app, Expr.eval_const, papp_some_some]
      exact PCA.k_dom a
  | app e₁ e₂ ih₁ ih₂ =>
      obtain ⟨x₁, h₁⟩ : ∃ x : A, (e₁.abst n).eval ρ = Part.some x :=
        ⟨_, (Part.some_get ih₁).symm⟩
      obtain ⟨x₂, h₂⟩ : ∃ x : A, (e₂.abst n).eval ρ = Part.some x :=
        ⟨_, (Part.some_get ih₂).symm⟩
      simp only [Expr.abst, Expr.eval_app, Expr.eval_const, h₁, h₂]
      exact s_papp_dom _ _

/-- **Combinatory completeness**, expression form: applying the abstraction of `e` over `n` to an
element `a` computes at least the value of `e` with `n` set to `a`. -/
theorem abst_app (n : ℕ) (e : Expr A) (ρ : ℕ → A) (a : A) :
    e.eval (Function.update ρ n a) ≤ ((e.abst n).eval ρ) ⬝ Part.some a := by
  induction e with
  | var m =>
      by_cases h : m = n
      · subst h
        simp [Expr.abst]
      · simp only [Expr.abst, if_neg h, Expr.eval_var, Function.update_of_ne h,
          Expr.eval_app, Expr.eval_const, papp_some_some]
        rw [papp_some_right]
        exact le_of_eq (PCA.k_app _ _).symm
  | const b =>
      simp only [Expr.abst, Expr.eval_const, Expr.eval_app, papp_some_some]
      rw [papp_some_right]
      exact le_of_eq (PCA.k_app _ _).symm
  | app e₁ e₂ ih₁ ih₂ =>
      obtain ⟨x₁, h₁⟩ : ∃ x : A, (e₁.abst n).eval ρ = Part.some x :=
        ⟨_, (Part.some_get (abst_dom n e₁ ρ)).symm⟩
      obtain ⟨x₂, h₂⟩ : ∃ x : A, (e₂.abst n).eval ρ = Part.some x :=
        ⟨_, (Part.some_get (abst_dom n e₂ ρ)).symm⟩
      have hstep : (e₁.eval (Function.update ρ n a)) ⬝ (e₂.eval (Function.update ρ n a))
          ≤ (Part.some x₁ ⬝ Part.some a) ⬝ (Part.some x₂ ⬝ Part.some a) := by
        refine papp_mono ?_ ?_
        · simpa [h₁] using ih₁
        · simpa [h₂] using ih₂
      refine le_trans (le_of_eq (by simp)) (le_trans hstep ?_)
      simpa [Expr.abst, h₁, h₂] using s_papp x₁ x₂ a

namespace PCA

/-- The element of the algebra representing the abstraction `λ* n. e` in the environment `ρ`. -/
noncomputable def lam (n : ℕ) (e : Expr A) (ρ : ℕ → A) : A :=
  ((e.abst n).eval ρ).get (abst_dom n e ρ)

theorem eval_abst (n : ℕ) (e : Expr A) (ρ : ℕ → A) :
    (e.abst n).eval ρ = Part.some (lam n e ρ) := (Part.some_get _).symm

/-- **Combinatory completeness**. -/
theorem lam_app (n : ℕ) (e : Expr A) (ρ : ℕ → A) (a : A) :
    e.eval (Function.update ρ n a) ≤ PCA.app (lam n e ρ) a := by
  have := abst_app n e ρ a
  rwa [eval_abst, papp_some_some] at this

/-- Iterated abstraction: applying `λ* n. λ* m. e` to `a` yields exactly `λ* m. e[a/n]`. -/
theorem lam_lam_app (n m : ℕ) (e : Expr A) (ρ : ℕ → A) (a : A) :
    PCA.app (lam n (e.abst m) ρ) a = Part.some (lam m e (Function.update ρ n a)) := by
  have h := lam_app n (e.abst m) ρ a
  rw [eval_abst] at h
  exact Part.eq_some_iff.2 (h _ (Part.mem_some _))

/-- A default environment, using the constant `k`. -/
noncomputable def env0 (A : Type u) [PCA A] : ℕ → A := fun _ => (k : A)

/-- `λ x. e`, for an expression `e` in the variable `0`. -/
noncomputable def lam1 (e : Expr A) : A := lam 0 e (env0 A)

theorem lam1_app (e : Expr A) (a : A) :
    e.eval (Function.update (env0 A) 0 a) ≤ Part.some (lam1 e) ⬝ Part.some a := by
  rw [papp_some_some]
  exact lam_app 0 e (env0 A) a

/-- `λ x y. e`, for an expression `e` in the variables `0` and `1`. -/
noncomputable def lam2 (e : Expr A) : A := lam 0 (e.abst 1) (env0 A)

theorem lam2_app (e : Expr A) (a : A) :
    Part.some (lam2 e) ⬝ Part.some a
      = Part.some (lam 1 e (Function.update (env0 A) 0 a)) := by
  rw [papp_some_some, lam2, lam_lam_app]

theorem lam2_app_app (e : Expr A) (a b : A) :
    e.eval (Function.update (Function.update (env0 A) 0 a) 1 b)
      ≤ (Part.some (lam2 e) ⬝ Part.some a) ⬝ Part.some b := by
  rw [lam2_app, papp_some_some]
  exact lam_app 1 e (Function.update (env0 A) 0 a) b

theorem lam2_app_dom (e : Expr A) (a : A) :
    (Part.some (lam2 e) ⬝ Part.some a).Dom := by
  rw [lam2_app]
  trivial

/-- `λ x y z. e`, for an expression `e` in the variables `0`, `1` and `2`. -/
noncomputable def lam3 (e : Expr A) : A := lam 0 ((e.abst 2).abst 1) (env0 A)

theorem lam3_app (e : Expr A) (a : A) :
    Part.some (lam3 e) ⬝ Part.some a
      = Part.some (lam 1 (e.abst 2) (Function.update (env0 A) 0 a)) := by
  rw [papp_some_some, lam3, lam_lam_app]

theorem lam3_app_app (e : Expr A) (a b : A) :
    (Part.some (lam3 e) ⬝ Part.some a) ⬝ Part.some b
      = Part.some (lam 2 e (Function.update (Function.update (env0 A) 0 a) 1 b)) := by
  rw [lam3_app, papp_some_some, lam_lam_app]

theorem lam3_app_app_app (e : Expr A) (a b c : A) :
    e.eval (Function.update (Function.update (Function.update (env0 A) 0 a) 1 b) 2 c)
      ≤ ((Part.some (lam3 e) ⬝ Part.some a) ⬝ Part.some b) ⬝ Part.some c := by
  rw [lam3_app_app, papp_some_some]
  exact lam_app 2 e _ c

theorem lam3_app_dom (e : Expr A) (a : A) : (Part.some (lam3 e) ⬝ Part.some a).Dom := by
  rw [lam3_app]; trivial

theorem lam3_app_app_dom (e : Expr A) (a b : A) :
    ((Part.some (lam3 e) ⬝ Part.some a) ⬝ Part.some b).Dom := by
  rw [lam3_app_app]; trivial

/-- The combinator `k i = λxy. y`, the second projection. -/
noncomputable def kI (A : Type u) [PCA A] : A :=
  lam 0 (Expr.abst 1 (Expr.var 1)) (env0 A)

theorem kI_app (a b : A) :
    (Part.some (kI A) ⬝ Part.some a) ⬝ Part.some b = Part.some b := by
  simp only [papp_some_some, kI]
  rw [lam_lam_app, papp_some_some]
  have h := lam_app 1 (Expr.var 1) (Function.update (env0 A) 0 a) b
  refine Part.eq_some_iff.2 (h b ?_)
  simp

theorem k_app_app (a b : A) :
    (Part.some (k : A) ⬝ Part.some a) ⬝ Part.some b = Part.some a := k_papp a b

/-- Composition: `comp f g` applies `f` after `g`. -/
noncomputable def comp (f g : A) : A :=
  lam 0 (Expr.app (Expr.const f) (Expr.app (Expr.const g) (Expr.var 0))) (env0 A)

theorem comp_app (f g a : A) :
    (Part.some f ⬝ (Part.some g ⬝ Part.some a)) ≤ Part.some (comp f g) ⬝ Part.some a := by
  rw [papp_some_some (comp f g) a]
  simp only [comp]
  refine le_trans (le_of_eq ?_) (lam_app 0 _ (env0 A) a)
  simp

/-- The body `p x y = λf. f x y` of the Church pairing, as an expression in the variables
`0` (first component), `1` (second component) and `2` (the continuation). -/
def pairBody (A : Type u) [PCA A] : Expr A :=
  Expr.app (Expr.app (Expr.var 2) (Expr.var 0)) (Expr.var 1)

/-- Church pairing of two elements. -/
noncomputable def pairEl (a b : A) : A :=
  lam 2 (pairBody A) (Function.update (Function.update (env0 A) 0 a) 1 b)

/-- The Church pairing **combinator**, `λxyf. f x y`. -/
noncomputable def pairComb (A : Type u) [PCA A] : A :=
  lam 0 (((pairBody A).abst 2).abst 1) (env0 A)

theorem pairComb_app (a b : A) :
    (Part.some (pairComb A) ⬝ Part.some a) ⬝ Part.some b = Part.some (pairEl a b) := by
  rw [papp_some_some (pairComb A) a]
  simp only [pairComb]
  rw [lam_lam_app, papp_some_some, lam_lam_app]
  rfl

theorem pairEl_app (a b f : A) :
    ((Part.some f ⬝ Part.some a) ⬝ Part.some b) ≤ Part.some (pairEl a b) ⬝ Part.some f := by
  rw [papp_some_some (pairEl a b) f]
  simp only [pairEl]
  refine le_trans (le_of_eq ?_) (lam_app 2 _ _ f)
  simp [pairBody, Function.update_of_ne]

/-- The first projection combinator, `λp. p k`. -/
noncomputable def fstComb (A : Type u) [PCA A] : A :=
  lam 0 (Expr.app (Expr.var 0) (Expr.const (k : A))) (env0 A)

/-- The second projection combinator, `λp. p (k i)`. -/
noncomputable def sndComb (A : Type u) [PCA A] : A :=
  lam 0 (Expr.app (Expr.var 0) (Expr.const (kI A))) (env0 A)

theorem fstComb_pairEl (a b : A) :
    Part.some (fstComb A) ⬝ Part.some (pairEl a b) = Part.some a := by
  have h := lam_app 0 (Expr.app (Expr.var 0) (Expr.const (k : A))) (env0 A) (pairEl a b)
  rw [papp_some_some]
  refine Part.eq_some_iff.2 (h a ?_)
  have h2 : a ∈ (Part.some (pairEl a b) ⬝ Part.some (k : A)) :=
    (pairEl_app a b (k : A)) _ (by rw [k_papp]; exact Part.mem_some _)
  simpa [fstComb] using h2

theorem sndComb_pairEl (a b : A) :
    Part.some (sndComb A) ⬝ Part.some (pairEl a b) = Part.some b := by
  have h := lam_app 0 (Expr.app (Expr.var 0) (Expr.const (kI A))) (env0 A) (pairEl a b)
  rw [papp_some_some]
  refine Part.eq_some_iff.2 (h b ?_)
  have h2 : b ∈ (Part.some (pairEl a b) ⬝ Part.some (kI A)) :=
    (pairEl_app a b (kI A)) _ (by rw [kI_app]; exact Part.mem_some _)
  simpa [sndComb] using h2

end PCA

end Realizability
