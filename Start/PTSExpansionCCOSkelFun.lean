/-!
# Series V, round 4, run 2, part B: kind-level functions in the skeletons of `CC^ω`
(row M29-EP-CCOMEGA)

Round 4 run 1 stopped at `CCO.clO_beta_fails`: the first-order classifier gives
`(λK : Type 0. K) Prop` the class `obj` and its reduct `Prop` the class `kind 0 ∗`.  The fix is to
classify kind-level functions by terms of a stratified simply typed calculus of skeletons, one base
sort per level `Type ℓ`.

This module gives that calculus and the route chosen for its β-theory:

* `SkTy` — skeleton types: `base ℓ` (skeletons of kinds of level `ℓ`) and arrows (kind-level
  functions); `SkTy.lev` is the level of a skeleton type;
* `Var`, `SkT` — intrinsically typed skeleton terms with variables, `λ` and application;
* `SkT.rename`, `SkT.subst` and the β-step `SkT.Step` (closed under all term formers);
* `SkT.eval` — evaluation into a set-theoretic model `Sem D` (`Sem D (base ℓ) = D ℓ`,
  `Sem D (arr a b) = Sem D a → Sem D b`).  It is defined by structural recursion on the term, so it
  is total without a normalization proof: this replaces the normalization of skeletons by recursion
  on the level (the shorter route: the classes of kind-level functions are values in the model,
  not syntactic normal forms);
* **`SkT.eval_subst`** (substitution lemma) and **`SkT.eval_step`**: evaluation is invariant under
  β-reduction of skeleton terms, and `SkT.eval_steps` for its reflexive–transitive closure.

The classifier of `CC^ω` expressions into `SkT` (the level-generic replacement of `CCO.clO`) and
its β-invariance `CCO.clO_beta` are the next lemmas; see `docs/goal/evidence/M29-EP.md`.
-/

set_option autoImplicit false

namespace PureTypeSystem.CCO.SkF

/-- Skeleton types: `base ℓ` classifies the skeletons of kinds of level `ℓ`; `arr a b` classifies
kind-level functions. -/
inductive SkTy : Type where
  | base : Nat → SkTy
  | arr : SkTy → SkTy → SkTy
  deriving DecidableEq

/-- The level of a skeleton type: a kind-level function from level `ℓ` to level `ℓ'` lives one
level above both (predicativity of the rules `(Type i, Type j, Type (max i j))` for its type). -/
def SkTy.lev : SkTy → Nat
  | .base ℓ => ℓ
  | .arr a b => max (a.lev + 1) b.lev

/-- Typed de Bruijn variables. -/
inductive Var : List SkTy → SkTy → Type where
  | zero {Γ : List SkTy} {a : SkTy} : Var (a :: Γ) a
  | succ {Γ : List SkTy} {a b : SkTy} : Var Γ a → Var (b :: Γ) a

/-- Intrinsically typed skeleton terms; `cst ℓ` is an opaque skeleton constant of level `ℓ`
(the skeleton `∗` of a sort-headed kind). -/
inductive SkT : List SkTy → SkTy → Type where
  | var {Γ : List SkTy} {a : SkTy} : Var Γ a → SkT Γ a
  | cst {Γ : List SkTy} (ℓ : Nat) : SkT Γ (.base ℓ)
  | lam {Γ : List SkTy} {a b : SkTy} : SkT (a :: Γ) b → SkT Γ (.arr a b)
  | app {Γ : List SkTy} {a b : SkTy} : SkT Γ (.arr a b) → SkT Γ a → SkT Γ b

namespace SkT

/-- Renamings and substitutions. -/
abbrev Ren (Γ Δ : List SkTy) := ∀ {a : SkTy}, Var Γ a → Var Δ a
abbrev Sub (Γ Δ : List SkTy) := ∀ {a : SkTy}, Var Γ a → SkT Δ a

def Ren.up {Γ Δ : List SkTy} {b : SkTy} (r : Ren Γ Δ) : Ren (b :: Γ) (b :: Δ)
  | _, .zero => .zero
  | _, .succ v => .succ (r v)

def rename {Γ Δ : List SkTy} (r : Ren Γ Δ) : {a : SkTy} → SkT Γ a → SkT Δ a
  | _, .var v => .var (r v)
  | _, .cst ℓ => .cst ℓ
  | _, .lam t => .lam (rename (Ren.up r) t)
  | _, .app t u => .app (rename r t) (rename r u)

def Sub.up {Γ Δ : List SkTy} {b : SkTy} (σ : Sub Γ Δ) : Sub (b :: Γ) (b :: Δ)
  | _, .zero => .var .zero
  | _, .succ v => rename (fun w => .succ w) (σ v)

def subst {Γ Δ : List SkTy} (σ : Sub Γ Δ) : {a : SkTy} → SkT Γ a → SkT Δ a
  | _, .var v => σ v
  | _, .cst ℓ => .cst ℓ
  | _, .lam t => .lam (subst (Sub.up σ) t)
  | _, .app t u => .app (subst σ t) (subst σ u)

/-- The substitution of `u` for the variable `0`. -/
def sub0 {Γ : List SkTy} {b : SkTy} (u : SkT Γ b) : Sub (b :: Γ) Γ
  | _, .zero => u
  | _, .succ v => .var v

/-- One β-step of skeleton terms, closed under all term formers. -/
inductive Step : {Γ : List SkTy} → {a : SkTy} → SkT Γ a → SkT Γ a → Prop where
  | beta {Γ : List SkTy} {a b : SkTy} (t : SkT (a :: Γ) b) (u : SkT Γ a) :
      Step (.app (.lam t) u) (subst (sub0 u) t)
  | lam {Γ : List SkTy} {a b : SkTy} {t t' : SkT (a :: Γ) b} : Step t t' → Step (.lam t) (.lam t')
  | appL {Γ : List SkTy} {a b : SkTy} {t t' : SkT Γ (.arr a b)} (u : SkT Γ a) :
      Step t t' → Step (.app t u) (.app t' u)
  | appR {Γ : List SkTy} {a b : SkTy} (t : SkT Γ (.arr a b)) {u u' : SkT Γ a} :
      Step u u' → Step (.app t u) (.app t u')

/-- Reflexive–transitive closure of `Step`. -/
inductive Steps {Γ : List SkTy} {a : SkTy} : SkT Γ a → SkT Γ a → Prop where
  | refl (t : SkT Γ a) : Steps t t
  | tail {t u v : SkT Γ a} : Steps t u → Step u v → Steps t v

/-! ### The set-theoretic model -/

/-- The semantic value of a skeleton type over base domains `D ℓ`. -/
def Sem (D : Nat → Type) : SkTy → Type
  | .base ℓ => D ℓ
  | .arr a b => Sem D a → Sem D b

/-- Environments. -/
abbrev Env (D : Nat → Type) (Γ : List SkTy) := ∀ {a : SkTy}, Var Γ a → Sem D a

def Env.cons {D : Nat → Type} {Γ : List SkTy} {a : SkTy} (x : Sem D a) (ρ : Env D Γ) :
    Env D (a :: Γ)
  | _, .zero => x
  | _, .succ v => ρ v

/-- Evaluation; `c ℓ` interprets the constant of level `ℓ`. -/
def eval {D : Nat → Type} (c : ∀ ℓ, D ℓ) {Γ : List SkTy} : {a : SkTy} → SkT Γ a → Env D Γ → Sem D a
  | _, .var v, ρ => ρ v
  | _, .cst ℓ, _ => c ℓ
  | _, .lam t, ρ => fun x => eval c t (Env.cons x ρ)
  | _, .app t u, ρ => (eval c t ρ) (eval c u ρ)

variable {D : Nat → Type} (c : ∀ ℓ, D ℓ)

theorem eval_rename {Γ Δ : List SkTy} {a : SkTy} (t : SkT Γ a) :
    ∀ (r : Ren Γ Δ) (ρ : Env D Δ), eval c (rename r t) ρ = eval c t (fun v => ρ (r v)) := by
  induction t generalizing Δ with
  | var v => intro r ρ; rfl
  | cst ℓ => intro r ρ; rfl
  | lam t ih =>
    intro r ρ
    funext x
    simp only [rename, eval]
    rw [ih]
    congr 1
    funext b v
    cases v <;> rfl
  | app t u iht ihu => intro r ρ; simp only [rename, eval]; rw [iht, ihu]

/-- **The substitution lemma** for the model. -/
theorem eval_subst {Γ Δ : List SkTy} {a : SkTy} (t : SkT Γ a) :
    ∀ (σ : Sub Γ Δ) (ρ : Env D Δ), eval c (subst σ t) ρ = eval c t (fun v => eval c (σ v) ρ) := by
  induction t generalizing Δ with
  | var v => intro σ ρ; rfl
  | cst ℓ => intro σ ρ; rfl
  | lam t ih =>
    intro σ ρ
    funext x
    simp only [subst, eval]
    rw [ih]
    congr 1
    funext b v
    cases v with
    | zero => rfl
    | succ w =>
      simp only [Sub.up, Env.cons]
      rw [eval_rename]
      rfl
  | app t u iht ihu => intro σ ρ; simp only [subst, eval]; rw [iht, ihu]

/-- **β-invariance of evaluation**: one β-step of skeleton terms does not change the value. -/
theorem eval_step {Γ : List SkTy} {a : SkTy} {t t' : SkT Γ a} (h : Step t t') :
    ∀ ρ : Env D Γ, eval c t ρ = eval c t' ρ := by
  induction h with
  | beta t u =>
    intro ρ
    simp only [eval]
    rw [eval_subst]
    congr 1
    funext b v
    cases v <;> rfl
  | lam _ ih => intro ρ; funext x; exact ih _
  | appL u _ ih => intro ρ; simp only [eval]; rw [ih]
  | appR t _ ih => intro ρ; simp only [eval]; rw [ih]

theorem eval_steps {Γ : List SkTy} {a : SkTy} {t t' : SkT Γ a} (h : Steps t t') (ρ : Env D Γ) :
    eval c t ρ = eval c t' ρ := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [ih, eval_step c hs]

/-- The example of `CCO.clO_beta_fails`, now classified: the skeleton of `λK : Type 0. K` applied
to the skeleton of `Prop` evaluates to the value of the skeleton of `Prop`. -/
theorem eval_idKind_beta (ρ : Env D []) :
    eval c (.app (.lam (.var .zero)) (.cst 0) : SkT [] (.base 0)) ρ = eval c (.cst 0) ρ :=
  eval_step c (Step.beta _ _) ρ

end SkT

end PureTypeSystem.CCO.SkF
