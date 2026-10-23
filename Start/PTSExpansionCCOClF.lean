import Start.PTSExpansionCCOSkel

/-!
# Series V, big round, run 2, item B1: level-generic classifiers of `CC^ω` expressions
(row M29-EP-CCOMEGA)

Round 4 run 2 chose to classify kind-level functions by *values* (`SkF.SkT.eval`), not by
syntactic skeletons.  This module makes the corresponding classifier of expressions
*environment-based*: a classifier is given by a class type `C`, the classes of the sorts, and
three combinators for application, abstraction and product, where the abstraction and product
combinators receive the class of the body **as a function of the class of the bound variable**
(not as a syntactic skeleton with a shifted variable).

* `clF` — the classifier `clF ρ M` relative to an environment `ρ : ℕ → C` of classes for the free
  variables, by structural recursion on `M`;
* `clF_rename` — classification commutes with renaming;
* **`clF_subst`** — the substitution lemma: `clF ρ (M.subst σ) = clF (fun n => clF ρ (σ n)) M`;
* **`clF_instantiate`** — `clF ρ (b[A/0]) = clF (cons (clF ρ A) ρ) b`, the level-generic
  `CCO.clF_subst` asked for by the board (in semantic form: the class of `A` is substituted
  for the variable, not its skeleton into a skeleton);
* **`clF_beta_of`** — β-invariance at a redex `(λx:A. b) U`, given only the β-law of the
  combinators at the classes involved (`appF (lamF cA f) cU = f cU`);
* `clF_beta` — if the β-law holds for all classes, the classifier is invariant under root
  β-steps (for `CC^ω` the β-law can only hold on well-classified arguments, since a class type
  with all its own function spaces is not a Lean inductive type: `C → C` is a negative occurrence).

These equations hold for *every* choice of combinators: the substitution lemma is a property of
environment semantics, not of the combinators.  What remains for the CC^ω classifier is the choice
of a class type that also classifies constructors polymorphic in kind variables
(`λK : Type ℓ. t` with `t` a constructor); see the notes (`docs/goal/evidence/M29-EP.md`).
-/

set_option autoImplicit false

universe u

namespace PureTypeSystem.CCO

/-- The data of an environment-based classifier with class type `C`. -/
structure ClfData (C : Type u) where
  prop : C
  type : ℕ → C
  appF : C → C → C
  lamF : C → (C → C) → C
  piF : C → (C → C) → C

/-- Extension of an environment by a class for the variable `0`. -/
def envCons {C : Type u} (v : C) (ρ : ℕ → C) : ℕ → C
  | 0 => v
  | n + 1 => ρ n

variable {C : Type u} (D : ClfData C)

/-- **The environment-based classifier.** -/
def clF : (ℕ → C) → Expr CSrt → C
  | ρ, .var n => ρ n
  | _, .sort .prop => D.prop
  | _, .sort (.type ℓ) => D.type ℓ
  | ρ, .app F U => D.appF (clF ρ F) (clF ρ U)
  | ρ, .lam A b => D.lamF (clF ρ A) (fun v => clF (envCons v ρ) b)
  | ρ, .pi A B => D.piF (clF ρ A) (fun v => clF (envCons v ρ) B)

theorem envCons_liftRen (v : C) (ρ : ℕ → C) (r : ℕ → ℕ) :
    envCons v ρ ∘ Expr.liftRen r = envCons v (ρ ∘ r) := by
  funext n; cases n <;> rfl

/-- Classification commutes with renaming. -/
theorem clF_rename (M : Expr CSrt) :
    ∀ (r : ℕ → ℕ) (ρ : ℕ → C), clF D ρ (M.rename r) = clF D (ρ ∘ r) M := by
  induction M with
  | var n => intros; rfl
  | sort s => intros; cases s <;> rfl
  | app F U ihF ihU => intro r ρ; simp only [Expr.rename, clF, ihF, ihU]
  | lam A b ihA ihb =>
    intro r ρ
    simp only [Expr.rename, clF, ihA]
    congr 1
    funext v
    rw [ihb, envCons_liftRen]
  | pi A B ihA ihB =>
    intro r ρ
    simp only [Expr.rename, clF, ihA]
    congr 1
    funext v
    rw [ihB, envCons_liftRen]

theorem clF_liftSub (v : C) (ρ : ℕ → C) (σ : ℕ → Expr CSrt) :
    (fun n => clF D (envCons v ρ) (Expr.liftSub σ n)) = envCons v (fun n => clF D ρ (σ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Expr.liftSub, envCons]
    rw [clF_rename]
    rfl

/-- **The substitution lemma** for environment-based classifiers. -/
theorem clF_subst (M : Expr CSrt) :
    ∀ (σ : ℕ → Expr CSrt) (ρ : ℕ → C),
      clF D ρ (M.subst σ) = clF D (fun n => clF D ρ (σ n)) M := by
  induction M with
  | var n => intros; rfl
  | sort s => intros; cases s <;> rfl
  | app F U ihF ihU => intro σ ρ; simp only [Expr.subst, clF, ihF, ihU]
  | lam A b ihA ihb =>
    intro σ ρ
    simp only [Expr.subst, clF, ihA]
    congr 1
    funext v
    rw [ihb, clF_liftSub]
  | pi A B ihA ihB =>
    intro σ ρ
    simp only [Expr.subst, clF, ihA]
    congr 1
    funext v
    rw [ihB, clF_liftSub]

/-- **`clF_instantiate`**: the class of `b[A/0]` is the class of `b` with the class of `A` for
the variable `0` (the level-generic `CCO.clF_subst`, semantic form). -/
theorem clF_instantiate (ρ : ℕ → C) (b A : Expr CSrt) :
    clF D ρ (b.instantiate A) = clF D (envCons (clF D ρ A) ρ) b := by
  rw [Expr.instantiate, clF_subst]
  congr 1
  funext n
  cases n <;> rfl

/-- **β-invariance at a redex**, given the β-law of the combinators at the classes involved. -/
theorem clF_beta_of (ρ : ℕ → C) (A b U : Expr CSrt)
    (hβ : D.appF (D.lamF (clF D ρ A) (fun v => clF D (envCons v ρ) b)) (clF D ρ U) =
      clF D (envCons (clF D ρ U) ρ) b) :
    clF D ρ (.app (.lam A b) U) = clF D ρ (b.instantiate U) := by
  rw [clF_instantiate]
  exact hβ

/-- The combinators satisfy the β-law **everywhere** if abstraction is semantic: then the
classifier is invariant under every β-step at the root. -/
theorem clF_beta (hβ : ∀ cA f cU, D.appF (D.lamF cA f) cU = f cU) (ρ : ℕ → C)
    (A b U : Expr CSrt) : clF D ρ (.app (.lam A b) U) = clF D ρ (b.instantiate U) :=
  clF_beta_of D ρ A b U (hβ _ _ _)

end PureTypeSystem.CCO
