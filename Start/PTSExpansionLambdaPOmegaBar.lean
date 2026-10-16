/-
**Toward expansion postponement for λPω̲ (M29-EP-CUBE-REST): classification and kind erasure.**

Steps 1 and 2 of the two-level hereditary substitution plan for λPω̲ (rules `(∗,∗)`, `(∗,□)`,
`(□,□)`).  Expansion postponement for λPω̲ is *not* proved here.

* `cube_classification`: in every corner of the cube, a legal term is a kind (its type is `□`), a
  constructor (its type has type `□`) or an object (its type has type `∗`).
* `Expr.eraseK`: the erasure of a kind to a simple type; object binders `Π x:A. K` are dropped,
  constructor binders `Π α:K₁. K₂` become arrows.  `eraseK_rename`, `eraseK_subst`: the erasure
  is unchanged by renaming and by every substitution whose values are not syntactic kinds and
  have trivial kind erasure (`NoKindSubst`; in λPω̲ only objects and constructors are substituted,
  and without the rule `(□,∗)` no type quantifies over a kind).
  This is the measure of constructor-level hereditary substitution.
-/

import Start.PTSExpansionLambdaP

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

universe u

open LambdaPi (Srt)

/-! ### Classification -/

/-- **Classification**: a legal term is a kind, a constructor or an object. -/
theorem cube_classification (f : CubeFeatures) {Γ : List (Expr Srt)} {M T : Expr Srt}
    (h : HasType (cubeSpec f) Γ M T) :
    T = .sort .box ∨ HasType (cubeSpec f) Γ T (.sort .box) ∨
      HasType (cubeSpec f) Γ T (.sort .star) := by
  rcases h.regularity with ⟨s, rfl⟩ | ⟨s, hT⟩
  · cases s with
    | box => exact .inl rfl
    | star => exact .inr (.inl (HasType.sort_of_valid h.valid ⟨rfl, rfl⟩))
  · cases s with
    | box => exact .inr (.inl hT)
    | star => exact .inr (.inr hT)

/-! ### Kind erasure -/

namespace Expr

variable {S : Type u}

/-- Boolean version of `IsKind`. -/
def isKindB : Expr S → Bool
  | sort _ => true
  | pi _ B => isKindB B
  | _ => false

theorem isKindB_iff (M : Expr S) : M.isKindB = true ↔ M.IsKind := by
  induction M with
  | var n => simp [isKindB, IsKind]
  | sort s => simp [isKindB, IsKind]
  | app f a _ _ => simp [isKindB, IsKind]
  | lam A b _ _ => simp [isKindB, IsKind]
  | pi A B _ ihB => exact ihB

/-- Erasure of kinds: object binders are dropped, constructor binders become arrows. -/
def eraseK : Expr S → STy
  | pi A B => if A.isKindB then .arr (eraseK A) (eraseK B) else eraseK B
  | _ => .base

theorem isKindB_rename (M : Expr S) (ρ : Nat → Nat) : (M.rename ρ).isKindB = M.isKindB := by
  have h1 := isKindB_iff (M.rename ρ)
  have h2 := isKindB_iff M
  rw [isKind_rename] at h1
  cases hM : M.isKindB <;> cases hM' : (M.rename ρ).isKindB <;> simp_all

theorem eraseK_rename (M : Expr S) (ρ : Nat → Nat) : (M.rename ρ).eraseK = M.eraseK := by
  induction M generalizing ρ with
  | var n => rfl
  | sort s => rfl
  | app f a _ _ => rfl
  | lam A b _ _ => rfl
  | pi A B ihA ihB => simp only [rename, eraseK, isKindB_rename, ihA, ihB]

/-- Substitutions whose values are not syntactic kinds and have trivial kind erasure (true of
the objects and constructors of λPω̲, which has no rule `(□,∗)`). -/
def NoKindSubst (σ : Nat → Expr S) : Prop := ∀ n, (σ n).isKindB = false ∧ (σ n).eraseK = .base

theorem NoKindSubst.lift {σ : Nat → Expr S} (h : NoKindSubst σ) : NoKindSubst (liftSub σ) := by
  intro n
  cases n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n => simp only [liftSub, isKindB_rename, eraseK_rename]; exact h n

theorem isKindB_subst (M : Expr S) {σ : Nat → Expr S} (hσ : NoKindSubst σ) :
    (M.subst σ).isKindB = M.isKindB := by
  induction M generalizing σ with
  | var n => exact (hσ n).1
  | sort s => rfl
  | app f a _ _ => rfl
  | lam A b _ _ => rfl
  | pi A B _ ihB => exact ihB hσ.lift

/-- **Kind erasure is invariant under substitution** of objects and constructors. -/
theorem eraseK_subst (M : Expr S) {σ : Nat → Expr S} (hσ : NoKindSubst σ) :
    (M.subst σ).eraseK = M.eraseK := by
  induction M generalizing σ with
  | var n => exact (hσ n).2
  | sort s => rfl
  | app f a _ _ => rfl
  | lam A b _ _ => rfl
  | pi A B ihA ihB => simp only [subst, eraseK, isKindB_subst A hσ, ihA hσ, ihB hσ.lift]

end Expr

end PureTypeSystem
