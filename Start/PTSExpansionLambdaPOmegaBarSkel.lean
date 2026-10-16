/-
**Toward expansion postponement for λPω̲ (M29-EP-CUBE-REST): the kind skeleton.**

The corrected measure for constructor-level hereditary substitution in λPω̲.  Unlike
`Expr.eraseK`, the skeleton keeps object binders:

* `skel ∗ = base` (and `base` for every term that is not a syntactic kind),
* `skel (Π x:A. K) = obj (skel K)` (encoded as `arr base (skel K)`) when `A` is not a kind,
* `skel (Π α:K₁. K₂) = arr (skel K₁) (skel K₂)`.

`skelK_rename` and `skelK_subst`: the skeleton is invariant under renaming and under every
substitution of objects and constructors (`NoKindSubst`), with the same proof as `eraseK_subst`.
`skelK_size_pi_obj` and `skelK_size_pi_kind`: the skeletons of the parts of a product kind
are strictly smaller, which is the termination measure of steps (c) of the plan.

Expansion postponement for λPω̲ is *not* proved here.
-/

import Start.PTSExpansionLambdaPOmegaBar

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

universe u

namespace Expr

variable {S : Type u}

/-- The kind skeleton: object binders are kept (as `arr base _`), constructor binders become
arrows. -/
def skelK : Expr S → STy
  | pi A B =>
    if B.isKindB then (if A.isKindB then .arr (skelK A) (skelK B) else .arr .base (skelK B))
    else .base
  | _ => .base

theorem skelK_of_not_kind (M : Expr S) (h : M.isKindB = false) : M.skelK = .base := by
  cases M with
  | pi A B => simp only [isKindB] at h; simp [skelK, h]
  | _ => rfl

/-- Size of a simple type. -/
def styWeight : STy → Nat
  | .base => 1
  | .arr a b => styWeight a + styWeight b + 1

theorem skelK_rename (M : Expr S) (ρ : Nat → Nat) : (M.rename ρ).skelK = M.skelK := by
  induction M generalizing ρ with
  | var n => rfl
  | sort s => rfl
  | app f a _ _ => rfl
  | lam A b _ _ => rfl
  | pi A B ihA ihB => simp only [rename, skelK, isKindB_rename, ihA, ihB]

/-- **The kind skeleton is invariant under substitution** of objects and constructors. -/
theorem skelK_subst (M : Expr S) {σ : Nat → Expr S} (hσ : NoKindSubst σ) :
    (M.subst σ).skelK = M.skelK := by
  induction M generalizing σ with
  | var n => exact skelK_of_not_kind _ (hσ n).1
  | sort s => rfl
  | app f a _ _ => rfl
  | lam A b _ _ => rfl
  | pi A B ihA ihB => simp only [subst, skelK, isKindB_subst A hσ, isKindB_subst B hσ.lift, ihA hσ, ihB hσ.lift]

theorem skelK_size_pi_obj (A B : Expr S) (hA : A.isKindB = false) (hB : B.isKindB = true) :
    styWeight B.skelK < styWeight (pi A B).skelK := by
  simp only [skelK, hA, hB]; simp [styWeight]

theorem skelK_size_pi_kind (A B : Expr S) (hA : A.isKindB = true) (hB : B.isKindB = true) :
    styWeight A.skelK < styWeight (pi A B).skelK ∧ styWeight B.skelK < styWeight (pi A B).skelK := by
  simp only [skelK, hA, hB, if_true, styWeight]; omega

end Expr

end PureTypeSystem
