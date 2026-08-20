/-
Turing's fixed-point combinator.

`Lambda.Theta` is Turing's combinator `Θ = A A` with `A = λx y. y (x x y)`.  Unlike Curry's `Y`,
it satisfies the fixed-point equation as a *reduction* rather than merely as a convertibility:
`Θ F` reduces to `F (Θ F)` (`Lambda.Theta_reduces`).  Hence every lambda term has a fixed point
(`Lambda.exists_fixed_point`).
-/

import Start.Combinators

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

/-- The body of Turing's combinator: `A = λx y. y (x x y)`. -/
def turingA : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.app (Lambda.var 0)
    (Lambda.app (Lambda.app (Lambda.var 1) (Lambda.var 1)) (Lambda.var 0))))

/-- Turing's fixed-point combinator `Θ = A A`. -/
def Theta : Lambda := Lambda.app turingA turingA

theorem turingA_closed : Lambda.IsClosed turingA := by
  intro s x
  simp [turingA, Lambda.subst]

theorem Theta_closed : Lambda.IsClosed Theta :=
  Lambda.IsClosed_app turingA_closed turingA_closed

/-- One unfolding of the combinator: `A A` reduces to `λy. y (A A y)`. -/
theorem turingA_app_reduces :
    Lambda.reduces Theta
      (Lambda.lam (Lambda.app (Lambda.var 0) (Lambda.app Theta (Lambda.var 0)))) := by
  have h := @Lambda.beta_reduces
    (Lambda.lam (Lambda.app (Lambda.var 0)
      (Lambda.app (Lambda.app (Lambda.var 1) (Lambda.var 1)) (Lambda.var 0)))) turingA
  simpa [Theta, turingA, Lambda.subst, Lambda.lift] using h

/-- **Turing's fixed-point property**: `Θ F` reduces to `F (Θ F)`, for every term `F`. -/
theorem Theta_reduces (F : Lambda) :
    Lambda.reduces (Lambda.app Theta F) (Lambda.app F (Lambda.app Theta F)) := by
  refine Lambda.reduces_trans
    (Lambda.reduces_app_left (t2 := F) turingA_app_reduces) ?_
  have h := @Lambda.beta_reduces
    (Lambda.app (Lambda.var 0) (Lambda.app Theta (Lambda.var 0))) F
  simpa [Theta, turingA, Lambda.subst, Lambda.lift] using h

/-- **Fixed-point theorem for the lambda calculus**: every term `F` has a term `X` that reduces
to `F X`. -/
theorem exists_fixed_point (F : Lambda) :
    ∃ X : Lambda, Lambda.reduces X (Lambda.app F X) :=
  ⟨Lambda.app Theta F, Theta_reduces F⟩

end Lambda
