/-
Kleene's second recursion theorem for the lambda calculus.

Every closed term `F` has a term `X` that reduces to `F` applied to *its own code*:
`X ↠ F ⌜X⌝`, where `⌜X⌝` is the Church numeral of `Lambda.encode X`.

The construction is the usual diagonal one, but it only needs a single realizer: the primitive
recursive diagonal function `c ↦ app_code c (church_code c)` is lambda-definable by a closed term
`diagTerm` (`Start/PartrecLambda.lean`), and `X = W ⌜W⌝` with `W = λz. F (diagTerm z)` then works.
-/

import Start.Undecidable

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- The diagonal code function: from the code of a term `W`, the code of `W ⌜W⌝`. -/
def diagCode (c : ℕ) : ℕ := Lambda.app_code c (Lambda.church_code c)

theorem diagCode_primrec : Primrec diagCode :=
  Primrec₂.comp Lambda.app_code_primrec Primrec.id Lambda.church_code_primrec

theorem diagCode_computable : Computable diagCode := diagCode_primrec.to_comp

/-- A closed lambda term computing the diagonal code function. -/
def diagTerm : Lambda :=
  Classical.choose (Lambda.exists_realizer_of_computable diagCode_computable)

theorem diagTerm_realizes : Realizes diagTerm diagCode :=
  Classical.choose_spec (Lambda.exists_realizer_of_computable diagCode_computable)

theorem diagTerm_closed : Lambda.IsClosed diagTerm := diagTerm_realizes.1

theorem diagTerm_app_reduces (n : ℕ) :
    Lambda.reduces (Lambda.app diagTerm (Lambda.church n)) (Lambda.church (diagCode n)) :=
  diagTerm_realizes.2 n

/-- The diagonal code of `W` really is the code of `W ⌜W⌝`. -/
theorem diagCode_encode (W : Lambda) :
    diagCode (Lambda.encode W) =
      Lambda.encode (Lambda.app W (Lambda.church (Lambda.encode W))) := by
  rw [Lambda.encode_app, diagCode, Lambda.encode_church_eq_church_code]

/-- **Kleene's second recursion theorem for the lambda calculus.**  Every closed term `F` has a
term `X` which reduces to `F` applied to the Church numeral of its own code. -/
theorem exists_code_fixed_point {F : Lambda} (hF : Lambda.IsClosed F) :
    ∃ X : Lambda, Lambda.reduces X (Lambda.app F (Lambda.church (Lambda.encode X))) := by
  set body : Lambda := Lambda.app F (Lambda.app diagTerm (Lambda.var 0)) with hbody
  set W : Lambda := Lambda.lam body
  refine ⟨Lambda.app W (Lambda.church (Lambda.encode W)), ?_⟩
  have hsubst : Lambda.subst (Lambda.church (Lambda.encode W)) 0 body =
      Lambda.app F (Lambda.app diagTerm (Lambda.church (Lambda.encode W))) := by
    simp [hbody, Lambda.subst, hF _ _, diagTerm_closed _ _]
  have hbeta : Lambda.reduces (Lambda.app W (Lambda.church (Lambda.encode W)))
      (Lambda.app F (Lambda.app diagTerm (Lambda.church (Lambda.encode W)))) := by
    rw [← hsubst]
    exact Lambda.beta_reduces
  refine Lambda.reduces_trans hbeta ?_
  have h := Lambda.reduces_app_right (t1 := F) (diagTerm_app_reduces (Lambda.encode W))
  rwa [diagCode_encode W] at h

end Lambda
