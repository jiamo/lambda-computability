/-
Kleene's recursion theorem *with parameters*, in the lambda calculus.

`Start/SecondRecursion.lean` produces, for a closed term `F`, a term `X` with `X ↠ F ⌜X⌝`.  The
version with parameters makes the fixed point depend on an extra numeric argument, *uniformly and
primitively recursively*: there is a primitive recursive `s` such that for every parameter `y` the
term coded by `s y` reduces to `F` applied to its own code and to `church y`,

    X_y ↠ F ⌜X_y⌝ (church y),      ⌜X_y⌝ = church (s y).

This is the lambda-calculus form of the parametrised recursion theorem, the statement usually used
to build families of programs that know their own index.
-/

import Start.SecondRecursion

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- The parametrised diagonal term `W_y = λz. F (diagTerm z) (church y)`. -/
def paramW (F : Lambda) (y : ℕ) : Lambda :=
  Lambda.lam (Lambda.app (Lambda.app F (Lambda.app diagTerm (Lambda.var 0))) (Lambda.church y))

/-- The parametrised fixed point `X_y = W_y ⌜W_y⌝`. -/
def paramFix (F : Lambda) (y : ℕ) : Lambda :=
  Lambda.app (paramW F y) (Lambda.church (Lambda.encode (paramW F y)))

/-- The code of the parametrised fixed point. -/
def paramCode (F : Lambda) (y : ℕ) : ℕ := Lambda.encode (paramFix F y)

theorem encode_paramW (F : Lambda) (y : ℕ) :
    Lambda.encode (paramW F y) =
      Lambda.lam_code (Lambda.app_code
        (Lambda.app_code (Lambda.encode F) (Lambda.encode (Lambda.app diagTerm (Lambda.var 0))))
        (Lambda.church_code y)) := by
  simp [paramW, Lambda.encode, Lambda.lam_code, Lambda.app_code,
    Lambda.encode_church_eq_church_code]

theorem paramCode_eq (F : Lambda) (y : ℕ) :
    paramCode F y = diagCode (Lambda.encode (paramW F y)) := by
  rw [paramCode, paramFix, diagCode_encode]

theorem encode_paramW_primrec (F : Lambda) : Primrec fun y => Lambda.encode (paramW F y) := by
  have h : Primrec fun y : ℕ =>
      Lambda.lam_code (Lambda.app_code
        (Lambda.app_code (Lambda.encode F) (Lambda.encode (Lambda.app diagTerm (Lambda.var 0))))
        (Lambda.church_code y)) :=
    Lambda.lam_code_primrec.comp
      (Lambda.app_code_primrec.comp (Primrec.const _) Lambda.church_code_primrec)
  exact h.of_eq fun y => (encode_paramW F y).symm

/-- The code of the parametrised fixed point depends primitively recursively on the parameter. -/
theorem paramCode_primrec (F : Lambda) : Primrec (paramCode F) := by
  have h : Primrec fun y => diagCode (Lambda.encode (paramW F y)) :=
    diagCode_primrec.comp (encode_paramW_primrec F)
  exact h.of_eq fun y => (paramCode_eq F y).symm

theorem paramFix_reduces {F : Lambda} (hF : Lambda.IsClosed F) (y : ℕ) :
    Lambda.reduces (paramFix F y)
      (Lambda.app (Lambda.app F (Lambda.church (paramCode F y))) (Lambda.church y)) := by
  set W : Lambda := paramW F y with hW
  set body : Lambda :=
    Lambda.app (Lambda.app F (Lambda.app diagTerm (Lambda.var 0))) (Lambda.church y) with hbody
  have hsubst : Lambda.subst (Lambda.church (Lambda.encode W)) 0 body =
      Lambda.app (Lambda.app F (Lambda.app diagTerm (Lambda.church (Lambda.encode W))))
        (Lambda.church y) := by
    simp [hbody, Lambda.subst, hF _ _, diagTerm_closed _ _, Lambda.church_closed y _ _]
  have hbeta : Lambda.reduces (paramFix F y)
      (Lambda.app (Lambda.app F (Lambda.app diagTerm (Lambda.church (Lambda.encode W))))
        (Lambda.church y)) := by
    rw [paramFix, ← hW, ← hsubst, hW, paramW, ← hbody]
    exact Lambda.beta_reduces
  refine Lambda.reduces_trans hbeta ?_
  have h := Lambda.reduces_app_left (t2 := Lambda.church y)
    (Lambda.reduces_app_right (t1 := F) (diagTerm_app_reduces (Lambda.encode W)))
  rwa [← paramCode_eq F y] at h

/-- **Kleene's recursion theorem with parameters, for the lambda calculus.**  For every closed
term `F` there is a primitive recursive function `s` such that, for every parameter `y`, the term
coded by `s y` reduces to `F` applied to its own code and to the numeral of `y`. -/
theorem exists_recursion_with_parameters {F : Lambda} (hF : Lambda.IsClosed F) :
    ∃ s : ℕ → ℕ, Primrec s ∧
      ∀ y : ℕ, ∃ X : Lambda, Lambda.decode (s y) = some X ∧
        Lambda.reduces X (Lambda.app (Lambda.app F (Lambda.church (s y))) (Lambda.church y)) := by
  refine ⟨paramCode F, paramCode_primrec F, fun y => ⟨paramFix F y, ?_, paramFix_reduces hF y⟩⟩
  exact decode_encode _

end Lambda
