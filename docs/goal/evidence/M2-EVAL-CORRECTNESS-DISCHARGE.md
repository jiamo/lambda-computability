# M2-EVAL-CORRECTNESS-DISCHARGE

Prove evaluator correctness instead of assuming it.

## Starting point

`LambdaComputable_imp_Partrec` (`Start/Arithmetic.lean`) took `Lambda.EvalCorrectness` as a
hypothesis, and `Start/EvalCorrect.lean` had already shown that this hypothesis is *false*
(`Lambda.not_evalCorrectness`): `Lambda.eval` iterates `Lambda.code_step`, which is built from the
uncorrected substitution.  The corrected leftmost evaluator `Lambda.eval'` was only proved sound
(`Start/EvalSound.lean`); its completeness half was isolated as the hypothesis
`Lambda.EvalNormalization`, i.e. the leftmost-reduction normalization theorem.

## What was done

The task's original wording ("derive `Lambda.EvalCorrectness`") is unachievable, since that exact
statement is refuted.  The claim was therefore discharged for a *different, fully verified*
code-level evaluator, which is what the milestone needs: an unconditional bridge from lambda
computability to `Partrec`.

* `Start/GrossKnuth.lean` proves that the Gross–Knuth strategy (iterating the complete development
  `Lambda.rho`) is normalizing:
  `Lambda.rho_iterate_eq_of_reduces_normal : reduces t u → is_normal u → ∃ k, Lambda.rho^[k] t = u`.
  The proof needs only the triangle property of parallel reduction that was already available:
  applying `Lambda.step_p_diamond_aux` twice gives monotonicity of `Lambda.rho`
  (`Lambda.rho_mono`), and a normal form has no proper parallel reduct.

* `Start/EvalGK.lean` arithmetizes the complete development (`Lambda.rho_step`, `Lambda.rho_code`),
  proves it primitive recursive (`Lambda.rho_code_primrec`) and correct
  (`Lambda.rho_code_correct : rho_code (encode t) = encode (rho t)`), and defines the evaluator
  `Lambda.eval_gk`, which iterates `Lambda.rho_code` to a fixed point (`Lambda.eval_gk_partrec`).

* Both halves of correctness are proved: `Lambda.eval_gk_sound` and `Lambda.eval_gk_complete`,
  giving the theorem `Lambda.evalCorrectnessGK : Lambda.EvalCorrectnessGK`, i.e.
  `reduces t (church n) ↔ eval_gk (encode t) = Part.some (church_code n)`.

* Hence `LambdaComputable_imp_Partrec_unconditional : LambdaComputable f → Partrec f`, with no
  correctness hypothesis.  `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.

The hypothesis-carrying `LambdaComputable_imp_Partrec` and the leftmost-evaluator statements
(`Lambda.EvalNormalization`, `Lambda.EvalCorrectness'`) are left in place unchanged; they are now
superseded by the unconditional result.

Gates:

```
python3 scripts/goal_state.py validate   # OK
lake build                               # Build completed successfully
```
