# M2-EVAL-NORMALIZATION-HOLDS

Show the main bridge carries no evaluator hypothesis.

## Claim

The bridge `LambdaComputable f → Partrec f` is a theorem with no correctness and no
normalization hypothesis, and the arithmetized evaluator it uses is *proved* to return
the normal form on every normalizing input.

## Evidence

* Normalization of the evaluator, `Start/EvalGK.lean`:

  ```lean
  def Lambda.EvalNormalizationGK : Prop :=
    ∀ t u, Lambda.reduces t u → Lambda.is_normal u →
      Lambda.eval_gk (Lambda.encode t) = Part.some (Lambda.encode u)

  theorem Lambda.evalNormalizationGK : Lambda.EvalNormalizationGK
  ```

  It is discharged by `Lambda.eval_gk_complete`, which combines the normalization of the
  Gross–Knuth strategy (`Lambda.rho_iterate_eq_of_reduces_normal`, `Start/GrossKnuth.lean`)
  with the correctness of the arithmetized complete development
  (`Lambda.rho_code_correct`).  Note that this is the *general* statement about arbitrary
  normal forms, not only about Church numerals.

* Unconditional bridge, `Start/EvalGK.lean`:

  ```lean
  theorem LambdaComputable_imp_Partrec_unconditional {f : ℕ →. ℕ}
      (hf : LambdaComputable f) : Partrec f
  ```

  Its statement has one explicit hypothesis, `hf`, and no evaluator hypothesis.

* The hypothesis-carrying versions survive unchanged as corollaries of the older analysis:
  `LambdaComputable_imp_Partrec_of_normalization` (`Start/EvalCorrect.lean`, assuming
  `Lambda.EvalNormalization` for the leftmost evaluator `Lambda.eval'`) and
  `LambdaComputable_imp_Partrec` (`Start/Arithmetic.lean`, assuming the refuted
  `Lambda.EvalCorrectness`).  Both are still built; they are simply no longer needed.

* Axiom audit:

  ```
  #print axioms LambdaComputable_imp_Partrec_unconditional
  -- [propext, Classical.choice, Quot.sound]
  ```

## Boundary

`Lambda.EvalNormalization` — the same statement for the *leftmost* evaluator `Lambda.eval'`
— is still only a definition, not a theorem.  Proving it needs a standardization theorem for
leftmost reduction, which this development does not contain.  It is not needed anywhere:
the bridge and the capstone equivalence go through `Lambda.eval_gk`.

## Gates

```
python3 scripts/goal_state.py validate   # OK
lake build                               # Build completed successfully
```
