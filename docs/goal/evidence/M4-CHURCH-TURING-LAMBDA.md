# M4-CHURCH-TURING-LAMBDA

Capstone: lambda-definable if and only if recursive.

## Claim

A single theorem, with no extra hypothesis, states the equivalence for total functions
(`Start/PartrecLambda.lean`):

```lean
theorem lambdaComputable_iff_computable {f : ℕ → ℕ} :
    LambdaComputable (fun n => Part.some (f n)) ↔ Computable f
```

## The two directions

* `→` is `LambdaComputable_imp_Partrec_unconditional` (`Start/EvalGK.lean`): the arithmetized
  Gross–Knuth evaluator is primitive recursive, is proved sound and complete, and computes the
  function represented by the term.  It carries no evaluator hypothesis (see
  `M2-EVAL-NORMALIZATION-HOLDS`).  For a total function `Computable f` is by definition
  `Partrec` of its coercion, so no extra step is needed.

* `←` is `lambdaComputable_of_computable` (`Start/PartrecLambda.lean`): the compiler over the
  primitive recursive constructors combined with Kleene's normal form and the minimisation
  combinator (see `M3-PARTREC-IMP-LAMBDACOMPUTABLE`).

## Scope

The equivalence is stated on total functions, which is the common class the two directions are
available on.  The forward direction holds for arbitrary partial functions; the reverse one
would additionally need the divergence half of minimisation (`M3-LAMBDA-MU-CORRECTNESS`).

## Axiom audit

```
#print axioms lambdaComputable_iff_computable
-- [propext, Classical.choice, Quot.sound]
```

## Gates

```
python3 scripts/goal_state.py validate   # OK
lake build                               # Build completed successfully
```
