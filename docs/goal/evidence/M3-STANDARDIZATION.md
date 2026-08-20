# M3-STANDARDIZATION

Normalizing-strategy theorem: a term with a normal form is reached by a canonical strategy.

## Claim

The complete-development (Gross–Knuth) strategy `Lambda.rho` is normalizing: if `t` reduces
to a normal form `u`, then finitely many iterations of `Lambda.rho` from `t` reach `u`
exactly.

## Evidence

`Start/GrossKnuth.lean`:

```lean
theorem Lambda.rho_iterate_eq_of_reduces_normal {t u : Lambda}
    (h : Lambda.reduces t u) (hu : Lambda.is_normal u) : ∃ k, Lambda.rho^[k] t = u
```

The proof uses only the parallel-reduction infrastructure already present: `Lambda.rho` is
the complete development, the triangle property gives monotonicity (`Lambda.rho_mono`), and
a normal form has no proper parallel reduct (`Lambda.rho_normal`).

The theorem is used directly from the evaluator files:

* `Lambda.eval_gk_complete` and `Lambda.evalNormalizationGK` (`Start/EvalGK.lean`) are proved
  from it, via the arithmetized complete development `Lambda.rho_code`;
* `Lambda.evalCorrectnessGK` and `LambdaComputable_imp_Partrec_unconditional` follow.

`#print axioms` on these results reports only `propext`, `Classical.choice`, `Quot.sound`,
and there is no `sorry` in the module.

## Scope note

The canonical strategy proved normalizing here is the complete development, not
leftmost-outermost reduction.  The exit criteria of this task ask for *a* canonical strategy
that is usable from the evaluator files, and the complete development satisfies them.  A
standardization theorem for leftmost reduction (which would additionally discharge
`Lambda.EvalNormalization` for `Lambda.eval'`) is not part of this development.

## Gates

```
python3 scripts/goal_state.py validate   # OK
lake build                               # Build completed successfully
```
