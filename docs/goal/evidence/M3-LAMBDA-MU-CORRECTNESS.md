# M3-LAMBDA-MU-CORRECTNESS

Correctness of `Lambda.mu`: the lambda minimisation operator agrees with `rfind`.

## Status

Complete: both the convergence and the divergence half are proved.

## Convergence half

`Start/Minimization.lean` proves the specification stated in `Start/Recursion.lean`:

```lean
theorem Lambda.muCorrectness : Lambda.MuCorrectness
```

that is: if `F` is closed and computes `f` on Church numerals, and `n` is the least zero of
`f`, then `Lambda.app Lambda.mu F` reduces to `Lambda.church n`.

The proof unfolds the fixed-point combinator once (`Lambda.mu_reduces_muX`,
`Lambda.muX_unfold`), gives the loop's one-turn law (`Lambda.muX_step`), and does a downward
induction on the distance to the witness (`Lambda.muX_works`).

The parameterised form needed by the compiler is in `Start/PartrecLambda.lean`:

```lean
theorem Lambda.Realizes.muParam {H : Lambda} {h : ℕ → ℕ} (hH : Realizes H h) (m : ℕ → ℕ)
    (hm0 : ∀ n, h (Nat.pair n (m n)) = 0)
    (hmlt : ∀ n y, y < m n → h (Nat.pair n y) ≠ 0) :
    Realizes (Lambda.muParam H) m
```

## Divergence half

`Start/Divergence.lean` proves

```lean
theorem Lambda.muDivergence : Lambda.MuDivergence
```

if the tested function has no zero, then `Lambda.app Lambda.mu F` reduces to no Church
numeral — in fact (`Lambda.mu_not_reduces_whnf`) to no weak head normal form at all.

The missing ingredient identified earlier — the syntactic theory of weak head normal forms
plus a standardization theorem — is supplied by `Start/WeakHead.lean` and
`Start/Standardization.lean`:

* `Lambda.whnIn_of_step`: an arbitrary beta step never increases the number of weak head
  steps that remain before a weak head normal form is reached;
* `Lambda.sred_of_reduces`: every reduction is standard;
* `Lambda.hasWhnfEval_of_reduces_whnf`: consequently the weak head strategy is normalizing.

The divergence proof is then an infinite descent along the weak head strategy
(`Lambda.not_hasWhnfEval_of_loop`, `Lambda.muX_wstep`, `Lambda.muX_loop_step_from`).

## Consequence

With both halves available, `Start/PartialCapstone.lean` upgrades the capstone from total to
arbitrary partial functions: `lambdaComputable_iff_partrec`.

## Gates

```
python3 scripts/goal_state.py validate   # OK: 16 tasks validated
lake build                               # Build completed successfully, no warnings
```
