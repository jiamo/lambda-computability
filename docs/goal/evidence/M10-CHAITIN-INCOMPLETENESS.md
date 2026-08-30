# M10-CHAITIN-INCOMPLETENESS

**Status:** DONE_STRONG

Module `Start/ChaitinIncompleteness.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings, and
`#print axioms` on `Lambda.chaitin_incompleteness` and
`Lambda.exists_true_unprovable_kolm_lower_bound` reports only `propext`, `Classical.choice` and
`Quot.sound`.

## The question

`Start/Kolmogorov.lean` shows that Kolmogorov complexity is not computable, and that
incompressible numbers exist: for every `n` some `x` has `kolm x ≥ n`.  Chaitin's observation is
that these true statements are also, from some point on, *unprovable*: model a formal system by
the set of assertions `kolm x > n` it proves; if that set is recursively enumerable and contains
only true assertions, then the thresholds `n` occurring in it are bounded.

## The argument

Write `S x n` for "the system proves `kolm x > n`".

* `Lambda.Post.exists_test_of_rePred` — every r.e. predicate is "some stage of a primitive
  recursive test succeeds".  This is the converse of the existing
  `Lambda.Post.rePred_of_exists_test`, and is read off the standard numbering: take an index `e`
  with `P x ↔ Wset e x` (`Lambda.Post.exists_index`) and use the bounded evaluation
  `Nat.Partrec.Code.evaln`, which is primitive recursive and, by `evaln_sound`/`evaln_complete`,
  succeeds at some stage exactly when the machine halts.
* `Lambda.exists_partrec_select` — an r.e. relation has a partial recursive **selection**
  function.  A single unbounded search over pairs (candidate, stage) finds a witness `x` for `n`
  whenever one exists, and returns only genuine witnesses.
* `Lambda.exists_const_kolm_apply_le_of_partrec` — applying a fixed lambda term to a shortest
  program costs an additive constant: for partial recursive `V`, `kolm (V n) ≤ kolm n + c`.  The
  witness is `F p` where `F` realizes `V` (`lambdaComputable_of_partrec_closed`) and `p` is a
  shortest program for `n`.
* `Lambda.exists_lt_two_pow` and `Lambda.exists_bound_of_lt_size` — a linear function of the bit
  length is eventually dominated by its argument, since `m * m ≤ 2 ^ m` from `m = 4` on and
  `2 ^ (Nat.size n - 1) ≤ n`.  Hence `n < a * Nat.size n + b` bounds `n`.

Putting these together: if the system proves something about the threshold `n`, the selection
function halts on `n` and returns an `x` with `S x n`, so soundness gives `n < kolm x`, while
`kolm x ≤ kolm n + c` and `kolm n ≤ c₁ * (Nat.size n + 1)` (the logarithmic bound of
`Start/KolmogorovBinary.lean`).  Therefore `n < c₁ * Nat.size n + (c₁ + c)`, which bounds `n`.

## Results

* **`Lambda.chaitin_incompleteness`** — for a sound r.e. system of lower bounds, the thresholds
  are bounded: `∃ c, ∀ x n, S x n → n < c`.
* **`Lambda.exists_true_unprovable_kolm_lower_bound`** — hence there is a threshold `c` at which
  the system proves nothing, `∀ x, ¬ S x c`, although `kolm x > c` holds for some `x`
  (`Lambda.exists_incompressible`).

## Boundary

The complexity measure is the project's `Lambda.kolm`, the least *size* of a closed lambda term
reducing to the Church numeral; the logarithmic bound `kolm n = O(log n)` that the argument needs
is `Lambda.exists_const_kolm_le_size`.  The formal system is modelled semantically, by the r.e.
set of assertions it proves, rather than by a proof calculus; no arithmetization of provability is
involved.

## Gates

```bash
python3 scripts/goal_state.py validate
python3 scripts/check_closure.py
lake build Start.ChaitinIncompleteness
```
