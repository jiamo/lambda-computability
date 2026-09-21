# M14-QBF-PSPACE-FAMILY

**Status:** DONE_STRONG

The formula produced by `Start/QbfMachine.lean` is *closed*, hence an instance of
`Complexity.Qbf.TQBF`, and for a whole language in `Complexity.Space.PSPACE` the formulas of its
inputs are bounded by a single polynomial in the input length.

## What is built

### `Start/QbfClosed.lean` — no free variables

`Complexity.Qbf.QBF.InBlock m a i` says that the variable `i` is one of the `m` variables of block
`a`.  Each piece of the construction is given the block it can leave free:

* `mem_free_exBits`, `mem_free_allBits` — quantifying over a block removes exactly its variables;
* `mem_free_conjAll`, `mem_free_disjAny`, `mem_free_eqBlock`, `mem_free_litF`, `mem_free_iffVar` —
  the generic combinators (the constant `tt` that closes a conjunction over a list mentions the
  variable `0`, so every bound carries the alternative `i = 0`);
* `mem_free_reachF` — by induction on the depth: the reachability formula is free only in its two
  endpoint blocks, because the three scratch blocks of a level are quantified away;
* `mem_free_cfgF`, `mem_free_tgtF`, `mem_free_stepF`, `mem_free_initF`, `mem_free_accF` — the
  formulas of the machine are free only in the blocks they speak about.

Hence `Complexity.Qbf.QBF.closed_machineF`: the body of `machineF` is free only inside blocks `0`
and `1`, which the two outer quantifiers bind, so the formula is closed.  With the correctness of
the reduction this gives `Complexity.Qbf.QBF.tqbf_machineF_iff`: the formula is a *true* closed
quantified Boolean formula exactly when the machine accepts the input.

### `Start/QbfPspace.lean` — one polynomial for a whole class

`Complexity.PolyBound.mul` adds closure under products to the existing closure lemmas for
polynomial bounds.  `wBound`, `kBound` and `sizeBound` express the width of a configuration word,
a bound on the depth of the recursion (through `Nat.clog 2 m ≤ m`) and the size of the whole
formula as functions of the input length; `size_machineF_le_sizeBound` shows the formula of an
input of length `n` fits in `sizeBound M s n`, for every machine, and `polyBound_sizeBound` shows
that bound is polynomial whenever the space bound is.

## Results

* `Complexity.Qbf.QBF.closed_machineF` — the formula of the reduction is closed.
* `Complexity.Qbf.QBF.tqbf_machineF_iff` — it is in `TQBF` exactly when the machine accepts the
  input.
* `Complexity.Qbf.QBF.npspace_polySize_qbf` — for a language in `NPSPACE` there is one polynomial
  `p` and, for each input `x`, a formula of size at most `p |x|` whose value under every
  assignment is the membership of `x`.
* `Complexity.Qbf.QBF.npspace_polySize_tqbf`, `Complexity.Qbf.QBF.pspace_polySize_tqbf` — the same
  statement with `TQBF`: **every language in nondeterministic polynomial space, hence every
  language in polynomial space, reduces to `TQBF` by a map of polynomial size.**

## Boundary

The map `x ↦ machineF M x s` is not shown to be computable in polynomial time; that is the only
missing ingredient for the `PSPACE`-hardness of `TQBF`, and it is what the open task
`M14-TQBF-PSPACE-HARD` now records.

## Gates

```
lake build                        # Build completed successfully, 0 errors
python3 scripts/check_sorry.py    # OK: no sorry/admit
python3 scripts/check_closure.py  # OK: all modules in the import closure and registered
python3 scripts/goal_state.py validate
python3 scripts/check_manifest.py
```
