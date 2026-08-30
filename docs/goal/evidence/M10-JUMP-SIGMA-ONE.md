# M10-JUMP-SIGMA-ONE

**Status:** DONE_STRONG

Module `Start/JumpSigmaOne.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

`Start/OracleUniversal.lean` defines the Turing jump `A'` of an oracle and shows that it is r.e.
in `A`.  This task proves the matching hardness: the jump is `Σ₁`-hard, and hardness is *uniform*
in the oracle — a single computable reduction works for every oracle at once.

## What is proved

* `Lambda.Oracle.constMaster`, `Lambda.Oracle.exists_index_const` — a machine that ignores its
  oracle and simulates a fixed partial recursive function, with a computable index for it.
* `Lambda.Oracle.exists_partrec_dom` — an r.e. predicate is the domain of a partial recursive
  function.
* `Lambda.Oracle.exists_index_repred` — **the jump is `Σ₁`-hard, uniformly in the oracle**: for
  every r.e. predicate `P` there is one computable `k` with `P x ↔ k x ∈ A'` for *every* oracle
  `A`.
* `Lambda.Oracle.manyOneReducible_jump` — hence `P ≤₀ A'`.
* `Lambda.Oracle.charOracle`, `Lambda.Oracle.turingReducible_jumpChar_of_repred` — every r.e.
  predicate is decidable relative to the jump of any oracle.
* `Lambda.Oracle.haltingOracle`, `Lambda.Oracle.turingReducible_haltingOracle_of_repred` — in
  particular relative to `∅'`.

## Boundary

None.

## Gates

* `lake build` — the whole library, no error and no warning.
* `python3 scripts/check_closure.py`.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: the results above depend only on `propext`, `Classical.choice` and `Quot.sound`.
