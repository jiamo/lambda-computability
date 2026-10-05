# M15-BGS-COLLAPSE — an oracle with `P^A = NP^A`

`Start/CollapsingOracle.lean` builds an oracle that collapses the relativized classes of
`Start/OracleClasses.lean`, with no hypothesis and without any space-bounded machine.

## The construction

A query is read as a padded word `z = 1^K 0 1^L 0 1^c 0 x` (`Complexity.Collapse.pad`, injective
by `Complexity.Collapse.pad_inj`), where `c` is the number of an oracle Cobham term `v` under an
injective numbering (`Complexity.Collapse.termCode`, from the countability of `Complexity.CobQ`
proved in `Start/OracleEnum.lean`).  `Complexity.Collapse.Step B z` says that `z` has this shape and
that `v`, run with `B` **restricted to words shorter than `z`** (`Complexity.Collapse.trunc`),
accepts `(x, w)` for some `w` with `|w| ≤ L`.  Because of the restriction, the step on `z` only
looks at `B` below `|z|` (`Complexity.Collapse.step_congr`), so the approximations
`Complexity.Collapse.approx` stabilise and

* `Complexity.Collapse.oracleC : Oracle` — the oracle, and
* `Complexity.Collapse.oracleC_eq (z) : oracleC z = decide (Step oracleC z)` — its fixed-point
  equation.

## The collapse

* `Complexity.Collapse.peqNP_rel_oracleC : PeqNP_rel oracleC`.  For `L ∈ NP^A` with verifier `v`,
  witness bound `p ≤ a (n+1)^k` and query-length bound `q` (`Complexity.CobQ.polyQueryLen`), choose
  `L = a (n+1)^k` and `K = b (n+1)^j ≥ q(n + a (n+1)^k)`.  The padded word is computed from `x` by a
  Cobham term (`Complexity.Collapse.queryWordC`, `eval_queryWordC`), and the decider asks the oracle
  once (`Complexity.Collapse.decider`, `eval_decider`).  Every query of `v` on `(x, w)` with
  `|w| ≤ L` is shorter than the padded word, so by the use principle
  (`Complexity.CobQ.eval_congr`) the restricted run is the real run; acceptance forces
  `|w| ≤ p(n) ≤ L`, so the oracle's answer is exactly membership of `x` in `L`.
* `Complexity.bgs_equal : ∃ A : Oracle, PeqNP_rel A`.

This is not the classical Baker–Gill–Solovay oracle (a `PSPACE`-complete language); that version,
`P^TQBF = NP^TQBF`, remains the row `M15-BGS-EQUAL`.  For the relativization barrier any collapsing
oracle suffices.

## Gates

`#print axioms Complexity.bgs_equal` and `#print axioms Complexity.no_relativizing_resolution`:
`propext`, `Classical.choice`, `Quot.sound`.  `python3 scripts/check_sorry.py`,
`python3 scripts/check_closure.py`, `python3 scripts/goal_state.py validate`.  See the build note
in `docs/goal/evidence/M15-NO-RELATIVIZING-PROOF.md`.
