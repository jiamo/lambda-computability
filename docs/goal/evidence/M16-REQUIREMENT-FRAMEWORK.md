# M16-REQUIREMENT-FRAMEWORK — the frame a priority construction runs in

Two modules, answering the three exit criteria.

## The use function — `Start/OracleUse.lean`

`Start/OracleMachine.lean` had the use principle in existential form ("some bound exists").  A
strategy has to name the bound it protects, so the bound is made a function of the computation.

* `Lambda.Oracle.Converges A c x` — the search defining `Lambda.Oracle.evalOracle` succeeds at
  some stage;
* `Lambda.Oracle.useStage` — the least such stage, and `Lambda.Oracle.use` — one more than it
  (`0` for a divergent computation);
* `Lambda.Oracle.oracleStep_eq_none_of_lt_useStage`, `Lambda.Oracle.useStage_le_of_isSome`,
  `Lambda.Oracle.use_le_succ_of_isSome` — **minimality**: nothing below the use stage converges,
  so the use is the least bound of its kind;
* `Lambda.Oracle.evalOracle_eq_of_agree_below_use` — **the use principle with the explicit
  bound**: an oracle agreeing with `A` below `use A c x` gives the same computation;
* `Lambda.Oracle.use_eq_of_agree_below_use`, `Lambda.Oracle.use_mono_of_agree` — such an oracle
  also has the same use, so protecting the use protects the whole computation, permanently.

## Constructions and requirements — `Start/Priority.lean`

* `Lambda.Priority.Construction` — **a construction**: a primitive recursive sequence
  `approx : ℕ → List ℕ` of finite approximations that only grows.
  `Lambda.Priority.Construction.set` is the set it enumerates and
  `Lambda.Priority.Construction.rePred_set` proves that set c.e., through
  `Lambda.Post.rePred_of_exists_test` and the auxiliary
  `Lambda.Priority.primrec_mem_list` (membership in a list of naturals is primitive recursive).
* `Lambda.Priority.Requirement` — **a requirement**: a predicate on the approximation.  It is
  *met at* a stage (`MetAt`) when the approximation of that stage satisfies it, *injured at* a
  stage (`InjuredAt`) when it is met there and not at the next stage, and *met* (`Met`) when it is
  met at every stage from some point on.  `Lambda.Priority.Requirement.met_of_not_injured`: a
  requirement met once and never injured afterwards is met.

## Boundary

The frame is generic; it has not yet been instantiated by an actual construction.  The finite
injury lemma on top of it is `M16-FINITE-INJURY`, and the first construction to run in the frame
is Friedberg–Muchnik, `M16-FRIEDBERG-MUCHNIK`, still open.

## Gates

`lake build` (whole tree, no errors and no new warnings), `python3 scripts/check_sorry.py`,
`python3 scripts/check_closure.py`, `python3 scripts/goal_state.py validate`,
`python3 scripts/check_manifest.py`.
