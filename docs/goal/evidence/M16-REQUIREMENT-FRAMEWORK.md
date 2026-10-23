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

## Big round 2, run 1

Closed as DONE_STRONG: the exit criteria are met as written.

* "The use function of an oracle computation is defined and its monotonicity and the use principle
  proved." — `Lambda.Oracle.use` and `Lambda.Oracle.useStage` (Start/OracleUse.lean); monotonicity
  `Lambda.Oracle.use_mono_of_agree` (an oracle respecting the use does not raise it), with
  minimality `useStage_le_of_isSome`, `use_le_succ_of_isSome`; the use principle
  `Lambda.Oracle.evalOracle_eq_of_agree_below_use` and `use_eq_of_agree_below_use`.
* "A requirement is a predicate on the stage-indexed approximation, with a notion of being met and
  of being injured." — `Lambda.Priority.Requirement` with `MetAt`, `Met`, `InjuredAt`, and
  `Requirement.met_of_not_injured` (Start/Priority.lean).
* "A construction is a stage-indexed sequence of finite approximations, with the enumeration it
  defines proved c.e." — `Lambda.Priority.Construction` and `Construction.rePred_set`.

The former boundary (no construction instantiates the frame yet) is not an exit criterion of this
row; it is tracked by `M16-FINITE-INJURY` and `M16-FRIEDBERG-MUCHNIK`.

## Big round 2, run 6 (restoration after the move to a new project)

The big round 2 sections of this note (runs 1 to 3) were lost with the old project and were recreated
in run 6 from its command logs, which record the text that was appended; the Lean modules they cite
were restored from the old project's export, rebuilt with `lake build --wfail`, and their axioms
regenerated (`docs/goal/evidence/*-axioms.txt`, section "Big round 2, run 6").

## Big round 2, run 7 (restoration after the export of run 6)

The platform's export of run 6's project dropped this note; it was put back from the copy of before big round 2 (our tree at ce8fe5e), and the
big round 2 sections that run 6 had restored were added again in run 7 from the command logs of
runs 1 to 3 (the appended text is recorded there verbatim). The axioms files of the big round 2 rows
were regenerated with `#print axioms` in run 7 (section "Big round 2, run 7").
