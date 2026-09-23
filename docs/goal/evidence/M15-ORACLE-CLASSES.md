# M15-ORACLE-CLASSES — relativized complexity classes `P^A`, `NP^A`, `PSPACE^A`

Relativizing a class means attaching an oracle to the machine model that defines it.  This
library has two models — Cobham's class for polynomial *time*
(`Start/ComplexityClasses.lean`) and the offline Turing machine for *space*
(`Start/SpaceMachine.lean`) — so both are relativized, each in its own way.

## The time side: oracle Cobham terms (`Start/OracleCob.lean`)

`Complexity.CobQ` is Cobham's syntax with one further constructor, `query`, which asks the
oracle `A : Complexity.Oracle = List Bool → Bool` about the first argument and answers with the
truth value `[true]` / `[]`.

Evaluation is `Complexity.CobQ.run`, which returns the value **together with the list of words
the oracle was asked about**, in order; `Complexity.CobQ.eval` and `Complexity.CobQ.queries`
are its two components, and the usual unfolding lemmas for the six unrelativized constructors
hold verbatim (`eval_comp`, `eval_bRec_cons`, `queries_comp`, `queries_bRec_cons`, …).  The
queries are kept because a diagonalization against polynomial-time oracle machines needs them:
it has to know that the machine cannot have looked at every word of a given length.

Three bounds are proved, in a single induction over the term
(`Complexity.CobQ.Bounded`, `Complexity.CobQ.bounded`), with constants that **do not depend on
the oracle**:

* `Complexity.CobQ.polyLen` — the value is polynomially long in the longest argument;
* `Complexity.CobQ.polyQueryCount` — the *number* of queries is polynomially bounded;
* `Complexity.CobQ.polyQueryLen` — every queried word is polynomially long.

The bounds are stated with `Complexity.PolyMono` — a monotone polynomial bound — which is closed
under sum, product and composition (`Complexity.PolyMono.add`, `.mul`, `.comp`), so that the
induction over the term can build its bound step by step; the `bRec` case goes through
`Complexity.CobQ.bRec_bounds`, an induction along the recursion.

The **use principle** is `Complexity.CobQ.run_congr`: if two oracles agree on the words actually
queried, the whole run — value and queries — is the same; `Complexity.CobQ.eval_congr` is the
statement for the value alone.  Its `bRec` case is `Complexity.CobQ.bRec_run_congr`.

## The classes of polynomial time (`Start/OracleClasses.lean`)

* `Complexity.InP_rel A L`, `Complexity.InNP_rel A L` — `P^A` and `NP^A`, with the definitions of
  `Complexity.InP` and `Complexity.InNP` word for word, an oracle term in place of a term;
* `Complexity.PolyManyOne_rel`, `Complexity.PeqNP_rel` — reductions computed with the oracle and
  the statement `P^A = NP^A`.

That this *is* a relativization:

* `Complexity.CobQ.ofCob` reads an ordinary Cobham term as an oracle term, with the same value
  (`Complexity.CobQ.eval_ofCob`), so `Complexity.InP.to_rel` and `Complexity.InNP.to_rel` give
  `P ⊆ P^A` and `NP ⊆ NP^A` for every oracle;
* `Complexity.CobQ.erase` replaces a query by the answer of the empty oracle, giving an ordinary
  Cobham term with the same value (`Complexity.CobQ.eval_erase`), so
  `Complexity.inP_rel_empty_iff` and `Complexity.inNP_rel_empty_iff`: **the empty oracle gives
  back `P` and `NP` exactly**;
* `Complexity.inNP_rel_of_inP_rel` — `P^A ⊆ NP^A`;
* `Complexity.InP_rel.compl`, `.inter`, `.union`, `.of_reduction` — the closure properties of `P`
  relativize;
* `Complexity.inP_rel_oracle` — the oracle itself is decided in `P^A`, which is what makes the
  relativized classes bigger than the unrelativized ones in general.

## The space side (`Start/OracleSpace.lean`)

`Complexity.Space.OMachine` is the offline machine of `Start/SpaceMachine.lean` with a query
tape: an instruction may append a bit to it, and in a *query state* (`OMachine.query q = some
(qyes, qno)`) the machine hands the tape to the oracle, erases it and continues in `qyes` or
`qno` according to the answer.  The query tape counts towards the space bound
(`Complexity.Space.OConfig.space`), which is the standard oracle-space convention.

* `Complexity.Space.ODSPACE`, `.ONSPACE`, `.InPSPACE_rel`, `.InNPSPACE_rel` — the classes;
* `Complexity.Space.onspace_of_odspace`, `.ODSPACE.mono`, `.ONSPACE.mono`,
  `.inNPSPACE_rel_of_inPSPACE_rel` — their elementary structure;
* `Complexity.Space.ofMachine` embeds an ordinary offline machine as an oracle machine with no
  query state; its runs are exactly the runs of the original machine
  (`Complexity.Space.ofMachine_steps_iff`, `.ofMachine_accepts_iff`,
  `.ofMachine_spaceBounded`), whence `Complexity.Space.odspace_of_dspace` and
  `Complexity.Space.inPSPACE_rel_of_pspace`: **`PSPACE ⊆ PSPACE^A` for every oracle**, and the
  oracle is irrelevant on that part of the model
  (`Complexity.Space.inPSPACE_rel_oracle_free`).

## Honest boundary

`NP^A ⊆ PSPACE^A` is **not** proved, and the reason is structural rather than incidental: time
and space are measured on different models here, so even the unrelativized `P ⊆ PSPACE` is not
in the library — it needs a compiler from Cobham terms to space-bounded machines, which is the
routine but long half of the model-independence of these classes.  What is proved above is the
part that does not need that bridge: `P ⊆ P^A`, `NP ⊆ NP^A`, `PSPACE ⊆ PSPACE^A`,
`P^A ⊆ NP^A`, and the recovery of the unrelativized classes by the empty oracle.

## Gates

`lake build` (whole tree, no errors and no new warnings), `python3 scripts/check_sorry.py`,
`python3 scripts/check_closure.py`, `python3 scripts/goal_state.py validate`,
`python3 scripts/check_manifest.py`.
