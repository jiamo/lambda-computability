# M15-ORACLE-PROG — tape programs for oracle machines, and `NP^A ⊆ PSPACE^A`

## Programs with a query tape (`Start/OracleProg.lean`)

`Complexity.Space.OProg` is `Complexity.Space.Prog` with two more instructions: `qbit` appends the
scanned work-tape bit to the query tape, and `ask p p'` asks the oracle about the query tape,
erases it and continues with `p` or `p'`.  `lift` embeds the unrelativized programs.  The
semantics `OExec` is the big-step relation of `Prog.Exec` with the query tape added;
`oexec_lift` says a lifted program runs as before, the query tape untouched.

The compiler `OProg.omachine` lays a program out as an oracle machine
`Complexity.Space.OMachine` (`omachine_wellFormed`, `omachine_deterministic`), with the accepting
and rejecting states after the program.  `opath_of_oexec` turns an execution into a path of the
machine and `reach_on_path` says a deterministic machine reaches nothing off that path, so

* `Complexity.Space.OProg.odspace_of_oexec` — an execution from the initial configuration within
  `B x ≤ s |x|` cells, ending on a scanned bit that is set exactly on `L`, gives
  `ODSPACE A s L`.

## The combinator library with an oracle (`Start/OracleProgLib.lean`)

`ORunsQ A x B p s q s' q'` is the exact-state specification of `SpaceProgLib.Runs` with the
query tape at both ends; `ORuns` is the case of an empty query tape.

* `ORunsQ.lift` — **every specification of an unrelativized program is a specification of its
  lift**, so the whole track library of `Start/SpaceProgTracks.lean` carries over unchanged;
* `ORunsQ.seq`, `.ite`, `.loop_stages`, `.qbit`, `.askT`, `.askF` — the rules;
* `opopBranch`, `owhileNE` — the two track combinators whose bodies are oracle programs;
* `oruns_queryReg` — the query gadget: register `d` becomes `[true]` or `[]` according to the
  oracle's answer on register `a`.

## The compiler for oracle terms (`Start/OracleCobSpace.lean`)

`CobQ.spaceW`, `CobQ.need` extend the space and register measures of `Start/CobhamSpace.lean`
(a query costs one register's worth of query tape); `compileQ` is the compiler of
`Start/CobhamSpace.lean` with the query constructor compiled to `queryReg`; and

* `Complexity.Space.OProg.compileQOK` — for every oracle term, the compiled program sets the
  destination register to the value of the term with oracle `A`, within
  `(spaceW c N + 3)(2K + 1)` cells.

## The classes (`Start/OracleNPSpace.lean`)

* `Complexity.Space.OProg.inPSPACE_rel_of_oruns` — a specification from the empty configuration
  within a polynomial bound gives `InPSPACE_rel A L`;
* `Complexity.Space.inPSPACE_rel_of_inP_rel` — `P^A ⊆ PSPACE^A`;
* `Complexity.Space.inPSPACE_rel_of_inNP_rel` — **`NP^A ⊆ PSPACE^A`**.  With the witness bound
  `p n ≤ a (n+1)^k`, set `m = a (n+1)^k + 1`.  A counter `u` runs through all words of length `m`
  (`NPW.bits`, advanced by the Cobham term `NPW.incrC`); each `u = 1^j 0 w` codes the witness `w`
  (`NPW.decodeW`, `decodeW_code`), so every witness of length `< m` is coded (`exists_witness_iff`).
  The loop body (`NPW.npBody`, `oruns_npBody`) runs the compiled verifier on `(x, decode u)`,
  ors the answer into a flag register, sets the continue register to "u is not all ones" and
  increments `u`; `NPW.oruns_npProg` is the specification of the whole program, and every register
  stays within `n + m + 1` bits, a polynomial.

## Gates

`#print axioms Complexity.Space.inPSPACE_rel_of_inNP_rel` and
`#print axioms Complexity.Space.inPSPACE_rel_of_inP_rel`: `propext`, `Classical.choice`,
`Quot.sound`.  No `sorry`.
