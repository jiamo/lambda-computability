# M4-TM2-IMP-PARTREC

Machine side: TM2-computable implies partial recursive.

## Status

Complete.  Both directions are proved and combined into an equivalence.

## Machine implies partial recursive

`Start/TM2Partrec.lean` arithmetizes an arbitrary bundled machine `tm : Turing.FinTM2` whose
stack alphabets are all finite.  A configuration is represented by an element of the concrete
`Primcodable` type

```
NCfg tm = Option (Fin nL) × Fin nS × (Fin nK → List ℕ)
```

obtained by transporting the finite label, state and stack-index types along the canonical
equivalences with `Fin`, and by numbering stack symbols.  The file proves:

* `TM2Partrec.primrec_nstep` — the one-step transition, read through this representation, is
  primitive recursive (induction on `Turing.TM2.Stmt`);
* `TM2Partrec.primrec_nrun` — so is the step-indexed iteration;
* `TM2Partrec.partrec_evalCode : Partrec (evalCode tm)` — minimising over the halting time
  gives a partial recursive function `evalCode tm : List ℕ →. List ℕ`, the code-level
  behaviour of the machine;
* `TM2Partrec.evalCode_of_outputs` — soundness against `Turing.TM2Outputs`, and
  `TM2Partrec.exists_halted_of_evalCode` — completeness: whenever `evalCode` converges the
  machine really reaches a halted configuration;
* `TM2Partrec.partrec_of_tm2Computable` — the same statement in the shape of Mathlib's
  `Turing.TM2Computable`.

## Partial recursive implies machine

Mathlib compiles a `Turing.ToPartrec.Code` into the TM2 machine
`Turing.PartrecToTM2.tr`, whose label type `Λ'` is infinite, so it is not a bundled
`Turing.FinTM2`.  Two new files close that gap:

* `Start/TM2Restrict.lean` restricts an arbitrary TM2 machine to a finite set of labels it
  never leaves (`TM2Partrec.restrict`) and proves the restriction simulates it step by step
  (`TM2Partrec.mapCfg_step`, `TM2Partrec.iterate_map_opt`); the translation of configurations
  is injective, so the simulation can be read in both directions;
* `Start/TM2Forward.lean` applies this to `codeSupp c Cont'.halt`, the finite support given by
  `Turing.PartrecToTM2.tr_supports`, producing the bundled machine `TM2Partrec.trFinTM2 c` and
  proving `TM2Partrec.trFinTM2_outputs`: the machine started on `trList v` halts with
  `trList w` on its output stack whenever `w ∈ Code.eval c v`.

## The equivalence

`Start/TM2Capstone.lean` combines the two directions.  To state an equivalence for partial
functions on the naturals, a machine is bundled with computable translations of a number into
the initial contents of its input stack and of the final contents of its output stack back
into a number (`TM2Partrec.TM2Realization`, `TM2Partrec.TM2ComputableNat`).  The translations
used for the forward direction are the machine's own binary encoding, arithmetized:

* `TM2Partrec.natBits` / `TM2Partrec.numOf`, with `TM2Partrec.primrec_natBits`,
  `TM2Partrec.primrec_numOf`, `TM2Partrec.natBits_eq_trNat` and `TM2Partrec.numOf_natBits`.

The capstone is

```lean
theorem TM2Partrec.tm2Computable_iff_partrec {f : ℕ →. ℕ} : TM2ComputableNat f ↔ Partrec f
```

Together with `lambdaComputable_iff_partrec` (`Start/PartialCapstone.lean`) this closes the
triangle: lambda-definable, partial recursive and Turing computable coincide.

## Gates

```
python3 scripts/goal_state.py validate   # OK: 16 tasks validated
lake build                               # Build completed successfully, no warnings
```

`#print axioms TM2Partrec.tm2Computable_iff_partrec` reports only
`propext, Classical.choice, Quot.sound`.
