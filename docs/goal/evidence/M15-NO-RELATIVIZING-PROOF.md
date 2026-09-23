# M15-NO-RELATIVIZING-PROOF — the relativization barrier

`Start/Relativization.lean` states what it means for a statement about the complexity classes to
relativize, and draws from `Start/BakerGillSolovay.lean` the half of the barrier that the library
can prove outright.

## What is proved

* `Complexity.Relativizes (S : Oracle → Prop) : Prop` — the statement `S` holds with every oracle
  attached.  A proof technique is called relativizing when its conclusion has this form; the two
  instances of interest are `Complexity.PeqNP_rel` (`P^A = NP^A`) and `Complexity.PneNP_rel`
  (`P^A ≠ NP^A`).
* `Complexity.peqnp_does_not_relativize : ¬ Complexity.Relativizes Complexity.PeqNP_rel` — **the
  statement `P = NP` does not relativize.**  Immediate from `Complexity.bgs_different`: some
  oracle separates the classes, so no argument whose conclusion survives every oracle proves
  `P = NP`.
* `Complexity.pnenp_does_not_relativize` and `Complexity.no_relativizing_resolution` — the barrier
  in full, under the hypothesis `∃ A, Complexity.PeqNP_rel A`: neither `P = NP` nor `P ≠ NP`
  relativizes, so a relativizing technique settles neither side.

## The boundary

The hypothesis of the last two statements is exactly `M15-BGS-EQUAL`, the collapsing half of
Baker–Gill–Solovay: an oracle `A` with `P^A = NP^A`, classically a `PSPACE`-complete language.
The library does not have it, for the reason already recorded in the boundary of
`M15-ORACLE-CLASSES`: time is measured on Cobham's class and space on the offline machine of
`Start/SpaceMachine.lean`, so simulating an `NP^A` computation in polynomial space — and hence
even the unrelativized `P ⊆ PSPACE` — needs a compiler from Cobham terms to space-bounded
machines, which is not in the library.  The unconditional half, and the conditional full barrier,
are what is delivered here.

## Gates

`lake build` (whole tree, no errors and no new warnings), `python3 scripts/check_sorry.py`,
`python3 scripts/check_closure.py`, `python3 scripts/goal_state.py validate`,
`python3 scripts/check_manifest.py`.
