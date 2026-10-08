# M26-DELIVERY-12-MERGE

Merged the existing Aristotle update from `/Users/jiamo/Downloads/12` on
2026-10-08, incrementally over delivery 8.

## Imported update

- 975 upstream DegreeRigidity modules as flat `Start/Rigidity*.lean` modules.
- `Start/RigidityBridge.lean`, identifying the upstream quotient with
  `Lambda.Oracle.SetDegree` and proving `Lambda.Oracle.setDegreeRigidity`.
- `Start/LogspaceAmplification.lean`, proving `RL ⊆ BPL` and deriving the
  remaining equalities conditional on `BPL ⊆ L`.
- Additive root imports and Capstones registrations, the updated README,
  NOTICE, absorption evidence, and the two changed M26 task rows.

All 977 new Lean files and the updated degree-comparison module are copied
unchanged from the delivery. Existing version pins, public interfaces,
ignore rules, local submission tools and previous merge/task records are
preserved. The previously recorded `Finset.prod_le_one` adaptation remains
in NOTICE. Unrelated old-module edits and input transport/scratch files are
excluded.

The producer's original report is retained in
`M26-ARISTOTLE-DELIVERY-12-REPORT.md`, separately from these local checks.

## Verification

- Manifest check passes with the original Lean/Mathlib pins.
- Sorry/admit check passes for 1788 modules.
- Closure/registration check passes for 1787 library modules.
- Task-board validation passes with preserved local rows.
- Full compilation was stopped at the user's explicit request to merge only.
  It did not complete, and terminal-proof axiom checks were not run locally.
  The partial log is `/tmp/church-turing-delivery12-build.log`.
- The 977 new Lean files match the delivery byte for byte; the local build
  pins and previous task/tooling records are preserved.

## Remaining scope

The delivered DegreeRigidity row now includes a theorem proof rather than only
a proposition definition. Its producer-reported status is preserved; this
merge does not claim completed local compilation. Logspace is still `DONE_WEAK`: amplification establishes
`RL ⊆ BPL`, but the supplied update does not prove `BPL ⊆ L`.
DepthThree's host-model bridges and the missing WeisfeilerLeman paper title
are unchanged. This merge supplies none of those missing constructions.

This record concerns the merged working tree; no library delivery archive is
produced or claimed to have been gated at `HEAD`.
