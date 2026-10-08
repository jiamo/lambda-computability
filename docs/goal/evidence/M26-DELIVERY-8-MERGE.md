# M26-DELIVERY-8-MERGE

Merged the existing Aristotle delivery from `/Users/jiamo/Downloads/8` on
2026-10-08. This is integration of delivered proofs, not completion of the
remaining mathematical tasks.

## Imported work

The merge adds 300 ordinary `Start/` modules: 298 adapted upstream modules
(33 TypeSystem, 1 Logspace, 5 SolenoidalRecorder, 37 StarHeight,
43 WeisfeilerLeman, 179 DepthThree) and the two new modules
`PTSLambdaPi` and `OracleDegreeBridge`. Their Lean source is unchanged from
the delivery. Root imports, Capstones registrations, the README attribution
section, the producer's evidence and M26 rows are merged as well.

The delivered closure-check optimization is included. The missing DepthThree
listing is added to `NOTICE` as required attribution bookkeeping.

Existing public Lean contracts, the toolchain, `lakefile.toml`, the manifest,
ignore rules, the local Aristotle submission tools and their M26 rows are
preserved. Unrelated old-module changes, transport attachments, root scratch
files and local settings are excluded.

One delivered compatibility change in an existing module is also included:
`CoinDecode.lean` makes seven `ℕ` binder types explicit in casts to `ZMod p`.
It resolves the full build's type-elaboration mismatch in `ShamirSoundness`.
This file is copied unchanged from the delivery; no proof is reconstructed.

The producer's original report is retained in
`M26-ARISTOTLE-DELIVERY-8-REPORT.md`; it is distinct from local verification.

## Verification

- Manifest check: the unchanged pins agree with the manifest.
- Sorry/admit check: 811 modules pass.
- Closure and registration check: 810 library modules pass.
- Task-board validation: 297 tasks pass, including the preserved local rows.
- Full `LEAN_NUM_THREADS=4 lake build` succeeds (9530 jobs), with existing and
  delivered linter warnings. The successful log is
  `/tmp/church-turing-delivery8-build-final.log`.
- `#print axioms` on the ten principal new results reports only `propext`,
  `Classical.choice`, and `Quot.sound` (the degree embedding uses just the
  first and third). No additional proof assumption is introduced.
- All 300 new Lean files match the delivered files byte for byte, and all
  three build/pin files match the pre-merge Git tree.

Verification is of the merged working tree. No library archive is produced
or claimed to have been gated at `HEAD` by this merge.

## Remaining scope

This does not complete the original absorption objective. Logspace proves
only `L ⊆ RL` and `L ⊆ BPL`; the named converse task remains open.
DegreeRigidity remains unabsorbed and its proposition is not proved.
DepthThree retains upstream machine/circuit models without the host-library
bridges. WeisfeilerLeman still lacks a verified paper title in its attribution.

The delivery proceeded beyond unfinished Logspace despite the original order
rule. Its later proofs are retained under the user's explicit instruction to
merge the existing delivery; this does not certify compliance with that rule.
No missing theorem or model bridge is filled in by this merge.
