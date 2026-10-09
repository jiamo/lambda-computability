# M26-DELIVERY-15-MERGE

Merged the existing Aristotle update from `/Users/jiamo/Downloads/15` on
2026-10-09, incrementally over delivery 12. No local Lean compilation or
missing-proof implementation is performed, as requested by the user.

## Absorption checked in source

All 39 upstream Logspace modules from openai/math commit
`301488868beec11bfd897168433b0a64f5258559` have corresponding ordinary
`Start/` modules: the existing deterministic module plus 38 newly added
modules. Upstream `Amplification.lean` is named `LogspaceTableAmplification`
to coexist with this library's earlier amplification proof.

`Start/LogspaceEquality.lean` includes complete proof bodies for:

```lean
theorem ExactDerandomization.BPL_subset_L : BPL ⊆ L
theorem ExactDerandomization.exact_logarithmic_space_derandomization :
    L = RL ∧ RL = BPL
```

These declarations have no extra derandomization assumption. The machine
and language-class definitions, and the earlier amplification proof, are
unchanged apart from comments. The 39 absorbed modules contain no
sorry/admit/axiom tokens. The equality module is imported by `Start.lean`
and its two terminal results have explicit-type registrations in Capstones.
The upstream comparator stub was not imported.

The new files retain source path, family 103, paper title and commit-specific
attribution. The supplied `cord_mono` repair and amplification reconciliation
are documented in their headers. Both Logspace task rows are merged as
producer-reported `DONE_STRONG`, with empty open boundaries.

## Merge scope

The merge copies all 38 new Lean files and updates the root import,
Capstones, the two existing Logspace headers, README, NOTICE and absorption
evidence. Existing local task/tooling/merge records, ignore rules, public
interfaces and build pins are preserved. Transport JSON, root scratch files,
local settings and unrelated old-module edits are excluded.

The original report is retained in `M26-ARISTOTLE-DELIVERY-15-REPORT.md`.
It reports a successful 10545-job build and standard-only terminal axioms.
Those are the producer's checks; no local compilation or axiom readback is
claimed by this merge. Local checks are source comparison, import/registration
inspection and the repository's lightweight offline gates.

This closes the previously missing Logspace source absorption. Connecting
its machine model to `Complexity.Space.LOGSPACE`, and the earlier DepthThree
model to the host circuit interfaces, remain separate integration work.
