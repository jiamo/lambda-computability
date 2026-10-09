# M26 Logspace: newly published upstream proof

Checked on 2026-10-08 without compiling Lean or modifying library proofs.

## Original snapshot

The local full upstream repository at `/Users/jiamo/projects/math` has commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, independently resolved through
the public GitHub API. Its complete Git tree contains 122140 Lean files.
`lean/OAI/Computability/Logspace/` contains only `Deterministic.lean`, and
the original formalization catalogue has no Logspace equality entry.

The original source archive includes that file and all 20 files of the
family-103 paper, with contents matching the fixed upstream tree. The
upload was complete for that snapshot. A full-tree Lean keyword search
found no further relevant Logspace result; other catalytic matches concern
ordered semigroups and matrix multiplication.

The recursive GitHub tree API response is truncated and was not used to
infer absence. The complete local Git tree supplied the original inventory.

## New upstream revision

Commit `301488868beec11bfd897168433b0a64f5258559`, published on
2026-10-08 at 05:03:50 UTC, adds 38 Logspace modules. The directory now has
39 Lean files totalling 1846513 bytes; `Deterministic.lean` is unchanged.
All 39 files have been downloaded and checked against their Git blob hashes.
Their `OAI` imports are entirely within the supplied directory.

`lean/OAI/Computability/Logspace/Equality.lean` now supplies proofs of:

```lean
theorem BPL_subset_L : BPL ⊆ L := by ...
theorem exact_logarithmic_space_derandomization : L = RL ∧ RL = BPL := by ...
```

The source is under `OAI.ExactDerandomization`. The terminal declarations
have no extra derandomization hypothesis. The official scope file
`lean/docs/103.md`, catalogue and comparator configuration now identify the
equality target. The comparator Lean file intentionally contains a `sorry`:
it is a reference specification, not the proof source, and must stay outside
`Start/`. The 39 actual Logspace modules contain no sorry/admit/axiom tokens.

The upstream pin remains Lean v4.34.1 with Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Porting must preserve this
library's existing Lean/Mathlib v4.33.0 pins.

## Supplement and next work

Prepared in `.aristotle/logspace-3014888/` (ignored by Git):

- `oai-math-logspace-3014888.bundle.json`: all 39 source modules plus official
  scope, comparator, catalogue, upstream pin metadata and provenance.
- `restore_source_bundle.py`: the existing standalone attachment restorer.
- `prompt.txt`: continuation instructions to absorb the new proof dependency
  chain, reconcile the two Amplification modules, retain attribution and
  register the unconditional theorem under this library's namespace.

The bundle has 47 reference files. At the user's explicit request it was
submitted with the restoration script and continuation prompt to the existing
Aristotle project `04009a97-5b4f-4a0f-872c-515ae1fa69cc`.
The returned task is `09049798-e579-4c30-8a95-c3515ea63c99`; an independent
SDK readback confirmed the project identity and status `QUEUED`.
The receipt is `.aristotle/logspace-3014888/last-submission.json` and contains
no API key.

Task: https://aristotle.harmonic.fun/projects/04009a97-5b4f-4a0f-872c-515ae1fa69cc?task=09049798-e579-4c30-8a95-c3515ea63c99

No new local proof or compilation is claimed. The remaining task is now
porting existing upstream code, rather than reconstructing the paper's
derandomization proof from scratch.

Sources:

- https://github.com/openai/math/commit/301488868beec11bfd897168433b0a64f5258559
- https://github.com/openai/math/blob/301488868beec11bfd897168433b0a64f5258559/lean/OAI/Computability/Logspace/Equality.lean
- https://github.com/openai/math/blob/301488868beec11bfd897168433b0a64f5258559/lean/docs/103.md
