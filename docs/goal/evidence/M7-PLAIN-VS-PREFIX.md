# M7-PLAIN-VS-PREFIX

**Status:** DONE_STRONG

Module `Start/PlainVsPrefix.lean` (imported by `Start.lean`).

Two complexity measures live in the development: plain complexity `Lambda.kolm` (least
number of syntax *nodes* of a closed program) and prefix complexity `Lambda.kolmP` (least
number of *bits* of a closed program in the self-delimiting coding `Lambda.bits`).

* `Lambda.size_le_bits_length`, `Lambda.kolm_le_kolmP` and
  `Lambda.kolm_le_kolmP_le_two_mul_kolm : kolm s ≤ kolmP s ∧ kolmP s ≤ 2 * kolm s` — the
  comparison is sharp in both directions, with no logarithmic correction term: the
  self-delimiting code spends between one and two bits per syntax node.
* `Lambda.exists_const_kolmP_le_size` — with the compact numerals of
  `Start/KolmogorovBinary.lean`, `kolmP n = O(log n)`.
* `Lambda.exists_incompressible_kolmP` — numbers of arbitrarily large prefix complexity
  exist (counting, as for the plain measure).
* `Lambda.bits_length_le_encode`, `Lambda.not_computablePred_kolmP_le` and
  `Lambda.not_computable_kolmP` — the prefix measure is uncomputable too, by the same
  Berry argument with the bit measure in place of the node measure.

Gates: `lake build` succeeds; no `sorry`; no linter warnings.
