# M7-OMEGA-ML-RANDOM

**Status:** DONE_STRONG

Modules `Start/OmegaUIncompressible.lean` and `Start/OmegaURandom.lean`, both imported by
`Start.lean`.

The open boundary recorded earlier for this task was that the machine underlying `kolmP` —
closed λ-terms under the self-delimiting `Lambda.bits` code, with no input stream — is not
additively optimal, so Levin–Schnorr could not be run over it.  That boundary was removed by
building a genuinely universal *prefix* machine by Kraft–Chaitin allocation
(`Start/KCMachine.lean`, `KC.U`, complexity `KC.KU`, halting probability `KC.Omega`), proving
Chaitin incompressibility for its binary expansion (`Start/OmegaUIncompressible.lean`,
`KC.omegaSeq`, `KC.exists_const_le_KU_omegaPrefix`), and then running the converse half of
Levin–Schnorr over that machine here.

## The converse half of Levin–Schnorr

Given a Martin-Löf test `T : Lambda.MLTest`, level `c` of the test is turned into a computable
stream of Kraft–Chaitin requests:

* `KC.discovered T c j` — the string discovered at step `j` of level `c`; the step index `j`
  codes a pair `(σ, s)` and `σ` is discovered when it has entered level `c` by stage `s`.
* `KC.cutLength T c j` — the common length at which the `j`-th discovery is cut into cylinders:
  the largest length discovered so far, and at least `c` (`KC.le_cutLength`,
  `KC.cutLength_mono`, `KC.discLen_le_cutLength`).
* `KC.covered T c τ j` — whether `τ` already extends a string discovered before step `j`
  (`KC.covered_iff`).
* `KC.piece T c j m` — the `m`-th piece of the `j`-th discovery: the extension of the discovered
  string to length `cutLength T c j` with numerical value `m`, kept only when it is not already
  covered.  Distinct pieces of one level are incomparable (`KC.piece_not_prefix`), so their
  cylinders are pairwise disjoint (`KC.disjoint_cylinder_piece`) and lie inside the level
  (`KC.cylinder_piece_subset_level`); hence any finite family of them has total weight at most
  `2 ^ (-c)` (`KC.sum_wt_pieces_le`, using the cylinder-measure lemmas
  `Lambda.disjoint_cylinder` and `Lambda.sum_two_inv_pow_length_le` in `Start/MartinLof.lean`).
* `KC.testReq T i` — the request stream: the piece named by `i = ⟨k, j, m⟩` is a piece of level
  `2 * k + 2`, requested with a saving of `k` bits.  Its total weight is at most `1`
  (`KC.sum_wtOpt_testReq_le`, summing `∑ₖ 2 ^ (-k-2)`), and it is computable
  (`KC.computable_testReq`).
* `KC.exists_piece_prefix` — every sequence caught by level `2 * k + 2` of the test has a prefix
  which is requested with a saving of `k` bits.

Feeding `KC.testReq T` to the Kraft–Chaitin theorem `KC.exists_const_KU_le` gives a constant
`c₁` with `KU (prefixList X N) ≤ N - k + c₁` for every sequence `X` caught at level `2k + 2`,
which contradicts incompressibility `KC.exists_const_le_KU_omegaPrefix` for `Ω` once
`k = c₀ + c₁ + 1`.  Hence

* `KC.mlRandom_omegaSeq : Lambda.MLRandom KC.omegaSeq` — **Chaitin's `Ω` is Martin-Löf random.**

Auxiliary material added along the way:

* `Lambda.measurableSet_cylinder`, `Lambda.prefixList_eq_of_mem_cylinder`,
  `Lambda.prefix_of_mem_cylinder`, `Lambda.disjoint_cylinder`,
  `Lambda.sum_two_inv_pow_length_le` in `Start/MartinLof.lean`.
* `BitStr.isPrefixB` with `BitStr.isPrefixB_iff` and `BitStr.primrec_isPrefixB` (also
  `BitStr.primrec_isPrefix`) in `Start/BitString.lean`: the prefix test as an arithmetic
  `Bool`-valued function, which is what keeps the computability proofs of the request stream
  tractable.

Gates: `lake build` succeeds; no `sorry`; no linter warnings;
`#print axioms KC.mlRandom_omegaSeq` reports only `propext, Classical.choice, Quot.sound`.
