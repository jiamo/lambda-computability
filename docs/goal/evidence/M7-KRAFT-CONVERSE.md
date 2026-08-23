# M7-KRAFT-CONVERSE

**Status:** DONE_STRONG

Module `Start/KraftConverse.lean`, imported by `Start.lean`.  `Start/Kraft.lean` proves Kraft's
inequality — the weights `2 ^ (-|w|)` of a prefix free family sum to at most `1`.  This module
proves the converse for a non-decreasing sequence of lengths, so the two together characterize
exactly which length sequences are realizable.

## Definitions

* `Kraft.bitsOfNat len a` — the `len`-bit big-endian binary representation of `a`.
* `Kraft.kraftIndex n i = ∑_{j < i} 2 ^ (n i - n j)` — the partial Kraft sum below `i`, rescaled
  by `2 ^ n i`.  Monotonicity of the lengths is what makes it a natural number, which keeps the
  whole construction inside `ℕ`: no real binary expansions are needed.
* `Kraft.kraftCode n i` — the `i`-th code word: the `n i`-bit representation of
  `kraftIndex n i`.

## Theorems

* `Kraft.eq_div_of_bitsOfNat_prefix` — truncating a fixed-width representation to a prefix
  divides by a power of two.
* `Kraft.kraftIndex_lt` — the Kraft hypothesis says exactly that `kraftIndex n i < 2 ^ n i`, so
  the code word exists.
* `Kraft.le_kraftIndex` — the gap estimate `(kraftIndex n i + 1) * 2 ^ (n j - n i) ≤
  kraftIndex n j` for `i < j`: truncating the `j`-th code word to `n i` bits already overshoots
  the `i`-th one.
* `Kraft.prefixFreeCoding_kraftCode` — **the converse of Kraft's inequality**: the construction
  is prefix free, and `Kraft.length_kraftCode` says its code words have exactly the prescribed
  lengths.
* `Kraft.exists_prefixFree_iff` — the resulting characterization: for monotone lengths, a prefix
  free coding with those lengths exists **iff** every finite Kraft sum is at most `1`.

Gates: `lake build` succeeds; no `sorry`; `#print axioms` reports only
`propext, Classical.choice, Quot.sound`.  A sanity check by evaluation: for lengths
`1, 2, 3, …` the construction returns `0, 10, 110, …`, and for the constant length `3` it
returns `000, 001, 010, 011, 100`.

## Boundary

This is only the **combinatorial** half of the Kraft–Chaitin machine existence theorem.  The
effective half — producing the code words uniformly computably from a computable enumeration of
requests, and assembling them into a prefix machine — is not formalized, and neither is the
online (unsorted) version of the allocation.  Consequently the hard half of the Levin–Schnorr
theorem remains open; see `M7-OMEGA-ML-RANDOM`.
