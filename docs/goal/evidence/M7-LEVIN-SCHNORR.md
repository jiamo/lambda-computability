# M7-LEVIN-SCHNORR

**Status:** DONE_STRONG

Modules `Start/OmegaURandom.lean` (converse half) and `Start/LevinSchnorr.lean` (easy half and
the equivalence), both imported by `Start.lean`.  They build without `sorry` and without linter
warnings, and the headline results depend only on `propext`, `Classical.choice`, `Quot.sound`.

The complexity in question is `KC.KU`, the prefix complexity of the Kraft–Chaitin universal
prefix machine `KC.U` of `Start/KCMachine.lean`.  That machine is additively optimal, which is
what makes both directions available; the lambda-machine complexity `Lambda.kolmP` of
`Start/Kolmogorov.lean` is not additively optimal, and only the easy half is proved for it
(`Lambda.exists_const_le_kolmP_prefix_of_mlRandom`, `Start/MartinLof.lean`).

## The converse half (first exit criterion)

* `KC.mlRandom_of_exists_const_le_KU` — if `∃ c, ∀ n, n ≤ KU ⌜X ↾ n⌝ + c` then `X` is Martin-Löf
  random.  Given a test `T`, the request stream `KC.testReq T` (already built in
  `Start/OmegaURandom.lean`) is computable and of total weight at most one, so the Kraft–Chaitin
  theorem `KC.exists_const_KU_le` supplies a constant `c₁` with `KU x ≤ r + c₁` for every request
  `(r, x)`; `KC.exists_piece_prefix` produces, for a sequence caught by level `2k+2` of `T`, a
  request that compresses one of its prefixes by `k` bits, and taking `k = c₀ + c₁ + 1`
  contradicts the assumed incompressibility.

## The easy half (second exit criterion)

* `KC.kuFound`, `KC.kuEnter` — the compression test of `KC.U`: level `c` enumerates the strings
  `σ` for which some allocation step hands out a program of length `L` for `⌜σ⌝` with
  `L + c < |σ|`.  `KC.computable_kuEnter` proves the enumeration computable (via
  `KC.primrec_kuFound` and `KC.slot_primrec`), and `KC.exists_kuEnter_iff` identifies the
  enumerated set with `{σ | KU ⌜σ⌝ + c < |σ|}` — the `←` direction uses `KC.KU_spec`, i.e. that
  every number really has a shortest program.
* `KC.kraft_KU_ennreal` and `KC.cantorMeasure_kuEnter_le` — Kraft's inequality `KC.kraft_KU`
  transported to `ℝ≥0∞` bounds the measure of level `c` by `2 ^ (-c)`, so `KC.kuTest` is a
  Martin-Löf test.
* `KC.exists_const_le_KU_prefix_of_mlRandom` — a random sequence escapes `KC.kuTest`, which is
  exactly incompressibility of its prefixes.

## The equivalence (third exit criterion)

* `KC.mlRandom_iff_exists_const_le_KU : MLRandom X ↔ ∃ c, ∀ n, n ≤ KU ⌜X ↾ n⌝ + c`.
* `KC.mlRandom_omegaSeq` is now literally
  `mlRandom_of_exists_const_le_KU exists_const_le_KU_omegaPrefix`: the Martin-Löf randomness of
  `Ω` is the special case of the converse half applied to Chaitin incompressibility.

## Boundary

The equivalence is about `KC.KU`.  Only one half of the comparison with `Lambda.kolmP` is
available: `KC.exists_const_KU_le_kolmP` (M8-KU-OPTIMAL, `Start/KUOptimal.lean`) gives
`KU s ≤ kolmP s + c`.  The opposite bound, which is what would transport the equivalence to the
lambda machine, is *not* proved and is not expected to hold in that form: writing `ℓ` payload
bits into a lambda term costs more than `ℓ + O(1)` bits.
