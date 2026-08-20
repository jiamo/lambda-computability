# M5-ENCODINGS-MULTIARG

**Status:** DONE_STRONG

New module `Start/Encodings.lean` (imported by `Start.lean`), plus a strengthening in
`Start/PartialCapstone.lean`.

* `Lambda.partialTerm_closed` and `lambdaComputable_of_partrec_closed` — the compiler from partial
  recursive functions into lambda terms produces a *closed* term.  This is what makes the currying
  construction below possible; the old `lambdaComputable_of_partrec` is now a corollary.
* `Lambda.uncurryTerm`, `Lambda.curryTerm` and their reduction lemmas — explicit terms translating
  between curried application to two numerals and application to the `Nat.pair` code of the pair.
* `lambdaComputable2_iff_partrec₂` — a binary partial function is lambda-definable in curried form
  exactly when it is partial recursive; `lambdaComputable2_iff_tm2Computable` adds the machine side.
* `LambdaComputableEnc`, `TM2ComputableEnc`, `lambdaComputableEnc_iff_partrec`,
  `tm2ComputableEnc_iff_partrec`, `lambdaComputableEnc_iff_tm2ComputableEnc`,
  `lambdaComputableEnc_iff_computable` — the same equivalences for arbitrary `Primcodable`
  domains and codomains, with a non-vacuity example on `List ℕ`.

Gates: `lake build Start.Encodings` succeeds; no `sorry`.
