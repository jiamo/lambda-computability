# M7-BLC-BRIDGE

**Status:** DONE_STRONG

Module `Start/BLC.lean`, imported by `Start.lean`.  The library already had the *encoder*
`Lambda.bits` for the binary lambda calculus (BLC) self-delimiting code: `00 b` for an
abstraction, `01 b₁ b₂` for an application, `1ⁱ 0` for the de Bruijn index `i`.  This module adds
the *decoder* and proves that the two are mutually inverse, which is the bridge between the
bit-string presentation of terms and the term/numeral presentation used everywhere else in the
development.

## Definitions

* `Lambda.readOnes` — reads the unary prefix `1ⁱ 0` of a variable code.
* `Lambda.decodeAux` — the fuel-driven parser for a prefix of a bit string, returning the term
  and the unconsumed remainder.
* `Lambda.blcDecode` / `Lambda.blcDecodeFull` — the parser at the top level, the latter demanding
  that the whole string be consumed.
* `Lambda.isBLC` — the decidable predicate "this bit string is the BLC code of some term".
* `Lambda.bitsEquiv : Lambda ≃ {bs : List Bool // isBLC bs = true}` — the resulting bijection.
* `Lambda.bitsOfNat` / `Lambda.natOfBits` — the round trip between the project's numeric codes
  for terms and BLC bit strings.

## Theorems

* `Lambda.decodeAux_bits` and `Lambda.decodeAux_sound` — the parser accepts exactly the codes
  produced by `Lambda.bits`, with the expected remainder.
* `Lambda.blcDecodeFull_eq_some_iff : blcDecodeFull bs = some t ↔ bs = bits t` — the coding is
  invertible; this is the bridge statement.
* `Lambda.isBLC_iff` — `isBLC bs` holds exactly when `bs` is some term's code.
* `Lambda.natOfBits_bitsOfNat` and `Lambda.bitsOfNat_natOfBits` — the numeric codes and the BLC
  bit strings translate into each other.
* `noncomputable instance : Primcodable Lambda` together with `Lambda.primrec_encode` — the
  decoder is what makes the terms a `Primcodable` type, which is what the computability layer
  (for instance `Start/HaltingComplete.lean`) consumes.

Gates: `lake build` succeeds; no `sorry`; `#print axioms` reports only the standard axioms.
