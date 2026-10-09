# M19-DESCRIPTION-COST-AUDIT — counting for the raw size measure

**Status:** DONE_WEAK.

`Lambda.kolm` and `Lambda.kolmCond` minimise `Lambda.size` (a de Bruijn index `i` costs `i+1`),
not binary length.  `Start/KolmogorovCount.lean` (this library's own):

* `Lambda.sizeBits` — explicit prefix-free binary code (`var i ↦ 1^(i+1)0`, `lam t ↦ 01·bits t`,
  `app a b ↦ 00·bits a·bits b`); `Lambda.sizeBits_append_inj` (unique decoding).
* `Lambda.size_le_length_sizeBits`, `Lambda.length_sizeBits_le` — `size t ≤ |bits t| ≤ 2·size t`.
* `Lambda.card_size_le : Nat.card {t // size t ≤ m} ≤ 4 ^ m`.
* `Lambda.card_kolm_le`, `Lambda.card_kolmCond_le` — at most `4^m` numbers of (conditional)
  complexity `≤ m`.
* `Lambda.exists_le_four_pow_kolm_gt`, `Lambda.exists_le_four_pow_kolmCond_gt` — some `s ≤ 4^m`
  has (conditional) complexity `> m`.
* `Lambda.kolmBits` with `kolm_le_kolmBits`, `kolmBits_le_two_mul_kolm`.

Consequence for the symmetry law: counting for `kolm` is base 4, so each "log₂ of a count" step
of the classical hard-half argument costs a factor 2 when stated for `kolm`; the transfer to a bit
measure is only up to the factor 2 of `kolmBits`.  Not yet done: the hard half itself
(`M19-SYMMETRY-HARD-HALF`) — the enumeration of `{(s,y) : K(s,y) ≤ m}` and the conditional
decoding of `s` from its index given `y` and `m`, through `Start/KCMachine.lean`.
