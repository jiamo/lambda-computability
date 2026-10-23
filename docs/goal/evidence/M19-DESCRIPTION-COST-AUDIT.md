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

## Big round 2, run 1

Kept DONE_WEAK.  Its earlier gap `M19-INDEX-CODE-RATE` is DONE_STRONG (constant 3 per bit,
`Lambda.kolm_le_three_log`; no constant below 1/2, `Lambda.kolm_index_rate_lower`).  The second exit
criterion ("Determine the justified quantitative target for M19-SYMMETRY-HARD-HALF ...") is
therefore settled only up to a factor 6.  The gap is the new row `M19-INDEX-CODE-OPTIMAL`, on which
this row now depends:

    theorem Lambda.kolm_index_rate_upper {p q : ℕ} (h : q < 2 * p) :
      ∃ c : ℕ, ∀ N i : ℕ, i < N → q * Lambda.kolm i ≤ p * Nat.log 2 N + c

## Big round 2, run 6 (restoration after the move to a new project)

The big round 2 sections of this note (runs 1 to 3) were lost with the old project and were recreated
in run 6 from its command logs, which record the text that was appended; the Lean modules they cite
were restored from the old project's export, rebuilt with `lake build --wfail`, and their axioms
regenerated (`docs/goal/evidence/*-axioms.txt`, section "Big round 2, run 6").

## Big round 2, run 7 (restoration after the export of run 6)

The platform's export of run 6's project dropped this note; it was put back from the copy of before big round 2 (our tree at ce8fe5e), and the
big round 2 sections that run 6 had restored were added again in run 7 from the command logs of
runs 1 to 3 (the appended text is recorded there verbatim). The axioms files of the big round 2 rows
were regenerated with `#print axioms` in run 7 (section "Big round 2, run 7").
