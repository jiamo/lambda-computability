# M6-KOLMOGOROV-OMEGA

**Status:** DONE_STRONG

New modules `Start/Kraft.lean` and `Start/ChaitinOmega.lean`, both imported by `Start.lean`.

## Prefix-free coding of terms (`Start/ChaitinOmega.lean`)

* `Lambda.bits : Lambda → List Bool` — the binary lambda calculus coding:
  `var i ↦ 1^(i+1) 0`, `lam t ↦ 00 ++ bits t`, `app a b ↦ 01 ++ bits a ++ bits b`.
* `Lambda.bits_append_inj` — the self-delimiting statement: `bits s ++ u = bits t ++ v` forces
  `s = t` and `u = v` (structural induction, with `Lambda.replicate_true_append_inj` handling the
  block of `true` bits of a variable).
* `Lambda.bits_prefixFree` / `Lambda.bits_prefixFreeCoding` — no code word is a prefix of another
  one; `Lambda.bits_injective` follows.
* `Lambda.bits_length_le_two_mul_size` — a code word is at most twice the syntactic size of its
  term, which links the bit measure to the node measure of `Start/Kolmogorov.lean`.

## Kraft's inequality (`Start/Kraft.lean`)

* `Kraft.wt w = 2 ^ (-|w|)`, `Kraft.PrefixFreeCoding c` — `c i <+: c j → i = j`.
* `Kraft.boolLists n`, `Kraft.ext w n` — the bit strings of length `n` and the extensions of `w`
  to length `|w| + n`, with `card_boolLists`, `card_ext`.
* `Kraft.sum_two_pow_sub_le` — the counting core: extensions of distinct code words to a common
  length `N` are disjoint, so `∑ 2 ^ (N - |c i|) ≤ 2 ^ N`.
* `Kraft.sum_wt_le_one` (finite), `Kraft.summable_wt`, `Kraft.tsum_wt_le_one` — Kraft's inequality
  `∑ 2 ^ (-|c i|) ≤ 1` for any prefix free coding.
* `Kraft.tsum_wt_add_le_one` — a subfamily leaves room for the weight of any excluded code word.

## Prefix complexity and Chaitin's Ω (`Start/ChaitinOmega.lean`)

* `Lambda.kolmP s` — prefix complexity: the least bit length of a closed program for `s`;
  `Lambda.exists_program_of_kolmP` gives a shortest one, and
  `Lambda.kolmP_le_two_mul_kolm` compares it with plain complexity.
* `Lambda.shortestProgram_prefixFreeCoding` — shortest programs for different numbers are
  incomparable (confluence, via `Lambda.unique_church_reduct`), hence
  `Lambda.kraft_kolmP : ∑' s, 2 ^ (-kolmP s) ≤ 1`.
* `Lambda.Halts t` — `t` is closed and has a normal form; `Lambda.halts_I`,
  `Lambda.not_halts_omega`.
* `Lambda.summable_haltingWeight` — the halting weights are summable (Kraft), so
  `Lambda.chaitinOmega = ∑' t halting, 2 ^ (-|bits t|)` is a convergent sum.
* `Lambda.chaitinOmega_le_one` — Kraft's inequality for the halting set.
* `Lambda.chaitinOmega_pos`, `Lambda.chaitinOmega_lt_one`, `Lambda.chaitinOmega_mem_Ioo` —
  `0 < Ω < 1`: positivity because `I` halts, strictness because `omega` does not halt and its own
  weight `2 ^ (-|bits omega|)` is left over in Kraft's inequality
  (`Lambda.chaitinOmega_add_omega_weight_le_one`).

Honest boundary: the algorithmic randomness of `Ω` (its incompressibility, and the fact that its
first `n` bits decide the halting problem for programs of length `≤ n`) is not proved here; only
the definition, convergence, and `0 < Ω < 1` were in the exit criteria.

Gates: `lake build` succeeds; no `sorry`; no linter warnings in the new modules; `#print axioms`
on `Lambda.chaitinOmega_mem_Ioo`, `Lambda.kraft_kolmP` and `Kraft.tsum_wt_le_one` reports only
`propext, Classical.choice, Quot.sound`.
