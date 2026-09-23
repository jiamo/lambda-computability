# M15-ORACLE-DIAG — the counting step of a diagonalization against oracle machines

`Start/OracleDiag.lean` proves the combinatorial heart of a Baker–Gill–Solovay construction, on
top of the oracle Cobham terms of `Start/OracleCob.lean`.  It is not the separating oracle
itself (see the boundary of `M15-BGS-DIFFERENT`), but the step that makes such a construction
possible at all: a polynomial-time oracle machine cannot have asked about every word of a given
length.

## What is proved

* `Complexity.exists_mul_pow_lt_two_pow (c k)` — `c * n ^ k < 2 ^ n` from some point on.  The
  proof transfers `tendsto_pow_const_div_const_pow_of_one_lt` from the reals.
* `Complexity.PolyMono.lt_two_pow` — a monotone polynomial bound `p` satisfies `p n < 2 ^ n`
  from some point on; `(n+1)^k ≤ 2^k · n^k` for `n ≥ 1` reduces it to the previous statement.
* `Complexity.card_words_of_length n` — the words of length `n`, as the image of
  `Fin n → Bool` under `List.ofFn`, are `2 ^ n` in number.
* `Complexity.exists_word_length_not_mem` — a list of fewer than `2 ^ n` words misses a word of
  length `n`.
* `Complexity.CobQ.exists_word_not_queried` — **the diagonalization step.**  For every oracle
  Cobham term `t` there is an `n₀` such that for every oracle `A`, every argument list whose
  longest entry has length at most `n`, and every `n ≥ n₀`, some word of length `n` does not
  occur in `Complexity.CobQ.queries A t args`.  The three inputs are the query count of
  `Complexity.CobQ.polyQueryCount` (polynomial, uniformly in the oracle), the monotonicity of
  the bound, and the counting lemma above.
* `Complexity.CobQ.exists_word_not_queried_unary` — the same on the input `1^n`, the shape used
  by the language `{1^n : some word of length n lies in B}`.

Together with the use principle `Complexity.CobQ.run_congr`, this says exactly what a stage of
the construction needs: after running the `e`-th machine on `1^n` with the oracle built so far,
one may put a word of length `n` into the oracle, or keep it out, without changing that run.

## What is still missing for `M15-BGS-DIFFERENT`

An enumeration of the oracle machines: a surjection `ℕ → Complexity.CobQ`.  `CobQ` is a nested
inductive (a constructor carries a `List CobQ`), for which the `Countable` deriving handler does
not apply, so the encoding and its decoder have to be written by hand.  With that in place the
stages can be defined by recursion and the separating oracle assembled.

## Gates

`lake build` (whole tree, no errors and no new warnings), `python3 scripts/check_sorry.py`,
`python3 scripts/check_closure.py`, `python3 scripts/goal_state.py validate`,
`python3 scripts/check_manifest.py`.
