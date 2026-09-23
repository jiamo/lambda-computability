# M19-KT-DEFINITIONS — time-bounded Kolmogorov complexity `K^T`

**Status:** DONE_WEAK (the first two exit criteria are proved; the `NP` membership is not).

`Start/KolmogorovTime.lean` adds the *time-bounded* measure, as opposed to Levin's `Kt` of
`Start/LevinKt.lean`: `K^T(s)` charges nothing for time but forbids running longer than `T`.

## The definition, as a description system

* `Lambda.IsProgramForWithin p T s` — `p` is closed and `reducesIn n p (church s)` for some
  `n ≤ T`;
* `Lambda.ktimeSystem T : Complexity.DescSystem Lambda ℕ` — the programs above with their
  syntactic size, so the measure is an instance of `Start/DescriptionSystem.lean`;
* `Lambda.ktime T s` — `K^T(s)`, the least size of such a program;
* `Lambda.ktime_le_of_isProgramForWithin`, `Lambda.exists_program_of_ktime` — the minimum is
  attained;
* `Lambda.ktime_le_iff` — `K^T(s) ≤ k` **iff** there is a bounded certificate: a program of size
  at most `k` together with a run of at most `T` steps.

## Basic theory

* `Lambda.ktime_antitone` — `K^T` decreases as `T` grows;
* `Lambda.kolm_le_ktime` — `K ≤ K^T`;
* `Lambda.ktime_le_church` — `K^T(s) ≤ 3s + 3`, the size of the numeral itself, for every `T`
  (the "length plus a constant" bound in this encoding of the objects);
* `Lambda.exists_bound_ktime_eq_kolm`, `Lambda.ktime_eq_kolm_of_le` — for every `s` there is a
  bound from which on `K^T(s) = K(s)`;
* `Lambda.finite_setOf_ktime_le`, `Lambda.exists_incompressible_ktime` — the counting bound and
  incompressibility, inherited from `K`;
* `Lambda.kt_le_ktime_add_log`, `Lambda.ktime_le_of_kt` — comparison with Levin's `Kt`.

## Invariance

* `Lambda.ktimeWithSystem U T`, `Lambda.ktimeWith U T s` — the measure read through a fixed
  interpreter `U`;
* `Lambda.ktimeWithTranslation` — applying `U` is a `Complexity.DescSystem.Translation` of cost
  `size U + 1` that costs **no extra beta steps**;
* `Lambda.ktime_le_ktimeWith` — hence the invariance estimate: a change of interpreter costs at
  most the additive constant `size U + 1` and leaves the time bound unchanged (in the lambda
  calculus interpretation is free, which is stronger than the usual "polynomial change of the
  bound");
* `Lambda.ktimeWith_I_le_ktime` — the converse for the identity interpreter, at the price of one
  extra step in the bound.

## Not done

The third exit criterion — that `{(x, k) : K^T(x) ≤ k}` is a language in `NP` in the time model of
`Start/ComplexityClasses.lean` — is **not** proved. `Lambda.ktime_le_iff` supplies its
combinatorial half (the certificate is a program of size at most `k`); what is missing is that
the certificate is *checked* in polynomial time, i.e. that running a guessed term for `T` steps
is a polynomial-time predicate of the encodings. The pieces for that are the Krivine machine in
the Cobham model (`Start/KrivineCobStep.lean`, `Start/KrivineCobWord.lean`), which computes one
transition by a single Cobham term at polynomial cost, plus an encoding of lambda terms as words
and the bridge between Krivine transitions and beta steps of `Start/KrivineDecode.lean`.

## Gates

`lake build` (whole tree, no errors and no linter warnings), `scripts/check_sorry.py`,
`scripts/check_closure.py`, `scripts/goal_state.py validate`. `#print axioms` on every theorem
above reports only `propext`, `Classical.choice`, `Quot.sound`.
