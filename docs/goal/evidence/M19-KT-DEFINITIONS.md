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

## Big round 2, run 1

Kept DONE_WEAK.  The first two exit criteria are met (Start/KolmogorovTime.lean); the third,
"The set of pairs (x, k) with K^t(x) <= k is in NP", is not.  Its gap is the new row `M19-KT-NP`,
on which this row now depends:

    theorem Lambda.ktimeLang_inNP {T : ℕ → ℕ} (hT : Complexity.PolyBound T) :
      Complexity.InNP (Lambda.ktimeLang T)

with `Lambda.ktimeLang T` the words coding a pair `(s, k)` (s in binary, k in unary) with
`Lambda.ktime (T n) s ≤ k`, `n` the word length.  `Lambda.ktime_le_iff` is the certificate half.

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
