# M11-SPECKER-REAL

**Status:** DONE_STRONG

`Start/SpeckerReal.lean` completes the Specker construction of `Start/Specker.lean` by taking the
limit of the sequence and proving that this real number is not computable — the classical form of
Specker's theorem.  The module is imported from `Start.lean`, registered in
`Start/Capstones.lean`, free of `sorry` and of linter warnings, and its results depend only on
`propext`, `Classical.choice`, `Quot.sound`.

## The limit exists (first exit criterion)

* `Lambda.speckerVal_bddAbove` — the sequence, viewed in `ℝ`, is bounded above by `1`;
* `Lambda.speckerReal` — the limit, defined as the supremum of the sequence;
* `Lambda.speckerVal_le_speckerReal`, `Lambda.speckerReal_nonneg`, `Lambda.speckerReal_le_one`,
  `Lambda.exists_speckerVal_gt` — the basic properties of the supremum used later.

## Approximations are decided by natural-number arithmetic (second exit criterion)

* `Lambda.dyadic_lt_speckerVal_iff` — a dyadic rational `a / 2 ^ m - 1 / 2 ^ m` is below the
  stage `s` of the sequence exactly when `a * 2 ^ s < speckerNum s * 2 ^ m + 2 ^ s`, a comparison
  of natural numbers;
* `Lambda.speckerFound`, `Lambda.computable_speckerFound` — the resulting search predicate is
  computable whenever the candidate approximation is.

## The limit is not computable (third exit criterion)

* `Lambda.specker_limit_not_computable` — there is no computable `f : ℕ → ℕ` with
  `|speckerReal - f m / 2 ^ m| < 1 / 2 ^ m` for all `m`.  Given one, an unbounded search
  (`Nat.rfind`) over `Lambda.speckerFound` returns, for each `k`, a stage `s` with
  `speckerReal - speckerVal s < 2 ^ (-(k+3))`.  Any index `k` entering the halting set after
  stage `s` would raise the sequence by at least `2 ^ (-(k+1))` (`Lambda.speckerVal_jump`), which
  the bound forbids; so `k ∈ K` is decided by `entered k s`, contradicting
  `Lambda.not_rePred_not_haltK`.

Because the limit is nonnegative, restricting the numerators of the approximating dyadic
rationals to `ℕ` is no loss of generality.

## Scope

The general theory of computable reals — the Cauchy representation, the arithmetic of computable
reals, and the Weihrauch degree of monotone convergence — is not part of this task; the limit of
this particular sequence and its non-computability are.
