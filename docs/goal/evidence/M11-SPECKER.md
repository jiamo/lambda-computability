# M11-SPECKER

**Status:** DONE_STRONG

`Start/Specker.lean` takes the first step from function realizability into computable analysis:
a *Specker sequence*, a computable, nondecreasing, bounded sequence of rationals whose limit is
not computable.  The module is imported from `Start.lean`, registered in `Start/Capstones.lean`,
free of `sorry` and of linter warnings, and its results depend only on `propext`,
`Classical.choice`, `Quot.sound`.

## The sequence is computable (first exit criterion)

* `Lambda.entered` — "`k` has entered the halting set by stage `s`", defined from
  `Nat.Partrec.Code.evaln`, with `Lambda.primrec_entered` its primitive recursiveness,
  `Lambda.entered_mono` its monotonicity in the stage, and `Lambda.haltK_iff_entered` the bridge
  to `Lambda.HaltK` of `Start/KleeneK.lean`;
* `Lambda.speckerVal` — the sequence: at stage `n`, the sum of `2^{-(k+1)}` over the indices
  `k < n` that have entered the halting set by stage `n`;
* `Lambda.speckerNum`, `Lambda.computable_speckerNum`, `Lambda.speckerVal_eq` — the numerator of
  `speckerVal n` over the denominator `2 ^ n` is a computable function of `n`, so the sequence is
  a computable sequence of rationals.

## The sequence is nondecreasing and bounded (second exit criterion)

* `Lambda.speckerVal_monotone` — nondecreasing, because a term once present never disappears
  (`Lambda.speckerTerm_le`, `Lambda.speckerVal_eq_sum_range`);
* `Lambda.speckerVal_lt_one` — bounded above by `1`, by comparison with the geometric series
  (`Lambda.sum_half_pow`);
* `Lambda.speckerVal_jump` — when a new index `k` enters the halting set between two stages, the
  sequence increases by at least `2^{-(k+1)}`.

## No computable modulus of convergence (third exit criterion)

* `Lambda.specker_no_computable_modulus` — there is no computable `g : ℕ → ℕ` with
  `speckerVal n - speckerVal (g m) < 2^{-m}` for all `n ≥ g m`.  Given one, `k ∈ K` would be
  decided by `entered k (g (k + 2))`: if `k` entered later, the jump of at least `2^{-(k+1)}`
  granted by `speckerVal_jump` would exceed the allowed `2^{-(k+2)}`.  That contradicts the
  undecidability of the halting set (`Lambda.not_rePred_not_haltK`).

Effectively, therefore, the monotone convergence theorem fails: the limit of this computable,
nondecreasing, bounded rational sequence is not a computable real.

## Scope

The real number that is the limit, and the general theory of computable reals (Cauchy
representation, the Weihrauch degree of monotone convergence), are not part of this task; the
sequence, its computability, its monotonicity and boundedness, and the absence of a computable
modulus are.
