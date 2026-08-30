# M10-SCOTT-CURRY

**Status:** DONE_STRONG

Module `Start/ScottCurry.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

`Start/Scott.lean` already proves Scott's theorem — a set of lambda terms that is invariant
under convertibility and has a closed member and a closed non-member has a non-computable code
set — and Rice's theorem for the lambda calculus as its numerical form.  Both are statements
about *one* invariant set and its complement.  The Scott–Curry theorem is the sharper,
two-sided statement: *any* two convertibility-invariant sets of terms, each with a closed
member, already have recursively inseparable code sets.  Inseparability is strictly stronger
than undecidability of either side: it says that no computable predicate can even be correct on
both sets while being arbitrary elsewhere.

## What is proved

* `Lambda.RecursivelyInseparable A B` — no computable predicate contains `A` and avoids `B`.
* `Lambda.SeparatesCodes C A B` — the predicate `C` on codes answers "yes" on the code of every
  term of `A` and "no" on the code of every term of `B`.
* `Lambda.scott_curry` — **the Scott–Curry theorem**.  If `A` and `B` are invariant under
  convertibility, `M ∈ A` and `N ∈ B` are closed and `C` is a computable predicate on codes,
  then `C` does not separate the codes of `A` from the codes of `B`.
* `Lambda.scott_curry_codeSet` — the same statement as recursive inseparability of
  `Lambda.CodeSet A` and `Lambda.CodeSet B`.
* `Lambda.not_computablePred_codeSet_of_scott_curry` — Scott's theorem recovered as the special
  case `B = fun t => ¬ A t`, so Rice's theorem for the lambda calculus is a corollary of the
  inseparability statement as well.
* `Lambda.recursivelyInseparable_conv_church`, `Lambda.disjoint_conv_church` — the concrete
  instance: for `m ≠ n` the terms convertible with `church m` and those convertible with
  `church n` form disjoint invariant sets, so their code sets are recursively inseparable.

## The proof

Curry's diagonal argument, run on the term that `Start/Scott.lean` already builds.  From a
computable `C` one obtains a closed lambda term `F` that decides `C` on Church numerals
(`Lambda.exists_code_decider_of_computablePred`, factored out of the decider construction that
was previously inlined in the proof of `Lambda.exists_decider_of_computablePred`: run a realizer
of the characteristic function and test the result for zero).  Kleene's second recursion theorem
(`Lambda.exists_code_fixed_point`) then supplies a term `X` with

    X  ↠  (λc. if F c then N else M) ⌜X⌝  ↠  if F ⌜X⌝ then N else M .

If `C ⌜X⌝` holds then `F ⌜X⌝ ↠ true`, so `X ↠ N`; invariance of `B` gives `X ∈ B`, and a
separating predicate must then fail on `⌜X⌝`.  If `C ⌜X⌝` fails then `F ⌜X⌝ ↠ false`, so
`X ↠ M`, invariance of `A` gives `X ∈ A`, and a separating predicate must hold on `⌜X⌝`.  Either
way the assumption is contradicted.

Disjointness of `A` and `B` is not a hypothesis: if the two sets meet then no separating
predicate exists for trivial reasons, and the theorem is exactly the statement that none exists.

## Gates

* `lake build` — the whole library, no error and no warning.
* `python3 scripts/check_closure.py` — every module in the import closure of `Start.lean` and
  registered.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: `Lambda.scott_curry`, `Lambda.scott_curry_codeSet`,
  `Lambda.not_computablePred_codeSet_of_scott_curry` and
  `Lambda.recursivelyInseparable_conv_church` depend only on `propext`, `Classical.choice` and
  `Quot.sound`.
