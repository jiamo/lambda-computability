# M4-SCOTT-RICE — Scott's theorem and Rice's theorem for the lambda calculus

## What was added

`Start/Scott.lean` (imported by `Start.lean`).

- `Lambda.Conv` — convertibility, defined as "having a common reduct"; by confluence this is
  β-equality.  `conv_refl`, `Conv.symm` and `Conv.trans` (the last one via
  `Lambda.confluence_theorem`) make it an equivalence relation.
- `Lambda.ConvInvariant A` — `A` does not distinguish convertible terms.
- `Lambda.Decides F A` — `F` applied to the Church numeral of the code of `X` reduces to
  `Lambda.true` when `A X` and to `Lambda.false` when `¬ A X`.
- `Lambda.scott_theorem` — **Scott's theorem**: if `A` is convertibility-invariant, has a closed
  member `M` and a closed non-member `N`, then no closed term decides `A`.
- `Lambda.CodeSet A` — the set of codes of the terms in `A`.
- `Lambda.exists_decider_of_computablePred` — a computable characteristic function for
  `CodeSet A` yields a closed lambda decider for `A` (built from a realizer of
  `c ↦ cond (f c) 0 1` and `Lambda.isZero`).
- `Lambda.not_computablePred_codeSet` — **Rice's theorem for the lambda calculus**.
- `Lambda.not_decides_conv_church_zero` and
  `Lambda.not_computablePred_codeSet_conv_church_zero` — the concrete instance "convertible with
  `church 0`", non-trivial because `Lambda.omega` is convertible with no normal form
  (`Lambda.not_conv_omega_church`).

## Proof outline

The diagonal term is `scottTerm F N M = λc. if F c then N else M`, closed by the `IsClosedAt`
calculus.  Kleene's second recursion theorem (`Lambda.exists_code_fixed_point`) produces `X` with
`X ↠ scottTerm F N M ⌜X⌝`, so `X` reduces to `N` when `A X` holds and to `M` when it does not; in
both cases convertibility-invariance contradicts the choice of `M` and `N`.

Notably this needs no lambda-level self-interpreter: the recursion theorem, which the repository
already had, is enough.

## Verification

- `lake build` succeeds (8064 jobs), no errors and no linter warnings.
- No `sorry`/`admit` in `Start/Scott.lean`.
- `#print axioms` on `Lambda.scott_theorem`, `Lambda.not_computablePred_codeSet`,
  `Lambda.not_decides_conv_church_zero` and
  `Lambda.not_computablePred_codeSet_conv_church_zero`: only
  `propext, Classical.choice, Quot.sound`.
