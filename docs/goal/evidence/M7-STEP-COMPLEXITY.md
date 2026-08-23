# M7-STEP-COMPLEXITY

**Status:** DONE_STRONG

Module `Start/StepComplexity.lean`, imported by `Start.lean`.  Mathlib's
`Nat.Partrec.Code.evaln k c x` runs the code `c` on the input `x` with `k` units of fuel; the
least amount of fuel that suffices is a Blum complexity measure, and this module develops it.

## Definitions

* `Complexity.steps c x` — the least `k` such that `evaln k c x` is defined.
* `Complexity.StepsLe c x m` — "`c` converges on `x` within `m` units of fuel".
* `Complexity.WithinFuel c t f` — "the code `c` computes the total function `f`, on every input
  `x` within `t x` units of fuel".
* `Complexity.diag t` — the diagonal function for the bound `t`.

## Theorems

* `Complexity.steps_dom_iff` — **the first Blum axiom**: the measure is defined exactly on the
  domain of the function.
* `Complexity.primrec_stepsLe`, `Complexity.decidable_stepsLe` — **the second Blum axiom**: the
  bounded-convergence predicate is primitive recursive, in particular decidable.
* `Complexity.stepsLe_mono` — more fuel never hurts.
* `Complexity.computable_diag`, `Complexity.exists_computable_not_withinFuel` — **for every
  computable fuel bound `t` there is a total computable function that no code computes within
  `t`**.  So no computable bound captures all computable functions: the complexity classes given
  by computable bounds are a proper hierarchy of subclasses of the computable functions.
* `Complexity.exists_computable_steps_gt` — the same statement phrased with the measure: any
  code computing that function exceeds the bound on some input.

Gates: `lake build` succeeds; no `sorry`; `#print axioms` reports only
`propext, Classical.choice, Quot.sound`.

## Boundary

This is a *fuel*-counting measure, not the step count of a concrete machine, and `evaln`'s
convention (convergence requires `x < k`) makes the fuel bound at least the size of the input.
Nothing here develops `P`, `NP`, reductions or completeness: for those one needs a cost model
over a machine with a robust notion of composition, and mathlib's
`Turing.TM2ComputableInPolyTime` does not yet provide the closure properties that a
Cook–Levin-style argument requires.  That gap is recorded honestly rather than papered over: a
fuel count is not a faithful time-complexity model.
