# M10-MYHILL-ISO

**Status:** DONE_STRONG

Module `Start/MyhillIso.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

`Start/CreativeCodeSets.lean` places the lambda-calculus halting set, convergence to a numeral and
convertibility with a Church numeral at the same *many-one* degree as Kleene's `K`, and the
evidence note for that task records that recursive isomorphism was not claimed.  This task closes
that boundary in general: one-one equivalence and recursive isomorphism coincide.

## What is proved

* `Lambda.Myhill.RecIso` — two sets of numbers are recursively isomorphic when some computable
  bijection of `ℕ` carries one onto the other.
* The chase (`Lambda.Myhill.escRun`, `Lambda.Myhill.esc`, `Lambda.Myhill.esc_spec`,
  `Lambda.Myhill.exists_escape`): from a start point, follow `x, G (F x), G (F (G (F x))), …` until
  `F` of the current point leaves a finite list.  Because the intermediate points are distinct
  elements of a finite set, the search terminates within one more step than the list is long, and
  the value it returns is outside the list.
* The stages (`Lambda.Myhill.PMap`, `Lambda.Myhill.Good`, `Lambda.Myhill.extDom`,
  `Lambda.Myhill.extRan`, `Lambda.Myhill.stage`): a stage is a finite partial map, injective in
  both directions, all of whose pairs `(x, y)` satisfy `A x ↔ B y`.  `Lambda.Myhill.good_extDom`
  and `Lambda.Myhill.good_extRan` prove that both extension steps preserve this invariant, and
  `Lambda.Myhill.mem_dom_stage` / `Lambda.Myhill.mem_ran_stage` prove that the alternation puts
  every number into the domain and into the range.
* `Lambda.Myhill.isoFun`, with `Lambda.Myhill.isoFun_injective`,
  `Lambda.Myhill.isoFun_surjective` and `Lambda.Myhill.isoFun_spec` — the union of the stages is a
  bijection of `ℕ` carrying `A` onto `B`.
* `Lambda.Myhill.computable_stage` and `Lambda.Myhill.computable_isoFun` — the construction is
  computable, using the auxiliary `Lambda.Myhill.computable_iterate` (a computable state iterated a
  computable number of times) and primitive recursiveness of the finite-map operations
  (`Lambda.Myhill.primrec_look`, `Lambda.Myhill.primrec_colook`, `Lambda.Myhill.primrec_dom`,
  `Lambda.Myhill.primrec_ran`, `Lambda.Myhill.primrec_swapMap`).
* `Lambda.Myhill.recIso_of_oneOneEquiv` — **Myhill's isomorphism theorem**.
* `Lambda.Myhill.exists_computable_inverse` — the inverse of a computable bijection of `ℕ` is
  computable (search for the unique preimage), whence the converse
  `Lambda.Myhill.oneOneEquiv_of_recIso` and the characterisation
  `Lambda.Myhill.recIso_iff_oneOneEquiv : RecIso A B ↔ OneOneEquiv A B`.

## Boundary

None.  Both directions are proved for arbitrary predicates on `ℕ`; one-one equivalence is
Mathlib's `OneOneEquiv`, so the statement composes with the reductions already in the library.

## Gates

* `lake build` — the whole library, no error and no warning.
* `python3 scripts/check_closure.py`.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: `Lambda.Myhill.recIso_of_oneOneEquiv`, `Lambda.Myhill.oneOneEquiv_of_recIso` and
  `Lambda.Myhill.recIso_iff_oneOneEquiv` depend only on `propext`, `Classical.choice` and
  `Quot.sound`.
