# M10-RICE-CREATIVE

**Status:** DONE_STRONG

Module `Start/RiceCreative.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

`Start/Scott.lean` shows that a non-trivial convertibility-invariant set of lambda terms has a
non-computable code set, and `Start/ScottCurry.lean` sharpens undecidability to recursive
inseparability.  Neither measures *how* undecidable such a code set is.  This task supplies the
measurement for the invariant sets that contain no unsolvable term: their code sets are many-one
above Kleene's diagonal halting set.

## What is proved

* `Lambda.haltTest` — the total, computable, step-indexed diagonal halting test:
  `haltTest (pair n k) = 0` exactly when the `n`-th code halts on the input `n` within `k` steps
  (`Lambda.haltTest_computable`, `Lambda.haltTest_eq_zero_iff`), with
  `Lambda.haltK_iff_exists_haltTest : HaltK n ↔ ∃ k, haltTest (pair n k) = 0`.
* `Lambda.searchTerm n` — the lambda term that searches for such a stage, obtained from the
  parameterised minimisation `Lambda.muParam` of `Start/PartialCapstone.lean` applied to a closed
  realizer of `haltTest`.  It reduces to a Church numeral when the `n`-th machine halts
  (`Lambda.searchTerm_reduces_church`) and has no head normal form otherwise
  (`Lambda.searchTerm_not_hasHnf`, through the divergence half of minimisation).
* `Lambda.riceTerm M n = (searchTerm n) I M` — the term of the reduction:
  `Lambda.riceTerm_reduces` (it reduces to `M` when the machine halts) and
  `Lambda.riceTerm_not_solvable` (it is unsolvable otherwise, because a head normal form of an
  application gives one of its function part).  Its code depends primitively recursively on `n`
  (`Lambda.riceCode_eq`, `Lambda.riceCode_primrec`).
* `Lambda.manyOneReducible_haltK_codeSet` — **Rice's theorem, effective form**: if `A` is
  invariant under convertibility, contains a term `M`, and contains no unsolvable term, then
  `HaltK ≤₀ CodeSet A`.
* `Lambda.not_rePred_compl_codeSet` — the complement of such a code set is not recursively
  enumerable.
* `Lambda.creative_codeSet` — such a code set is creative, in the sense of
  `Start/PostCreative.lean`, as soon as it is recursively enumerable (through
  `Lambda.Post.creative_of_manyOneComplete` and the completeness of `HaltK`).
* Instances: `Lambda.manyOneReducible_haltK_codeSet_solvable` and
  `Lambda.not_rePred_compl_codeSet_solvable` (solvability of a lambda term is many-one hard for
  the halting problem, and the codes of the unsolvable terms are not r.e.), and
  `Lambda.manyOneReducible_haltK_codeSet_conv_church`,
  `Lambda.not_rePred_compl_codeSet_conv_church` for convertibility with a Church numeral.

## The hypothesis on `A`

"Contains no unsolvable term" is what makes the negative half of the reduction work: when the
search diverges, the term produced is unsolvable, and that is the only way the construction can
place it outside `A`.  It is satisfied by solvability itself and by convertibility with any
solvable term, in particular with any Church numeral.

## Gates

* `lake build` — the whole library, no error and no warning.
* `python3 scripts/check_closure.py` — every module in the import closure of `Start.lean` and
  registered.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: `Lambda.manyOneReducible_haltK_codeSet`, `Lambda.not_rePred_compl_codeSet`,
  `Lambda.creative_codeSet`, `Lambda.manyOneReducible_haltK_codeSet_solvable` and
  `Lambda.not_rePred_compl_codeSet_conv_church` depend only on `propext`, `Classical.choice` and
  `Quot.sound`.
