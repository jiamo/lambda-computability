# M8-KU-OPTIMAL

**Status:** DONE_STRONG

Module `Start/KUOptimal.lean`, imported by `Start.lean`.  It builds without `sorry` and without
linter warnings, and its results depend only on `propext`, `Classical.choice`, `Quot.sound`.

The file compares the two prefix complexities of this development: `KC.KU`, the complexity of the
Kraft–Chaitin universal prefix machine `KC.U` (`Start/KCMachine.lean`), and `Lambda.kolmP`, the
complexity of the lambda prefix machine, whose programs are the self-delimiting bit codes
`Lambda.bits t` of closed lambda terms (`Start/ChaitinOmega.lean`).

## The request stream (first exit criterion)

* `KC.lamHit e m i` — the code `e` is a valid code of a closed term whose leftmost run
  (`Lambda.nstep_code`, `Start/LeftmostRun.lean`) reaches `Lambda.church_code m` after `i` steps.
* `KC.lamFirst` keeps only the first such `i`, which is what makes the stream emit at most one
  request per term; `KC.nstep_code_church` and `KC.lamHit_mono` say the run stays at a Church
  numeral once it gets there, and `KC.lamFirst_unique` derives the uniqueness.
* `KC.lamReq` reads its index as a triple `(e, m, i)` and issues the request
  `(Lambda.bitsLen_code e, m)`.  `KC.computable_lamReq` proves it computable, out of
  `Lambda.is_valid_code_primrec`, `Lambda.freeMax_code_primrec`,
  `Lambda.nstep_code_iterate_primrec`, `Lambda.church_code_primrec` and
  `Lambda.bitsLen_code_primrec`.
* `KC.exists_lamReq_of_isProgramFor` — every closed term `t` reducing to `church m` really does
  produce the request `(|bits t|, m)`.

## The weight bound (second exit criterion)

* `KC.sum_wtOpt_lamReq_le` — for every finite set of indices the accumulated weight is at most
  one.  Indices that emit are mapped injectively to the terms they name (`Lambda.decodeD`,
  `Lambda.encode_decodeD`), and the resulting sum is bounded by Kraft's inequality
  `Kraft.sum_wt_le_one` for the prefix free coding `Lambda.bits_prefixFreeCoding`.

## Optimality (third exit criterion)

* `KC.exists_const_KU_le_kolmP : ∃ c, ∀ s, KU s ≤ Lambda.kolmP s + c`, by feeding the stream to
  the Kraft–Chaitin theorem `KC.exists_const_KU_le` and instantiating at a shortest lambda
  program (`Lambda.exists_program_of_kolmP`).
* `KC.exists_const_le_kolmP_prefix_of_exists_const_le_KU` transports `KU`-incompressibility of
  the prefixes of a sequence to `Lambda.kolmP`.

## Boundary

Only this direction is proved, and only this direction is expected: a `U`-program is an arbitrary
bit string, whereas a lambda program spends two bits per node of its syntax tree, so `kolmP` can
exceed `KU` by more than an additive constant.  In particular this does **not** transport the
Levin–Schnorr equivalence `KC.mlRandom_iff_exists_const_le_KU` (M7) from `KU` to `kolmP`.
