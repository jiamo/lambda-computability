# M6-KOLMOGOROV-INVARIANCE

**Status:** DONE_STRONG

In `Start/Kolmogorov.lean` and the new module `Start/KolmogorovBinary.lean`.

Interpreter invariance (additive, lambda-internal):

* `Lambda.kolmWith U s` — complexity relative to a closed interpreter term `U`: the least size of a
  closed `p` with `U p ↠ church s`.
* `Lambda.kolm_le_kolmWith` — `kolm s ≤ kolmWith U s + size U + 1`: changing the interpreter costs
  at most an additive constant.
* `Lambda.kolmWith_I_le_kolm`, `Lambda.kolm_le_kolmWith_I` — the identity interpreter returns
  `kolm` itself up to the constant `3`.

Cross-model invariance:

* `Lambda.exists_const_kolm_le_of_partrec` — for a partial recursive description system `V`,
  `kolm s ≤ 3 * p + c` whenever `V p = s`.  The factor `3` is the size of the *unary* Church
  numeral for `p` (`size (church p) = 3 * p + 3`).
* `Lambda.exists_const_kolm_le_of_tm2` — the same for Turing machines, through
  `TM2Partrec.tm2Computable_iff_partrec`; this is the sense in which the measure is model
  independent.

Logarithmic refinement (`Start/KolmogorovBinary.lean`):

* `Lambda.dbl`, `Lambda.binNum` — compact numerals: a closed term of size `O(log n)` reducing to
  `church n`, built by reading the binary expansion with the doubling term `mult (church 2)` and
  `succ`; `Lambda.binNum_closed`, `Lambda.binNum_reduces`, `Lambda.size_binNum_le`
  (`size (binNum n) ≤ binCost * k + 3` whenever `n < 2 ^ k`).
* `Lambda.exists_const_kolm_le_size` — every `n` has a program of size `O(bit length of n)`.
* `Lambda.exists_const_kolm_le_size_of_partrec`, `Lambda.exists_const_kolm_le_size_of_tm2` — the
  invariance theorem with description length measured in *bits*: `kolm s ≤ c * (Nat.size p + 1)`.

Honest boundary: additivity holds for the node measure (`Lambda.kolm_le_kolmWith`); on *bit*
lengths the bounds are up to a multiplicative constant, because each bit of a compact numeral costs
a constant number of syntax nodes.  A bit-counting measure, and a prefix-free one as Chaitin's `Ω`
needs, are not built here; see `M6-KOLMOGOROV-OMEGA`.

Gates: `lake build` succeeds; no `sorry`; no linter warnings; `#print axioms` on the headline
results reports only `propext, Classical.choice, Quot.sound`.
