# M10-POST-SIMPLE-INCOMPLETE

**Status:** DONE_STRONG

Modules `Start/PostSimple.lean` and `Start/PostIncomplete.lean`, both imported by `Start.lean`
and registered in `Start/Capstones.lean`.  They build without `sorry` and without linter
warnings, and `#print axioms` on the results below reports only `propext`, `Classical.choice`
and `Quot.sound`.

## The question

`Start/KleeneK.lean` proves that the halting set `K` is one-one complete: every r.e. predicate
reduces to it, injectively.  Post asked whether *every* r.e. set that is not computable is
complete in this sense.  The answer is no, and Post's own way of seeing it is to build a set that
is *too thin* to be complete: a **simple** set, i.e. an r.e. set whose complement is infinite but
contains no infinite r.e. set.

## The construction — `Start/PostSimple.lean`

`Lambda.Post.Wset e` is the `e`-th r.e. set, the domain of the `e`-th partial recursive function
of mathlib's numbering `Nat.Partrec.Code`; `Lambda.Post.exists_index` shows that every r.e.
predicate occurs in the numbering.

The search is made effective by a primitive recursive stage predicate:
`Lambda.Post.found e s x` says that the `e`-th machine accepts `x` within `s` steps and that
`2 * e < x`; `Lambda.Post.test` runs it on a single number coding the pair `(s, x)`;
`Lambda.Post.noneBelow` and `Lambda.Post.hit` select the *first* such pair.  Post's set

    Lambda.Post.simpleSet x  ↔  ∃ e k, hit e k ∧ (Nat.unpair k).2 = x

is therefore the set of first witnesses.  `Lambda.Post.primrec_found`,
`Lambda.Post.primrec_test`, `Lambda.Post.primrec_noneBelow` and `Lambda.Post.primrec_hit` are the
effectiveness of the search — `Nat.Partrec.Code.primrec_evaln` is what makes the bounded
evaluation primitive recursive — and hence **`Lambda.Post.rePred_simpleSet`**: the set is r.e.

Three properties are then proved.

* **`Lambda.Post.card_filter_simpleSet_le`** — at most `n` of the numbers below `2 * n` belong to
  the set.  Each index `e` contributes at most one number (`Lambda.Post.hit_unique`: the first
  witness is unique), and only the indices `e < n` can contribute below `2 * n`
  (`Lambda.Post.index_lt_of_mem`, since a witness for `e` exceeds `2 * e`).  Hence
  **`Lambda.Post.simpleSet_compl_infinite`**: the complement is infinite.
* **`Lambda.Post.simpleSet_meets`**, **`Lambda.Post.simpleSet_meets_rePred`** — the set meets
  every infinite r.e. set: an infinite `W e` has an element above `2 * e`, so the search for `e`
  succeeds and its first witness lies in `W e` and in the set.  The complement is *immune*.
* **`Lambda.Post.not_rePred_compl_simpleSet`**, **`Lambda.Post.not_computablePred_simpleSet`** —
  the complement is not r.e. (it is infinite, so if it were r.e. it would meet the set), hence the
  set is not computable.  **`Lambda.Post.simpleSet_infinite`** — the set is infinite as well,
  since otherwise the infinite computable set of numbers above a bound of it would avoid it.

The three properties are packaged abstractly: `Lambda.Post.Immune P` says that `P` is infinite and
every infinite r.e. set has an element outside `P`, and `Lambda.Post.Simple S` says that `S` is
r.e. with immune complement.  **`Lambda.Post.simple_simpleSet`** is the statement that Post's set
is simple, and **`Lambda.Post.Simple.not_computablePred`** proves that no simple set is
computable.

## Incompleteness — `Start/PostIncomplete.lean`

`Lambda.Post.Productive P` is the usual notion: a computable function which, from any index of an
r.e. subset of `P`, produces an element of `P` outside that subset.

* `Lambda.Post.exists_index_fun` — the s-m-n theorem in the form used here (via
  `Nat.Partrec.Code.curry`): a partial recursive function of two arguments has a computable
  indexing of its sections.  Its three instances are an index for the empty set
  (`Lambda.Post.exists_empty_index`), an index for `W e ∪ {a}` (`Lambda.Post.exists_adjoin`) and
  an index for the preimage of an r.e. set under a computable function
  (`Lambda.Post.exists_preimage_index`).
* **`Lambda.Post.productive_compl_haltK`** — the complement of the halting set is productive, with
  the identity as production function.
* **`Lambda.Post.Productive.of_manyOneReducible`** — productivity of a complement travels along a
  many-one reduction: the preimage index turns an r.e. subset of the complement of the target into
  one of the complement of the source.
* **`Lambda.Post.exists_infinite_re_subset`** — *a productive set contains an infinite r.e.
  subset*.  Iterate: start from the empty set, apply the production function to the index of the
  set built so far, and adjoin the element produced.  The elements are pairwise distinct because
  each is outside the set of its predecessors, the sequence is computable, so its range is an
  infinite r.e. subset of the productive set.
* **`Lambda.Post.Simple.not_manyOneReducible_haltK`** — hence `K` does not many-one reduce to any
  simple set: otherwise the complement of that set would be productive and would contain an
  infinite r.e. set, which the set meets by immunity.  So
  **`Lambda.Post.Simple.not_manyOneComplete`**, and specializing to Post's set along
  `Lambda.Post.simple_simpleSet` gives `Lambda.Post.not_manyOneReducible_haltK_simpleSet`,
  **`Lambda.Post.simpleSet_not_manyOneComplete`** and

      Lambda.Post.exists_rePred_not_computable_not_manyOneComplete :
        ∃ p : ℕ → Prop, REPred p ∧ ¬ ComputablePred p ∧ ¬ ∀ q, REPred q → q ≤₀ p

  — **Post's problem for many-one reducibility**, solved.

## Boundary

Post's problem for *Turing* reducibility is not addressed: nothing here says that a simple set is
Turing-incomplete (it need not be), and the Friedberg–Muchnik priority construction is not
formalized.

## Gates

```
python3 scripts/goal_state.py validate
python3 scripts/check_closure.py
lake build Start.PostSimple Start.PostIncomplete
lake build
```
