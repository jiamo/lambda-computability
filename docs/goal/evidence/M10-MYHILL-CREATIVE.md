# M10-MYHILL-CREATIVE

**Status:** DONE_STRONG

Module `Start/PostCreative.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings, and
`#print axioms` on the results below reports only `propext`, `Classical.choice` and `Quot.sound`.

## The question

`M10-POST-SIMPLE-INCOMPLETE` shows the *thin* side of Post's programme: a simple set is r.e.,
undecidable, and not many-one complete.  This task records the opposite extreme.  A set is
**creative** when it is r.e. and its complement is productive — the halting set is the standard
example — and Myhill's theorem says that creativity is a positive form of completeness: a creative
set is many-one complete, hence many-one equivalent to the halting set.

## The recursion theorem with parameters

**`Lambda.Post.exists_recursion_index`**: for a partial recursive `G : ℕ → ℕ → ℕ →. ℕ` there is a
computable `h` with

    Wset (h x) y ↔ (G (h x) x y).Dom

so the `x`-th named set may refer to its own index.  The proof feeds Kleene's second recursion
theorem (`Nat.Partrec.Code.fixed_point₂`) the function `(c, n) ↦ G ⌜curry c (n)₁⌝ (n)₁ (n)₂`, whose
self-index is primitive recursive in `c` and `n` by `Nat.Partrec.Code.primrec₂_curry`; the
parametrized indices are then `h x = ⌜curry c x⌝`, and `Code.eval_curry` identifies
`Wset (h x)` with the `x`-section.

## Creative sets

`Lambda.Post.Creative C` is `REPred C ∧ Productive (fun x => ¬ C x)`.

* **`Lambda.Post.creative_haltK`** — the halting set is creative (`Lambda.rePred_haltK` and
  `Lambda.Post.productive_compl_haltK`).
* **`Lambda.Post.Productive.not_rePred`** — a productive set is not r.e.: applying the production
  function to an index of the set itself produces an element of the set outside it.
* **`Lambda.Post.Creative.not_computablePred`** — hence no creative set is computable.

## Myhill's theorem

**`Lambda.Post.manyOneReducible_of_productive_compl`**: if the complement of `C` is productive with
production function `p`, then every r.e. `A` satisfies `A ≤₀ C`.

The recursion theorem is applied to `G e x y = if y = p e then (A x)? else ↑` — a partial recursive
function, using `Lambda.Post.computable_decide_eq` for the test and the semi-decision procedure of
`A` for the body.  This gives a computable `h` with

    Wset (h x) = if x ∈ A then {p (h x)} else ∅.

If `x ∈ A` and `p (h x) ∉ C` then `Wset (h x)` is an r.e. subset of the complement of `C`, so
productivity would put `p (h x)` outside `Wset (h x)`, which it is not; hence `p (h x) ∈ C`.  If
`x ∉ A` then `Wset (h x)` is empty, so productivity gives `p (h x) ∉ C` directly.  Thus
`x ↦ p (h x)` is a many-one reduction.

Consequences:

* **`Lambda.Post.Creative.manyOneComplete`** — every creative set is many-one complete;
* **`Lambda.Post.Creative.manyOneEquiv_haltK`** — and therefore many-one equivalent to the halting
  set, using `Lambda.rePred_le_haltK` for the other direction;
* **`Lambda.Post.Creative.manyOneEquiv`** — and so any two creative sets are many-one equivalent;
* **`Lambda.Post.Creative.not_simple`**, **`Lambda.Post.not_creative_simpleSet`** — no creative set
  is simple (simple sets are not many-one complete, `Lambda.Post.Simple.not_manyOneComplete`), so
  Post's set is not creative.

The converse is cheap once productivity is known to travel along many-one reductions
(`Lambda.Post.Productive.of_manyOneReducible`): a many-one complete r.e. set has the halting set
below it, so its complement is productive — **`Lambda.Post.creative_of_manyOneComplete`**.  Together
the two directions give **`Lambda.Post.creative_iff_manyOneComplete`**: an r.e. set is creative
exactly when it is many-one complete.

## Boundary

The Myhill isomorphism theorem (one-one equivalent sets are recursively isomorphic) is not
addressed here, and nothing is claimed about Turing reducibility.

## Gates

```
python3 scripts/goal_state.py validate
python3 scripts/check_closure.py
lake build Start.PostCreative
lake build
```
