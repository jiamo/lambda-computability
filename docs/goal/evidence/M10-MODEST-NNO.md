# M10-MODEST-NNO

**Status:** DONE_STRONG

`Start/ModestNNO.lean` — the assembly of natural numbers is modest, so the modest assemblies (and
hence the partial equivalence relations) have a natural numbers object.

## What is proved

* `Realizability.PCA.subsingleton_of_k_app_k` — if `k k = k` in a partial combinatory algebra then
  the algebra has at most one element.
* `Realizability.PCA.k_ne_pairEl_k` — over an algebra with more than one element `k` is never a
  Church pair whose first component is `k`.
* `Realizability.nestK` — the tower of nested pairs `k`, `pair k k`, `pair k (pair k k)`, …, with
  `Realizability.nestK_mem_iterp` (it is the value of the `n`-fold iterate of the tagging
  combinator `λx. pair k x` on `k`) and `Realizability.nestK_injective` (towers of different
  heights differ, by injectivity of Church pairing and `k_ne_pairEl_k`).
* `Realizability.Assembly.modest_natAsm` — **the assembly of natural numbers is modest** over an
  algebra with more than one element: a realizer of `n` applied to the tagging combinator and the
  base point computes `nestK n`, and those values are pairwise distinct.
* `Realizability.Modest.natModest`, `natZeroModest`, `natSuccModest` — the natural numbers as an
  object of `ModestCat A`, with its zero and successor.
* `Realizability.Modest.isNNO_natModest` — **the modest assemblies have a natural numbers object**,
  the same one as `Asm(A)`; the inclusion is full, so recursion in the subcategory is recursion in
  `Asm(A)`.

## Scope

Everything is claimed under `[Nontrivial A]`.  Over a one-element algebra every element realizes
every natural number, so `natAsm` is not modest there and the statement is not claimed.

## Gates

```
lake build Start.ModestNNO          # no error, no warning
python3 scripts/check_closure.py
python3 scripts/goal_state.py validate
```

`#print axioms` on the headline results reports only `propext`, `Classical.choice` and
`Quot.sound`.  The module contains no `sorry` and no `axiom`, and is registered in
`Start/Capstones.lean`.
