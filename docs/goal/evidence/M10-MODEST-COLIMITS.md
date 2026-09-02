# M10-MODEST-COLIMITS

**Status:** DONE_STRONG

`Start/ModestColimits.lean` — the modest assemblies, and hence the partial equivalence relations,
are finitely complete and finitely cocomplete.

## What is proved

* `Realizability.PCA.k_ne_kI` — in a partial combinatory algebra with more than one element the
  two boolean combinators differ: from `k = k i` one gets `a = k a b = (k i) a b = b` for all `a`
  and `b`.
* Stability of modesty:
  * `Realizability.Assembly.Modest.sub` — a sub-assembly of a modest assembly is modest, hence
    `Modest.eq` for equalizers;
  * `Realizability.Assembly.modest_emptyAsm` — the initial assembly is modest, vacuously;
  * `Realizability.Assembly.Modest.coeq` — a coequalizer of a modest assembly is modest: a
    realizer of two classes realizes a representative of each, and modesty of the ambient assembly
    identifies those representatives;
  * `Realizability.Assembly.Modest.coprod` — **a coproduct of modest assemblies is modest** over an
    algebra with more than one element: the tag of a realizer says which summand its element lies
    in (this is where `k ≠ k i` is used) and the payload determines the element there.
* The (co)limits of the subcategory, built with the inclusion being full: `Modest.eqForkModest`,
  `.eqForkModestIsLimit`, `.emptyModest`, `.isInitialEmptyModest`, `.coeqCoforkModest`,
  `.coeqCoforkModestIsColimit`, `.coprodCofanModest`, `.coprodCofanModestIsColimit`, and the
  instances `Modest.instHasFiniteLimits` and **`Modest.instHasFiniteColimits`**.
* Transported along the equivalence of `Start/ModestEquiv.lean`:
  `Realizability.PER.instHasFiniteLimits` and `Realizability.PER.instHasFiniteColimits`.

## Scope

Finite colimits of the modest assemblies are claimed under `[Nontrivial A]`.  Over a one-element
algebra the tags carry no information; the statement is not claimed there.

## Gates

```
lake build Start.ModestColimits     # no error, no warning
python3 scripts/check_closure.py    # OK: 335 modules, all in the import closure and all registered
python3 scripts/goal_state.py validate
```

`#print axioms` on the headline results reports only `propext`, `Classical.choice` and
`Quot.sound`.  The module contains no `sorry` and no `axiom`, and is registered in
`Start/Capstones.lean`.
