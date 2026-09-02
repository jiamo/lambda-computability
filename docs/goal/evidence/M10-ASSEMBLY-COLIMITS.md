# M10-ASSEMBLY-COLIMITS

**Status:** DONE_STRONG

`Start/AssemblyColimits.lean` — the category of assemblies over an arbitrary partial combinatory
algebra has all finite colimits.

## What is proved

* `Realizability.Assembly.emptyAsm`, `.fromEmpty`, `.isInitialEmptyAsm` — the empty assembly is
  initial; there is nothing to realize and nothing to track.
* `Realizability.Assembly.coprodAsm` — the coproduct is the disjoint union, an element being
  realized by a Church pair whose first component is the boolean tag `k` (left) or `k i` (right)
  and whose second component realizes the element in its summand.
  * `.tagComb`, `.tagComb_app` — the tagging combinator `λx. pair t x`, and the injections
    `.coprodInl`, `.coprodInr` it tracks;
  * `.descBody`, `.coprodDesc` — the copairing.  Its tracker reads the tag and uses it to
    **select** one of the two trackers — ordinary elements of the algebra, so the branch not taken
    cannot diverge — before applying the selected one to the payload;
  * `.coprodCofanIsColimit` — the universal property.
* `Realizability.Assembly.CoeqRel`, `.coeqAsm`, `.coeqProj`, `.coeqDesc`,
  `.coeqCoforkIsColimit` — the coequalizer of two morphisms is the quotient of the codomain by the
  relation they generate, an element being realized by the realizers of its representatives.  The
  projection is tracked by the identity combinator, and a map out of the quotient is tracked by
  whatever tracked the map it descends from.
* The conclusions: `instHasBinaryCoproducts`, `instHasFiniteCoproducts`, `instHasCoequalizers`,
  **`instHasFiniteColimits`** and `instHasPushouts`.

Together with `Start/AssemblyLimits.lean` this makes `Asm(A)` finitely complete and finitely
cocomplete.

## Gates

```
lake build Start.AssemblyColimits   # no error, no warning
python3 scripts/check_closure.py    # OK: 335 modules, all in the import closure and all registered
python3 scripts/goal_state.py validate
```

`#print axioms` on the headline results reports only `propext`, `Classical.choice` and
`Quot.sound`.  The module contains no `sorry` and no `axiom`, and is registered in
`Start/Capstones.lean`.
