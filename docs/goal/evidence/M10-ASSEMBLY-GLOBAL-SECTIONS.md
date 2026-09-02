# M10-ASSEMBLY-GLOBAL-SECTIONS

**Status:** DONE_STRONG

Module `Start/AssemblyGlobalSections.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

The category of assemblies sits over the category of sets: an assembly has an underlying set, and
a set can be made into an assembly with no computational content.  What remained is to prove that
these two constructions are adjoint, and to identify the underlying set intrinsically.

## What is proved

* `Realizability.Assembly.nablaAsm`, `.tracked_toNabla`, `.toNabla` — the indiscrete assembly on a
  set, in which every element of the algebra realizes every element, and the fact that every
  function into it is tracked.
* `Realizability.Assembly.propAsm_eq_nablaAsm` — the classifier of `Start/AssemblySubobject.lean`
  is the indiscrete assembly on `Prop`.
* `Realizability.Assembly.nablaFunctor`, `.gammaFunctor` — the indiscrete assembly and the
  global-sections (carrier) functors.
* `Realizability.Assembly.homNablaEquiv`, `.gammaNablaAdj` — **the adjunction** `Γ ⊣ ∇`.
* `Realizability.Assembly.nablaFullyFaithful` — `∇` is fully faithful, with the resulting `Full`
  and `Faithful` instances.
* `Realizability.Assembly.globalSectionsEquiv` — the carrier of an assembly is its set of global
  sections: morphisms out of the terminal assembly correspond to elements of the carrier, using
  that every element is tracked by a constant combinator (`Realizability.Assembly.pointMap`).

## Boundary

Only the adjunction `Γ ⊣ ∇` is constructed.  The further left adjoint (the discrete assembly, in
which an element is realized only by the codes attached to it) and the resulting string of
adjoints, as well as any statement about geometric morphisms or the realizability topos, are not
formalized.

## Gates

* `lake build Start.AssemblyGlobalSections` — no error and no warning.
* `python3 scripts/check_closure.py`.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: `Realizability.Assembly.gammaNablaAdj`,
  `Realizability.Assembly.nablaFullyFaithful` and
  `Realizability.Assembly.globalSectionsEquiv` depend only on `propext`, `Classical.choice` and
  `Quot.sound`.
