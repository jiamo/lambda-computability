# M10-ASSEMBLY-SUBOBJECT

**Status:** DONE_STRONG

Module `Start/AssemblySubobject.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

`Start/AssemblyLimits.lean` carves the sub-assembly `subAsm X P` out of an assembly `X`: the
elements satisfying a predicate `P`, with exactly the realizers they had in `X`.  What remained is
to show that these sub-assemblies are *classified*, i.e. that they are the pullbacks of a single
universal mono.

## What is proved

* `Realizability.Assembly.propAsm` — the assembly of propositions: the carrier is `Prop` and every
  element of the algebra realizes every proposition, so the truth of a proposition carries no
  computational content.
* `Realizability.Assembly.tracked_toPropAsm` — every function into `propAsm` is tracked, by the
  identity combinator.
* `Realizability.Assembly.charMap`, `.trueMap` — the characteristic map of a predicate, and the
  global element of `propAsm` picking out `True`.
* `Realizability.Assembly.homPropEquiv` — morphisms `X ⟶ propAsm A` are exactly the predicates on
  the carrier of `X`.
* `Realizability.Assembly.pointMap` — the global element of an assembly given by an element of its
  carrier, tracked by `k b` for a realizer `b`.
* `Realizability.Assembly.charCone`, `.charConeIsLimit`, `.isPullback_subAsm` — **the classifying
  square is a pullback**: `subAsm X P` is the pullback of `true : 1 ⟶ Ω` along the characteristic
  map of `P`.
* `Realizability.Assembly.charMap_uniq`, `.exists_unique_charMap` — the characteristic map is the
  unique map making that square a pullback.

## Boundary

`propAsm` classifies the *sub-assemblies* of an assembly, equivalently the regular subobjects —
those whose realizers are inherited from the ambient assembly.  It does not classify every
monomorphism: a mono may realize its elements with strictly fewer realizers than the codomain
does, and `Asm(A)` is not a topos.  The quasitopos structure (strong subobjects, the realizability
topos itself) is not formalized.

## Gates

* `lake build Start.AssemblySubobject` — no error and no warning.
* `python3 scripts/check_closure.py`.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: `Realizability.Assembly.isPullback_subAsm` and
  `Realizability.Assembly.exists_unique_charMap` depend only on `propext`, `Classical.choice` and
  `Quot.sound`.
