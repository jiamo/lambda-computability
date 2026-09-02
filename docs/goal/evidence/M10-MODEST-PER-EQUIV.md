# M10-MODEST-PER-EQUIV

**Status:** DONE_STRONG

Module `Start/ModestEquiv.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings; `#print axioms` on
`Realizability.perEquivModest`, `Realizability.PER.arrowIso` and `Realizability.Assembly.toPERIso`
reports only `propext`, `Classical.choice`, `Quot.sound`.

## What was already there

`Start/PER.lean` defines a partial equivalence relation `R` over a partial combinatory algebra
`A`, its domain, its quotient `R.Quot`, the arrow PER `R ⇒ S`, and the assembly `R.toAsm` it
presents, which `Realizability.PER.modest_toAsm` proves modest.  `Start/Modest.lean` goes back at
the level of objects (`Realizability.Assembly.toPER`) and shows that modesty is stable under the
terminal object, binary products and exponentials of `Asm(A)`.  The dictionary was therefore only
established on objects.

## What this task adds

**Morphisms of PERs.**  `Realizability.PER.Tracked R S f` says that one element of the algebra
computes `f : R.Quot → S.Quot` on representatives: applied to any `a` in the domain of `R` it
converges to a representative of `f (R.cls a)`.  `Realizability.PER.tracked_iff` proves this is
literally the same condition as being tracked as a map of the presented assemblies.
`Realizability.PER.Hom` bundles a function with a tracking element and
`Realizability.PER.instCategory` makes PERs a category — the identity is tracked by `i` and
composites by the composition combinator, both imported through `tracked_iff` from the assembly
side.

**The comparison functor.**  `Realizability.modestProperty` is modesty as an `ObjectProperty` of
`Assembly.{u,u} A` and `Realizability.ModestCat A` is the resulting full subcategory.
`Realizability.PER.toModest` sends `R` to `⟨R.toAsm, R.modest_toAsm⟩` and a tracked map to itself;
`Realizability.PER.toModestFullyFaithful` is fully faithfulness, and it is again exactly
`tracked_iff`.

**Essential surjectivity.**  `Realizability.Assembly.toPERIso` is the isomorphism
`(toPER hX).toAsm ≅ X` for a modest assembly `X`.  Its forward map sends a class to the element of
`X` that any representative realizes — well defined precisely because `X` is modest — and its
inverse sends `x` to the class of a chosen realizer of `x`.  The two objects have *the same*
realizers, so both directions are tracked by the identity combinator.

**The equivalence.**  `Realizability.perEquivModest : PER A ≌ ModestCat A`.

**Exponentials.**  `Realizability.PER.arrowIso : (arrow R S).toAsm ≅ expAsm R.toAsm S.toAsm`.  A
class of the arrow PER is the function computed by any of its representatives
(`PER.arrowFun`, `PER.realizesFun_arrowFun`), and conversely a tracked function is the class of any
of its trackers, because two elements tracking the same function are related by the arrow PER
(`PER.rel_of_realizesFun`).  Both directions are again tracked by the identity combinator.

## Gates

- `lake build Start.ModestEquiv` — success, no warnings.
- `lake build` — the whole library still builds.
- `python3 scripts/check_closure.py` — every module in the import closure and registered.
- `python3 scripts/goal_state.py validate` — board validates.
