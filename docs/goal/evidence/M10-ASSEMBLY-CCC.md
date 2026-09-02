# M10-ASSEMBLY-CCC

**Status:** DONE_STRONG

Modules `Start/Assembly.lean`, `Start/AssemblyCcc.lean` and `Start/Modest.lean`, all imported by
`Start.lean`.  They build without `sorry`; `#print axioms` on the headline declarations reports
only `propext`, `Classical.choice`, `Quot.sound`.

Fix a partial combinatory algebra `A`.

## The category — `Start/Assembly.lean`

`Realizability.Assembly A` is a carrier together with a realizability relation `realizes : A →
carrier → Prop` such that every element has a realizer (`exists_realizer`).  `RealizesFun X Y r f`
says `r` tracks `f`, `Tracked X Y f` that some realizer does; `tracked_id` and `Tracked.comp` make
tracking closed under identity and composition, so `AsmHom` (a function together with a proof that
it is tracked) gives `instCategoryStruct` and `instCategory`, with `hom_ext` for extensionality.

* `unitAsm`, `toUnit`, `isTerminalUnitAsm` — the one-point assembly is terminal, giving
  `HasTerminal`;
* `prodAsm` (realizers are `pairEl`-pairs), `prodFst`, `prodSnd`, `prodLift` with its `toFun` simp
  lemmas, `prodFan`, `prodFanIsLimit` — binary products, giving `HasBinaryProducts`.

## Cartesian closure — `Start/AssemblyCcc.lean`

`terminalCone` and `prodCone` package the above as chosen finite products, whence
`Realizability.Assembly.cartesianMonoidal` via `CartesianMonoidalCategory.ofChosenFiniteProducts`,
with `tensorObj_eq`, `fst_eq`, `snd_eq`, `whiskerLeft_toFun` computing the monoidal data back into
elementary terms.

`expAsm X Y` has as carrier the tracked maps `X ⟶ Y` and as realizers the elements that track them.
`postCompBody`/`postCompBody_eval` realize post-composition, giving `expMap` and the functor
`expFunctor X : Assembly A ⥤ Assembly A`.  `curryBody`/`curryBody_eval` and
`uncurryBody`/`uncurryBody_eval` are explicit combinators realizing currying and uncurrying;
`curry_realizesFun`, `curryAsm`, `uncurryAsm` build the morphisms and `curryEquiv` proves them
mutually inverse.  Naturality then yields **`instClosed`** and
**`Realizability.Assembly.monoidalClosed`**: in this Mathlib version, "cartesian closed" is
`CartesianMonoidalCategory` together with `MonoidalClosed`, and both are provided.

## Modest assemblies — `Start/Modest.lean`

`Modest X` says distinct elements have disjoint sets of realizers.  `modest_unitAsm`,
`Modest.prod` (using injectivity of pairing, `pairEl_inj`) and `Modest.exp` show the cartesian
closed structure restricts to modest assemblies; `Assembly.toPER` and `dom_toPER` turn a modest
assembly into a partial equivalence relation.

## Boundary

None for this task.  A packaged `CartesianClosed` instance on a *category of PERs* in its own right
is not part of this entry; what is proved here is closure of modesty under the structure of
`Asm(A)`.
