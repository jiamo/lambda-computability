# M10-ASM-PROJECTIVE

**Status:** DONE_STRONG

Module `Start/AssemblyProjective.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings, and its results
depend only on `propext`, `Classical.choice` and `Quot.sound`.

## What this task adds

`Start/AssemblyRegular.lean` identifies the strong epimorphisms of `Asm(A)` as the morphisms that
*lift realizers*.  This module identifies the objects projective for those covers.

- `Realizability.Assembly.partAsm`, `.Partitioned`, `.partitioned_partAsm` — the assembly on a set
  with one chosen realizer per element, and the property of having exactly one realizer per point.
- `Realizability.Assembly.RegularProjective` — projectivity with respect to the morphisms that
  lift realizers, i.e. with respect to the strong (equivalently regular) epimorphisms.
- **`Realizability.Assembly.Partitioned.regularProjective`** — a partitioned assembly is regular
  projective: if `t` tracks the map and `l` is a lifting combinator of the cover, then `comp l t`
  tracks the lift, whose value at a point is chosen among the preimages the combinator lands in.
  This is the constructive content of the axiom of choice in realizability.
- `Realizability.Assembly.coverAsm`, `.coverHom`, `.partitioned_coverAsm`,
  `.liftsRealizers_coverHom` — the canonical cover of an assembly by the pairs `(a, x)` with `a` a
  realizer of `x`, realized by `a` alone; the covering map forgets the realizer and lifts
  realizers by the identity combinator.
- **`Realizability.Assembly.exists_partitioned_cover`** — `Asm(A)` has enough regular projectives.
- **`Realizability.Assembly.exists_partitioned_iso_of_regularProjective`**,
  **`.regularProjective_iff`** — conversely a regular projective splits its canonical cover, and
  transporting the realizer picked out by the splitting makes it isomorphic to a partitioned
  assembly; so the regular projectives are exactly the assemblies isomorphic to partitioned ones.
  (`Realizability.Assembly.RegularProjective.of_iso` is the transport used for the easy
  direction.)
- `Realizability.Assembly.Partitioned.prod`, `.prodMapIso`, `.RegularProjective.prod` — the
  Church pair of the two chosen realizers is the chosen realizer of a pair, so partitioned
  assemblies, and hence the regular projectives, are closed under binary products.

Over Kleene's first algebra this separates the two notions of projectivity:

- `Realizability.Kleene.partitioned_natK1`, **`.regularProjective_natK1`** — the standard numbers
  assembly is partitioned, hence regular projective.
- `Realizability.Kleene.natToNabla`, `.epi_natToNabla`,
  **`.not_liftsRealizers_natToNabla`** — the identity function onto the indiscrete assembly on the
  numbers is an epimorphism, but no element of `K₁` can produce a realizer of every number from
  one and the same argument, so it does not lift realizers: the epimorphisms and the strong
  epimorphisms of `Asm(K₁)` differ.
- **`Realizability.Kleene.not_projective_natK1`** — along that epimorphism the non-computable
  diagonal function `n ↦ φₙ(n) + 1` has no lift, so the standard numbers assembly is not
  projective in the sense of `CategoryTheory.Projective`, although it is regular projective.

## Gates

- `lake build Start.AssemblyProjective` — success, no warnings.
- `lake build` — the whole library still builds, with no error and no warning.
- `python3 scripts/check_closure.py` — all modules in the import closure and all registered.
- `python3 scripts/goal_state.py validate` — board validates.
