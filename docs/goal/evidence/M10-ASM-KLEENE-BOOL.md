# M10-ASM-KLEENE-BOOL

**Status:** DONE_STRONG

Module `Start/AssemblyKleeneBool.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings, and its results
depend only on `propext`, `Classical.choice` and `Quot.sound`.

## What this task adds

`Start/AssemblyKleene.lean` identifies the maps of the standard numbers assembly over Kleene's
first algebra with the computable functions.  This module does the same for boolean-valued maps
and reads off what the booleans of `Asm(K₁)` can and cannot classify.

- `Realizability.Kleene.exists_index_of_partrec`, `.exists_index_of_computable` — every partial
  recursive function of one variable is `natApp r` for a fixed index `r`; this is the packaging of
  the enumeration theorem used throughout the module.
- `Realizability.Kleene.boolNum`, `.boolK1`, `.modest_boolK1` — the standard assembly of booleans:
  `true` is realized by `1`, `false` by `0`, and a realizer determines its element.
- **`Realizability.Kleene.tracked_boolK1_iff`** — *effective Church's thesis for boolean-valued
  functions*: `f : ℕ → Bool` is tracked from the standard numbers assembly to the standard
  booleans exactly when it is computable.  A tracker `r` satisfies `φ_r(n) = boolNum (f n)`, and
  the boolean numeral is the Gödel encoding of a boolean, so `f` is computable; conversely an
  index for `n ↦ boolNum (f n)` is a tracker.
- `Realizability.Kleene.toBoolFun`, `.computable_toBoolFun`, `.boolHomEquiv` — hence the morphisms
  from the numbers to the booleans are in bijection with the computable boolean-valued functions.
- **`Realizability.Kleene.exists_charBool_iff`** — a predicate on the natural numbers is cut out
  by a characteristic morphism into the booleans exactly when it is a computable predicate.
- `Realizability.Kleene.selfHalt`, **`.not_computable_selfHalt`**, `.not_computable_selfHalt_false`
  — self-halting `(φ_n(n))↓` is undecidable: an index `r` for the machine that diverges exactly
  when a putative decision procedure answers "halts" contradicts the procedure at `r`; negating
  the procedure gives the same for the opposite polarity.
- **`Realizability.Kleene.no_charBool_selfHalt`**, **`.boolK1_not_classifier`** — self-halting
  therefore has no characteristic morphism into the booleans, of either polarity: in `Asm(K₁)` the
  booleans do *not* classify sub-assemblies, in contrast with the indiscrete assembly on `Prop`
  of `Start/AssemblySubobject.lean`, which classifies every sub-assembly.

- `Realizability.Kleene.rePred_iff_exists_index`, `.rePred_selfHalt`,
  `.not_computablePred_selfHalt` — a predicate on the numbers is recursively enumerable exactly
  when it is the domain of convergence of a single element of `K₁`; self-halting is such a
  predicate, so it is semidecidable, and by the above it is nevertheless undecidable.
- `Realizability.Kleene.tagDecode`, `.boolOfSum`, `.sumOfBool`, `.boolK1IsoCoprod`,
  `.falsePt`, `.truePt`, **`.boolCofanIsColimit`** — the tag of a coproduct realizer is decoded by
  applying it to `0` and then `1`, which the left tag `k` answers with `0` and the right tag `k i`
  with `1`; this and the constant indices in the other direction make the booleans isomorphic to
  the coproduct assembly of `Start/AssemblyColimits.lean`, so the two points `false` and `true`
  exhibit `boolK1` as the coproduct `1 + 1`.

## Gates

- `lake build Start.AssemblyKleeneBool` — success, no warnings.
- `lake build` — the whole library still builds, with no error and no warning.
- `python3 scripts/check_closure.py` — all modules in the import closure and all registered.
- `python3 scripts/goal_state.py validate` — board validates.
