# M10-ASSEMBLY-NNO

**Status:** DONE_STRONG

Modules `Start/AssemblyLimits.lean` and `Start/AssemblyNNO.lean`, imported by `Start.lean` and
registered in `Start/Capstones.lean`.  They build without `sorry` and without linter warnings.

## What the task asked

`Start/Assembly.lean` and `Start/AssemblyCcc.lean` build the category of assemblies over an
arbitrary partial combinatory algebra and show it is cartesian closed.  What remained is the rest
of the structure a realizability topos needs at this level: finite limits, and a natural numbers
object.

## What is proved

* `Realizability.Assembly.subAsm`, `.subIncl`, `.subLift`, `.mono_subIncl` — the sub-assembly of a
  predicate, with the realizers inherited from the ambient assembly.
* `Realizability.Assembly.eqAsm`, `.eqFork`, `.eqForkIsLimit` — equalizers of tracked maps, hence
  `.instHasEqualizers`, `.instHasFiniteLimits` and `.instHasPullbacks`.
* `CategoryTheory.Limits.IsNNO` — Lawvere's natural numbers object, for a category with a terminal
  object: a unique map defined by iteration out of `zero` and `succ`.
* `Realizability.iterp`, `Realizability.cnum`, `Realizability.IsNumeral`,
  `Realizability.isNumeral_cnum` — iterated partial application, the Church numerals of a partial
  combinatory algebra, and the proof that the `n`-th numeral computes the `n`-fold iterate.
* `Realizability.Assembly.natAsm`, `.natZero`, `.natSucc` — the assembly of natural numbers and
  its zero and successor maps, tracked by explicit combinators (`Realizability.succEl`).
* `Realizability.Assembly.iterEl`, `.tracked_iter` — the iteration map is realized uniformly by
  `λ n. n f x`.
* `Realizability.Assembly.isNNO_natAsm` — **the universal property**: for every assembly `X`, base
  point `q` and endomorphism `f` there is a unique tracked map out of `natAsm` commuting with zero
  and successor.

## Boundary

Only the *natural numbers object* is proved; the subobject classifier and the exactness properties
that would make `Asm(A)` a quasitopos, and the realizability topos itself, are not formalized.

## Gates

* `lake build Start.AssemblyLimits Start.AssemblyNNO` — no error and no warning.
* `python3 scripts/check_closure.py`.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: `Realizability.Assembly.isNNO_natAsm` and
  `Realizability.Assembly.instHasFiniteLimits` depend only on `propext`, `Classical.choice` and
  `Quot.sound`.
