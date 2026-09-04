# M11-REWRITING-INTERFACE

**Status:** DONE_STRONG

Module `Start/Rewriting.lean`, imported by `Start.lean` and registered in `Start/Capstones.lean`.
It builds without `sorry` and without linter warnings, and its results depend only on `propext`,
`Classical.choice` and `Quot.sound`.

## What this task adds

`docs/consolidation-review.md` measured the one real duplication in the library: fourteen
hand-rolled reflexive–transitive closures and four parallel-reduction developments, each
re-deriving the same nine statements about an arbitrary binary relation.  This module proves them
once, for `r : α → α → Prop`.

- `Rewriting.Star`, `Rewriting.Plus`, `Rewriting.Alt`, `Rewriting.Conv`, `Rewriting.Joins` — the
  reflexive–transitive closure, the transitive closure, the union of two relations, the generated
  conversion and joinability, with the closure API: `Star.refl`, `Star.single`, `Star.trans`,
  `Star.head`, `Star.tail`, `Star.rec_tail`, `Star.cases_head`, `Star.mono`, `Star.head_split`
  (splitting a nonempty reduction at its first step), `Plus.head_split`, `Conv.symm`,
  `Conv.of_joins`.
- `Rewriting.Diamond`, `Confluent`, `LocallyConfluent`, `Commute`, `StronglyCommute`, `Postpones`,
  `PostponesPlus`, `SN`, `Terminating` — the properties, with `SN.step`, `SN.star`.
- **`Rewriting.strip`**, **`Rewriting.confluent_of_diamond`** — the diamond property implies the
  strip lemma and confluence of the closure; `confluent_of_star_iff` transfers confluence along an
  equality of closures.
- **`Rewriting.conv_iff_joins_of_confluent`** — for a confluent relation, conversion is exactly
  joinability (Church–Rosser).
- **`Rewriting.commute_of_stronglyCommute`** — Hindley's lemma: strongly commuting relations have
  commuting closures, through the commutation strip `strip_stronglyCommute`.
- **`Rewriting.confluent_alt_of_commute`** — Hindley–Rosen: two confluent commuting relations have
  a confluent union, via the composite `Rewriting.Comp` whose closure is that of the union
  (`star_comp_eq_star_alt`) and which has the diamond property.
- **`Rewriting.postpones_of_par`**, `postponesPlus_of_par` — local postponement through a
  *parallel* relation `p` between `s` and `s*` gives postponement of `s` after `r`;
  **`Rewriting.star_alt_iff_of_postpones`** — hence a mixed reduction factors as `r*` then `s*`.
- **`Rewriting.terminating_of_measure`** — a relation strictly decreasing a natural-number measure
  terminates; **`Rewriting.sn_alt_of_postponesPlus`** (with `sn_alt_aux`) — termination transfers
  to the union from termination of `r`, a measure decreased by `s`, and sharp postponement.
- `Rewriting.exists_normal_of_sn` — a strongly normalizing point has a normal form.
- **`Rewriting.confluent_of_sn`**, **`Rewriting.confluent_of_newman`** — Newman's lemma, pointwise
  and globally.

A client keeps its own inductive closure and needs only a bridging lemma `Red t u ↔ Star Step t u`
in order to use all of this; that migration is `M11-REWRITING-MIGRATE` and no existing module is
changed by the present task.

## Gates

- `lake build Start.Rewriting` — success, no warnings.
- `python3 scripts/check_closure.py` — all modules in the import closure and all registered.
- `python3 scripts/goal_state.py validate` — board validates.
