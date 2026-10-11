# M15-NO-RELATIVIZING-PROOF — the relativization barrier

`Start/Relativization.lean` states what it means for a statement about the complexity classes to
relativize and proves the barrier in full, **with no hypothesis**.

## What is proved

* `Complexity.Relativizes (S : Oracle → Prop) : Prop` — `S` holds with every oracle attached.
* `Complexity.peqnp_does_not_relativize : ¬ Relativizes PeqNP_rel` — from the separating oracle
  `Complexity.bgs_different` (`Start/BakerGillSolovay.lean`).
* `Complexity.pnenp_does_not_relativize : ¬ Relativizes PneNP_rel` — from the collapsing oracle
  `Complexity.bgs_equal` (`Start/CollapsingOracle.lean`, row `M15-BGS-COLLAPSE`).  The conditional
  form is kept as `Complexity.pnenp_does_not_relativize_of`.
* `Complexity.no_relativizing_resolution : ¬ Relativizes PeqNP_rel ∧ ¬ Relativizes PneNP_rel`.

`#print axioms Complexity.no_relativizing_resolution`: `propext`, `Classical.choice`,
`Quot.sound`.

## How the collapsing oracle was obtained

The task board planned the collapsing half through `P^TQBF = NP^TQBF`, which needs
`NP^A ⊆ PSPACE^A` (`M15-ORACLE-PROG`) and `TQBF ∈ PSPACE` (`M14-TQBF-IN-PSPACE`).  The barrier only
needs *some* oracle with `P^A = NP^A`; `Start/CollapsingOracle.lean` builds one directly by a
self-referential construction (see `docs/goal/evidence/M15-BGS-COLLAPSE.md`).  The TQBF version
stays open as `M15-BGS-EQUAL`.

## Gates

`python3 scripts/check_sorry.py`, `python3 scripts/check_closure.py`,
`python3 scripts/goal_state.py validate`.  The modules `Start/CollapsingOracle.lean` and
`Start/Relativization.lean` and their imports were built with `lake build` in a copy of the tree
configured for the toolchain available in the build environment of this delivery (Lean v4.28.0
with the matching Mathlib); the shipped `lean-toolchain` / `lakefile.toml` pins (v4.33.0) were not
available there.  See the delivery report.
