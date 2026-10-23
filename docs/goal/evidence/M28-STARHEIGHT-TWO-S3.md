# M28-STARHEIGHT-TWO-S3: languages recognized by S3 have height at most two

## Big round 2, run 4

`Start/StarHeightTwoS3.lean`:

- `alternatingGroup_three_comm`: `A₃` is abelian (`decide`).
- `height_one_of_S3`: every language recognized by `S₃` has generalized star height at most one.
  It is `height_one_of_abelian_prime_index` (Start/StarHeightIndexPrime.lean)
  with `N = alternatingGroup (Fin 3)`, which has index 2 (`alternatingGroup.index_eq_two`).
- `height_two_of_S3`: the terminal statement, by `HasHeightAtMost.mono`.

Exit criterion, as written: "height_two_of_S3 is proved, or a language recognized by S3 is proved
to have height greater than two." It is proved, in the stronger form with height one. The result
is not new: S₃ has an abelian normal subgroup of prime index, and the project already had the
theorem for such groups. The row's earlier description, which linked height one for S₃ to the open
S3-core, mixed up languages recognized by S₃ with the counts `hcount ρ g x w mod n` over S₃. Those
counts are recognized by `Zₙ ≀ S₃`, not by S₃, and they stay open in M28-STARHEIGHT-S3-CORE.

Axioms: `M28-STARHEIGHT-TWO-S3-axioms.txt` (propext, Classical.choice, Quot.sound).

## Big round 2, run 7 (rebuilt)

The module of run 4 was lost with the old project (its file was written with the file tool, so the
command log does not record it). Run 7 wrote it again from this note and run 4's final message,
with the same terminal theorem names; it builds with `lake build --wfail`, standard axioms only
(regenerated with `#print axioms`, section "Big round 2, run 7" of the axioms file).
