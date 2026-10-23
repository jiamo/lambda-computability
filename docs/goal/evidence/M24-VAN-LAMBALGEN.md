# M24-VAN-LAMBALGEN: van Lambalgen's theorem

## Big round 2, run 2

Item W9: **advanced**. The first missing lemma `Lambda.MLRandom.join_left` is proved, together
with its mirror image, and relativized tests are defined. About 20 minutes used (of 120).

- Lean, `Start/MartinLofJoin.lean`:
  - `Lambda.halfSeq b Z = (n ↦ Z (2n + b))`, its finite-string analogue `Lambda.halfList b`
    (primitive recursive, `primrec_halfList`);
  - **`Lambda.map_halfSeq_cantorMeasure`** (`b < 2`): taking every second bit preserves the
    fair-coin measure (`Measure.eq_infinitePi` on boxes);
  - `Lambda.openOf_half`: `openOf {τ | halfList b τ ∈ S} = halfSeq b ⁻¹' openOf S`;
  - `Lambda.MLTest.half b hb T`: the pull-back of a Martin-Löf test (same measure bound),
    `MLTest.half_level`, `MLRandom.of_halfSeq`;
  - **`Lambda.MLRandom.join_left (A B : ℕ → Bool) : MLRandom (fun n => if n % 2 = 0 then A (n / 2) else B (n / 2)) → MLRandom A`**
    and **`Lambda.MLRandom.join_right`** (`… → MLRandom B`);
  - relativized tests: `Lambda.oracleOf X`, `Lambda.MLTestRel X` (the enumeration matrix is
    `ComputableIn (oracleOf X)`, Mathlib's relative computability), `Lambda.MLRandomRel X Z`,
    `Lambda.MLRandomRel.mlRandom` (relative randomness implies randomness).
- Axioms: `propext`, `Classical.choice`, `Quot.sound` (`M24-VAN-LAMBALGEN-axioms.txt`).
- First missing lemma (the relativized half of the forward direction):
  `theorem Lambda.MLRandom.join_right_rel (A B : ℕ → Bool) : Lambda.MLRandom (fun n => if n % 2 = 0 then A (n / 2) else B (n / 2)) → Lambda.MLRandomRel A B`
  (a test for `B` relative to `A`, uniform in the oracle, gives an unrelativized test for the
  join through the oracle's use; this needs the use principle for `Nat.RecursiveIn`), then the
  converse `MLRandom A → MLRandomRel A B → MLRandom (join A B)` (Fubini over the two halves).

## Big round 2, run 7 (restoration after the export of run 6)

The platform's export of run 6's project dropped this note; it was put back from its copy at the end of run 3; it already contains the big round 2 sections of runs 1 to 3. The axioms files of the big round 2 rows
were regenerated with `#print axioms` in run 7 (section "Big round 2, run 7").
