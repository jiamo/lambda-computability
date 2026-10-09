> Original Aristotle report accompanying Downloads/15. These are the producer's claims;
> local merge and static inspection are recorded in M26-DELIVERY-15-MERGE.md.

# Summary of changes for run 09049798-e579-4c30-8a95-c3515ea63c99
The equality \(\mathsf L = \mathsf{RL} = \mathsf{BPL}\) is now proved in our namespace with no `sorry`. I absorbed the Logspace proof from openai/math commit 3014888 into ordinary `Start` modules, and `lake build Start` succeeds (10545 jobs). Both task-board rows are closed.

**Terminal theorems** (in `Start/LogspaceEquality.lean`):
- `ExactDerandomization.BPL_subset_L : BPL ⊆ L`
- `ExactDerandomization.exact_logarithmic_space_derandomization : L = RL ∧ RL = BPL`

Both depend only on `propext`, `Classical.choice` and `Quot.sound` (checked with `#print axioms`). That matches the axioms the comparator permits. All 25 definitions in upstream's comparator spec, `Word` through `BPL`, appear unchanged (up to whitespace) in our existing `Start/LogspaceDeterministic.lean`. So the theorem states exactly the comparator's claim. I did not import or copy the comparator stub. As upstream notes, the paper's explicit compiler and running-time bounds are not stated separately.

**What was absorbed**
- The 38 new upstream modules became `Start/Logspace<Name>.lean`. The `OAI` namespace was dropped and imports were renamed. Each file has a header crediting openai/math, its original path, family 103, the paper title "Exact Derandomization of Logarithmic Space: L = RL = BPL" and commit 3014888.
- The existing `Deterministic.lean` port was reused. Upstream did not change it; I only updated its header to name commit 3014888.
- Two changes were needed for our Lean v4.33.0 / Mathlib v4.33.0 pins:
  - the same scripted renaming as for earlier directories: `ite_eq_left`, `ite_eq_right`, `dite_eq_left`, `dite_eq_right` became `if_pos`, `if_neg`, `dif_pos`, `dif_neg`;
  - one proof, `cord_mono` in `Start/LogspaceRecursivePrograms.lean`, needed an added `all_goals norm_num` for a leftover `1 ≤ 2` side goal. Its header records this.

**Reconciling the two amplification files.** Upstream's `Amplification.lean` ends with `ExactDerandomization.RL_subset_BPL`, the same name and statement our `Start/LogspaceAmplification.lean` already proves. Upstream's file is absorbed as `Start/LogspaceTableAmplification.lean` with that last theorem left out, so nothing is declared twice. `Start/LogspaceEquality.lean` uses our existing `RL_subset_BPL` instead. No public statement was weakened or renamed.

**Wiring and records**
- `Start/LogspaceEquality.lean` is imported from `Start.lean`. `Start/Capstones.lean` registers both terminal theorems (with their full types) and `Table.TM.prob_twice`, and its Logspace section is rewritten.
- `M26-LOGSPACE-CONVERSE` and `M26-OAI-LOGSPACE` are now DONE_STRONG with empty open boundaries. `docs/current-goal-state.md` has been regenerated.
- `NOTICE`, `README.md` and the header of `Start/LogspaceAmplification.lean` are updated. In `docs/goal/evidence/M26-OAI-ABSORPTION.md` I marked the earlier "no upstream Lean proof" conclusion as applying only to commit adc7f1241, and added a section on this absorption.
- `check_sorry.py`, `check_closure.py`, `goal_state.py validate` and `pack_gate.sh HEAD` all pass.
- In the Properties table, the `BPL ⊆ L` row and a new row for the full equality are marked proved.

The absorbed files print many style-linter warnings (spacing, line length) because the code is upstream's formatting, kept unchanged. Everything is committed.

