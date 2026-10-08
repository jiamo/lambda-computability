> Original Aristotle report accompanying Downloads/8. These are the producer's claims;
> local merge and verification results are recorded separately in M26-DELIVERY-8-MERGE.md.

# Summary of changes for run 79ddcf9b-59ab-4dbe-ad7b-c84b3cc9dc17
I absorbed the first four directories on your list (TypeSystem, Logspace, SolenoidalRecorder, StarHeight, WeisfeilerLeman, DepthThree), plus a Lean comparison of the two degree definitions. DegreeRigidity is not absorbed: my answer to whether it is worth it is no (last paragraph). `lake build Start` succeeds (9530 jobs), and `check_sorry.py` (811 modules), `check_closure.py` (810 modules), `goal_state.py validate` (294 tasks) and `scripts/pack_gate.sh HEAD` all pass. Every terminal theorem below depends only on `propext`, `Classical.choice` and `Quot.sound`. Everything is committed.

**The Degree question.** The two oracle functions are the same term:
- theirs: `def oracleFunction (A : Oracle) : ℕ →. ℕ := fun n => Part.some (if A n then 1 else 0)`, with `abbrev Oracle := ℕ → Bool`;
- ours: `def oracleFun (A : ℕ → Bool) : ℕ →. ℕ := fun n => Part.some (if A n then 1 else 0)`.

So their `Reduces A B := TuringReducible (oracleFunction A) (oracleFunction B)` unfolds to our relation. The degree types differ, and neither wraps the other:
- theirs: `def Degree := Antisymmetrization Oracle Reduces`, a quotient of total 0/1 oracles;
- ours: mathlib's `TuringDegree := Antisymmetrization (ℕ →. ℕ) TuringReducible`, a quotient of all partial functions.

`Start/OracleDegreeBridge.lean` restates their five definitions, proves `oracleFunction_eq` (`rfl`), and builds an order embedding `SetDegree.toTuringDegree : SetDegree ↪o TuringDegree` whose range is exactly the degrees containing a 0/1 oracle (`range_toTuringDegree`). I did not settle whether the embedding is onto. Their definitions therefore port directly, and every statement about their `Degree` is a statement about our degrees of sets.

**What was absorbed, and under what names.** 298 files became flat `Start/` modules; the `OAI` namespace was dropped and each file has an attribution header. They are imported from `Start.lean` and registered in `Start/Capstones.lean`. Verbatim terminal statements:
- **TypeSystem → `Start/PTS*.lean`:** `theorem weak_implies_strong {S : Type u} (P : Specification S) (h : SystemWeaklyNormalizing P) : SystemStronglyNormalizing P`.
- **Logspace → `Start/LogspaceDeterministic.lean`:** `theorem L_subset_RL : L ⊆ RL` and `theorem L_subset_BPL : L ⊆ BPL`. As you suspected, the file carries only these easy inclusions, not L = RL = BPL.
- **SolenoidalRecorder → `Start/Solenoidal*.lean`:** `theorem halting_iff (w : List M.Symbol) (r₀ : ℤ) (hr₀ : 2 ≤ r₀) : (∃ (N : ℕ) (c : Config M), Steps N (initial w r₀) c ∧ Terminal c) ↔ M.Halts w`, together with `nonhalting_execution`.
- **StarHeight → `Start/StarHeight*.lean`:** `theorem main {Alphabet : Type u} [Finite Alphabet] (L : Language Alphabet) (hL : L.IsRegular) : HasHeightAtMost L 3`.
- **WeisfeilerLeman → `Start/WL*.lean`:** `theorem WLTime.unconditional_time_lower_bound : WLTime.MainClaim`. The family-133 paper is not in the snapshot, so its header says so instead of naming a title.
- **DepthThree → `Start/DepthThree*.lean`:** `theorem exists_polynomial_time_language_depth_three_lower_bound : ∃ (L : List Bool → Bool) (M : FiniteMultiTapeMachine) (C a : ℕ), 0 < C ∧ 0 < a ∧ (∀ w, MultiTapeHaltsIn M w (L w) (C * (w.length + 1) ^ a)) ∧ ∀ A : ℝ, 0 < A → ∃ N, ∀ n, N ≤ n → ∀ D : Circuit3 (Fin n), D.Computes (fun x => L (List.ofFn x)) → (2 : ℝ) ^ (A * Real.sqrt n) < D.gateCount`. The circuits are OR-of-AND-of-OR with unbounded fan-in, in upstream's own model. That model and upstream's machine model are not yet connected to `Start/PolyCircuit.lean` or `Start/UniformCircuit.lean`.

On λΠ: `Start/LambdaPiSN.lean` stays an independent proof. Using `weak_implies_strong` would need weak normalization of λΠ, and that is only available as a consequence of strong normalization, so it would be circular. Instead, `Start/PTSLambdaPi.lean` (our own code) makes λΠ an instance of the PTS framework. It defines `lambdaPiSpec`, translates framework derivations into our λΠ derivations, and proves `lambdaPi_systemStronglyNormalizing : SystemStronglyNormalizing lambdaPiSpec` from `LambdaPi.Typing.sn`.

Bookkeeping:
- The board has milestone M26 with 9 rows:
  - DONE_STRONG: the Degree question, TypeSystem, SolenoidalRecorder, StarHeight, WeisfeilerLeman, DepthThree.
  - DONE_WEAK: Logspace. It depends on a new row, `M26-LOGSPACE-CONVERSE` (TODO_NEEDS_DESIGN), for RL ⊆ L and BPL ⊆ L, which are not in upstream Lean.
  - TODO_NEEDS_DESIGN: DegreeRigidity.

  No earlier M26 row existed, so there was nothing to preserve.
- New files: `NOTICE`, a README section that credits these results as upstream's (not this library's), and `docs/goal/evidence/M26-OAI-ABSORPTION.md`.
- I rewrote `scripts/check_closure.py`'s name-matching step to run in linear time. With 810 modules it had grown to about 4 minutes; it now takes about 3 seconds, and its output is identical to the old version.
- The Properties table lists the new results.
- `oai-math-relevant.bundle.json` and the restore script came committed in the repository, and I left them in place.

**What was reconstructed rather than adapted.** Nothing; every absorbed proof is upstream's, adapted. The changes needed for our pin were:
- `dite_eq_left`, `dite_eq_right`, `ite_eq_left`, `ite_eq_right` renamed to `dif_pos`, `dif_neg`, `if_pos`, `if_neg`;
- `Finset.prod_le_prod₀` renamed to `Finset.prod_le_prod`;
- upstream's one-hypothesis `Finset.prod_le_prod` changed to `Finset.prod_le_prod'`;
- `Finset.prod_le_one₀` renamed to `Finset.prod_le_one`;
- the import `Mathlib.Basic.Real.Basic`, which does not exist on our pin, replaced by `import Mathlib` in five files.

Each file that needed a fix beyond the scripted renaming records it in its header. The new code that is ours, not upstream's, is `Start/PTSLambdaPi.lean` and the bridge in `Start/OracleDegreeBridge.lean`.

**Is DegreeRigidity worth absorbing? Not into `Start`.** It is 975 files and 84,104 lines, about 54% of the library's size before this milestone. Of that, 674 files (57.7k lines) are a ZF set-model, constructibility and forcing development that nothing else here uses, and the recursion-theory part imports it throughout, so it cannot be split off. The work itself would probably be cheap, given that the 298 files above needed only a handful of renamings. The real cost is weight: 975 more modules for the gates, a much longer clean build, and a set-theory subtree that every future pin change has to carry, all for one theorem. That theorem is already stated in our namespace as `Lambda.Oracle.SetDegreeRigidity`, tied exactly to our degrees by the embedding. If you want it proved, I'd host it as a separate library target in this repository and leave `Start` untouched. That choice is yours, so the row stays TODO_NEEDS_DESIGN.

