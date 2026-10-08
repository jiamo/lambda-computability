# M26 — absorbing github.com/openai/math (commit adc7f1241, Apache-2.0)

Reference input: the `lean/OAI/Computability` snapshot (1275 Lean files) with its README, restored
outside the repository.  Nothing of it is vendored; every absorbed file is an ordinary `Start/`
module with an attribution header, listed in `NOTICE`.  Lean pin unchanged (v4.33.0, Mathlib
`v4.33.0`).  All terminal theorems below depend only on `propext`, `Classical.choice`,
`Quot.sound` (`#print axioms`).

## The Degree question (settled first)

Upstream `DegreeRigidity/Model.lean`:

```lean
abbrev Oracle := ℕ → Bool
def oracleFunction (A : Oracle) : ℕ →. ℕ := fun n => Part.some (if A n then 1 else 0)
def Reduces (A B : Oracle) : Prop := TuringReducible (oracleFunction A) (oracleFunction B)
def Degree := Antisymmetrization Oracle Reduces
```

This library (`Start/OracleSim.lean`, `Start/OracleJoin.lean`, `Start/OracleCone.lean`, ...):

```lean
def oracleFun (A : ℕ → Bool) : ℕ →. ℕ := fun n => Part.some (if A n then 1 else 0)
-- degrees are stated in mathlib's
abbrev TuringDegree := Antisymmetrization (ℕ →. ℕ) TuringReducible
```

`oracleFunction` and `oracleFun` are the same term (`Lambda.Oracle.oracleFunction_eq : ... := rfl`),
and `Reduces A B` unfolds to `TuringReducible (oracleFun A) (oracleFun B)`
(`Lambda.Oracle.setReduces_iff`, `Iff.rfl`).  The degree types are **not** the same object and
neither wraps the other: upstream quotients total `0/1` oracles, mathlib/this library quotients
all partial functions.  `Lambda.Oracle.SetDegree.toTuringDegree : SetDegree ↪o TuringDegree` is an
order embedding whose range is the set of degrees containing a `0/1` oracle
(`SetDegree.range_toTuringDegree`).  Whether that range is all of `TuringDegree` is not settled
here.  Consequence: every upstream statement about `Degree` transfers along this embedding to a
statement about the degrees of sets inside our `TuringDegree`; the definitions are directly portable,
and the proofs do not depend on the choice.

## Absorbed directories

| row | upstream | modules | terminal statement |
|---|---|---|---|
| `M26-OAI-TYPESYSTEM` | `TypeSystem/` (33), family 245 | `Start/PTS*.lean` | `PureTypeSystem.weak_implies_strong` |
| `M26-OAI-LOGSPACE` | `Logspace/` (1), family 103 | `Start/LogspaceDeterministic.lean` | `ExactDerandomization.L_subset_RL`, `L_subset_BPL` |
| `M26-OAI-SOLENOIDAL` | `SolenoidalRecorder/` (5), family 376 | `Start/Solenoidal*.lean` | `Solenoidal.Recorder.halting_iff`, `nonhalting_execution` |
| `M26-OAI-STARHEIGHT` | `StarHeight/` (37), family 134 | `Start/StarHeight*.lean` | `GeneralizedStarHeight.main` |
| `M26-OAI-WEISFEILERLEMAN` | `WeisfeilerLeman/` (43), family 133 | `Start/WL*.lean` | `WLTime.unconditional_time_lower_bound` |
| `M26-OAI-DEPTHTHREE` | `DepthThree/` (179), family 112 | `Start/DepthThree*.lean` | `DepthThreeLowerBound.exists_polynomial_time_language_depth_three_lower_bound` |

Verbatim terminal statements:

```lean
theorem weak_implies_strong {S : Type u} (P : Specification S)
    (h : SystemWeaklyNormalizing P) : SystemStronglyNormalizing P

theorem L_subset_RL : L ⊆ RL
theorem L_subset_BPL : L ⊆ BPL

theorem halting_iff (w : List M.Symbol) (r₀ : ℤ) (hr₀ : 2 ≤ r₀) :
    (∃ (N : ℕ) (c : Config M), Steps N (initial w r₀) c ∧ Terminal c) ↔ M.Halts w
theorem nonhalting_execution (w : List M.Symbol) (r₀ : ℤ) (hr₀ : 2 ≤ r₀)
    (h : ¬M.Halts w) :
    ∃ c : ℕ → Config M, c 0 = initial w r₀ ∧ ∀ n : ℕ, Step (c n) (c (n + 1))

theorem main {Alphabet : Type u} [Finite Alphabet] (L : Language Alphabet) (hL : L.IsRegular) :
    HasHeightAtMost L 3

theorem WLTime.unconditional_time_lower_bound : WLTime.MainClaim
-- def MainClaim : Prop :=
--   ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
--     ∀ convention : Convention, ∀ p : InputClass, ∀ A : Model,
--       Decides A convention k p → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
--         (n : ℝ) ^ (c * (k : ℝ)) ≤ (worstTime A p n : ℝ)

theorem exists_polynomial_time_language_depth_three_lower_bound :
    ∃ (L : List Bool → Bool) (M : FiniteMultiTapeMachine) (C a : ℕ),
      0 < C ∧ 0 < a ∧
      (∀ w : List Bool, MultiTapeHaltsIn M w (L w) (C * (w.length + 1) ^ a)) ∧
      ∀ A : ℝ, 0 < A → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ D : Circuit3 (Fin n), D.Computes (fun x => L (List.ofFn x)) →
          (2 : ℝ) ^ (A * Real.sqrt (n : ℝ)) < (D.gateCount : ℝ)
```

## What changed in adaptation

Every proof was adapted, none reconstructed.  Per file: the `OAI` namespace was dropped, imports were
renamed, and the attribution header was added.  Lemma names differing between the two pins:
`dite_eq_left/right`, `ite_eq_left/right` became `dif_pos/neg`, `if_pos/neg` (TypeSystem, 29
uses; also in later directories by the same script); `Finset.prod_le_prod₀` became
`Finset.prod_le_prod` (`StarHeightTagPartitions`); upstream's one-hypothesis `Finset.prod_le_prod`
became `Finset.prod_le_prod'` (`WLPadding`); `Finset.prod_le_one₀` became `Finset.prod_le_one`
(`DepthThreeMomentBounds`).  The nonexistent import `Mathlib.Basic.Real.Basic` became
`import Mathlib` (5 DepthThree files).  Each changed file records the change in its header.

## Caveats on the statements

* **Logspace.**  The upstream file does not carry `L = RL = BPL`: it proves only the easy
  inclusions `L ⊆ RL` and `L ⊆ BPL`.  The converse inclusions are not in upstream Lean; the row is
  `DONE_WEAK`, depending on `M26-LOGSPACE-CONVERSE`.
* **DepthThree.**  `Circuit3` is an unbounded fan-in OR-of-AND-of-OR circuit with literal and
  constant inputs, and the gate count counts all gates; the machine model is upstream's
  `FiniteMultiTapeMachine` (mathlib `Turing.Tape`s).  Neither is yet connected to
  `Start/PolyCircuit.lean` or `Start/UniformCircuit.lean`.
* **SolenoidalRecorder.**  Only the discrete recorder machine is formalized upstream; the fluid
  dynamics of the paper is not.
* **WeisfeilerLeman.**  The paper itself is not part of the snapshot.

## λΠ and the PTS theorem

`Start/PTSLambdaPi.lean` (this library's own) defines `PureTypeSystem.lambdaPiSpec` (`∗ : □`,
rules `(∗,s,s)`), shows that the framework syntax over `Srt` is `LambdaPi.Tm`
(`toTm`, commuting with renaming/substitution/instantiation, `beta_toTm`), that every framework
derivation is a `λΠ` derivation (`HasType.toTyping`, `ValidContext.toWf`), and proves
`lambdaPi_systemStronglyNormalizing : SystemStronglyNormalizing lambdaPiSpec` from
`LambdaPi.Typing.sn`.  `Start/LambdaPiSN.lean` stays an independent proof: `weak_implies_strong`
needs system-wide weak normalization as a hypothesis, and the only weak-normalization proof for
`λΠ` is a corollary of strong normalization, so deriving SN from the PTS theorem would be
circular.  `lambdaPi_weak_implies_strong_consistent` records that the theorem applies.

## DegreeRigidity: is it worth absorbing?  (Original assessment, superseded below)

`DegreeRigidity/` has 975 files and 84 104 lines.  For comparison, `Start/` was 155 k lines before
this milestone and 89 k lines were absorbed above.  `SetModels`, `CohenForcing`,
`OrdinalCodes`, `Constructibility` and `Syntax` together are 674 files and 57.7 k lines: a ZF
set-model, constructibility and forcing development that nothing else in this library would use.
The recursion-theory part imports it throughout, so it cannot be detached.  Labour is not the main
cost: the 298 files absorbed above needed four distinct one-line renamings and one import fix, so
adaptation would probably be cheap.  The cost is weight:
* about +54 % on the pre-milestone library and +975 modules for the closure and registration
  gates;
* an hour-scale increase in clean build time;
* a set-theory subtree that every future pin move would have to carry;
* all of this for one terminal theorem.

That theorem is already *stated* in our namespace (`Lambda.Oracle.SetDegreeRigidity`), and
`SetDegree.toTuringDegree` relates it exactly to our degrees.  Recommendation: do not absorb into
`Start`.  If the rigidity theorem is wanted as a proved result, the right design is a second
`lean_lib` target in this repository (the set theory and rigidity proof), with `Start` untouched.
That is a design decision for the maintainers, so the row stays `TODO_NEEDS_DESIGN`.

## Follow-up: DegreeRigidity absorbed, Logspace converse reduced to `BPL ⊆ L`

The assessment above left two parts of the original goal open.  Both were taken up.

### DegreeRigidity (row `M26-OAI-DEGREE-RIGIDITY`)

All 975 upstream files were absorbed into `Start` as flat modules `Start/Rigidity<Name>.lean`
(`OAI.Computability.DegreeRigidity.<Dir>.<Name>` ↦ `Start.Rigidity<Name>`; upstream file names
are unique across its subdirectories), with the `OAI` namespace dropped and an attribution header
in each file.  Every proof is upstream's.  Changes needed for this pin, beyond the renamings
already listed: `dite_eq_left/right`, `ite_eq_left/right` ↦ `dif_pos/neg`, `if_pos/neg` (94 files);
`Filter.eventuallyEqSet_iff` ↦ `Filter.eventuallyEq_set` (2 files); `apply Measurable.of_eval` ↦
`apply measurable_pi_lambda` (7 files); the case `| ind` of `Ordinal.lt_wf.induction` ↦ `| h`
(1 file).  The 10 files with changes beyond the scripted renamings record them in their headers.
`lake build Start` succeeds (10507 jobs); `#print axioms` for `TuringRigidity.ManuscriptMain.rigidity`
and `Lambda.Oracle.setDegreeRigidity` shows only `propext`, `Classical.choice`, `Quot.sound`.

`RigidityMain` imports 973 of the other modules; the one upstream module it does not import,
`RigidityArithmeticRepresentation`, is imported from `Start.lean` so the directory is absorbed
whole.  Both are registered in `Start/Capstones.lean`.

`Start/RigidityBridge.lean` (this library's own) identifies upstream's `Degree` with
`Lambda.Oracle.SetDegree` (`setDegreeOrderIso`, the identity map: both are the same quotient) and
proves the exit criterion:

```lean
theorem Lambda.Oracle.setDegreeRigidity : Lambda.Oracle.SetDegreeRigidity
-- SetDegreeRigidity := ∀ π : SetDegree ≃o SetDegree, ∀ a : SetDegree, π a = a
```

from `TuringRigidity.ManuscriptMain.rigidity : TuringRigidity.MainTheorem`.

### Logspace converse (row `M26-LOGSPACE-CONVERSE`)

The upstream Lean contains no proof of `RL ⊆ L` or `BPL ⊆ L`, so there is nothing further to
absorb; the derandomization direction is the main theorem of the 7.9k-line preprint (median of
estimates of a correction/copy hierarchy, property (T) mixing, fingerprinting, a catalytic
log-space controller) and is not formalized here.  What was added, in upstream's machine model,
is `Start/LogspaceAmplification.lean` (this library's own):

```lean
theorem ExactDerandomization.RL_subset_BPL : RL ⊆ BPL
theorem ExactDerandomization.RL_subset_L_of_BPL_subset_L (h : BPL ⊆ L) : RL ⊆ L
theorem ExactDerandomization.L_eq_RL_and_L_eq_BPL_of_BPL_subset_L (h : BPL ⊆ L) : L = RL ∧ L = BPL
```

The machine `M.twoTrial` runs two copies of `M` on disjoint work tapes and input heads,
alternating steps, so that the copies read the even and odd coin bits; it accepts iff either copy
accepts.  Proved: it halts by `2T` if `M` halts by `T` (`twoTrial_haltsBy`), its acceptance
probability at `2T` is `1 - (1 - p)^2` (`twoTrial_acceptanceProbability`), and its space is at
most the sum of the two copies' (`twoTrial_spaceThrough`, `twoTrial_logSpace`).  So only
`BPL ⊆ L` remains open; the row stays `TODO_NEEDS_DESIGN` and `M26-OAI-LOGSPACE` stays
`DONE_WEAK`.
