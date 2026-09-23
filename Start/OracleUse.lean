/-
**The use of an oracle computation.**

`Start/OracleMachine.lean` proves the use principle in existential form: a converging oracle
computation has *some* bound below which the oracle may not be changed.  A priority construction
needs the bound itself, as a function of the computation, because a strategy has to know which
part of the oracle it is protecting.  This file defines it.

The computation `evalOracle A c x` searches over stages `s`, each stage supplying both the fuel
and the length of the oracle segment; the *use stage* is the least stage at which the search
succeeds, and the **use** is one more than it — an oracle that agrees with `A` below the use gives
the same computation, with the same use.

* `Lambda.Oracle.Converges` — the oracle computation halts;
* `Lambda.Oracle.useStage`, `Lambda.Oracle.use` — the least converging stage, and the use;
* `Lambda.Oracle.useStage_le_of_isSome`, `Lambda.Oracle.use_le_succ_of_isSome` — minimality: no
  stage below the use stage converges, so the use is the least such bound;
* `Lambda.Oracle.evalOracle_eq_some_of_converges` — the computation is the value found at the use
  stage;
* `Lambda.Oracle.evalOracle_eq_of_agree_below_use` — **the use principle with the explicit
  bound**: agreement below the use preserves the whole computation;
* `Lambda.Oracle.use_eq_of_agree_below_use` — and preserves the use itself;
* `Lambda.Oracle.use_mono_of_agree` — hence the use is monotone along an extension of the oracle
  that respects it.
-/

import Start.OracleMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Oracle

open Encodable Denumerable
open Nat.Partrec (Code)

variable {A B : ℕ → Bool} {c : Code} {x : ℕ}

/-- The oracle computation halts: some stage of the search succeeds. -/
def Converges (A : ℕ → Bool) (c : Code) (x : ℕ) : Prop := ∃ s, (oracleStep A c x s).isSome

theorem converges_of_mem {y : ℕ} (h : y ∈ evalOracle A c x) : Converges A c x := by
  obtain ⟨s, hs⟩ := exists_stage_of_mem_evalOracle h
  exact ⟨s, by simp [hs]⟩

/-- The least stage at which the search succeeds; `0` for a divergent computation. -/
noncomputable def useStage (A : ℕ → Bool) (c : Code) (x : ℕ) : ℕ :=
  open Classical in
  if h : Converges A c x then Nat.find h else 0

/-- **The use of an oracle computation**: one more than the least stage at which it converges, and
`0` when it diverges.  Changing the oracle only at arguments `≥ use` changes nothing. -/
noncomputable def use (A : ℕ → Bool) (c : Code) (x : ℕ) : ℕ :=
  open Classical in
  if Converges A c x then useStage A c x + 1 else 0

theorem use_eq_zero_of_not_converges (h : ¬ Converges A c x) : use A c x = 0 := by
  simp [use, h]

theorem use_eq_succ (h : Converges A c x) : use A c x = useStage A c x + 1 := by
  simp [use, h]

theorem useStage_lt_use (h : Converges A c x) : useStage A c x < use A c x := by
  rw [use_eq_succ h]; omega

/-- The search succeeds at the use stage. -/
theorem isSome_oracleStep_useStage (h : Converges A c x) :
    (oracleStep A c x (useStage A c x)).isSome := by
  classical
  rw [useStage, dif_pos h]
  exact Nat.find_spec h

/-- No stage below the use stage succeeds. -/
theorem oracleStep_eq_none_of_lt_useStage (h : Converges A c x) {m : ℕ}
    (hm : m < useStage A c x) : oracleStep A c x m = none := by
  classical
  rw [useStage, dif_pos h] at hm
  have := Nat.find_min h hm
  cases hval : oracleStep A c x m with
  | none => rfl
  | some y => exact absurd (by simp [hval]) this

/-- Minimality of the use stage: every converging stage is at least the use stage. -/
theorem useStage_le_of_isSome (h : Converges A c x) {s : ℕ} (hs : (oracleStep A c x s).isSome) :
    useStage A c x ≤ s := by
  classical
  rw [useStage, dif_pos h]
  exact Nat.find_le hs

/-- Minimality of the use: it is the least bound of the form "stage `+ 1`". -/
theorem use_le_succ_of_isSome (h : Converges A c x) {s : ℕ} (hs : (oracleStep A c x s).isSome) :
    use A c x ≤ s + 1 := by
  rw [use_eq_succ h]
  exact Nat.succ_le_succ (useStage_le_of_isSome h hs)

/-- The value of a converging computation is the value found at the use stage. -/
theorem evalOracle_eq_some_of_converges (h : Converges A c x) {y : ℕ}
    (hy : oracleStep A c x (useStage A c x) = some y) : evalOracle A c x = Part.some y := by
  have hmem : y ∈ evalOracle A c x :=
    mem_evalOracle_iff.2 ⟨useStage A c x, hy, fun m hm => oracleStep_eq_none_of_lt_useStage h hm⟩
  exact Part.eq_some_iff.2 hmem

/-- A converging computation converges, with the same value, for every oracle agreeing below the
use. -/
theorem oracleStep_congr_of_agree_below_use (h : Converges A c x)
    (hAB : ∀ n < use A c x, A n = B n) {s : ℕ} (hs : s ≤ useStage A c x) :
    oracleStep A c x s = oracleStep B c x s := by
  refine oracleStep_congr (u := use A c x) ?_ hAB
  exact lt_of_le_of_lt hs (useStage_lt_use h)

/-- **The use principle, with the explicit bound.**  Two oracles that agree below the use of a
converging computation give the same computation. -/
theorem evalOracle_eq_of_agree_below_use (h : Converges A c x)
    (hAB : ∀ n < use A c x, A n = B n) : evalOracle B c x = evalOracle A c x := by
  obtain ⟨y, hy⟩ : ∃ y, oracleStep A c x (useStage A c x) = some y := by
    have := isSome_oracleStep_useStage h
    cases hval : oracleStep A c x (useStage A c x) with
    | none => rw [hval] at this; exact absurd this (by simp)
    | some y => exact ⟨y, rfl⟩
  have hB : oracleStep B c x (useStage A c x) = some y := by
    rw [← oracleStep_congr_of_agree_below_use h hAB le_rfl]; exact hy
  have hBconv : Converges B c x := ⟨useStage A c x, by simp [hB]⟩
  have hBmem : y ∈ evalOracle B c x := by
    refine mem_evalOracle_iff.2 ⟨useStage A c x, hB, fun m hm => ?_⟩
    rw [← oracleStep_congr_of_agree_below_use h hAB (le_of_lt hm)]
    exact oracleStep_eq_none_of_lt_useStage h hm
  rw [Part.eq_some_iff.2 hBmem, evalOracle_eq_some_of_converges h hy]

/-- Agreement below the use preserves the use itself. -/
theorem use_eq_of_agree_below_use (h : Converges A c x) (hAB : ∀ n < use A c x, A n = B n) :
    use B c x = use A c x := by
  have hstep : ∀ s ≤ useStage A c x, oracleStep A c x s = oracleStep B c x s := fun s hs =>
    oracleStep_congr_of_agree_below_use h hAB hs
  have hBsome : (oracleStep B c x (useStage A c x)).isSome := by
    rw [← hstep _ le_rfl]; exact isSome_oracleStep_useStage h
  have hBconv : Converges B c x := ⟨useStage A c x, hBsome⟩
  have hle : useStage B c x ≤ useStage A c x := useStage_le_of_isSome hBconv hBsome
  have hge : useStage A c x ≤ useStage B c x := by
    by_contra hcon
    push Not at hcon
    have hnone : oracleStep B c x (useStage B c x) = none := by
      rw [← hstep _ (le_of_lt hcon)]
      exact oracleStep_eq_none_of_lt_useStage h hcon
    have hsome := isSome_oracleStep_useStage hBconv
    rw [hnone] at hsome
    exact absurd hsome (by simp)
  rw [use_eq_succ hBconv, use_eq_succ h, le_antisymm hle hge]

/-- The use is *monotone* in the sense a construction needs: an oracle that respects the use of a
converging computation keeps the computation and does not raise its use. -/
theorem use_mono_of_agree (h : Converges A c x) (hAB : ∀ n < use A c x, A n = B n) :
    use B c x ≤ use A c x :=
  le_of_eq (use_eq_of_agree_below_use h hAB)

end Oracle
end Lambda
