/-
**The levels of the midpoint recursion are swept by a single Cobham term.**

`Start/QbfWordStream.lean` writes the code of the reachability formula as one block per level of
the midpoint recursion, `Complexity.Qbf.QBF.reachPre`, and `Start/QbfCobLevel.lean` writes one such
block with a Cobham term.  What is left is the sweep: the level `j` uses the block indices
`3 * j`, `3 * j + 1`, `3 * j + 2`, so all six fields the block term expects are affine in `j` with
the common slope `3 * m`, and a single range sweep writes every level.

Main definitions:

* `Complexity.Qbf.QBF.levelsParam`, `.levelsT` — the parameter word and the term of the sweep.

Main results:

* `Complexity.Qbf.QBF.length_reachPre_le` — the block of a level is short;
* `Complexity.Qbf.QBF.eval_levelsT` — **all the levels of the recursion are written by one Cobham
  term**.
-/

import Mathlib
import Start.QbfCobLevel
import Start.QbfVarBound
import Start.QbfCobInitAcc

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

open Complexity

/-! ### The block of a level is short -/

theorem size_legsF (m a b t : ℕ) : (legsF m a b t).size = 40 * m + 19 := by
  simp only [legsF, size, size_eqBlock]
  ring

theorem varBound_legsF_le (m a b t : ℕ) (hm : 0 < m) (ha : a < t + 3) (hb : b < t + 3) :
    (legsF m a b t).varBound ≤ (t + 3) * m := by
  simp only [legsF, varBound, max_le_iff]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    exact varBound_eqBlock_le hm (by omega) (by omega)

/-- One of the three quantifier prefixes of a level is short. -/
theorem length_quantStream_le (tag : List Bool) (m c N : ℕ) (h3 : tag.length = 3)
    (hc : (c + 1) * m ≤ N) :
    ((List.range m).flatMap fun l => tag ++ unary (c * m + l)).length ≤ m * (N + 3) := by
  have hall : ∀ l ∈ List.range m, (tag ++ unary (c * m + l)).length ≤ N + 3 := by
    intro l hl
    have hl' : l < m := List.mem_range.1 hl
    have hlt : c * m + l < (c + 1) * m := by
      have hexp : (c + 1) * m = c * m + m := by ring
      omega
    simp only [List.length_append, h3, length_unary]
    omega
  have h := length_flatMap_le (List.range m) _ (N + 3) hall
  simpa using h

/-- **The block of one level of the recursion is short.** -/
theorem length_reachPre_le (m a b t : ℕ) (hm : 0 < m) (ha : a < t + 3) (hb : b < t + 3) :
    (reachPre m a b t).length
      ≤ 3 * (m * ((t + 3) * m + 3)) + 5 + (40 * m + 19) * ((t + 3) * m + 3) := by
  have hmono : ∀ c : ℕ, c + 1 ≤ t + 3 → (c + 1) * m ≤ (t + 3) * m := by
    intro c hc
    exact Nat.mul_le_mul_right _ hc
  have h1 := length_quantStream_le [true, true, true] m t ((t + 3) * m) rfl (hmono t (by omega))
  have h2 := length_quantStream_le [true, true, false] m (t + 1) ((t + 3) * m) rfl
    (hmono (t + 1) (by omega))
  have h3 := length_quantStream_le [true, true, false] m (t + 2) ((t + 3) * m) rfl
    (hmono (t + 2) (by omega))
  have hlegs : (enc (legsF m a b t)).length ≤ (40 * m + 19) * ((t + 3) * m + 3) := by
    have h := length_enc_le (legsF m a b t) ((t + 3) * m) (varBound_legsF_le m a b t hm ha hb)
    rwa [size_legsF] at h
  simp only [reachPre, List.length_append, List.length_cons, List.length_nil]
  omega

/-- The crude cubic bound the sweep uses for the block of a level. -/
theorem reachPre_bound_le (m t Q : ℕ) (hm : m ≤ Q) (ht : t + 3 ≤ Q) (hQ : 1 ≤ Q) :
    3 * (m * ((t + 3) * m + 3)) + 5 + (40 * m + 19) * ((t + 3) * m + 3) ≤ 256 * (Q * Q * Q) := by
  have hR : (t + 3) * m + 3 ≤ 4 * (Q * Q) := by nlinarith
  have h1 : 3 * (m * ((t + 3) * m + 3)) ≤ 12 * (Q * Q * Q) := by
    have := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hm hR)
    calc 3 * (m * ((t + 3) * m + 3)) ≤ 3 * (Q * (4 * (Q * Q))) := this
      _ = 12 * (Q * Q * Q) := by ring
  have h2 : (40 * m + 19) * ((t + 3) * m + 3) ≤ 236 * (Q * Q * Q) := by
    have := Nat.mul_le_mul (show 40 * m + 19 ≤ 59 * Q by omega) hR
    calc (40 * m + 19) * ((t + 3) * m + 3) ≤ (59 * Q) * (4 * (Q * Q)) := this
      _ = 236 * (Q * Q * Q) := by ring
  have hQ3 : 1 ≤ Q * Q * Q := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hQ hQ) hQ
    simpa using this
  set A := 3 * (m * ((t + 3) * m + 3)) with hA
  set B := (40 * m + 19) * ((t + 3) * m + 3) with hB
  set C := Q * Q * Q with hC
  omega

/-! ### The sweep -/

/-- The padding field of the sweep over levels. -/
def levelsPad (m k : ℕ) : ℕ := (m + 3 * k + 8) * (m + 3 * k + 8) * (m + 3 * k + 8)

/-- The fields of the parameter word of the sweep over levels: the number of levels, then the
multiples of the width the block term needs, then the padding. -/
def levelsFields (m k : ℕ) : List ℕ := [k, m, 2 * m, 3 * m, 4 * m, levelsPad m k]

/-- The parameter word of the sweep over levels. -/
def levelsParam (m k : ℕ) : Word := fieldsWord (levelsFields m k)

/-- The offset of the level `j`, `3 * m * j`, obtained by multiplying the index of the sweep with
the field holding `3 * m`. -/
def levelOffT : Cob := .comp .smash [.proj 0, fldT 3]

/-- The block of the sweep over levels. -/
def levelsBlockT : Cob :=
  .comp levelTerm
    [fldT 1,
      Cob.fieldsT
        [fldT 1, Cob.uAdd levelOffT (fldT 2), Cob.uAdd levelOffT (fldT 3),
          Cob.uAdd levelOffT (fldT 4), levelOffT, Cob.uAdd levelOffT (fldT 1)]]

/-- **The term sweeping the levels of the midpoint recursion.** -/
def levelsT : Cob := rangeEmitTerm levelsBlockT 256

theorem eval_levelsBlockT (m k j : ℕ) :
    levelsBlockT.eval [List.replicate j true, levelsParam m k]
      = reachPre m (3 * j) (3 * j + 1) (3 * j + 2) := by
  set as := levelsFields m k with has
  have hlen : as.length = 6 := rfl
  have hfld : ∀ n, ∀ _ : n < 6, (fldT n).eval [List.replicate j true, levelsParam m k]
      = List.replicate (as.getD n 0) true := by
    intro n hn
    exact eval_fldT n as (by omega) _
  have e1 : as.getD 1 0 = m := rfl
  have e2 : as.getD 2 0 = 2 * m := rfl
  have e3 : as.getD 3 0 = 3 * m := rfl
  have e4 : as.getD 4 0 = 4 * m := rfl
  have hoff : levelOffT.eval [List.replicate j true, levelsParam m k]
      = List.replicate (j * (3 * m)) true := by
    simp only [levelOffT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash,
      Cob.eval_proj, List.getD_cons_zero, List.getD_cons_succ, hfld 3 (by omega), e3,
      List.length_replicate]
  have hparam : (Cob.fieldsT
      [fldT 1, Cob.uAdd levelOffT (fldT 2), Cob.uAdd levelOffT (fldT 3),
        Cob.uAdd levelOffT (fldT 4), levelOffT, Cob.uAdd levelOffT (fldT 1)]).eval
        [List.replicate j true, levelsParam m k]
      = levelParam m (3 * j) (3 * j + 1) (3 * j + 2) := by
    have v0 : m = m := rfl
    have v1 : (3 * j + 2) * m = j * (3 * m) + 2 * m := by ring
    have v2 : (3 * j + 2 + 1) * m = j * (3 * m) + 3 * m := by ring
    have v3 : (3 * j + 2 + 2) * m = j * (3 * m) + 4 * m := by ring
    have v4 : 3 * j * m = j * (3 * m) := by ring
    have v5 : (3 * j + 1) * m = j * (3 * m) + m := by ring
    rw [levelParam, v1, v2, v3, v4, v5]
    refine Cob.eval_fieldsT ?_
    exact .cons (by rw [hfld 1 (by omega), e1])
      (.cons (Cob.eval_uAdd hoff (by rw [hfld 2 (by omega), e2]))
        (.cons (Cob.eval_uAdd hoff (by rw [hfld 3 (by omega), e3]))
          (.cons (Cob.eval_uAdd hoff (by rw [hfld 4 (by omega), e4]))
            (.cons hoff (.cons (Cob.eval_uAdd hoff (by rw [hfld 1 (by omega), e1])) .nil)))))
  simp only [levelsBlockT, Cob.eval_comp, List.map_cons, List.map_nil, hparam,
    hfld 1 (by omega), e1]
  exact (reachPre_eval m (3 * j) (3 * j + 1) (3 * j + 2)).symm

theorem lead1_levelsParam (m k : ℕ) : lead1 (levelsParam m k) = k := by
  simp [levelsParam, levelsFields]

theorem levelsPad_le_length (m k : ℕ) : levelsPad m k ≤ (levelsParam m k).length := by
  simp [levelsParam, levelsFields, fieldsWord]
  omega

/-- **All the levels of the midpoint recursion are written by one Cobham term.** -/
theorem eval_levelsT (m k : ℕ) (hm : 0 < m) :
    levelsT.eval [List.replicate k true, levelsParam m k]
      = (List.range k).flatMap fun j => reachPre m (3 * j) (3 * j + 1) (3 * j + 2) := by
  have hb : ∀ j : ℕ, j ≤ k →
      (reachPre m (3 * j) (3 * j + 1) (3 * j + 2)).length
        ≤ 256 * ((levelsParam m k).length + 1) := by
    intro j hj
    have h1 := length_reachPre_le m (3 * j) (3 * j + 1) (3 * j + 2) hm (by omega) (by omega)
    have h2 := reachPre_bound_le m (3 * j + 2) (m + 3 * k + 8) (by omega) (by omega) (by omega)
    have h3 : levelsPad m k ≤ (levelsParam m k).length := levelsPad_le_length m k
    have h4 : (m + 3 * k + 8) * (m + 3 * k + 8) * (m + 3 * k + 8) = levelsPad m k := rfl
    rw [h4] at h2
    have h5 : 256 * levelsPad m k ≤ 256 * ((levelsParam m k).length + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  exact eval_rangeEmitTerm levelsBlockT _ (levelsParam m k) (lead1_levelsParam m k)
    (fun j => eval_levelsBlockT m k j) hb

/-! ### The block indices of the recursion of the reduction -/

theorem aAt_zero_two (j : ℕ) : aAt 0 2 j = 3 * j := by
  cases j with
  | zero => rfl
  | succ j => simp only [aAt]; omega

theorem bAt_one_two (j : ℕ) : bAt 1 2 j = 3 * j + 1 := by
  cases j with
  | zero => rfl
  | succ j => simp only [bAt]; omega

end QBF

end Complexity.Qbf
