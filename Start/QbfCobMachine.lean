/-
**The code of the whole reduction formula is written by a single Cobham term.**

The previous modules write the pieces: the two quantifier prefixes over the endpoint blocks
(`Start/QbfCobPrefix.lean`), the initial and accepting constraints (`Start/QbfCobInitAcc.lean`),
the levels of the midpoint recursion (`Start/QbfCobLevels.lean`), the block equality of the base
case (`Start/QbfCobEqBlock.lean`) and the step formula (`Start/QbfCobStep.lean`).  This module
concatenates them.  The depth of the recursion is a parameter, so the term written here is correct
for `Complexity.Qbf.QBF.machineFk` at every depth; the reduction instantiates it at a depth that
is a polynomial in the length of the input.

Main definitions:

* `Complexity.Qbf.QBF.machineParam`, `.machineTerm` — the parameter word and the term.

Main results:

* `Complexity.Qbf.QBF.enc_machineFk_stream` — the code of the reduction formula, piece by piece;
* `Complexity.Qbf.QBF.enc_machineFk_eval` — **the code of the reduction formula is the value of
  one Cobham term** at the input and the parameter word.
-/

import Mathlib
import Start.QbfCobLevels
import Start.QbfMachineDepth

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

open Complexity Complexity.Space

/-! ### The code, piece by piece -/

/-- **The code of the reduction formula at a given depth**: the two quantifier prefixes over the
endpoint blocks, the tag bits of the two conjunctions, the codes of the initial and accepting
constraints, one block per level of the midpoint recursion, and the code of the base case. -/
theorem enc_machineFk_stream (M : Machine) (x : List Bool) (s k : ℕ) :
    enc (machineFk M x s k)
      = (quantPrefixTerm [true, true, true] 4).eval
            [List.replicate (cfgWidth M x s) true, widthOffsetWord (cfgWidth M x s) 0]
        ++ (quantPrefixTerm [true, true, true] 4).eval
            [List.replicate (cfgWidth M x s) true,
              widthOffsetWord (cfgWidth M x s) (cfgWidth M x s)]
        ++ [true, false, false] ++ [true, false, false]
        ++ enc (initF M x s 0) ++ enc (accF M x s 1)
        ++ ((List.range k).flatMap fun j =>
              reachPre (cfgWidth M x s) (3 * j) (3 * j + 1) (3 * j + 2))
        ++ [true, false, true]
        ++ enc (eqBlock (cfgWidth M x s) (3 * k) (3 * k + 1))
        ++ enc (stepF M x s (3 * k) (3 * k + 1)) := by
  have hlevels : ((List.range k).flatMap fun j =>
      reachPre (cfgWidth M x s) (aAt 0 2 j) (bAt 1 2 j) (2 + 3 * j))
        = (List.range k).flatMap fun j =>
            reachPre (cfgWidth M x s) (3 * j) (3 * j + 1) (3 * j + 2) := by
    refine List.flatMap_congr ?_
    intro j _
    rw [aAt_zero_two, bAt_one_two, show 2 + 3 * j = 3 * j + 2 by omega]
  have hbase : enc (reachF (stepF M x s) (cfgWidth M x s) 0
      (aAt 0 2 k) (bAt 1 2 k) (2 + 3 * k))
        = [true, false, true] ++ enc (eqBlock (cfgWidth M x s) (3 * k) (3 * k + 1))
            ++ enc (stepF M x s (3 * k) (3 * k + 1)) := by
    rw [reachF_zero, aAt_zero_two, bAt_one_two, enc_disj]
    simp
  rw [machineFk, enc_exBits_eval, enc_exBits_eval, enc_conj, enc_conj,
    enc_reachF (stepF M x s) (cfgWidth M x s) k 0 1 2, hlevels, hbase]
  simp [List.append_assoc]

/-! ### The parameter word -/

/-- The fields of the parameter word of the whole reduction. -/
def machineFields (M : Machine) (x : List Bool) (s k : ℕ) : List ℕ :=
  [cfgWidth M x s, k, s, x.length, M.states, M.states + (x.length + 1),
    M.states + (x.length + 1) + s, 3 * k * cfgWidth M x s, 2 * cfgWidth M x s,
    3 * cfgWidth M x s, 4 * cfgWidth M x s, levelsPad (cfgWidth M x s) k]

/-- The parameter word of the whole reduction: its unary fields, then the input. -/
def machineParam (M : Machine) (x : List Bool) (s k : ℕ) : Word :=
  fieldsWord (machineFields M x s k) ++ x

/-! ### The term -/

/-- The parameter word a quantifier prefix over the block at offset zero expects. -/
def woT0 : Cob := Cob.catL [fldT 0, Cob.constT [false]]

/-- The parameter word a quantifier prefix over the block at offset `cfgWidth` expects. -/
def woTW : Cob := Cob.catL [fldT 0, Cob.constT [false], fldT 0]

/-- **The term writing the code of the whole reduction formula.** -/
def machineTerm (M : Machine) : Cob :=
  Cob.catL
    [.comp (quantPrefixTerm [true, true, true] 4) [fldT 0, woT0],
      .comp (quantPrefixTerm [true, true, true] 4) [fldT 0, woTW],
      Cob.constT [true, false, false],
      Cob.constT [true, false, false],
      .comp initTerm [.proj 0, Cob.fieldsT [fldT 0, constU 0, fldT 4, fldT 5, fldT 6, fldT 2]],
      .comp (accTerm M) [.proj 0,
        Cob.fieldsT [fldT 0, fldT 0, fldT 4, fldT 5, fldT 6, fldT 3, fldT 2]],
      .comp levelsT [fldT 1, Cob.fieldsT [fldT 1, fldT 0, fldT 8, fldT 9, fldT 10, fldT 11]],
      Cob.constT [true, false, true],
      .comp (eqBlockTerm 1 2 24)
        [fldT 0, Cob.fieldsT [fldT 0, fldT 7, Cob.uAdd (fldT 7) (fldT 0)]],
      Cob.constT (enc tt),
      .comp (stepTerm M) [.proj 0,
        Cob.catL
          [Cob.fieldsT [fldT 0, fldT 7, Cob.uAdd (fldT 7) (fldT 0), fldT 4, fldT 5, fldT 6,
              fldT 3, fldT 2],
            Cob.dropFieldsT 12 (.proj 1)]]]

/-- **The code of the reduction formula is the value of one Cobham term** at the input word and
the parameter word of the reduction. -/
theorem enc_machineFk_eval (M : Machine) (x : List Bool) (s k : ℕ) (hstates : 0 < M.states) :
    enc (machineFk M x s k) = (machineTerm M).eval [x, machineParam M x s k] := by
  set W := cfgWidth M x s with hW
  set as := machineFields M x s k with has
  have hlen : as.length = 12 := rfl
  have hfld : ∀ n, ∀ _ : n < 12, (fldT n).eval [x, machineParam M x s k]
      = List.replicate (as.getD n 0) true := by
    intro n hn
    exact eval_fldT_app n as (by omega) _ _
  have e0 : as.getD 0 0 = W := rfl
  have e1 : as.getD 1 0 = k := rfl
  have e2 : as.getD 2 0 = s := rfl
  have e3 : as.getD 3 0 = x.length := rfl
  have e4 : as.getD 4 0 = M.states := rfl
  have e5 : as.getD 5 0 = M.states + (x.length + 1) := rfl
  have e6 : as.getD 6 0 = M.states + (x.length + 1) + s := rfl
  have e7 : as.getD 7 0 = 3 * k * W := rfl
  have e8 : as.getD 8 0 = 2 * W := rfl
  have e9 : as.getD 9 0 = 3 * W := rfl
  have e10 : as.getD 10 0 = 4 * W := rfl
  have e11 : as.getD 11 0 = levelsPad W k := rfl
  have f0 : (fldT 0).eval [x, machineParam M x s k] = List.replicate W true := by
    rw [hfld 0 (by omega), e0]
  have f1 : (fldT 1).eval [x, machineParam M x s k] = List.replicate k true := by
    rw [hfld 1 (by omega), e1]
  -- the two quantifier prefixes
  have hwo0 : woT0.eval [x, machineParam M x s k] = widthOffsetWord W 0 := by
    simp only [woT0, Cob.eval_catL, List.map_cons, List.map_nil, f0, Cob.eval_constT,
      List.flatten_cons, List.flatten_nil, List.append_nil, widthOffsetWord]
    simp
  have hwoW : woTW.eval [x, machineParam M x s k] = widthOffsetWord W W := by
    simp only [woTW, Cob.eval_catL, List.map_cons, List.map_nil, f0, Cob.eval_constT,
      List.flatten_cons, List.flatten_nil, List.append_nil, widthOffsetWord]
    simp [List.append_assoc]
  -- the initial constraint
  have hinitP : (Cob.fieldsT [fldT 0, constU 0, fldT 4, fldT 5, fldT 6, fldT 2]).eval
      [x, machineParam M x s k] = initParam M x s 0 := by
    rw [initParam, show (0 : ℕ) * W = 0 from by ring]
    refine Cob.eval_fieldsT ?_
    exact .cons f0 (.cons (eval_constU 0 _) (.cons (by rw [hfld 4 (by omega), e4])
      (.cons (by rw [hfld 5 (by omega), e5]) (.cons (by rw [hfld 6 (by omega), e6])
        (.cons (by rw [hfld 2 (by omega), e2]) .nil)))))
  have hinit : (Cob.comp initTerm
      [.proj 0, Cob.fieldsT [fldT 0, constU 0, fldT 4, fldT 5, fldT 6, fldT 2]]).eval
        [x, machineParam M x s k] = enc (initF M x s 0) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, hinitP]
    exact (enc_initF_eval M x s 0 hstates _).symm
  -- the accepting constraint
  have haccP : (Cob.fieldsT [fldT 0, fldT 0, fldT 4, fldT 5, fldT 6, fldT 3, fldT 2]).eval
      [x, machineParam M x s k] = accParam M x s 1 := by
    rw [accParam, show (1 : ℕ) * W = W from by ring]
    refine Cob.eval_fieldsT ?_
    exact .cons f0 (.cons f0 (.cons (by rw [hfld 4 (by omega), e4])
      (.cons (by rw [hfld 5 (by omega), e5]) (.cons (by rw [hfld 6 (by omega), e6])
        (.cons (by rw [hfld 3 (by omega), e3]) (.cons (by rw [hfld 2 (by omega), e2]) .nil))))))
  have hacc : (Cob.comp (accTerm M)
      [.proj 0, Cob.fieldsT [fldT 0, fldT 0, fldT 4, fldT 5, fldT 6, fldT 3, fldT 2]]).eval
        [x, machineParam M x s k] = enc (accF M x s 1) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, haccP]
    exact (enc_accF_eval M x s 1 _).symm
  -- the levels of the recursion
  have hlevP : (Cob.fieldsT [fldT 1, fldT 0, fldT 8, fldT 9, fldT 10, fldT 11]).eval
      [x, machineParam M x s k] = levelsParam W k := by
    rw [levelsParam, levelsFields]
    refine Cob.eval_fieldsT ?_
    exact .cons f1 (.cons f0 (.cons (by rw [hfld 8 (by omega), e8])
      (.cons (by rw [hfld 9 (by omega), e9]) (.cons (by rw [hfld 10 (by omega), e10])
        (.cons (by rw [hfld 11 (by omega), e11]) .nil)))))
  have hlev : (Cob.comp levelsT
      [fldT 1, Cob.fieldsT [fldT 1, fldT 0, fldT 8, fldT 9, fldT 10, fldT 11]]).eval
        [x, machineParam M x s k]
      = (List.range k).flatMap fun j => reachPre W (3 * j) (3 * j + 1) (3 * j + 2) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, hlevP, f1]
    exact eval_levelsT W k (cfgWidth_pos M x s)
  -- the block equality of the base case
  have heqP : (Cob.fieldsT [fldT 0, fldT 7, Cob.uAdd (fldT 7) (fldT 0)]).eval
      [x, machineParam M x s k] = fieldsWord [W, 3 * k * W, (3 * k + 1) * W] := by
    have hsum : (3 * k + 1) * W = 3 * k * W + W := by ring
    rw [hsum]
    refine Cob.eval_fieldsT ?_
    exact .cons f0 (.cons (by rw [hfld 7 (by omega), e7])
      (.cons (Cob.eval_uAdd (by rw [hfld 7 (by omega), e7]) f0) .nil))
  have heq : (Cob.comp (eqBlockTerm 1 2 24)
      [fldT 0, Cob.fieldsT [fldT 0, fldT 7, Cob.uAdd (fldT 7) (fldT 0)]]).eval
        [x, machineParam M x s k] ++ enc tt = enc (eqBlock W (3 * k) (3 * k + 1)) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, heqP, f0]
    exact (enc_eqBlock_eval W (3 * k) (3 * k + 1)).symm
  -- the step formula of the base case
  have hstepP : (Cob.catL
      [Cob.fieldsT [fldT 0, fldT 7, Cob.uAdd (fldT 7) (fldT 0), fldT 4, fldT 5, fldT 6,
          fldT 3, fldT 2],
        Cob.dropFieldsT 12 (.proj 1)]).eval [x, machineParam M x s k]
      = stepParam M x s (3 * k) (3 * k + 1) := by
    have hx : (Cob.dropFieldsT 12 (.proj 1)).eval [x, machineParam M x s k] = x :=
      eval_dropFieldsT_app 12 as (by omega) _ _
    have hfields : (Cob.fieldsT [fldT 0, fldT 7, Cob.uAdd (fldT 7) (fldT 0), fldT 4, fldT 5,
        fldT 6, fldT 3, fldT 2]).eval [x, machineParam M x s k]
          = fieldsWord (stepFields M x s (3 * k) (3 * k + 1)) := by
      rw [stepFields]
      have hsum : (3 * k + 1) * W = 3 * k * W + W := by ring
      rw [hsum]
      refine Cob.eval_fieldsT ?_
      exact .cons f0 (.cons (by rw [hfld 7 (by omega), e7])
        (.cons (Cob.eval_uAdd (by rw [hfld 7 (by omega), e7]) f0)
          (.cons (by rw [hfld 4 (by omega), e4]) (.cons (by rw [hfld 5 (by omega), e5])
            (.cons (by rw [hfld 6 (by omega), e6]) (.cons (by rw [hfld 3 (by omega), e3])
              (.cons (by rw [hfld 2 (by omega), e2]) .nil)))))))
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, hfields, hx, List.flatten_cons,
      List.flatten_nil, List.append_nil]
    rw [stepParam]
  have hstep : (Cob.comp (stepTerm M) [.proj 0,
      Cob.catL
        [Cob.fieldsT [fldT 0, fldT 7, Cob.uAdd (fldT 7) (fldT 0), fldT 4, fldT 5, fldT 6,
            fldT 3, fldT 2],
          Cob.dropFieldsT 12 (.proj 1)]]).eval [x, machineParam M x s k]
      = enc (stepF M x s (3 * k) (3 * k + 1)) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, hstepP, Cob.eval_proj,
      List.getD_cons_zero]
    exact (enc_stepF_eval M x s (3 * k) (3 * k + 1)).symm
  rw [enc_machineFk_stream M x s k, ← hW]
  simp only [machineTerm, Cob.eval_catL, List.map_cons, List.map_nil, Cob.eval_comp,
    Cob.eval_constT, f0, hwo0, hwoW, hinit, hacc, hlev, hstep, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  rw [← heq]
  simp [List.append_assoc, f0]

end QBF

end Complexity.Qbf
