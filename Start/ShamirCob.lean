/-
**One step of the verifier of Shamir's protocol as Cobham terms** (task-board row
`M21-VERIFIER-STEP-COB`).

The machine `Complexity.Shamir.stepW` of `Start/ShamirMachine.lean` works on eight words.  This
module writes its step as eight Cobham terms of those words and of the parameters `1^p`, `1^N`,
`1^d` (`Complexity.Shamir.stepTs`), proved to compute the step on **every** state
(`Complexity.Shamir.eval_stepTs`) — no invariant is needed for the step itself; the invariant of
`Start/ShamirBound.lean` is only needed to bound the length of the states.

The step is a selection, by the number of the branch of `stepW` taken
(`Complexity.Shamir.caseW`, computed in unary by `Complexity.Shamir.caseT`), among the terms
computing each branch.

Main definitions:

* word terms: `Complexity.Cob.recGetT`, `.recSkipT`, `.encMsgT` (records),
  `Complexity.Cob.dropFsU`, `.fieldAtU`, `.setFieldU` (unary fields at a unary position),
  `Complexity.Cob.trimT` (a message normalised);
* `Complexity.Shamir.caseW`, `Complexity.Shamir.branchW` — the branches of the step;
* `Complexity.Shamir.caseT`, `Complexity.Shamir.stepTs` — the step as Cobham terms.

Main results:

* `Complexity.Shamir.stepW_eq_branch` — the step is its branch;
* `Complexity.Shamir.eval_caseT` — the branch number is a Cobham function;
* `Complexity.Shamir.eval_stepTs` — **the eight terms compute the step**.
-/

import Start.ShamirBound
import Start.QbfEvalCob

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Complexity.Shamir

/-! ### Word terms -/

/-- The content of the first record. -/
def Cob.recGetT (t : Cob) : Cob :=
  Cob.takeBy (.comp Cob.leadOnes [t]) (Cob.dropBy (.comp (.app true) [.comp Cob.leadOnes [t]]) t)

@[simp] theorem Cob.eval_recGetT (t : Cob) (args : List Word) :
    (Cob.recGetT t).eval args = recGet (t.eval args) := by
  simp [Cob.recGetT, Cob.eval_takeBy, recGet]

/-- The rest after the first record. -/
def Cob.recSkipT (t : Cob) : Cob :=
  Cob.dropBy (.comp (.app true) [.comp Cob.concat [.comp Cob.leadOnes [t], .comp Cob.leadOnes [t]]])
    t

@[simp] theorem Cob.eval_recSkipT (t : Cob) (args : List Word) :
    (Cob.recSkipT t).eval args = recSkip (t.eval args) := by
  simp [Cob.recSkipT, recSkip]; congr 1; omega

/-- The record of a word. -/
def Cob.encMsgT (t : Cob) : Cob := .comp Cob.concat [Cob.onesOf t, .comp (.app false) [t]]

@[simp] theorem Cob.eval_encMsgT (t : Cob) (args : List Word) :
    (Cob.encMsgT t).eval args = encMsg (t.eval args) := by
  simp [Cob.encMsgT, encMsg]

/-- The concatenation of two terms. -/
def Cob.catT (t u : Cob) : Cob := .comp Cob.concat [t, u]

@[simp] theorem Cob.eval_catT (t u : Cob) (args : List Word) :
    (Cob.catT t u).eval args = t.eval args ++ u.eval args := by
  simp [Cob.catT]

/-- Dropping the first unary field. -/
def Cob.dropFT (t : Cob) : Cob := .comp Cob.tail [.comp Cob.dropOnes [t]]

@[simp] theorem Cob.eval_dropFT (t : Cob) (args : List Word) :
    (Cob.dropFT t).eval args = dropF (t.eval args) := by
  simp [Cob.dropFT, dropF]

theorem dropFs_succ' (i : ℕ) (A : Word) : dropFs (i + 1) A = dropF (dropFs i A) := by
  rw [dropFs_add]; rfl

/-- Dropping `|i|` unary fields of `A`, on `[i, A]`. -/
def Cob.dropFsR : Cob :=
  .bRec (.proj 0) (Cob.dropFT (.proj 1)) (Cob.dropFT (.proj 1)) (.proj 1)

theorem Cob.eval_dropFsR (A : Word) : ∀ i : Word, Cob.dropFsR.eval [i, A] = dropFs i.length A
  | [] => by simp [Cob.dropFsR, dropFs]
  | b :: i => by
      rw [Cob.dropFsR, Cob.eval_bRec_cons, ← Cob.dropFsR, Cob.eval_dropFsR A i]
      have hl : (dropF (dropFs i.length A)).length ≤ A.length :=
        (length_dropF_le _).trans (length_dropFs_le _ _)
      cases b <;>
      · simp only [Bool.false_eq_true, if_false, if_true, Cob.eval_dropFT, Cob.eval_proj,
          List.getD_cons_succ, List.getD_cons_zero, List.length_cons]
        rw [List.take_of_length_le hl, dropFs_succ']

/-- Dropping `|i|` unary fields. -/
def Cob.dropFsU (i t : Cob) : Cob := .comp Cob.dropFsR [i, t]

@[simp] theorem Cob.eval_dropFsU (i t : Cob) (args : List Word) :
    (Cob.dropFsU i t).eval args = dropFs (i.eval args).length (t.eval args) := by
  simp [Cob.dropFsU, Cob.eval_dropFsR]

/-- The unary field at position `|i|`, in unary. -/
def Cob.fieldAtU (i t : Cob) : Cob := .comp Cob.leadOnes [Cob.dropFsU i t]

@[simp] theorem Cob.eval_fieldAtU (i t : Cob) (args : List Word) :
    (Cob.fieldAtU i t).eval args = un (fieldAt (i.eval args).length (t.eval args)) := by
  simp [Cob.fieldAtU, fieldAt, un]

/-- Overwriting the field at position `|i|` with `s` (a unary word). -/
def Cob.setFieldU (i s t : Cob) : Cob :=
  Cob.catT (Cob.catT (Cob.takeBy (Cob.dropBy (Cob.dropFsU i t) t) t)
    (Cob.catT s (Cob.constT [false]))) (Cob.dropFsU (.comp (.app true) [i]) t)

theorem Cob.eval_setFieldU {i s t : Cob} {args : List Word} {x : ℕ}
    (hs : s.eval args = un x) :
    (Cob.setFieldU i s t).eval args = setField (i.eval args).length x (t.eval args) := by
  simp [Cob.setFieldU, Cob.eval_takeBy, setField, takeFs, hs]

/-- A message with its trailing ones removed. -/
def Cob.trimT (t : Cob) : Cob := .comp Cob.revTerm [.comp Cob.dropOnes [.comp Cob.revTerm [t]]]

@[simp] theorem Cob.eval_trimT (t : Cob) (args : List Word) :
    (Cob.trimT t).eval args = trimW (t.eval args) := by
  simp [Cob.trimT, trimW]

/-- The length of a word, in unary. -/
theorem Cob.eval_onesOf' (t : Cob) (args : List Word) :
    (Cob.onesOf t).eval args = un (t.eval args).length := by
  simp [un]

end Complexity

namespace Complexity.Shamir

open Complexity.Qbf

/-! ### The branches of the step -/

/-- The number of the branch of `stepW` taken from the state `s`: `0` halted, `1` a variable
accepted, `2` reject, `3` a negation, `4` a binary node accepted, `5` a linearization accepted,
`6` a quantifier accepted. -/
def caseW (p N d : ℕ) (s : St) : ℕ :=
  if s.H ≠ [] then 0 else
  if bit 0 s.C = false then
    if bit 1 s.C = false then
      if fieldAt (lead1 (s.C.drop 2)) s.A = s.V.length then 1 else 2
    else 3
  else
    if bit 1 s.C = false then
      if dropFs 2 (trimW (recGet s.T)) = [] ∧ dropFs 1 (trimW (recGet s.T)) ≠ [] ∧
          comb p (bit 2 s.C) (fieldAt 0 (trimW (recGet s.T)) % p)
            (fieldAt 1 (trimW (recGet s.T)) % p) = s.V.length then 4 else 2
    else
      if dropFs (d + 1) (trimW (recGet s.T)) ≠ [] then 2 else
      if s.J.length < N then
        if fadd p (fmul p (fieldAt s.J.length s.A) (hornerN 1 p (decF (recGet s.T))))
            (fmul p (fsub p 1 (fieldAt s.J.length s.A)) (hornerN 0 p (decF (recGet s.T)))) =
            s.V.length then 5 else 2
      else
        if comb p (bit 2 s.C) (hornerN 0 p (decF (recGet s.T)))
            (hornerN 1 p (decF (recGet s.T))) = s.V.length then 6 else 2

/-- The state after the branch `c`. -/
def branchW (p : ℕ) : ℕ → St → St
  | 0, s => s
  | 1, s => pop { s with C := (drop1 (s.C.drop 2)).tail }
  | 3, s => { s with V := un (fsub p 1 s.V.length), C := s.C.drop 2 }
  | 4, s =>
      { s with
        C := s.C.drop 3
        V := un (fieldAt 0 (trimW (recGet s.T)) % p)
        S := encMsg s.A ++ encMsg (un (fieldAt 1 (trimW (recGet s.T)) % p)) ++ s.S
        T := recSkip (recSkip s.T) }
  | 5, s =>
      { s with
        J := true :: s.J
        A := setField s.J.length ((recGet (recSkip s.T)).length % p) s.A
        V := un (hornerN ((recGet (recSkip s.T)).length % p) p (decF (recGet s.T)))
        T := recSkip (recSkip s.T) }
  | 6, s =>
      { s with
        C := (drop1 (s.C.drop 3)).tail
        J := []
        A := setField (lead1 (s.C.drop 3)) ((recGet (recSkip s.T)).length % p) s.A
        V := un (hornerN ((recGet (recSkip s.T)).length % p) p (decF (recGet s.T)))
        T := recSkip (recSkip s.T) }
  | _, s => rej s

/-- **The step is the branch selected by `caseW`.** -/
theorem stepW_eq_branch (p N d : ℕ) (s : St) : stepW p N d s = branchW p (caseW p N d s) s := by
  unfold stepW caseW
  split_ifs <;> rfl

theorem caseW_le (p N d : ℕ) (s : St) : caseW p N d s ≤ 6 := by
  unfold caseW; split_ifs <;> omega

/-! ### The terms -/

/-- The arguments of the step terms: the eight words of the state and `1^p`, `1^N`, `1^d`. -/
def encArgs (p N d : ℕ) (s : St) : List Word :=
  [s.C, s.J, s.A, s.V, s.S, s.B, s.T, s.H, un p, un N, un d]

/-- The eight words of a state. -/
def encSt (s : St) : List Word := [s.C, s.J, s.A, s.V, s.S, s.B, s.T, s.H]

def sC : Cob := .proj 0
def sJ : Cob := .proj 1
def sA : Cob := .proj 2
def sV : Cob := .proj 3
def sS : Cob := .proj 4
def sB : Cob := .proj 5
def sT : Cob := .proj 6
def sH : Cob := .proj 7
def sP : Cob := .proj 8
def sN : Cob := .proj 9
def sD : Cob := .proj 10

/-- The constant `1^c`. -/
def uC (c : ℕ) : Cob := Cob.constT (un c)

/-- The current message. -/
def msgT : Cob := Cob.trimT (Cob.recGetT sT)

/-- The current random point, reduced modulo `p`. -/
def ptT : Cob := Cob.modT (Cob.onesOf (Cob.recGetT (Cob.recSkipT sT))) sP

/-- The two values of a message at a binary node, reduced modulo `p`. -/
def f0T : Cob := Cob.modT (Cob.fieldAtU (uC 0) msgT) sP
def f1T : Cob := Cob.modT (Cob.fieldAtU (uC 1) msgT) sP

/-- The polynomial of the message at `0`, `1` and at the random point. -/
def h0T : Cob := Cob.polyEvalT msgT (uC 0) sP
def h1T : Cob := Cob.polyEvalT msgT (uC 1) sP
def hsT : Cob := Cob.polyEvalT msgT ptT sP

/-- `comb p (bit 2 C)` of two terms. -/
def combT (x y : Cob) : Cob :=
  Cob.iteT (Cob.nthBit 2 sC) (Cob.fSub (uC 1) (Cob.fMul (Cob.fSub (uC 1) x sP) (Cob.fSub (uC 1) y sP) sP) sP)
    (Cob.fMul x y sP)

/-- The coordinate `J` of the point. -/
def ajT : Cob := Cob.fieldAtU sJ sA

/-- The check at a variable. -/
def varChkT : Cob := Cob.eqU (Cob.fieldAtU (.comp Cob.leadOnes [Cob.dropBy (uC 2) sC]) sA) sV

/-- The check at a binary node (after the shape of the message). -/
def binChkT : Cob := Cob.eqU (combT f0T f1T) sV

/-- The check at a linearization. -/
def linChkT : Cob :=
  Cob.eqU (Cob.fAdd (Cob.fMul ajT h1T sP) (Cob.fMul (Cob.fSub (uC 1) ajT sP) h0T sP) sP) sV

/-- The check at a quantifier. -/
def quantChkT : Cob := Cob.eqU (combT h0T h1T) sV

/-- **The branch number, in unary.** -/
def caseT : Cob :=
  Cob.iteT sH (uC 0)
    (Cob.iteT (Cob.nthBit 0 sC)
      (Cob.iteT (Cob.nthBit 1 sC)
        (Cob.iteT (Cob.dropFsU (.comp (.app true) [sD]) msgT) (uC 2)
          (Cob.iteT (Cob.ltU sJ sN) (Cob.iteT linChkT (uC 5) (uC 2))
            (Cob.iteT quantChkT (uC 6) (uC 2))))
        (Cob.iteT (Cob.dropFsU (uC 2) msgT) (uC 2)
          (Cob.iteT (Cob.dropFsU (uC 1) msgT) (Cob.iteT binChkT (uC 4) (uC 2)) (uC 2))))
      (Cob.iteT (Cob.nthBit 1 sC) (uC 3) (Cob.iteT varChkT (uC 1) (uC 2))))

/-- The terms computing the state after each branch. -/
def branchTs : ℕ → List Cob
  | 0 => [sC, sJ, sA, sV, sS, sB, sT, sH]
  | 1 => [Cob.dropFT (Cob.dropBy (uC 2) sC), sJ, Cob.iteT sS (Cob.recGetT sS) sA,
      Cob.iteT sS (Cob.recGetT (Cob.recSkipT sS)) sV, Cob.iteT sS (Cob.recSkipT (Cob.recSkipT sS)) sS,
      sB, sT, Cob.iteT sS sH (uC 1)]
  | 3 => [Cob.dropBy (uC 2) sC, sJ, sA, Cob.fSub (uC 1) (Cob.onesOf sV) sP, sS, sB, sT, sH]
  | 4 => [Cob.dropBy (uC 3) sC, sJ, sA, f0T, Cob.catT (Cob.catT (Cob.encMsgT sA) (Cob.encMsgT f1T)) sS,
      sB, Cob.recSkipT (Cob.recSkipT sT), sH]
  | 5 => [sC, .comp (.app true) [sJ], Cob.setFieldU sJ ptT sA, hsT, sS, sB,
      Cob.recSkipT (Cob.recSkipT sT), sH]
  | 6 => [Cob.dropFT (Cob.dropBy (uC 3) sC), .empty,
      Cob.setFieldU (.comp Cob.leadOnes [Cob.dropBy (uC 3) sC]) ptT sA, hsT, sS, sB,
      Cob.recSkipT (Cob.recSkipT sT), sH]
  | _ => [sC, sJ, sA, sV, sS, uC 1, sT, uC 1]

/-- The `j`-th word of the next state. -/
def compT (j : ℕ) : Cob :=
  Cob.tableSel ((List.range 7).map fun c => (branchTs c).getD j .empty) caseT

/-- **The step of the verifier as eight Cobham terms.** -/
def stepTs : List Cob := (List.range 8).map compT

/-! ### Correctness of the terms -/

section Eval

variable {p : ℕ} (N d : ℕ) (s : St)

theorem bit_eq_getD (k : ℕ) (C : Word) : bit k C = C.getD k false := by
  rw [bit, headD_drop]

@[simp] theorem e_sC : sC.eval (encArgs p N d s) = s.C := by
  simp [sC, encArgs]
@[simp] theorem e_sJ : sJ.eval (encArgs p N d s) = s.J := by
  simp [sJ, encArgs]
@[simp] theorem e_sA : sA.eval (encArgs p N d s) = s.A := by
  simp [sA, encArgs]
@[simp] theorem e_sV : sV.eval (encArgs p N d s) = s.V := by
  simp [sV, encArgs]
@[simp] theorem e_sS : sS.eval (encArgs p N d s) = s.S := by
  simp [sS, encArgs]
@[simp] theorem e_sB : sB.eval (encArgs p N d s) = s.B := by
  simp [sB, encArgs]
@[simp] theorem e_sT : sT.eval (encArgs p N d s) = s.T := by
  simp [sT, encArgs]
@[simp] theorem e_sH : sH.eval (encArgs p N d s) = s.H := by
  simp [sH, encArgs]
@[simp] theorem e_sP : sP.eval (encArgs p N d s) = un p := by
  simp [sP, encArgs]
@[simp] theorem e_sN : sN.eval (encArgs p N d s) = un N := by
  simp [sN, encArgs]
@[simp] theorem e_sD : sD.eval (encArgs p N d s) = un d := by
  simp [sD, encArgs]
@[simp] theorem e_uC (c : ℕ) (args : List Word) : (uC c).eval args = un c := by simp [uC]

theorem un_eq (n : ℕ) : un n = List.replicate n true := rfl

@[simp] theorem e_msgT : msgT.eval (encArgs p N d s) = trimW (recGet s.T) := by
  simp [msgT]

variable (hp : 0 < p)
include hp

theorem e_ptT : ptT.eval (encArgs p N d s) = un ((recGet (recSkip s.T)).length % p) :=
  Cob.eval_modT hp (by simp) (by simp [un_eq])

theorem e_f0T : f0T.eval (encArgs p N d s) = un (fieldAt 0 (trimW (recGet s.T)) % p) :=
  Cob.eval_modT hp (by simp [un_eq]) (by simp [un_eq])

theorem e_f1T : f1T.eval (encArgs p N d s) = un (fieldAt 1 (trimW (recGet s.T)) % p) :=
  Cob.eval_modT hp (by simp [un_eq]) (by simp [un_eq])

theorem e_poly {xT : Cob} {x : ℕ} (hx : xT.eval (encArgs p N d s) = un x) :
    (Cob.polyEvalT msgT xT sP).eval (encArgs p N d s) = un (hornerN x p (decF (recGet s.T))) :=
  Cob.eval_polyEvalT hp (by simp [fieldsWord_decF]) hx (by simp [un_eq])

theorem e_h0T : h0T.eval (encArgs p N d s) = un (hornerN 0 p (decF (recGet s.T))) :=
  e_poly N d s hp (by simp)

theorem e_h1T : h1T.eval (encArgs p N d s) = un (hornerN 1 p (decF (recGet s.T))) :=
  e_poly N d s hp (by simp)

theorem e_hsT : hsT.eval (encArgs p N d s) =
    un (hornerN ((recGet (recSkip s.T)).length % p) p (decF (recGet s.T))) :=
  e_poly N d s hp (e_ptT N d s hp)

theorem e_combT {xT yT : Cob} {x y : ℕ} (hx : xT.eval (encArgs p N d s) = un x)
    (hy : yT.eval (encArgs p N d s) = un y) :
    (combT xT yT).eval (encArgs p N d s) = un (comb p (bit 2 s.C) x y) := by
  have h1 : (uC 1).eval (encArgs p N d s) = List.replicate 1 true := by simp [un_eq]
  have hP : sP.eval (encArgs p N d s) = List.replicate p true := by simp [un_eq]
  rw [combT, Cob.eval_iteW (Cob.eval_nthBit 2 sC _) rfl rfl, bit_eq_getD]
  simp only [e_sC]
  by_cases hb : s.C.getD 2 false = true
  · simp only [hb, if_true]
    exact Cob.eval_fSub hp h1 (Cob.eval_fMul hp (Cob.eval_fSub hp h1 hx hP)
      (Cob.eval_fSub hp h1 hy hP) hP) hP
  · simp only [Bool.not_eq_true] at hb
    simp only [hb]
    exact Cob.eval_fMul hp hx hy hP

omit hp in
theorem e_ajT : ajT.eval (encArgs p N d s) = un (fieldAt s.J.length s.A) := by
  simp [ajT]

omit hp in
theorem e_varChkT : varChkT.eval (encArgs p N d s) =
    bw (decide (fieldAt (lead1 (s.C.drop 2)) s.A = s.V.length)) := by
  simp [varChkT, Cob.eval_eqU]

theorem e_binChkT : binChkT.eval (encArgs p N d s) =
    bw (decide (comb p (bit 2 s.C) (fieldAt 0 (trimW (recGet s.T)) % p)
      (fieldAt 1 (trimW (recGet s.T)) % p) = s.V.length)) := by
  rw [binChkT, Cob.eval_eqU, e_combT N d s hp (e_f0T N d s hp) (e_f1T N d s hp)]
  simp

theorem e_linChkT : linChkT.eval (encArgs p N d s) =
    bw (decide (fadd p (fmul p (fieldAt s.J.length s.A) (hornerN 1 p (decF (recGet s.T))))
      (fmul p (fsub p 1 (fieldAt s.J.length s.A)) (hornerN 0 p (decF (recGet s.T)))) =
        s.V.length)) := by
  have h1 : (uC 1).eval (encArgs p N d s) = List.replicate 1 true := by simp [un_eq]
  have hP : sP.eval (encArgs p N d s) = List.replicate p true := by simp [un_eq]
  rw [linChkT, Cob.eval_eqU, Cob.eval_fAdd hp (Cob.eval_fMul hp (e_ajT N d s) (e_h1T N d s hp) hP)
    (Cob.eval_fMul hp (Cob.eval_fSub hp h1 (e_ajT N d s) hP) (e_h0T N d s hp) hP) hP]
  simp [fadd, fmul, fsub]

theorem e_quantChkT : quantChkT.eval (encArgs p N d s) =
    bw (decide (comb p (bit 2 s.C) (hornerN 0 p (decF (recGet s.T)))
      (hornerN 1 p (decF (recGet s.T))) = s.V.length)) := by
  rw [quantChkT, Cob.eval_eqU, e_combT N d s hp (e_h0T N d s hp) (e_h1T N d s hp)]
  simp

/-- **The branch number is computed by `caseT`.** -/
theorem eval_caseT : caseT.eval (encArgs p N d s) = un (caseW p N d s) := by
  simp only [caseT, Cob.eval_iteT_word, e_varChkT N d s, e_binChkT N d s hp,
    e_linChkT N d s hp, e_quantChkT N d s hp, Cob.eval_nthBit, e_sC, e_sH, Cob.eval_ltU, e_sJ,
    e_sN, Cob.eval_dropFsU, e_msgT, bw_eq_nil_iff, e_uC, e_sD, Cob.eval_comp, List.map_cons,
    List.map_nil, Cob.eval_app, List.getD_cons_zero, List.length_cons, length_un]
  unfold caseW
  simp only [bit_eq_getD]
  split_ifs <;> simp_all

theorem eval_branchTs : ∀ c, c ≤ 6 →
    (branchTs c).map (fun g => g.eval (encArgs p N d s)) = encSt (branchW p c s)
  | 0, _ => by simp [branchTs, branchW, encSt]
  | 1, _ => by
      have hP : sP.eval (encArgs p N d s) = List.replicate p true := by simp [un_eq]
      unfold branchTs branchW pop
      by_cases hS : s.S = []
      · simp [hS, Cob.eval_iteT_word, encSt, dropF, un]
      · simp [hS, Cob.eval_iteT_word, encSt, dropF]
  | 2, _ => by simp [branchTs, branchW, encSt, rej, un]
  | 3, _ => by
      have h1 : (uC 1).eval (encArgs p N d s) = List.replicate 1 true := by simp [un_eq]
      have hP : sP.eval (encArgs p N d s) = List.replicate p true := by simp [un_eq]
      simp only [branchTs, branchW, encSt, List.map_cons, List.map_nil]
      rw [Cob.eval_fSub (b := s.V.length) hp h1 (by simp) hP]
      simp [fsub, un_eq]
  | 4, _ => by
      simp only [branchTs, branchW, encSt, List.map_cons, List.map_nil, e_f0T N d s hp,
        Cob.eval_catT, Cob.eval_encMsgT, e_f1T N d s hp, Cob.eval_recSkipT]
      simp
  | 5, _ => by
      simp only [branchTs, branchW, encSt, List.map_cons, List.map_nil, e_hsT N d s hp,
        Cob.eval_setFieldU (e_ptT N d s hp), Cob.eval_recSkipT]
      simp
  | 6, _ => by
      simp only [branchTs, branchW, encSt, List.map_cons, List.map_nil, e_hsT N d s hp,
        Cob.eval_setFieldU (e_ptT N d s hp), Cob.eval_recSkipT]
      simp [dropF]
  | c + 7, h => by omega

/-- **The eight step terms compute the step of the verifier, on every state.** -/
theorem eval_stepTs :
    stepTs.map (fun g => g.eval (encArgs p N d s)) = encSt (stepW p N d s) := by
  have hc := eval_branchTs N d s hp (caseW p N d s) (caseW_le p N d s)
  rw [← stepW_eq_branch] at hc
  rw [← hc]
  have hlen : (branchTs (caseW p N d s)).length = 8 := by
    have := congrArg List.length hc
    simpa [encSt] using this
  apply List.ext_getElem (by simp [stepTs, hlen])
  intro j h₁ h₂
  have hj : j < 8 := by simpa [stepTs] using h₁
  simp only [stepTs, List.getElem_map, List.getElem_range, compT]
  rw [Cob.eval_tableSel _ caseT _ (caseW p N d s) (eval_caseT N d s hp)]
  have hle := caseW_le p N d s
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by omega)]

end Eval

end Complexity.Shamir
