/-
**`TQBF` is in `PSPACE`.**

`Start/QbfEvalMachine.lean` gives a machine on words that decides `Complexity.Qbf.tqbfLang`, with
every component of every reachable state polynomially bounded in the length of the input.
`Start/CobhamIterate.lean` runs on a tape any iteration whose initial state and step are given by
Cobham terms.  This module joins the two: it writes the initial state and the step of the word
evaluator as Cobham terms, and concludes that `TQBF` is decided in polynomial space.

A state is laid out as six words, `[P, fieldsWord S, M, Sg, D, H]`
(`Complexity.Qbf.EvalW.encS`).  The step is a selection, by the case number of the step
(`Complexity.Qbf.EvalW.caseT`, a Cobham term computing `caseNum` in unary), among the terms
computing each case (`Complexity.Qbf.EvalW.stepTs`).

Main results:

* `Complexity.Qbf.EvalW.eval_stepT` — **the step terms compute the step of the evaluator**, on
  every state;
* `Complexity.Qbf.EvalW.cobIter_eq` — the iteration of the terms is the run of the evaluator;
* `Complexity.Qbf.tqbf_pspace` — **`TQBF ∈ PSPACE`**;
* `Complexity.Space.pspaceComplete_tqbfLang` (also `Complexity.Qbf.pspaceComplete_TQBF`) —
  **`TQBF` is `PSPACE`-complete**.
-/

import Mathlib
import Start.QbfEvalMachine
import Start.CobhamIterate
import Start.CobhamUnary
import Start.CobhamFieldsApp
import Start.CobhamTransducer
import Start.QbfHard

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### General term combinators -/

/-- `1^{|t|}`. -/
def Cob.onesOf (t : Cob) : Cob := .comp .smash [t, Cob.trueC]

@[simp] theorem Cob.eval_onesOf (t : Cob) (args : List Word) :
    (Cob.onesOf t).eval args = List.replicate (t.eval args).length true := by
  simp [Cob.onesOf]

/-- The conditional on whether a word is empty. -/
theorem Cob.eval_iteT_word (c s t : Cob) (args : List Word) :
    (Cob.iteT c s t).eval args = if c.eval args = [] then t.eval args else s.eval args := by
  simp [Cob.iteT]

/-- The value of `t` with its first `|u|` bits removed. -/
def Cob.dropBy (u t : Cob) : Cob := .comp Cob.dropU [u, t]

@[simp] theorem Cob.eval_dropBy (u t : Cob) (args : List Word) :
    (Cob.dropBy u t).eval args = (t.eval args).drop (u.eval args).length := by
  simp [Cob.dropBy]

/-- The first `|u|` bits of the value of `t`. -/
def Cob.takeBy (u t : Cob) : Cob :=
  .comp Cob.revTerm [Cob.dropBy (.comp Cob.dropN [u, Cob.onesOf t]) (.comp Cob.revTerm [t])]

theorem Cob.eval_takeBy (u t : Cob) (args : List Word) :
    (Cob.takeBy u t).eval args = (t.eval args).take (u.eval args).length := by
  simp only [Cob.takeBy, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_dropBy,
    Cob.eval_onesOf, Cob.eval_dropN, Cob.eval_revTerm, List.length_drop, List.length_replicate]
  set w := t.eval args
  set j := (u.eval args).length
  rw [List.reverse_drop, List.reverse_reverse, List.length_reverse]
  by_cases h : j ≤ w.length
  · congr 1; omega
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-- The value of `l` with its bit number `|j|` set to the bit computed by `b`. -/
def Cob.setBy (j b l : Cob) : Cob :=
  .comp Cob.concat [Cob.takeBy j l,
    Cob.iteT (Cob.ltU j l) (Cob.consT b (Cob.dropBy (.comp (.app true) [j]) l)) .empty]

theorem Cob.eval_setBy {j b l : Cob} {args : List Word} {p : Bool} (hb : b.eval args = bw p) :
    (Cob.setBy j b l).eval args = (l.eval args).set (j.eval args).length p := by
  rw [Cob.setBy, Cob.eval_comp]
  simp only [List.map_cons, List.map_nil, Cob.eval_concat, Cob.eval_takeBy]
  rw [Cob.eval_iteW (Cob.eval_ltU j l args) (Cob.eval_consT hb rfl) rfl,
    List.set_eq_take_append_cons_drop]
  simp only [Cob.eval_dropBy, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_app,
    List.getD_cons_zero, List.length_cons, Cob.eval_empty]
  split_ifs <;> simp_all

/-- A word of `|x| + 1` zeros, `x` the first argument. -/
def Cob.zerosT : Cob :=
  .bRec (Cob.constT [false]) (.comp (.app false) [.proj 1]) (.comp (.app false) [.proj 1])
    (.comp (.app true) [.proj 0])

theorem Cob.eval_zerosT (x : Word) (rest : List Word) :
    Cob.zerosT.eval (x :: rest) = List.replicate (x.length + 1) false := by
  induction x with
  | nil => simp [Cob.zerosT]
  | cons b x ih =>
      rw [Cob.zerosT, Cob.eval_bRec_cons, ← Cob.zerosT, ih]
      cases b <;> simp [List.replicate_succ]

theorem fieldsWord_eq_nil {as : List ℕ} : fieldsWord as = [] ↔ as = [] := by
  cases as <;> simp [fieldsWord]

/-- Reading a unary field, beyond the last one as well. -/
theorem Cob.eval_fieldTerm' : ∀ (k : ℕ) (t : Cob) (as : List ℕ) (args : List Word),
    t.eval args = fieldsWord as →
    (Cob.fieldTerm k t).eval args = List.replicate (as.getD k 0) true := by
  intro k
  induction k with
  | zero =>
      intro t as args ht
      cases as with
      | nil => simp [Cob.fieldTerm, ht, fieldsWord, lead1]
      | cons a as =>
          simp only [Cob.fieldTerm, Cob.eval_comp, List.map_cons, List.map_nil,
            Cob.eval_leadOnes, ht, lead1_fieldsWord]
          rfl
  | succ k ih =>
      intro t as args ht
      cases as with
      | nil =>
          have h' : (Cob.dropField t).eval args = fieldsWord [] := by
            simp [Cob.dropField, ht, fieldsWord, drop1]
          rw [Cob.fieldTerm, ih _ [] args h']
          simp
      | cons a as =>
          rw [Cob.fieldTerm, ih _ as args (Cob.eval_dropField t a as args ht)]
          rfl

/-- Dropping unary fields, beyond the last one as well. -/
theorem Cob.eval_dropFieldsT' : ∀ (k : ℕ) (t : Cob) (as : List ℕ) (args : List Word),
    t.eval args = fieldsWord as → (Cob.dropFieldsT k t).eval args = fieldsWord (as.drop k) := by
  intro k
  induction k with
  | zero => intro t as args ht; simpa [Cob.dropFieldsT] using ht
  | succ k ih =>
      intro t as args ht
      cases as with
      | nil =>
          have h' : (Cob.dropField t).eval args = fieldsWord [] := by
            simp [Cob.dropField, ht, fieldsWord, drop1]
          rw [Cob.dropFieldsT, ih _ [] args h']
          simp
      | cons a as =>
          rw [Cob.dropFieldsT, ih _ as args (Cob.eval_dropField t a as args ht)]
          rfl

theorem bw_eq_replicate (b : Bool) : bw b = List.replicate (Qbf.EvalW.bitN b) true := by
  cases b <;> rfl

namespace Qbf

namespace EvalW

open Complexity

/-! ### The layout and the terms -/

/-- A state of the evaluator as six words. -/
def encS (s : QS) : List Word := [s.P, fieldsWord s.S, s.M, s.Sg, s.D, s.H]

/-- The registers: the input and the six words of the state. -/
def qx : Cob := .proj 0
/-- The code still to be read. -/
def qP : Cob := .proj 1
/-- The stack. -/
def qF : Cob := .proj 2
/-- The mode. -/
def qM : Cob := .proj 3
/-- The assignment. -/
def qSg : Cob := .proj 4
/-- The bound variables. -/
def qD : Cob := .proj 5
/-- The halting flag. -/
def qH : Cob := .proj 6

/-- The constant `1^c`. -/
def cU (c : ℕ) : Cob := Cob.constT (List.replicate c true)

/-- `1^{bound |x|}`. -/
def boundT : Cob :=
  let u := Cob.pre (List.replicate 10 true) (.comp Cob.concat [Cob.onesOf qx, Cob.onesOf qx])
  .comp .smash [u, u]

/-- The stack has reached its bound. -/
def longT : Cob := Cob.leU boundT qF

/-- The case number of the step, in unary. -/
def caseT : Cob :=
  Cob.iteT qM
    (Cob.iteT qF
      (Cob.iteT (Cob.ltU (Cob.fieldTerm 0 qF) (cU 5)) (.comp Cob.concat [Cob.fieldTerm 0 qF, cU 6])
        (cU 0))
      (cU 5))
    (Cob.iteT (Cob.tailN 1 qP)
      (Cob.iteT (Cob.nthBit 0 qP)
        (Cob.iteT (Cob.tailN 2 qP)
          (Cob.iteT (Cob.nthBit 1 qP)
            (Cob.iteT (Cob.comp Cob.dropOnes [Cob.tailN 3 qP])
              (Cob.iteT longT (cU 0) (cU 4)) (cU 0))
            (Cob.iteT longT (cU 0) (cU 3)))
          (cU 0))
        (Cob.iteT (Cob.nthBit 1 qP)
          (Cob.iteT longT (cU 0) (cU 2))
          (Cob.iteT (Cob.comp Cob.dropOnes [Cob.tailN 2 qP])
            (Cob.iteT (Cob.bitU (Cob.comp Cob.leadOnes [Cob.tailN 2 qP]) qD) (cU 1) (cU 0))
            (cU 0))))
      (cU 0))

/-- `comb op v₁ v` on the fields `1` and `2` of the top record and the returned value. -/
def combT : Cob :=
  Cob.iteT (Cob.fieldTerm 1 qF)
    (Cob.orT (Cob.boolT (Cob.fieldTerm 2 qF)) (Cob.nthBit 0 qM))
    (Cob.andT (Cob.boolT (Cob.fieldTerm 2 qF)) (Cob.nthBit 0 qM))

/-- The terms of the default case: reject. -/
def stepTs0 : List Cob := [qP, qF, .empty, qSg, qD, .empty]

/-- The terms computing the step in each case. -/
def stepTs : ℕ → List Cob
  | 1 => [.comp Cob.tailC [.comp Cob.dropOnes [Cob.tailN 2 qP]], qF,
      Cob.consT (Cob.bitU (.comp Cob.leadOnes [Cob.tailN 2 qP]) qSg) .empty, qSg, qD, qH]
  | 2 => [Cob.tailN 2 qP, Cob.pre (fieldsWord [0, 0, 0, 0, 0, 0, 0]) qF, qM, qSg, qD, qH]
  | 3 => [Cob.tailN 3 qP,
      .comp Cob.concat [Cob.fieldsT [cU 1, Cob.nthBit 2 qP, .empty, .empty, .empty, .empty,
        .empty], qF], qM, qSg, qD, qH]
  | 4 =>
      let j := Cob.comp Cob.leadOnes [Cob.tailN 3 qP]
      let rest := Cob.comp Cob.tailC [.comp Cob.dropOnes [Cob.tailN 3 qP]]
      [rest,
        .comp Cob.concat [Cob.fieldsT [cU 3, Cob.nthBit 2 qP, .empty, j,
          .comp Cob.dropN [Cob.onesOf rest, Cob.onesOf qx], Cob.bitU j qSg, Cob.bitU j qD], qF],
        qM, Cob.setBy j .empty qSg, Cob.setBy j Cob.trueC qD, qH]
  | 5 => [qP, qF, Cob.andT (Cob.nthBit 0 qM) (.comp Cob.notC [qP]), qSg, qD, .empty]
  | 6 => [qP, Cob.dropFieldsT 7 qF, Cob.consT (Cob.notT (Cob.nthBit 0 qM)) .empty, qSg, qD, qH]
  | 7 => [qP, .comp Cob.concat [Cob.fieldsT [cU 2, Cob.fieldTerm 1 qF, Cob.nthBit 0 qM, .empty,
        .empty, .empty, .empty], Cob.dropFieldsT 7 qF], .empty, qSg, qD, qH]
  | 8 => [qP, Cob.dropFieldsT 7 qF, Cob.consT combT .empty, qSg, qD, qH]
  | 9 => [Cob.dropBy (Cob.fieldTerm 4 qF) qx,
      .comp Cob.concat [Cob.fieldsT [cU 4, Cob.fieldTerm 1 qF, Cob.nthBit 0 qM,
        Cob.fieldTerm 3 qF, Cob.fieldTerm 4 qF, Cob.fieldTerm 5 qF, Cob.fieldTerm 6 qF],
        Cob.dropFieldsT 7 qF],
      .empty, Cob.setBy (Cob.fieldTerm 3 qF) Cob.trueC qSg, qD, qH]
  | 10 => [qP, Cob.dropFieldsT 7 qF, Cob.consT combT .empty,
      Cob.setBy (Cob.fieldTerm 3 qF) (Cob.boolT (Cob.fieldTerm 5 qF)) qSg,
      Cob.setBy (Cob.fieldTerm 3 qF) (Cob.boolT (Cob.fieldTerm 6 qF)) qD, qH]
  | _ => stepTs0

/-- The `j`-th word of the next state. -/
def compT (j : ℕ) : Cob :=
  Cob.tableSel ((List.range 11).map fun c => (stepTs c).getD j .empty) caseT

/-- **The step of the evaluator as six Cobham terms.** -/
def stepT : List Cob := (List.range 6).map compT

/-- The initial state as six Cobham terms of the input. -/
def initT : List Cob := [.proj 0, .empty, .empty, Cob.zerosT, Cob.zerosT, Cob.constT [true]]

/-! ### Correctness -/

section Correct

variable (x : List Bool) (s : QS)

@[simp] theorem eval_qx : qx.eval (x :: encS s) = x := by
  simp [qx, encS]
@[simp] theorem eval_qP : qP.eval (x :: encS s) = s.P := by
  simp [qP, encS]
@[simp] theorem eval_qF : qF.eval (x :: encS s) = fieldsWord s.S := by
  simp [qF, encS]
@[simp] theorem eval_qM : qM.eval (x :: encS s) = s.M := by
  simp [qM, encS]
@[simp] theorem eval_qSg : qSg.eval (x :: encS s) = s.Sg := by
  simp [qSg, encS]
@[simp] theorem eval_qD : qD.eval (x :: encS s) = s.D := by
  simp [qD, encS]
@[simp] theorem eval_qH : qH.eval (x :: encS s) = s.H := by
  simp [qH, encS]

@[simp] theorem eval_cU (c : ℕ) (args : List Word) : (cU c).eval args = List.replicate c true := by
  simp [cU]

@[simp] theorem eval_field (k : ℕ) :
    (Cob.fieldTerm k qF).eval (x :: encS s) = List.replicate (s.S.getD k 0) true :=
  Cob.eval_fieldTerm' k qF s.S _ (eval_qF x s)

@[simp] theorem eval_drop7 : (Cob.dropFieldsT 7 qF).eval (x :: encS s) = fieldsWord (s.S.drop 7) :=
  Cob.eval_dropFieldsT' 7 qF s.S _ (eval_qF x s)

theorem eval_boundT : (boundT.eval (x :: encS s)).length = bound x.length := by
  simp [boundT, bound]; ring

@[simp] theorem eval_longT : longT.eval (x :: encS s) = bw (isLong x s) := by
  rw [longT, Cob.eval_leU, eval_boundT, eval_qF]; rfl

theorem eval_caseT : caseT.eval (x :: encS s) = List.replicate (caseNum x s) true := by
  obtain ⟨P, S, M, Sg, D, H⟩ := s
  simp only [caseT, Cob.eval_iteT_word]
  rcases M with _ | ⟨m, M⟩
  · rcases P with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨b2, r⟩⟩⟩ <;>
      simp [caseNum, Cob.eval_tailN, Cob.eval_nthBit, Cob.eval_bitU, bw] <;>
      split_ifs <;> simp_all
  · rcases S with _ | ⟨k, S⟩
    · simp [caseNum, fieldsWord]
    · by_cases hk : k < 5
      · simp [caseNum, Cob.eval_ltU, fieldsWord, hk, bw, List.replicate_add]
      · simp [caseNum, Cob.eval_ltU, fieldsWord, hk, bw]

theorem caseNum_le' : caseNum x s ≤ 10 := caseNum_le s

theorem eval_combT :
    combT.eval (x :: encS s) = bw (comb (s.S.getD 1 0) (s.S.getD 2 0) (s.M.headD false)) := by
  have hv : (Cob.boolT (Cob.fieldTerm 2 qF)).eval (x :: encS s) =
      bw (decide (s.S.getD 2 0 ≠ 0)) :=
    Cob.eval_boolT _ _ _ (by rw [eval_field]; simp)
  have hm : (Cob.nthBit 0 qM).eval (x :: encS s) = bw (s.M.headD false) := by
    rw [Cob.eval_nthBit, eval_qM]; cases s.M <;> rfl
  rw [combT, Cob.eval_iteT_word, eval_field, Cob.eval_andT hv hm, Cob.eval_orT hv hm, comb]
  simp only [List.replicate_eq_nil_iff]
  split_ifs <;> rfl

theorem eval_stepTs (c : ℕ) :
    (stepTs c).map (fun g => g.eval (x :: encS s)) = encS (stepAt x s c) := by
  have hm : (Cob.nthBit 0 qM).eval (x :: encS s) = bw (s.M.headD false) := by
    rw [Cob.eval_nthBit, eval_qM]; cases s.M <;> rfl
  match c with
  | 0 =>
      conv_rhs => simp only [stepAt, encS]
      simp [stepTs, stepTs0]
  | 1 =>
      conv_rhs => simp only [stepAt, encS]
      simp only [stepTs, List.map_cons, List.map_nil]
      rw [Cob.eval_consT (Cob.eval_bitU _ _ _) (Cob.eval_empty _)]
      simp [Cob.eval_tailN]
  | 2 =>
      conv_rhs => simp only [stepAt, encS]
      simp [stepTs, Cob.eval_tailN, fieldsWord]
  | 3 =>
      conv_rhs => simp only [stepAt, encS]
      simp only [stepTs, List.map_cons, List.map_nil, Cob.eval_comp]
      rw [Cob.eval_fieldsT (as := [1, bitN (s.P.getD 2 false), 0, 0, 0, 0, 0])
        (by simp [Cob.eval_nthBit, bw_eq_replicate])]
      simp [Cob.eval_tailN, fieldsWord]
  | 4 =>
      conv_rhs => simp only [stepAt, encS]
      simp only [stepTs, List.map_cons, List.map_nil, Cob.eval_comp]
      rw [Cob.eval_fieldsT (as := [3, bitN (s.P.getD 2 false), 0, lead1 (s.P.drop 3),
          x.length - (drop1 (s.P.drop 3)).tail.length,
          bitN (s.Sg.getD (lead1 (s.P.drop 3)) false), bitN (s.D.getD (lead1 (s.P.drop 3)) false)])
        (by simp [Cob.eval_nthBit, Cob.eval_bitU, Cob.eval_tailN, bw_eq_replicate]),
        Cob.eval_setBy (j := Cob.comp Cob.leadOnes [Cob.tailN 3 qP]) (b := .empty) (l := qSg)
          (p := false) (by simp [bw]),
        Cob.eval_setBy (j := Cob.comp Cob.leadOnes [Cob.tailN 3 qP]) (b := Cob.trueC) (l := qD)
          (p := true) (by simp [bw])]
      simp [Cob.eval_tailN, fieldsWord]
  | 5 =>
      conv_rhs => simp only [stepAt, encS]
      simp only [stepTs, List.map_cons, List.map_nil]
      rw [Cob.eval_andT (t := .comp Cob.notC [qP]) (q := s.P.isEmpty) hm
        (by cases h : s.P <;> simp [bw, h])]
      simp
  | 6 =>
      conv_rhs => simp only [stepAt, encS]
      simp only [stepTs, List.map_cons, List.map_nil]
      rw [Cob.eval_consT (Cob.eval_notT hm) (Cob.eval_empty _)]
      simp
  | 7 =>
      conv_rhs => simp only [stepAt, encS]
      simp only [stepTs, List.map_cons, List.map_nil, Cob.eval_comp]
      rw [Cob.eval_fieldsT (as := [2, s.S.getD 1 0, bitN (s.M.headD false), 0, 0, 0, 0])
        (by simp [hm, bw_eq_replicate])]
      simp [fieldsWord]
  | 8 =>
      conv_rhs => simp only [stepAt, encS]
      simp only [stepTs, List.map_cons, List.map_nil]
      rw [Cob.eval_consT (eval_combT x s) (Cob.eval_empty _)]
      simp
  | 9 =>
      conv_rhs => simp only [stepAt, encS]
      simp only [stepTs, List.map_cons, List.map_nil, Cob.eval_comp]
      rw [Cob.eval_fieldsT (as := [4, s.S.getD 1 0, bitN (s.M.headD false), s.S.getD 3 0,
          s.S.getD 4 0, s.S.getD 5 0, s.S.getD 6 0]) (by simp [hm, bw_eq_replicate]),
        Cob.eval_setBy (j := Cob.fieldTerm 3 qF) (b := Cob.trueC) (l := qSg) (p := true)
          (by simp [bw])]
      simp [fieldsWord]
  | 10 =>
      conv_rhs => simp only [stepAt, encS]
      simp only [stepTs, List.map_cons, List.map_nil]
      rw [Cob.eval_consT (eval_combT x s) (Cob.eval_empty _),
        Cob.eval_setBy (j := Cob.fieldTerm 3 qF) (b := Cob.boolT (Cob.fieldTerm 5 qF)) (l := qSg)
          (p := decide (s.S.getD 5 0 ≠ 0)) (Cob.eval_boolT _ _ _ (by simp)),
        Cob.eval_setBy (j := Cob.fieldTerm 3 qF) (b := Cob.boolT (Cob.fieldTerm 6 qF)) (l := qD)
          (p := decide (s.S.getD 6 0 ≠ 0)) (Cob.eval_boolT _ _ _ (by simp))]
      simp
  | c + 11 =>
      rw [show stepAt x s (c + 11) = ⟨s.P, s.S, [], s.Sg, s.D, []⟩ from rfl]
      change stepTs0.map _ = _
      conv_rhs => simp only [encS]
      simp [stepTs0]

/-- **The step terms compute the step of the evaluator**, on every state. -/
theorem eval_stepT : stepT.map (fun g => g.eval (x :: encS s)) = encS (qstep x s) := by
  have hc := eval_stepTs x s (caseNum x s)
  rw [← qstep] at hc
  rw [← hc]
  have hlen : (stepTs (caseNum x s)).length = 6 := by
    have := congrArg List.length hc
    simpa [encS] using this
  apply List.ext_getElem (by simp [stepT, hlen])
  intro j h₁ h₂
  have hj : j < 6 := by simpa [stepT] using h₁
  simp only [stepT, List.getElem_map, List.getElem_range, compT]
  rw [Cob.eval_tableSel _ caseT _ (caseNum x s) (eval_caseT x s)]
  have hle := caseNum_le' x s
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by omega)]

theorem eval_initT : initT.map (fun g => g.eval [x]) = encS (start x) := by
  simp [initT, start, encS, fieldsWord, Cob.eval_zerosT]

theorem length_initT : initT.length = 6 := rfl

theorem length_stepT : stepT.length = 6 := by simp [stepT]

end Correct

/-- **The iteration of the terms is the run of the evaluator.** -/
theorem cobIter_eq (x : List Bool) :
    ∀ k, Space.cobIter initT stepT x k = encS ((qstep x)^[k] (start x))
  | 0 => by rw [Space.cobIter, eval_initT]; rfl
  | k + 1 => by
      rw [Space.cobIter, cobIter_eq x k, eval_stepT, Function.iterate_succ_apply']

theorem polyBound_regBound : PolyBound regBound := by
  refine ⟨1000, 3, fun n => ?_⟩
  simp only [regBound, bound]
  have h1 : 1 ≤ n + 1 := by omega
  nlinarith [Nat.pow_le_pow_left h1 3, sq_nonneg (n + 1), Nat.zero_le n,
    Nat.mul_le_mul h1 h1]

theorem encS_bound {x : List Bool} {s : QS} (hs : Inv x s) :
    ∀ w ∈ encS s, w.length ≤ regBound x.length := by
  have hF := length_fieldsWord_le hs
  obtain ⟨hP, _, _, _, hM, hSg, hD, hH⟩ := hs
  have hPl := hP.length_le
  intro w hw
  simp only [encS, List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [regBound]
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

end EvalW

/-- **`TQBF` is decided in polynomial space.** -/
theorem tqbf_pspace : Space.PSPACE tqbfLang := by
  refine Space.pspace_of_cobIter EvalW.initT EvalW.stepT 6 5 2 tqbfLang EvalW.regBound
    EvalW.polyBound_regBound rfl EvalW.length_stepT (by norm_num) (by norm_num) (fun x => ?_)
  obtain ⟨t, ⟨T, hTH, hTt⟩, htH⟩ := EvalW.halts x
  refine ⟨T, fun k _ w hw => ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [EvalW.cobIter_eq] at hw
    exact EvalW.encS_bound (EvalW.inv_iterate x k) w hw
  · rw [EvalW.cobIter_eq]
    exact hTH k hk
  · rw [EvalW.cobIter_eq, hTt]
    exact htH
  · rw [EvalW.cobIter_eq, hTt, ← EvalW.accepts_iff]
    simp only [EvalW.encS, List.getD_cons_succ, List.getD_cons_zero]
    constructor
    · intro hM
      exact ⟨t, ⟨T, hTH, hTt⟩, htH, hM⟩
    · rintro ⟨t', ht', ht'H, ht'M⟩
      rwa [(EvalW.Steps.halt_unique ⟨T, hTH, hTt⟩ ht' htH ht'H)]

end Qbf

namespace Space

/-- **`TQBF` is `PSPACE`-complete.** -/
theorem pspaceComplete_tqbfLang : PSPACEComplete Complexity.Qbf.tqbfLang :=
  ⟨Complexity.Qbf.tqbf_pspace, pspaceHard_tqbfLang'⟩

end Space

namespace Qbf

/-- **`TQBF` is `PSPACE`-complete**, under the name used by the task board. -/
theorem pspaceComplete_TQBF : Space.PSPACEComplete tqbfLang := Space.pspaceComplete_tqbfLang

end Qbf

end Complexity
