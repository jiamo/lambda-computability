/-
**Iterating a P-uniform family: the loop whose body is a circuit.**

The rules collected so far write the gate with identifier `c` of the `n`-th circuit out of
arithmetic on `c`: a finite-state control (`Complexity.codeUniform_blockLayer`) or a Euclidean
division (`Complexity.codeUniform_gridLayer`).  A compiler that unrolls a bounded recursion needs a
loop of a different kind: the body of the loop is not a fixed pattern of gates, it is a *circuit* —
the one compiled for the step of the recursion — and the loop stacks polynomially many copies of it,
each copy reading the outputs of the copy below.

This module supplies that rule.  `Complexity.Tseitin.iterC B D w k` is the circuit obtained by
stacking `k` copies of the *stage* `B` on top of the *base* `D`, the inputs of each copy rewired to
the topmost `w` gates of the stack below it; and

* `Complexity.Tseitin.state_iterC` — its topmost `w` gates carry the `k`-th iterate of the step
  function of the stage, and
* `Complexity.codeUniform_iterC` — **if the stage and the base are P-uniform families and the
  number of copies is a Cobham function of `1^n`, so is the stack.**

The uniformity proof is where the two preceding modules are used: the token of the gate to write is
copied off the description of the stage by `Complexity.CircCode.selTokTerm`, relocated by
`Complexity.CircCode.rerouteTerm`, and the tokens are long — a copy near the bottom of the stack
already refers to gates whose identifiers are polynomial in `n` — so the padded grid rule
`Complexity.codeUniform_gridLayerP` is what applies.

Main definitions:

* `Complexity.Tseitin.iterC` — the stack of copies;
* `Complexity.Tseitin.stepC` — the step function of a stage on the values of its `w` wires;
* `Complexity.Tseitin.stateC` — the values carried by the topmost `w` gates of the stack.

Main results:

* `Complexity.Tseitin.wf_iterC` — the stack is well formed;
* `Complexity.Tseitin.state_iterC` — **the stack iterates the step function of its stage**;
* `Complexity.Tseitin.out_iterC` — its output is the output of the stage on the iterated state;
* `Complexity.codeUniform_iterC` — **the stack of a P-uniform stage over a P-uniform base is
  P-uniform.**
-/

import Start.UniformSelect
import Start.UniformBool

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### The stack of copies -/

/-- The stack: `k` copies of the stage `B` on top of the base `D`, the circuit inputs of each copy
rewired to the topmost `w` gates of the stack below it. -/
def iterC (B D : Circuit) (w : ℕ) : ℕ → Circuit
  | 0 => D
  | j + 1 =>
      reroute (iterC B D w j).length ((iterC B D w j).length - w) B ++ iterC B D w j

@[simp] theorem iterC_zero (B D : Circuit) (w : ℕ) : iterC B D w 0 = D := rfl

theorem iterC_succ (B D : Circuit) (w j : ℕ) :
    iterC B D w (j + 1) =
      reroute (iterC B D w j).length ((iterC B D w j).length - w) B ++ iterC B D w j := rfl

theorem length_iterC (B D : Circuit) (w j : ℕ) :
    (iterC B D w j).length = D.length + j * B.length := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [iterC_succ, List.length_append, length_reroute, ih]
      ring

theorem le_length_iterC {B D : Circuit} {w : ℕ} (hw : w ≤ D.length) (j : ℕ) :
    w ≤ (iterC B D w j).length := by
  rw [length_iterC]
  omega

/-- **The stack is well formed.** -/
theorem wf_iterC {B D : Circuit} {w : ℕ} (hB : wf B) (hD : wf D) (hin : inpsLt w B)
    (hw : w ≤ D.length) : ∀ j, wf (iterC B D w j) := by
  intro j
  induction j with
  | zero => exact hD
  | succ j ih =>
      have hle : w ≤ (iterC B D w j).length := le_length_iterC hw j
      have hsub : (iterC B D w j).length - ((iterC B D w j).length - w) = w := by omega
      refine wf_reroute_append _ ih _ (by omega) B hB ?_
      rw [hsub]
      exact hin

/-! ### The state carried by the stack -/

/-- The values carried by the topmost `w` gates of a circuit. -/
def topVals (w : ℕ) (v : List Bool) : List Bool := v.drop (v.length - w)

/-- The step function of a stage: from the values of its `w` input wires, the values of its
topmost `w` gates. -/
def stepC (B : Circuit) (w : ℕ) (s : List Bool) : List Bool := topVals w (vals s B)

/-- The state of the stack after `j` copies: the values of its topmost `w` gates. -/
def stateC (x : Word) (B D : Circuit) (w j : ℕ) : List Bool :=
  topVals w (vals x (iterC B D w j))

theorem vals_iterC_succ {B D : Circuit} {w : ℕ} (hB : wf B) (hin : inpsLt w B)
    (hw : w ≤ D.length) (x : Word) (j : ℕ) :
    vals x (iterC B D w (j + 1)) =
      vals x (iterC B D w j) ++ vals (stateC x B D w j) B := by
  have hle : w ≤ (iterC B D w j).length := le_length_iterC hw j
  have hsub : (iterC B D w j).length - ((iterC B D w j).length - w) = w := by omega
  have hlen : (vals x (iterC B D w j)).length = (iterC B D w j).length := by simp
  rw [iterC_succ, vals_reroute_append x _ _ (by omega) B hB (by rw [hsub]; exact hin)]
  congr 2
  rw [stateC, topVals, hlen]

/-- **The stack iterates the step function of its stage**: the topmost `w` gates of the stack of
`j + 1` copies carry the step function applied to the state of the stack of `j` copies. -/
theorem stateC_succ {B D : Circuit} {w : ℕ} (hB : wf B) (hin : inpsLt w B) (hw : w ≤ D.length)
    (hwB : w ≤ B.length) (x : Word) (j : ℕ) :
    stateC x B D w (j + 1) = stepC B w (stateC x B D w j) := by
  have hlen : (vals x (iterC B D w j)).length = (iterC B D w j).length := by simp
  have hlenB : (vals (stateC x B D w j) B).length = B.length := by simp
  rw [stateC, vals_iterC_succ hB hin hw x j, topVals, stepC, topVals, hlenB]
  have hL : (vals x (iterC B D w j) ++ vals (stateC x B D w j) B).length
      = (iterC B D w j).length + B.length := by
    rw [List.length_append, hlen, hlenB]
  rw [hL]
  have hsplit : (iterC B D w j).length + B.length - w
      = (vals x (iterC B D w j)).length + (B.length - w) := by
    rw [hlen]
    omega
  rw [hsplit, List.drop_append]
  simp

/-- **The state of the stack of `k` copies is the `k`-th iterate of the step function.** -/
theorem state_iterC {B D : Circuit} {w : ℕ} (hB : wf B) (hin : inpsLt w B) (hw : w ≤ D.length)
    (hwB : w ≤ B.length) (x : Word) (k : ℕ) :
    stateC x B D w k = (stepC B w)^[k] (topVals w (vals x D)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [stateC_succ hB hin hw hwB x k, ih, Function.iterate_succ_apply']

/-- **The output of the stack** is the output of its stage, run on the state of the stack below
it. -/
theorem out_iterC {B D : Circuit} {w : ℕ} {g : Gate} {C : Circuit} (hB : B = g :: C)
    (hwf : wf B) (hin : inpsLt w B) (hw : w ≤ D.length) (x : Word) (j : ℕ) :
    out x (iterC B D w (j + 1)) = out (stateC x B D w j) B := by
  have hle : w ≤ (iterC B D w j).length := le_length_iterC hw j
  have hsub : (iterC B D w j).length - ((iterC B D w j).length - w) = w := by omega
  have hlen : (vals x (iterC B D w j)).length = (iterC B D w j).length := by simp
  subst hB
  rw [iterC_succ, out_reroute_append x _ _ (by omega) g C hwf (by rw [hsub]; exact hin)]
  congr 1
  rw [stateC, topVals, hlen]

theorem getD_drop (l : List Bool) (m i : ℕ) : (l.drop m).getD i false = l.getD (m + i) false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem out_eq_vals_last {C : Circuit} (x : Word) (h : C ≠ []) :
    out x C = (vals x C).getD (C.length - 1) false := by
  cases C with
  | nil => exact absurd rfl h
  | cons g C =>
      simp only [out, List.length_cons, Nat.add_sub_cancel, vals_cons_getD_length]

/-- **The output of the stack is the last entry of its state.** -/
theorem out_iterC_state {B D : Circuit} {w : ℕ} (hw : 0 < w) (hwD : w ≤ D.length) (x : Word)
    (k : ℕ) : out x (iterC B D w k) = (stateC x B D w k).getD (w - 1) false := by
  have hle : w ≤ (iterC B D w k).length := le_length_iterC hwD k
  have hne : iterC B D w k ≠ [] := by
    intro h
    rw [h] at hle
    simp only [List.length_nil] at hle
    omega
  have hlen : (vals x (iterC B D w k)).length = (iterC B D w k).length := by simp
  rw [out_eq_vals_last x hne, stateC, topVals, hlen, getD_drop]
  congr 1
  omega

/-! ### The stack, laid out as a grid -/

/-- The stack without its base: `j` copies of the stage, the `i`-th of them relocated by
`dlen + i * |B|`. -/
def iterTop (B : Circuit) (dlen w : ℕ) : ℕ → Circuit
  | 0 => []
  | j + 1 =>
      reroute (dlen + j * B.length) (dlen + j * B.length - w) B ++ iterTop B dlen w j

theorem iterC_eq_iterTop (B D : Circuit) (w j : ℕ) :
    iterC B D w j = iterTop B D.length w j ++ D := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [iterC_succ, length_iterC, ih, iterTop, List.append_assoc]

end Tseitin

namespace CircCode

open Complexity.Tseitin

/-- Cutting a layer in two. -/
theorem layer_add (f : ℕ → Gate) (a b : ℕ) :
    layer f (a + b) = layer (fun i => f (b + i)) a ++ layer f b := by
  induction a with
  | zero => simp [layer]
  | succ a ih =>
      have hab : a + 1 + b = (a + b) + 1 := by omega
      rw [hab, layer, ih, layer]
      congr 2
      omega

/-- **The stack, as a layer**: the gate with identifier `L * i + j` of the stack above the base is
the gate with identifier `j` of the stage, relocated for the `i`-th copy. -/
theorem iterTop_eq_layer (B : Circuit) (dlen w : ℕ) (hB : 0 < B.length) (k : ℕ) :
    iterTop B dlen w k
      = layer (fun c => Gate.rewire (dlen + (c / B.length) * B.length)
          (dlen + (c / B.length) * B.length - w) (gateId B (c % B.length))) (k * B.length) := by
  induction k with
  | zero => rw [Nat.zero_mul]; rfl
  | succ k ih =>
      have hsucc : (k + 1) * B.length = B.length + k * B.length := by ring
      rw [iterTop, ih, hsucc, layer_add]
      congr 1
      have hcong : ∀ i, i < B.length →
          Gate.rewire (dlen + ((k * B.length + i) / B.length) * B.length)
              (dlen + ((k * B.length + i) / B.length) * B.length - w)
              (gateId B ((k * B.length + i) % B.length))
            = Gate.rewire (dlen + k * B.length) (dlen + k * B.length - w) (gateId B i) := by
        intro i hi
        have hd : (k * B.length + i) / B.length = k := by
          rw [Nat.mul_comm k B.length, Nat.mul_add_div hB, Nat.div_eq_of_lt hi]
          omega
        have hm : (k * B.length + i) % B.length = i := by
          rw [Nat.mul_comm k B.length, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
        rw [hd, hm]
      rw [layer_congr hcong, map_gateId (Gate.rewire (dlen + k * B.length)
        (dlen + k * B.length - w))]
      rfl

/-! ### The fields of a gate of a well-formed circuit -/

theorem fld_gateId_le {m : ℕ} : ∀ {C : Circuit}, wf C → inpsLt m C → ∀ o : ℕ,
    fld1 (gateId C o) ≤ m + C.length ∧ fld2 (gateId C o) ≤ m + C.length
  | [], _, _, _ => by simp [gateId, fld1, fld2]
  | g :: C, hwf, hin, o => by
      obtain ⟨hg, hC⟩ := hwf
      obtain ⟨hig, hinC⟩ := inpsLt_of_cons hin
      have hrec := fld_gateId_le (C := C) hC hinC o
      rcases eq_or_ne o C.length with rfl | hne
      · rw [gateId_cons_self]
        simp only [List.length_cons]
        cases g with
        | inp i =>
            have : i < m := hig
            exact ⟨by simp only [fld1]; omega, by simp only [fld2]; omega⟩
        | cst b => exact ⟨by simp [fld1], by simp [fld2]⟩
        | neg r =>
            have : r < C.length := hg
            exact ⟨by simp only [fld1]; omega, by simp only [fld2]; omega⟩
        | conj r s =>
            have h1 : r < C.length := hg.1
            have h2 : s < C.length := hg.2
            exact ⟨by simp only [fld1]; omega, by simp only [fld2]; omega⟩
        | disj r s =>
            have h1 : r < C.length := hg.1
            have h2 : s < C.length := hg.2
            exact ⟨by simp only [fld1]; omega, by simp only [fld2]; omega⟩
      · rw [gateId_cons_of_ne hne]
        simp only [List.length_cons]
        omega

end CircCode

/-! ### The uniformity of the stack -/

/-- **The stack of a P-uniform stage over a P-uniform base is P-uniform.**  The number of copies is
computed in unary from the instance, as is the number of wires the copies pass to one another; the
token of a gate is copied off the description of the stage by
`Complexity.CircCode.selTokTerm` and relocated by `Complexity.CircCode.rerouteTerm`, and the copy a
gate belongs to is recovered from its identifier by the Euclidean division of the grid rule. -/
theorem codeUniform_iterC {cb cd : ℕ → Tseitin.Circuit} {k w : ℕ → ℕ}
    (hcb : CodeUniform cb) (hcd : CodeUniform cd)
    (hwf : ∀ n, Tseitin.wf (cb n)) (hinp : ∀ n, Tseitin.inpsLt (w n) (cb n))
    (hwb : ∀ n, w n ≤ (cb n).length) (hbne : ∀ n, 0 < (cb n).length)
    {kT wT : Cob} (hk : ∀ x : Word, kT.eval [x] = List.replicate (k x.length) true)
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true) :
    CodeUniform (fun n => Tseitin.iterC (cb n) (cd n) (w n) (k n)) := by
  classical
  obtain ⟨genB, hgenB⟩ := hcb
  obtain ⟨lenB, hlenB⟩ := exists_lenTerm ⟨genB, hgenB⟩
  obtain ⟨lenD, hlenD⟩ := exists_lenTerm hcd
  -- the sizes
  set L : ℕ → ℕ := fun n => (cb n).length with hL
  set Dl : ℕ → ℕ := fun n => (cd n).length with hDl
  set S : ℕ → ℕ := fun n => Dl n + (k n + 1) * L n with hS
  -- the parameter word: `1^n 0 1^{S n}`
  set pw : ℕ → Word := fun n => dmW n (S n) with hpw
  have hLd : ∀ n, L n = (cb n).length := fun _ => rfl
  have hDld : ∀ n, Dl n = (cd n).length := fun _ => rfl
  have hSd : ∀ n, S n = Dl n + (k n + 1) * L n := fun _ => rfl
  have hpwd : ∀ n, pw n = dmW n (S n) := fun _ => rfl
  -- the terms reading the parameter
  set nT : Cob := .comp Cob.leadOnes [.proj 3] with hnT
  set dT : Cob := .comp Cob.concat
    [.comp lenD [nT], .comp .smash [.proj 1, .comp lenB [nT]]] with hdT
  set eT : Cob := .comp Cob.dropU [.comp wT [nT], dT] with heT
  set packT : Cob := Cob.catL [dT, Cob.constT [false], eT] with hpackT
  set gblkT : Cob := .comp CircCode.rerouteTerm
    [.comp CircCode.selTokTerm [.comp genB [nT], .proj 2], packT] with hgblkT
  set tmpl : ℕ → ℕ → ℕ → Tseitin.Gate := fun n i j =>
    Tseitin.Gate.rewire (Dl n + i * L n) (Dl n + i * L n - w n)
      (CircCode.gateId (cb n) j) with htmpl
  -- the number of gates of the stack above the base, and the width of a copy
  set lenT : Cob := .comp .smash [Cob.proj 0, Cob.constT [true]] with hlenT
  have hlenTn : ∀ x : Word, lenT.eval [x] = List.replicate x.length true := by
    intro x; simp [hlenT]
  set sizeT : Cob := .comp Cob.concat
    [lenD, .comp .smash [.comp (.app true) [kT], lenB]] with hsizeT
  have hsizeTn : ∀ x : Word, sizeT.eval [x] = List.replicate (S x.length) true := by
    intro x
    simp only [hsizeT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat,
      Cob.eval_smash, Cob.eval_app, hlenD x, hlenB x, hk x, List.getD_cons_zero,
      List.getD_cons_succ, List.length_replicate, List.length_cons, ← List.replicate_add]
    rw [hS, hDl, hL]
  set padT : Cob := Cob.catL [lenT, Cob.constT [false], sizeT] with hpadT
  have hpadTn : ∀ x : Word, padT.eval [x] = pw x.length := by
    intro x
    simp only [hpadT, Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, Cob.eval_constT, hlenTn x, hsizeTn x]
    simp [hpw, dmW]
  -- the parameter readers
  have hnTn : ∀ (n i j : ℕ) (y : Word),
      nT.eval [y, List.replicate i true, List.replicate j true, pw n]
        = List.replicate n true := by
    intro n i j y
    simp only [hnT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_leadOnes,
      Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero]
    rw [hpw, lead1_dmW]
  have hdTn : ∀ (n i j : ℕ) (y : Word),
      dT.eval [y, List.replicate i true, List.replicate j true, pw n]
        = List.replicate (Dl n + i * L n) true := by
    intro n i j y
    have hb : lenB.eval [List.replicate n true] = List.replicate (L n) true := by
      rw [hlenB (List.replicate n true), List.length_replicate]
    have hd : lenD.eval [List.replicate n true] = List.replicate (Dl n) true := by
      rw [hlenD (List.replicate n true), List.length_replicate]
    simp only [hdT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat,
      Cob.eval_smash, Cob.eval_proj, List.getD_cons_zero, List.getD_cons_succ,
      hnTn n i j y, hb, hd, List.length_replicate, ← List.replicate_add]
  have heTn : ∀ (n i j : ℕ) (y : Word),
      eT.eval [y, List.replicate i true, List.replicate j true, pw n]
        = List.replicate (Dl n + i * L n - w n) true := by
    intro n i j y
    have hw : wT.eval [List.replicate n true] = List.replicate (w n) true := by
      rw [hwT (List.replicate n true), List.length_replicate]
    simp only [heT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_dropU,
      hnTn n i j y, hw, hdTn n i j y, List.length_replicate, List.drop_replicate]
  have hpackTn : ∀ (n i j : ℕ) (y : Word),
      packT.eval [y, List.replicate i true, List.replicate j true, pw n]
        = CircCode.packDE (Dl n + i * L n) (Dl n + i * L n - w n) := by
    intro n i j y
    simp only [hpackT, Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, Cob.eval_constT, hdTn n i j y, heTn n i j y]
    simp [CircCode.packDE]
  -- the gate-writing term
  have hgblkTn : ∀ (n i j : ℕ) (y : Word), j < L n →
      gblkT.eval [y, List.replicate i true, List.replicate j true, pw n]
        = CircCode.encGate (tmpl n i j) := by
    intro n i j y hj
    have hgen : (Cob.comp genB [nT]).eval
        [y, List.replicate i true, List.replicate j true, pw n]
          = CircCode.encCirc (cb n) := by
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, hnTn n i j y]
      rw [hgenB (List.replicate n true), List.length_replicate]
    have hsel : (Cob.comp CircCode.selTokTerm [.comp genB [nT], Cob.proj 2]).eval
        [y, List.replicate i true, List.replicate j true, pw n]
          = CircCode.encCirc [CircCode.gateId (cb n) j] := by
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
        List.getD_cons_succ, List.getD_cons_zero, hgen]
      rw [CircCode.eval_selTokTerm_lt (C := cb n) (o := j) hj, CircCode.encCirc, CircCode.encCirc,
        List.append_nil]
    simp only [hgblkT, Cob.eval_comp, List.map_cons, List.map_nil, hsel, hpackTn n i j y]
    rw [CircCode.eval_rerouteTerm, Tseitin.reroute, List.map_cons, List.map_nil,
      CircCode.encCirc, CircCode.encCirc, List.append_nil, htmpl]
  -- the width and the count of the grid
  have hwidT : ∀ n : ℕ, (Cob.comp lenB [.comp Cob.leadOnes [.proj 0]]).eval [pw n]
      = List.replicate (L n) true := by
    intro n
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_leadOnes, Cob.eval_proj,
      List.getD_cons_zero]
    rw [hpw, lead1_dmW, hlenB (List.replicate n true), List.length_replicate]
  have hcntT : ∀ x : Word, (Cob.comp .smash [kT, lenB]).eval [x]
      = List.replicate (k x.length * L x.length) true := by
    intro x
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, hk x, hlenB x,
      List.getD_cons_zero, List.getD_cons_succ, List.length_replicate, hLd]
  -- the size bound
  have hbnd : ∀ n i j l : ℕ, j < L n → L n * i + j ≤ l →
      (CircCode.encGate (tmpl n i j)).length ≤ 11 * (l + (pw n).length + 1) := by
    intro n i j l hj hl
    have hLn := hLd n
    have hDn := hDld n
    have hSn := hSd n
    have hfl := CircCode.fld_gateId_le (hwf n) (hinp n) j
    have h1 : CircCode.fld1 (tmpl n i j) ≤ w n + L n + (Dl n + i * L n) + (Dl n + i * L n) := by
      refine le_trans (CircCode.fld1_rewire _ _ _) ?_
      have := hfl.1
      omega
    have h2 : CircCode.fld2 (tmpl n i j)
        ≤ 2 * (w n + L n) + (Dl n + i * L n) + (Dl n + i * L n) := by
      refine le_trans (CircCode.fld2_rewire _ _ _) ?_
      have ha := hfl.1
      have hb := hfl.2
      omega
    have ht := (CircCode.tag_le (tmpl n i j)).2
    have hcomm : i * L n = L n * i := Nat.mul_comm _ _
    have hil : i * L n ≤ l := by omega
    have hwL : w n ≤ L n := by rw [hLn]; exact hwb n
    have hmul : L n ≤ (k n + 1) * L n := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have hSl : L n ≤ S n := by omega
    have hDS : Dl n ≤ S n := by omega
    have hplen : (pw n).length = n + S n + 1 := by rw [hpwd n, length_dmW]
    rw [CircCode.length_encGate, hplen]
    omega
  -- the grid rule
  have hgrid : CodeUniform (fun n =>
      CircCode.layer (fun c => tmpl n (c / L n) (c % L n)) (k n * L n)) :=
    codeUniform_gridLayerP (K := 11) (w := L) (k := fun n => k n * L n) (pw := pw)
      (tmpl := tmpl) (gblk := gblkT) (cnt := .comp .smash [kT, lenB])
      (widT := .comp lenB [.comp Cob.leadOnes [.proj 0]]) (padT := padT)
      (fun n => hbne n) hcntT hpadTn hwidT hgblkTn hbnd
  have hfin := codeUniform_append hgrid hcd
  have heq : ∀ n, CircCode.layer (fun c => tmpl n (c / L n) (c % L n)) (k n * L n) ++ cd n
      = Tseitin.iterC (cb n) (cd n) (w n) (k n) := by
    intro n
    rw [Tseitin.iterC_eq_iterTop, CircCode.iterTop_eq_layer _ _ _ (hbne n)]
  simpa [funext heq] using hfin

end Complexity
