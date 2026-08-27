/-
**Boolean combinations of P-uniform circuit families.**

`Start/UniformShift.lean` stacks one circuit on top of another without connecting them, and
`Start/UniformCompose.lean` feeds the values of the lower circuit into the *inputs* of the upper
one.  What is still missing from the algebra is the simplest connection of all: joining the two
*outputs* by one gate.  This module supplies it.

`Complexity.Tseitin.conjC C D` writes `C` on top of `D`, relocated as `Start/UniformShift.lean`
prescribes, and puts a single conjunction gate on top of the two outputs; `disjC` and `negC` are
the two other Boolean connectives.  The semantics is exactly what it should be — the composite
outputs the conjunction (disjunction, negation) of the outputs of its parts on the *same* circuit
input — and all three operations preserve P-uniformity: the extra gate refers to the two topmost
identifiers, which are read off the descriptions of the parts by the gate counter of
`Start/CircuitCode.lean`.

Main definitions:

* `Complexity.Tseitin.stackC` — one circuit on top of another, with the references relocated;
* `Complexity.Tseitin.negC`, `Complexity.Tseitin.conjC`, `Complexity.Tseitin.disjC` — the three
  Boolean combinations of circuits.

Main results:

* `Complexity.Tseitin.out_negC`, `Complexity.Tseitin.out_conjC`, `Complexity.Tseitin.out_disjC` —
  **the combinations compute the Boolean connectives of the outputs**;
* `Complexity.Tseitin.wf_negC`, `Complexity.Tseitin.wf_conjC`, `Complexity.Tseitin.wf_disjC` — and
  they are well formed;
* `Complexity.codeUniform_gate` — a one-gate family is P-uniform as soon as its tag is constant
  and its two fields are Cobham functions of `1^n` in unary;
* `Complexity.codeUniform_negC`, `Complexity.codeUniform_conjC`, `Complexity.codeUniform_disjC` —
  **the Boolean combinations of P-uniform families are P-uniform.**
-/

import Start.UniformCompose
import Start.UniformLoop

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### Stacking, and the two topmost values -/

/-- The circuit `C` written on top of `D`, its references relocated by the length of `D`. -/
def stackC (C D : Circuit) : Circuit := reloc D.length C ++ D

@[simp] theorem length_stackC (C D : Circuit) :
    (stackC C D).length = C.length + D.length := by
  simp [stackC]

theorem wf_stackC {C D : Circuit} (hC : wf C) (hD : wf D) : wf (stackC C D) :=
  wf_reloc_append D hD C hC

theorem vals_stackC (x : Word) {C : Circuit} (D : Circuit) (hC : wf C) :
    vals x (stackC C D) = vals x D ++ vals x C :=
  vals_reloc_append x D C hC

@[simp] theorem stackC_nil (D : Circuit) : stackC [] D = D := by
  simp [stackC, reloc]

/-- **Stacking does not disturb the upper circuit**: the stack outputs what `C` outputs. -/
theorem out_stackC (x : Word) (D : Circuit) {C : Circuit} (hC : wf C) (hCne : C ≠ []) :
    out x (stackC C D) = out x C := by
  cases C with
  | nil => exact absurd rfl hCne
  | cons g C => exact out_reloc_append x D g C hC

/-- The value of the topmost gate of a circuit is its output. -/
theorem vals_getD_out (x : Word) : ∀ {C : Circuit}, C ≠ [] →
    (vals x C).getD (C.length - 1) false = out x C
  | [], h => absurd rfl h
  | g :: C, _ => by
      have h := vals_cons_getD_length x g C
      simpa [out] using h

/-- The value carried by the identifier of the output of the upper circuit of a stack. -/
theorem vals_stackC_left (x : Word) {C D : Circuit} (hC : wf C) (hCne : C ≠ []) :
    (vals x (stackC C D)).getD (C.length + D.length - 1) false = out x C := by
  have hlen : (vals x D).length = D.length := by simp
  have hCpos : 0 < C.length := List.length_pos_iff.2 hCne
  rw [vals_stackC x D hC, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), ← List.getD_eq_getElem?_getD]
  have : C.length + D.length - 1 - (vals x D).length = C.length - 1 := by omega
  rw [this]
  exact vals_getD_out x hCne

/-- The value carried by the identifier of the output of the lower circuit of a stack. -/
theorem vals_stackC_right (x : Word) {C D : Circuit} (hC : wf C) (hDne : D ≠ []) :
    (vals x (stackC C D)).getD (D.length - 1) false = out x D := by
  have hlen : (vals x D).length = D.length := by simp
  have hDpos : 0 < D.length := List.length_pos_iff.2 hDne
  rw [vals_stackC x D hC, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
  exact vals_getD_out x hDne

/-! ### The three Boolean combinations -/

/-- The negation of a circuit. -/
def negC (C : Circuit) : Circuit := Gate.neg (C.length - 1) :: C

/-- The conjunction of two circuits, run on the same circuit input. -/
def conjC (C D : Circuit) : Circuit :=
  Gate.conj (C.length + D.length - 1) (D.length - 1) :: stackC C D

/-- The disjunction of two circuits, run on the same circuit input. -/
def disjC (C D : Circuit) : Circuit :=
  Gate.disj (C.length + D.length - 1) (D.length - 1) :: stackC C D

@[simp] theorem length_negC (C : Circuit) : (negC C).length = C.length + 1 := by
  simp [negC]

@[simp] theorem length_conjC (C D : Circuit) :
    (conjC C D).length = C.length + D.length + 1 := by
  simp [conjC]

@[simp] theorem length_disjC (C D : Circuit) :
    (disjC C D).length = C.length + D.length + 1 := by
  simp [disjC]

theorem out_negC (x : Word) {C : Circuit} (hCne : C ≠ []) :
    out x (negC C) = !(out x C) := by
  rw [negC, out, gateVal, vals_getD_out x hCne]

theorem out_conjC (x : Word) {C D : Circuit} (hC : wf C) (hCne : C ≠ []) (hDne : D ≠ []) :
    out x (conjC C D) = (out x C && out x D) := by
  rw [conjC, out, gateVal, vals_stackC_left x hC hCne, vals_stackC_right x hC hDne]

theorem out_disjC (x : Word) {C D : Circuit} (hC : wf C) (hCne : C ≠ []) (hDne : D ≠ []) :
    out x (disjC C D) = (out x C || out x D) := by
  rw [disjC, out, gateVal, vals_stackC_left x hC hCne, vals_stackC_right x hC hDne]

theorem wf_negC {C : Circuit} (hC : wf C) (hCne : C ≠ []) : wf (negC C) := by
  have hCpos : 0 < C.length := List.length_pos_iff.2 hCne
  exact ⟨by simpa [gateWf] using Nat.sub_lt hCpos Nat.one_pos, hC⟩

theorem wf_conjC {C D : Circuit} (hC : wf C) (hD : wf D) (hCne : C ≠ []) (hDne : D ≠ []) :
    wf (conjC C D) := by
  have hCpos : 0 < C.length := List.length_pos_iff.2 hCne
  have hDpos : 0 < D.length := List.length_pos_iff.2 hDne
  refine ⟨?_, wf_stackC hC hD⟩
  simp only [gateWf, length_stackC]
  omega

theorem wf_disjC {C D : Circuit} (hC : wf C) (hD : wf D) (hCne : C ≠ []) (hDne : D ≠ []) :
    wf (disjC C D) := by
  have hCpos : 0 < C.length := List.length_pos_iff.2 hCne
  have hDpos : 0 < D.length := List.length_pos_iff.2 hDne
  refine ⟨?_, wf_stackC hC hD⟩
  simp only [gateWf, length_stackC]
  omega

end Tseitin

/-! ### Uniformity of a single gate -/

/-- **The number of gates of a P-uniform family is a Cobham function of `1^n`**, written in
unary. -/
theorem exists_lenTerm {cf : ℕ → Tseitin.Circuit} (h : CodeUniform cf) :
    ∃ T : Cob, ∀ x : Word, T.eval [x] = List.replicate (cf x.length).length true := by
  obtain ⟨f, hf⟩ := h
  refine ⟨.comp (cntTerm 10 CircCode.dstate CircCode.cinc 1) [f], fun x => ?_⟩
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, hf x]
  rw [eval_cntTerm (by norm_num) CircCode.dstate_lt CircCode.cinc_le _ [],
    CircCode.rcnt_encCirc]

/-- **A one-gate family is P-uniform** as soon as its tag does not depend on `n` and its two
fields are written in unary by Cobham terms. -/
theorem codeUniform_gate {gf : ℕ → Tseitin.Gate} {t : ℕ} {aT bT : Cob}
    (ht : ∀ n, CircCode.tag (gf n) = t)
    (ha : ∀ x : Word, aT.eval [x] = List.replicate (CircCode.fld1 (gf x.length)) true)
    (hb : ∀ x : Word, bT.eval [x] = List.replicate (CircCode.fld2 (gf x.length)) true) :
    CodeUniform (fun n => [gf n]) := by
  refine ⟨CircCode.tokTerm t aT bT, fun x => ?_⟩
  have h := CircCode.eval_tokTerm (g := gf x.length) (aT := aT) (bT := bT) (args := [x])
    (ha x) (hb x)
  rw [ht x.length] at h
  rw [h]
  simp [CircCode.encCirc]

/-! ### Uniformity of the Boolean combinations -/

theorem codeUniform_negC {cf : ℕ → Tseitin.Circuit} (hf : CodeUniform cf) :
    CodeUniform (fun n => Tseitin.negC (cf n)) := by
  obtain ⟨lf, hlf⟩ := exists_lenTerm hf
  have hgate : CodeUniform (fun n => [Tseitin.Gate.neg ((cf n).length - 1)]) := by
    refine codeUniform_gate (t := 4) (aT := .comp Cob.tail [lf]) (bT := .empty)
      (fun _ => rfl) (fun x => ?_) (fun x => ?_)
    · simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_tail, hlf x]
      rw [List.tail_replicate]
      rfl
    · simp [CircCode.fld2]
  exact codeUniform_append hgate hf

theorem codeUniform_conjC {cf cg : ℕ → Tseitin.Circuit} (hf : CodeUniform cf)
    (hg : CodeUniform cg) : CodeUniform (fun n => Tseitin.conjC (cf n) (cg n)) := by
  obtain ⟨lf, hlf⟩ := exists_lenTerm hf
  obtain ⟨lg, hlg⟩ := exists_lenTerm hg
  have hgate : CodeUniform (fun n =>
      [Tseitin.Gate.conj ((cf n).length + (cg n).length - 1) ((cg n).length - 1)]) := by
    refine codeUniform_gate (t := 5)
      (aT := .comp Cob.tail [.comp Cob.concat [lf, lg]]) (bT := .comp Cob.tail [lg])
      (fun _ => rfl) (fun x => ?_) (fun x => ?_)
    · simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_tail, Cob.eval_concat,
        hlf x, hlg x, ← List.replicate_add]
      rw [List.tail_replicate]
      rfl
    · simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_tail, hlg x]
      rw [List.tail_replicate]
      rfl
  exact codeUniform_append hgate (codeUniform_stack hf hg)

theorem codeUniform_disjC {cf cg : ℕ → Tseitin.Circuit} (hf : CodeUniform cf)
    (hg : CodeUniform cg) : CodeUniform (fun n => Tseitin.disjC (cf n) (cg n)) := by
  obtain ⟨lf, hlf⟩ := exists_lenTerm hf
  obtain ⟨lg, hlg⟩ := exists_lenTerm hg
  have hgate : CodeUniform (fun n =>
      [Tseitin.Gate.disj ((cf n).length + (cg n).length - 1) ((cg n).length - 1)]) := by
    refine codeUniform_gate (t := 6)
      (aT := .comp Cob.tail [.comp Cob.concat [lf, lg]]) (bT := .comp Cob.tail [lg])
      (fun _ => rfl) (fun x => ?_) (fun x => ?_)
    · simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_tail, Cob.eval_concat,
        hlf x, hlg x, ← List.replicate_add]
      rw [List.tail_replicate]
      rfl
    · simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_tail, hlg x]
      rw [List.tail_replicate]
      rfl
  exact codeUniform_append hgate (codeUniform_stack hf hg)

end Complexity
