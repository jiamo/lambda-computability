/-
**Composing circuits, and composing P-uniform families.**

`Start/UniformShift.lean` puts one circuit on top of another without connecting them.  This module
connects them.  `Complexity.Tseitin.reroute d e C` relocates `C` by `d`, as before, but it also
*rewires* its circuit inputs: the input `i` of `C` becomes a reference to the gate `i + e` of the
circuit underneath.  So `reroute D.length e C ++ D` runs `C` on the word read off the values of the
gates `e, e + 1, …` of `D`: this is the composition of the two circuits.

As in the case of relocation, the rewriting is performed on *descriptions* by a single Cobham term,
this time with the pair of shifts packed into one parameter word, and the composition of two
P-uniform families is therefore again P-uniform.

Main definitions:

* `Complexity.Tseitin.Gate.rewire`, `Complexity.Tseitin.reroute` — the composition;
* `Complexity.Tseitin.inpsLt` — the inputs of the upper circuit are in range;
* `Complexity.CircCode.rerouteTerm` — the Cobham term that rewires a description.

Main results:

* `Complexity.Tseitin.vals_reroute_append`, `Complexity.Tseitin.out_reroute_append` — **the
  composed circuit runs the upper circuit on the values of the lower one**;
* `Complexity.Tseitin.wf_reroute_append` — and it is well formed;
* `Complexity.CircCode.eval_rerouteTerm` — **rewiring is a Cobham function of the description**;
* `Complexity.codeUniform_reroute`, `Complexity.codeUniform_compose` — **two P-uniform families may
  be composed.**
-/

import Start.UniformShift

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### Rewiring -/

/-- Rewiring a gate: every reference to a gate is increased by `d`, and the circuit input `i`
becomes a reference to the gate `i + e`, read through a conjunction with itself. -/
def Gate.rewire (d e : ℕ) : Gate → Gate
  | .inp i => .conj (i + e) (i + e)
  | .cst b => .cst b
  | .neg r => .neg (r + d)
  | .conj r s => .conj (r + d) (s + d)
  | .disj r s => .disj (r + d) (s + d)

/-- Rerouting a circuit: relocating it by `d` and rewiring its inputs to the gates `e, e + 1, …`
of the circuit underneath. -/
def reroute (d e : ℕ) (C : Circuit) : Circuit := C.map (Gate.rewire d e)

@[simp] theorem length_reroute (d e : ℕ) (C : Circuit) : (reroute d e C).length = C.length := by
  simp [reroute]

theorem reroute_cons (d e : ℕ) (g : Gate) (C : Circuit) :
    reroute d e (g :: C) = Gate.rewire d e g :: reroute d e C := rfl

/-- The circuit inputs read by a gate are below `m`. -/
def inpLt (m : ℕ) : Gate → Prop
  | .inp i => i < m
  | _ => True

/-- Every gate of the circuit reads circuit inputs below `m`. -/
def inpsLt (m : ℕ) (C : Circuit) : Prop := ∀ g ∈ C, inpLt m g

theorem inpsLt_of_cons {m : ℕ} {g : Gate} {C : Circuit} (h : inpsLt m (g :: C)) :
    inpLt m g ∧ inpsLt m C :=
  ⟨h g (by simp), fun g' hg' => h g' (by simp [hg'])⟩

/-! ### The semantics of a composition -/

theorem gateVal_rewire {x : Word} {vs ws : List Bool} {e : ℕ} {g : Gate}
    (hg : gateWf ws.length g) (hi : inpLt (vs.length - e) g) (he : e ≤ vs.length) :
    gateVal x (vs ++ ws) (Gate.rewire vs.length e g) = gateVal (vs.drop e) ws g := by
  have key : ∀ r : ℕ, r < ws.length → (vs ++ ws).getD (r + vs.length) false
      = ws.getD r false := by
    intro r hr
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      ← List.getD_eq_getElem?_getD]
    simp
  cases g with
  | inp i =>
      have hlt : i + e < vs.length := by
        have : i < vs.length - e := hi
        omega
      have hval : (vs ++ ws).getD (i + e) false = (vs.drop e).getD i false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
          List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm e i]
      rw [Gate.rewire, gateVal, gateVal, hval, Bool.and_self]
  | cst b => rfl
  | neg r => rw [Gate.rewire, gateVal, gateVal, key r hg]
  | conj r s =>
      obtain ⟨h1, h2⟩ := hg
      rw [Gate.rewire, gateVal, gateVal, key r h1, key s h2]
  | disj r s =>
      obtain ⟨h1, h2⟩ := hg
      rw [Gate.rewire, gateVal, gateVal, key r h1, key s h2]

/-- **A composed circuit runs the upper circuit on the values of the lower one.** -/
theorem vals_reroute_append (x : Word) (D : Circuit) (e : ℕ) (he : e ≤ D.length) :
    ∀ C : Circuit, wf C → inpsLt (D.length - e) C →
      vals x (reroute D.length e C ++ D) = vals x D ++ vals ((vals x D).drop e) C := by
  intro C
  induction C with
  | nil => simp [reroute, vals]
  | cons g C ih =>
      intro hC hin
      obtain ⟨hg, hC'⟩ := hC
      obtain ⟨hig, hinC⟩ := inpsLt_of_cons hin
      rw [reroute_cons, List.cons_append, vals, ih hC' hinC, vals, List.append_assoc]
      congr 1
      have hlen : (vals x D).length = D.length := by simp
      have hval := gateVal_rewire (x := x) (vs := vals x D)
        (ws := vals ((vals x D).drop e) C) (e := e) (g := g)
        (by simpa using hg) (by rw [hlen]; exact hig) (by omega)
      rw [hlen] at hval
      rw [hval]

/-- Rewiring a gate keeps it well formed, provided the inputs it reads are in range. -/
theorem gateWf_rewire {j d e m : ℕ} {g : Gate} (hg : gateWf j g) (hi : inpLt m g)
    (hm : m + e ≤ d) : gateWf (j + d) (Gate.rewire d e g) := by
  cases g with
  | inp i =>
      have : i < m := hi
      exact ⟨by omega, by omega⟩
  | cst b => trivial
  | neg r => exact Nat.add_lt_add_right hg d
  | conj r s => exact ⟨Nat.add_lt_add_right hg.1 d, Nat.add_lt_add_right hg.2 d⟩
  | disj r s => exact ⟨Nat.add_lt_add_right hg.1 d, Nat.add_lt_add_right hg.2 d⟩

/-- **A composed circuit is well formed.** -/
theorem wf_reroute_append (D : Circuit) (hD : wf D) (e : ℕ) (he : e ≤ D.length) :
    ∀ C : Circuit, wf C → inpsLt (D.length - e) C → wf (reroute D.length e C ++ D) := by
  intro C
  induction C with
  | nil => intro _ _; exact hD
  | cons g C ih =>
      intro hC hin
      obtain ⟨hg, hC'⟩ := hC
      obtain ⟨hig, hinC⟩ := inpsLt_of_cons hin
      exact ⟨by simpa using gateWf_rewire (d := D.length) hg hig (by omega), ih hC' hinC⟩

/-- **The output of a composed circuit** is the output of the upper circuit, run on the values of
the gates `e, e + 1, …` of the lower one. -/
theorem out_reroute_append (x : Word) (D : Circuit) (e : ℕ) (he : e ≤ D.length) (g : Gate)
    (C : Circuit) (hC : wf (g :: C)) (hin : inpsLt (D.length - e) (g :: C)) :
    out x (reroute D.length e (g :: C) ++ D) = out ((vals x D).drop e) (g :: C) := by
  obtain ⟨hg, hC'⟩ := hC
  obtain ⟨hig, hinC⟩ := inpsLt_of_cons hin
  rw [reroute_cons, List.cons_append, out, out, vals_reroute_append x D e he C hC' hinC]
  have hlen : (vals x D).length = D.length := by simp
  have hval := gateVal_rewire (x := x) (vs := vals x D)
    (ws := vals ((vals x D).drop e) C) (e := e) (g := g)
    (by simpa using hg) (by rw [hlen]; exact hig) (by omega)
  rw [hlen] at hval
  exact hval

end Tseitin

namespace CircCode

open Complexity.Tseitin

/-! ### The code of a rerouted circuit -/

theorem encCirc_reroute (d e : ℕ) (C : Circuit) :
    encCirc (reroute d e C) = gmap (fun _ g => encGate (Gate.rewire d e g)) C := by
  induction C with
  | nil => rfl
  | cons g C ih => rw [reroute_cons, encCirc, ih, gmap]

theorem fld1_rewire (d e : ℕ) (g : Gate) : fld1 (Gate.rewire d e g) ≤ fld1 g + d + e := by
  cases g with
  | inp i => simp only [Gate.rewire, fld1]; omega
  | cst b => simp [Gate.rewire, fld1]
  | _ => simp only [Gate.rewire, fld1]; omega

theorem fld2_rewire (d e : ℕ) (g : Gate) :
    fld2 (Gate.rewire d e g) ≤ fld1 g + fld2 g + d + e := by
  cases g with
  | inp i => simp only [Gate.rewire, fld1, fld2]; omega
  | cst b => simp [Gate.rewire, fld2]
  | neg r => simp [Gate.rewire, fld2]
  | conj r s => simp only [Gate.rewire, fld1, fld2]; omega
  | disj r s => simp only [Gate.rewire, fld1, fld2]; omega

/-! ### The Cobham term that rewires a description -/

/-- The two shifts, packed into one parameter word. -/
def packDE (d e : ℕ) : Word :=
  List.replicate d true ++ false :: List.replicate e true

@[simp] theorem length_packDE (d e : ℕ) : (packDE d e).length = d + e + 1 := by
  simp only [packDE, List.length_append, List.length_cons, List.length_replicate]
  omega

theorem lead1_replicate_true (k : ℕ) : lead1 (List.replicate k true) = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, lead1, ih]

/-- The first shift, read off the parameter. -/
def pDT : Cob := .comp Cob.leadOnes [.proj 2]

/-- The second shift, read off the parameter. -/
def pET : Cob := .comp Cob.leadOnes [.comp Cob.tail [.comp Cob.dropOnes [.proj 2]]]

variable (y u : Word)

@[simp] theorem eval_pDT (d e : ℕ) :
    pDT.eval [y, u, packDE d e] = List.replicate d true := by
  simp only [pDT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_leadOnes, Cob.eval_proj,
    List.getD_cons_succ, List.getD_cons_zero, packDE]
  rw [lead1_replicate_append]
  simp [lead1]

@[simp] theorem eval_pET (d e : ℕ) :
    pET.eval [y, u, packDE d e] = List.replicate e true := by
  simp only [pET, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_leadOnes, Cob.eval_tail,
    Cob.eval_dropOnes, Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero, packDE]
  rw [drop1_replicate_append, drop1_false_cons, List.tail_cons, lead1_replicate_true]

/-- The first field, shifted by the first parameter. -/
def wFldAd : Cob := .comp Cob.concat [uFldA1, pDT]

/-- The second field, shifted by the first parameter. -/
def wFldBd : Cob := .comp Cob.concat [uFldB1, pDT]

/-- The first field, shifted by the second parameter. -/
def wFldAe : Cob := .comp Cob.concat [uFldA1, pET]

@[simp] theorem eval_wFldAd (d e : ℕ) :
    wFldAd.eval [y, u, packDE d e] = List.replicate (fldA y + d + 1) true := by
  simp only [wFldAd, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, eval_uFldA1,
    eval_pDT, ← List.replicate_add]
  congr 1
  omega

@[simp] theorem eval_wFldBd (d e : ℕ) :
    wFldBd.eval [y, u, packDE d e] = List.replicate (fldB y + d + 1) true := by
  simp only [wFldBd, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, eval_uFldB1,
    eval_pDT, ← List.replicate_add]
  congr 1
  omega

@[simp] theorem eval_wFldAe (d e : ℕ) :
    wFldAe.eval [y, u, packDE d e] = List.replicate (fldA y + e + 1) true := by
  simp only [wFldAe, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, eval_uFldA1,
    eval_pET, ← List.replicate_add]
  congr 1
  omega

/-- The rewired token of an input gate: a conjunction of the target gate with itself. -/
def rwInpT : Cob :=
  Cob.catL [Cob.constT [false, true, true, true, true, true, false], wFldAe,
    Cob.constT [false], wFldAe]

/-- The rewired token of a negation gate. -/
def rwNegT : Cob :=
  Cob.catL [Cob.constT [false, true, true, true, true, false], wFldAd, Cob.constT [false, true]]

/-- The rewired token of a conjunction gate. -/
def rwConjT : Cob :=
  Cob.catL [Cob.constT [false, true, true, true, true, true, false], wFldAd,
    Cob.constT [false], wFldBd]

/-- The rewired token of a disjunction gate. -/
def rwDisjT : Cob :=
  Cob.catL [Cob.constT [false, true, true, true, true, true, true, false], wFldAd,
    Cob.constT [false], wFldBd]

/-- The term emitted at each state and bit by the rewiring recursion. -/
def rwBlkT (s : ℕ) (b : Bool) : Cob :=
  if b then .empty
  else
    match s with
    | 3 => rwInpT
    | 4 => Cob.constT (encGate (.cst false))
    | 5 => Cob.constT (encGate (.cst true))
    | 6 => rwNegT
    | 7 => rwConjT
    | 8 => rwDisjT
    | _ => .empty

theorem eval_rwBlkT (s : ℕ) (b : Bool) (c d e : ℕ) :
    (rwBlkT s b).eval [y, List.replicate c true, packDE d e]
      = gblk (fun _ g => encGate (Gate.rewire d e g)) s b y c := by
  cases b with
  | true => simp [rwBlkT, gblk]
  | false =>
      rcases Nat.lt_or_ge s 9 with h9 | h9
      · interval_cases s
        · simp [rwBlkT, gblk, emits]
        · simp [rwBlkT, gblk, emits]
        · simp [rwBlkT, gblk, emits]
        · rw [show rwBlkT 3 false = rwInpT from rfl, gblk, if_pos (by simp [emits]),
            show readGate 3 y = Gate.inp (fldA y) from rfl, rwInpT]
          simp [Gate.rewire, encGate, tag, fld1, fld2, List.replicate_succ]
        · rw [show rwBlkT 4 false = Cob.constT (encGate (.cst false)) from rfl, gblk,
            if_pos (by simp [emits]), show readGate 4 y = Gate.cst false from rfl]
          simp [Gate.rewire]
        · rw [show rwBlkT 5 false = Cob.constT (encGate (.cst true)) from rfl, gblk,
            if_pos (by simp [emits]), show readGate 5 y = Gate.cst true from rfl]
          simp [Gate.rewire]
        · rw [show rwBlkT 6 false = rwNegT from rfl, gblk, if_pos (by simp [emits]),
            show readGate 6 y = Gate.neg (fldA y) from rfl, rwNegT]
          simp [Gate.rewire, encGate, tag, fld1, fld2, List.replicate_succ]
        · rw [show rwBlkT 7 false = rwConjT from rfl, gblk, if_pos (by simp [emits]),
            show readGate 7 y = Gate.conj (fldA y) (fldB y) from rfl, rwConjT]
          simp [Gate.rewire, encGate, tag, fld1, fld2, List.replicate_succ]
        · rw [show rwBlkT 8 false = rwDisjT from rfl, gblk, if_pos (by simp [emits]),
            show readGate 8 y = Gate.disj (fldA y) (fldB y) from rfl, rwDisjT]
          simp [Gate.rewire, encGate, tag, fld1, fld2, List.replicate_succ]
      · obtain ⟨k, rfl⟩ : ∃ k, s = k + 9 := ⟨s - 9, by omega⟩
        simp [rwBlkT, gblk, emits]

theorem length_gblk_rewire (s : ℕ) (b : Bool) (c d e : ℕ) :
    (gblk (fun _ g => encGate (Gate.rewire d e g)) s b y c).length
      ≤ 11 * (y.length + (packDE d e).length + 1) := by
  rw [gblk]
  split_ifs with h
  · rw [length_encGate, length_packDE]
    have ht := (tag_le (Gate.rewire d e (readGate s y))).2
    have h1 : fld1 (Gate.rewire d e (readGate s y)) ≤ y.length + d + e :=
      le_trans (fld1_rewire d e _) (by have := fld1_readGate_le (y := y) s; omega)
    have h2 : fld2 (Gate.rewire d e (readGate s y)) ≤ 2 * y.length + d + e :=
      le_trans (fld2_rewire d e _) (by
        have h1' := fld1_readGate_le (y := y) s
        have h2' := fld2_readGate_le (y := y) s
        omega)
    omega
  · simp

/-- **The Cobham term that rewires a description**: run over the code of a circuit with the two
shifts packed into the parameter, it rewrites every token. -/
def rerouteTerm : Cob := blkRunTerm 10 dstate cinc rwBlkT 1 11

/-- **Rewiring is a Cobham function of the description.** -/
theorem eval_rerouteTerm (C : Circuit) (d e : ℕ) :
    rerouteTerm.eval [encCirc C, packDE d e] = encCirc (reroute d e C) := by
  rw [rerouteTerm, eval_blkRunTerm (by norm_num) dstate_lt cinc_le rwBlkT (packDE d e)
    (fun s b y c => eval_rwBlkT y s b c d e)
    (fun s b y c _ => length_gblk_rewire y s b c d e),
    brun_gmap, encCirc_reroute]

end CircCode

/-! ### Composing two P-uniform families -/

/-- **A P-uniform family may be rerouted**, provided the two shifts are written in unary by Cobham
terms. -/
theorem codeUniform_reroute {cf : ℕ → Tseitin.Circuit} {d e : ℕ → ℕ} (hf : CodeUniform cf)
    {dT eT : Cob} (hd : ∀ x : Word, dT.eval [x] = List.replicate (d x.length) true)
    (he : ∀ x : Word, eT.eval [x] = List.replicate (e x.length) true) :
    CodeUniform (fun n => Tseitin.reroute (d n) (e n) (cf n)) := by
  obtain ⟨f, hf⟩ := hf
  refine ⟨.comp CircCode.rerouteTerm [f, Cob.catL [dT, Cob.constT [false], eT]], fun x => ?_⟩
  have hp : (Cob.catL [dT, Cob.constT [false], eT]).eval [x]
      = CircCode.packDE (d x.length) (e x.length) := by
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, Cob.eval_constT, hd x, he x,
      List.flatten_cons, List.flatten_nil, List.append_nil, CircCode.packDE]
    simp
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, hf x, hp]
  exact CircCode.eval_rerouteTerm _ _ _

/-- **Two P-uniform families may be composed**: the circuit `cf n` is written on top of `cg n`,
its references relocated and its inputs rewired to the gates `e n, e n + 1, …` of `cg n`.  By
`Complexity.Tseitin.out_reroute_append` and `Complexity.Tseitin.wf_reroute_append` the result is
well formed and runs `cf n` on the values those gates take, and the lemma says that its description
is again produced by a single Cobham term. -/
theorem codeUniform_compose {cf cg : ℕ → Tseitin.Circuit} {e : ℕ → ℕ} (hf : CodeUniform cf)
    (hg : CodeUniform cg) {eT : Cob}
    (he : ∀ x : Word, eT.eval [x] = List.replicate (e x.length) true) :
    CodeUniform (fun n => Tseitin.reroute (cg n).length (e n) (cf n) ++ cg n) := by
  obtain ⟨g, hgg⟩ := hg
  have hd : ∀ x : Word, (Cob.comp (cntTerm 10 CircCode.dstate CircCode.cinc 1) [g]).eval [x]
      = List.replicate (cg x.length).length true := by
    intro x
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, hgg x]
    rw [eval_cntTerm (by norm_num) CircCode.dstate_lt CircCode.cinc_le _ [],
      CircCode.rcnt_encCirc]
  exact codeUniform_append (codeUniform_reroute hf hd he) ⟨g, hgg⟩

end Complexity
