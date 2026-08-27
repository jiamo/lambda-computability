/-
**Relocating a circuit, and stacking two P-uniform families.**

`Start/UniformCircuit.lean` shows that the *descriptions* of two P-uniform families may be
concatenated.  Concatenating descriptions is not, however, concatenating circuits in any useful
sense: gates are numbered from the bottom of the list, so writing `C` on top of `D` shifts every
identifier of `C` by the length of `D`, and the gates of `C` then refer to the wrong wires.

This module supplies the missing operation.  `Complexity.Tseitin.reloc d C` relocates `C` by `d`:
every reference of every gate is increased by `d`, while inputs and constants are left alone.  The
point of the definition is that `reloc D.length C ++ D` is a well-formed circuit that computes what
`C` computes, with `D` sitting underneath it untouched — so two circuits can be put in one circuit.

The relocation is then shown to be a *Cobham function of the description*: the block-emitting
recursion of `Start/CobhamBlock.lean`, run over the code of `C` with the shift `1^d` as parameter,
rewrites every token of the code.  Together with `Complexity.codeUniform_append` this gives the
stacking rule: two P-uniform families may be stacked, and the result is again P-uniform.

Main definitions:

* `Complexity.Tseitin.Gate.shiftBy`, `Complexity.Tseitin.reloc` — relocation;
* `Complexity.CircCode.relocTerm` — the Cobham term that relocates a description.

Main results:

* `Complexity.Tseitin.vals_reloc_append`, `Complexity.Tseitin.out_reloc_append` — **relocation
  preserves the semantics**;
* `Complexity.Tseitin.wf_reloc_append` — and well-formedness;
* `Complexity.CircCode.eval_relocTerm` — **relocation is a Cobham function of the description**;
* `Complexity.codeUniform_reloc`, `Complexity.codeUniform_stack` — **two P-uniform families may be
  stacked.**
-/

import Start.UniformCircuit
import Start.CobhamTseitin

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### Relocation -/

/-- Relocating a gate by `d`: every reference to a gate is increased by `d`, while circuit inputs
and constants are left alone. -/
def Gate.shiftBy (d : ℕ) : Gate → Gate
  | .inp i => .inp i
  | .cst b => .cst b
  | .neg r => .neg (r + d)
  | .conj r s => .conj (r + d) (s + d)
  | .disj r s => .disj (r + d) (s + d)

/-- Relocating a circuit by `d`: every gate is relocated by `d`. -/
def reloc (d : ℕ) (C : Circuit) : Circuit := C.map (Gate.shiftBy d)

@[simp] theorem length_reloc (d : ℕ) (C : Circuit) : (reloc d C).length = C.length := by
  simp [reloc]

@[simp] theorem reloc_nil (d : ℕ) : reloc d [] = [] := rfl

theorem reloc_cons (d : ℕ) (g : Gate) (C : Circuit) :
    reloc d (g :: C) = Gate.shiftBy d g :: reloc d C := rfl

/-- The value of a relocated gate, read off a value list with `d` extra values underneath. -/
theorem gateVal_shiftBy {x : Word} {vs ws : List Bool} {g : Gate}
    (hg : gateWf ws.length g) :
    gateVal x (vs ++ ws) (Gate.shiftBy vs.length g) = gateVal x ws g := by
  have key : ∀ r : ℕ, r < ws.length → (vs ++ ws).getD (r + vs.length) false
      = ws.getD r false := by
    intro r hr
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      ← List.getD_eq_getElem?_getD]
    simp
  cases g with
  | inp i => rfl
  | cst b => rfl
  | neg r => rw [Gate.shiftBy, gateVal, gateVal, key r hg]
  | conj r s =>
      obtain ⟨h1, h2⟩ := hg
      rw [Gate.shiftBy, gateVal, gateVal, key r h1, key s h2]
  | disj r s =>
      obtain ⟨h1, h2⟩ := hg
      rw [Gate.shiftBy, gateVal, gateVal, key r h1, key s h2]

/-- **Relocation preserves the values of the gates**: writing `C`, relocated by the length of `D`,
on top of `D` leaves the values of `C` unchanged, and `D` untouched underneath. -/
theorem vals_reloc_append (x : Word) (D : Circuit) :
    ∀ C : Circuit, wf C → vals x (reloc D.length C ++ D) = vals x D ++ vals x C := by
  intro C
  induction C with
  | nil => simp [reloc, vals]
  | cons g C ih =>
      intro hC
      obtain ⟨hg, hC'⟩ := hC
      rw [reloc_cons, List.cons_append, vals, ih hC', vals, List.append_assoc]
      congr 1
      have hlen : (vals x D).length = D.length := by simp
      have hval := gateVal_shiftBy (x := x) (vs := vals x D) (ws := vals x C) (g := g)
        (by simpa using hg)
      rw [hlen] at hval
      rw [hval]

/-- Relocating a gate by `d` raises the identifiers it may refer to by `d`. -/
theorem gateWf_shiftBy {j d : ℕ} {g : Gate} (hg : gateWf j g) :
    gateWf (j + d) (Gate.shiftBy d g) := by
  cases g with
  | inp i => trivial
  | cst b => trivial
  | neg r => exact Nat.add_lt_add_right hg d
  | conj r s => exact ⟨Nat.add_lt_add_right hg.1 d, Nat.add_lt_add_right hg.2 d⟩
  | disj r s => exact ⟨Nat.add_lt_add_right hg.1 d, Nat.add_lt_add_right hg.2 d⟩

/-- **Relocation preserves well-formedness.** -/
theorem wf_reloc_append (D : Circuit) (hD : wf D) :
    ∀ C : Circuit, wf C → wf (reloc D.length C ++ D) := by
  intro C
  induction C with
  | nil => intro _; exact hD
  | cons g C ih =>
      intro hC
      obtain ⟨hg, hC'⟩ := hC
      exact ⟨by simpa using gateWf_shiftBy (d := D.length) hg, ih hC'⟩

/-- **Relocation preserves the output**: the circuit `C` stacked on top of `D` outputs what `C`
outputs. -/
theorem out_reloc_append (x : Word) (D : Circuit) (g : Gate) (C : Circuit)
    (hC : wf (g :: C)) :
    out x (reloc D.length (g :: C) ++ D) = out x (g :: C) := by
  obtain ⟨hg, hC'⟩ := hC
  rw [reloc_cons, List.cons_append, out, out, vals_reloc_append x D C hC']
  have hlen : (vals x D).length = D.length := by simp
  have hval := gateVal_shiftBy (x := x) (vs := vals x D) (ws := vals x C) (g := g)
    (by simpa using hg)
  rw [hlen] at hval
  exact hval

end Tseitin

namespace CircCode

open Complexity.Tseitin

/-! ### The code of a relocated circuit -/

theorem encCirc_reloc (d : ℕ) (C : Circuit) :
    encCirc (reloc d C) = gmap (fun _ g => encGate (Gate.shiftBy d g)) C := by
  induction C with
  | nil => rfl
  | cons g C ih => rw [reloc_cons, encCirc, ih, gmap]

@[simp] theorem tag_shiftBy (d : ℕ) (g : Gate) : tag (Gate.shiftBy d g) = tag g := by
  cases g with
  | cst b => cases b <;> rfl
  | _ => rfl

theorem fld1_shiftBy (d : ℕ) (g : Gate) : fld1 (Gate.shiftBy d g) ≤ fld1 g + d := by
  cases g with
  | inp i => simp [Gate.shiftBy, fld1]
  | cst b => simp [Gate.shiftBy, fld1]
  | _ => exact le_rfl

theorem fld2_shiftBy (d : ℕ) (g : Gate) : fld2 (Gate.shiftBy d g) ≤ fld2 g + d := by
  cases g with
  | conj r s => exact le_rfl
  | disj r s => exact le_rfl
  | _ => simp [Gate.shiftBy, fld2]

/-! ### The Cobham term that relocates a description -/

/-- The first field of the token at a marker, in unary and shifted by one: `1^{a+1}`. -/
def uFldA1 : Cob := .comp (.app true) [.comp Cob.tail [uFldA]]

/-- The second field of the token at a marker, in unary and shifted by one: `1^{b+1}`. -/
def uFldB1 : Cob := .comp (.app true) [.comp Cob.tail [uFldB]]

/-- The first field, relocated by the parameter: `1^{a+d+1}`. -/
def uFldAd : Cob := .comp Cob.concat [uFldA1, .proj 2]

/-- The second field, relocated by the parameter: `1^{b+d+1}`. -/
def uFldBd : Cob := .comp Cob.concat [uFldB1, .proj 2]

variable (y u p : Word)

@[simp] theorem eval_uFldA1 : uFldA1.eval [y, u, p] = List.replicate (fldA y + 1) true := by
  rw [uFldA1]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_app, Cob.eval_tail,
    eval_uFldA, List.tail_replicate, List.getD_cons_zero]
  rw [fldA, List.replicate_succ]

@[simp] theorem eval_uFldB1 : uFldB1.eval [y, u, p] = List.replicate (fldB y + 1) true := by
  rw [uFldB1]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_app, Cob.eval_tail,
    eval_uFldB, List.tail_replicate, List.getD_cons_zero]
  rw [fldB, List.replicate_succ]

@[simp] theorem eval_uFldAd (d : ℕ) :
    uFldAd.eval [y, u, List.replicate d true] = List.replicate (fldA y + d + 1) true := by
  rw [uFldAd]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, Cob.eval_proj,
    List.getD_cons_succ, List.getD_cons_zero, eval_uFldA1, ← List.replicate_add]
  congr 1
  omega

@[simp] theorem eval_uFldBd (d : ℕ) :
    uFldBd.eval [y, u, List.replicate d true] = List.replicate (fldB y + d + 1) true := by
  rw [uFldBd]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, Cob.eval_proj,
    List.getD_cons_succ, List.getD_cons_zero, eval_uFldB1, ← List.replicate_add]
  congr 1
  omega

/-- The relocated token of an input gate. -/
def shInpT : Cob := Cob.catL [Cob.constT [false, true, false], uFldA1, Cob.constT [false, true]]

/-- The relocated token of a negation gate. -/
def shNegT : Cob :=
  Cob.catL [Cob.constT [false, true, true, true, true, false], uFldAd, Cob.constT [false, true]]

/-- The relocated token of a conjunction gate. -/
def shConjT : Cob :=
  Cob.catL [Cob.constT [false, true, true, true, true, true, false], uFldAd,
    Cob.constT [false], uFldBd]

/-- The relocated token of a disjunction gate. -/
def shDisjT : Cob :=
  Cob.catL [Cob.constT [false, true, true, true, true, true, true, false], uFldAd,
    Cob.constT [false], uFldBd]

/-- The term emitted at each state and bit by the relocating recursion. -/
def shBlkT (s : ℕ) (b : Bool) : Cob :=
  if b then .empty
  else
    match s with
    | 3 => shInpT
    | 4 => Cob.constT (encGate (.cst false))
    | 5 => Cob.constT (encGate (.cst true))
    | 6 => shNegT
    | 7 => shConjT
    | 8 => shDisjT
    | _ => .empty

theorem eval_shBlkT (s : ℕ) (b : Bool) (c d : ℕ) :
    (shBlkT s b).eval [y, List.replicate c true, List.replicate d true]
      = gblk (fun _ g => encGate (Gate.shiftBy d g)) s b y c := by
  cases b with
  | true => simp [shBlkT, gblk]
  | false =>
      rcases Nat.lt_or_ge s 9 with h9 | h9
      · interval_cases s
        · simp [shBlkT, gblk, emits]
        · simp [shBlkT, gblk, emits]
        · simp [shBlkT, gblk, emits]
        · rw [show shBlkT 3 false = shInpT from rfl, gblk, if_pos (by simp [emits]),
            show readGate 3 y = Gate.inp (fldA y) from rfl, shInpT]
          simp [Gate.shiftBy, encGate, tag, fld1, fld2, List.replicate_succ]
        · rw [show shBlkT 4 false = Cob.constT (encGate (.cst false)) from rfl, gblk,
            if_pos (by simp [emits]), show readGate 4 y = Gate.cst false from rfl]
          simp [Gate.shiftBy]
        · rw [show shBlkT 5 false = Cob.constT (encGate (.cst true)) from rfl, gblk,
            if_pos (by simp [emits]), show readGate 5 y = Gate.cst true from rfl]
          simp [Gate.shiftBy]
        · rw [show shBlkT 6 false = shNegT from rfl, gblk, if_pos (by simp [emits]),
            show readGate 6 y = Gate.neg (fldA y) from rfl, shNegT]
          simp [Gate.shiftBy, encGate, tag, fld1, fld2, List.replicate_succ]
        · rw [show shBlkT 7 false = shConjT from rfl, gblk, if_pos (by simp [emits]),
            show readGate 7 y = Gate.conj (fldA y) (fldB y) from rfl, shConjT]
          simp [Gate.shiftBy, encGate, tag, fld1, fld2, List.replicate_succ]
        · rw [show shBlkT 8 false = shDisjT from rfl, gblk, if_pos (by simp [emits]),
            show readGate 8 y = Gate.disj (fldA y) (fldB y) from rfl, shDisjT]
          simp [Gate.shiftBy, encGate, tag, fld1, fld2, List.replicate_succ]
      · obtain ⟨k, rfl⟩ : ∃ k, s = k + 9 := ⟨s - 9, by omega⟩
        simp [shBlkT, gblk, emits]

theorem length_gblk_shiftBy (s : ℕ) (b : Bool) (c d : ℕ) :
    (gblk (fun _ g => encGate (Gate.shiftBy d g)) s b y c).length ≤ 11 * (y.length + d + 1) := by
  rw [gblk]
  split_ifs with h
  · rw [length_encGate]
    have ht := (tag_le (Gate.shiftBy d (readGate s y))).2
    have h1 : fld1 (Gate.shiftBy d (readGate s y)) ≤ y.length + d :=
      le_trans (fld1_shiftBy d _) (by have := fld1_readGate_le (y := y) s; omega)
    have h2 : fld2 (Gate.shiftBy d (readGate s y)) ≤ y.length + d :=
      le_trans (fld2_shiftBy d _) (by have := fld2_readGate_le (y := y) s; omega)
    omega
  · simp

/-- **The Cobham term that relocates a description**: run over the code of a circuit with the
shift `1^d` as parameter, it rewrites every token. -/
def relocTerm : Cob := blkRunTerm 10 dstate cinc shBlkT 1 11

/-- **Relocation is a Cobham function of the description.** -/
theorem eval_relocTerm (C : Circuit) (d : ℕ) :
    relocTerm.eval [encCirc C, List.replicate d true] = encCirc (reloc d C) := by
  rw [relocTerm, eval_blkRunTerm (by norm_num) dstate_lt cinc_le shBlkT
    (List.replicate d true) (fun s b y c => eval_shBlkT y s b c d)
    (fun s b y c _ => by
      simpa using length_gblk_shiftBy y s b c d),
    brun_gmap, encCirc_reloc]

end CircCode

/-! ### Stacking two P-uniform families -/

/-- **A P-uniform family may be relocated**, provided the shift is written in unary by a Cobham
term. -/
theorem codeUniform_reloc {cf : ℕ → Tseitin.Circuit} {d : ℕ → ℕ} (hf : CodeUniform cf)
    {dT : Cob} (hd : ∀ x : Word, dT.eval [x] = List.replicate (d x.length) true) :
    CodeUniform (fun n => Tseitin.reloc (d n) (cf n)) := by
  obtain ⟨f, hf⟩ := hf
  refine ⟨.comp CircCode.relocTerm [f, dT], fun x => ?_⟩
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, hf x, hd x]
  exact CircCode.eval_relocTerm _ _

/-- **Two P-uniform families may be stacked.**  The circuit `cf n` is written on top of `cg n`,
its references relocated by the length of `cg n`; by `Complexity.Tseitin.out_reloc_append` and
`Complexity.Tseitin.wf_reloc_append` the result is well formed and computes what `cf n` computes,
and the lemma says that its description is again produced by a single Cobham term. -/
theorem codeUniform_stack {cf cg : ℕ → Tseitin.Circuit} (hf : CodeUniform cf)
    (hg : CodeUniform cg) :
    CodeUniform (fun n => Tseitin.reloc (cg n).length (cf n) ++ cg n) := by
  obtain ⟨g, hgg⟩ := hg
  have hd : ∀ x : Word, (Cob.comp (cntTerm 10 CircCode.dstate CircCode.cinc 1) [g]).eval [x]
      = List.replicate (cg x.length).length true := by
    intro x
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, hgg x]
    rw [eval_cntTerm (by norm_num) CircCode.dstate_lt CircCode.cinc_le _ [],
      CircCode.rcnt_encCirc]
  exact codeUniform_append (codeUniform_reloc hf hd) ⟨g, hgg⟩

end Complexity
