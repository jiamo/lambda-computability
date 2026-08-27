/-
**Relocating a circuit: shifting its gate references is a Cobham function.**

Assembling a circuit out of pieces needs a *relocation*: when a circuit `C` is placed on top of a
circuit `D`, every reference of `C` must be increased by the number of gates of `D`.  This module
provides that operation on both sides.

Semantically, `shiftCirc k C` adds `k` to every gate reference of `C` (input indices are left
alone), and `vals_shiftCirc_append` proves that the values of the gates of `shiftCirc |D| C ++ D`
are the values of `D` followed by the values of `C`, so plugging a circuit under another one does
not disturb it.

Syntactically, the relocation is computed on the *codes* of circuits by a single Cobham term, by
the same block-emitting recursion that computes the Tseitin translation: at each marker the token
of the gate is rewritten with its fields increased by the parameter word.

Main definitions:

* `Complexity.CircCode.shiftGate`, `Complexity.CircCode.shiftCirc` — the relocation;
* `Complexity.CircCode.shiftCircTerm` — the Cobham term computing it on codes.

Main results:

* `Complexity.CircCode.wf_shiftCirc_append`, `Complexity.CircCode.vals_shiftCirc_append`,
  `Complexity.CircCode.out_shiftCirc_append` — plugging a circuit under another one is correct;
* `Complexity.CircCode.eval_shiftCircTerm` — **relocation is a Cobham function.**
-/

import Start.CobhamTseitin

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### Relocation -/

/-- A gate with its references increased by `k`.  Input indices are not references and are left
alone. -/
def shiftGate (k : ℕ) : Gate → Gate
  | .inp i => .inp i
  | .cst b => .cst b
  | .neg r => .neg (r + k)
  | .conj r s => .conj (r + k) (s + k)
  | .disj r s => .disj (r + k) (s + k)

/-- A circuit with all its gate references increased by `k`. -/
def shiftCirc (k : ℕ) : Circuit → Circuit := List.map (shiftGate k)

@[simp] theorem shiftCirc_nil (k : ℕ) : shiftCirc k [] = [] := rfl

@[simp] theorem shiftCirc_cons (k : ℕ) (g : Gate) (C : Circuit) :
    shiftCirc k (g :: C) = shiftGate k g :: shiftCirc k C := rfl

@[simp] theorem length_shiftCirc (k : ℕ) (C : Circuit) : (shiftCirc k C).length = C.length := by
  simp [shiftCirc]

/-- Relocating preserves well-formedness when the circuit is plugged on top of `k` further
gates. -/
theorem wf_shiftCirc_append {D : Circuit} (hD : wf D) :
    ∀ {C : Circuit}, wf C → wf (shiftCirc D.length C ++ D) := by
  intro C
  induction C with
  | nil => intro _; simpa using hD
  | cons g C ih =>
      rintro ⟨hg, hC⟩
      refine ⟨?_, ih hC⟩
      have hlen : (shiftCirc D.length C ++ D).length = C.length + D.length := by simp
      rw [hlen]
      cases g with
      | inp i => trivial
      | cst b => trivial
      | neg r => exact Nat.add_lt_add_right hg _
      | conj r s => exact ⟨Nat.add_lt_add_right hg.1 _, Nat.add_lt_add_right hg.2 _⟩
      | disj r s => exact ⟨Nat.add_lt_add_right hg.1 _, Nat.add_lt_add_right hg.2 _⟩

theorem getD_append_add (u v : List Bool) (r : ℕ) (d : Bool) :
    (u ++ v).getD (r + u.length) d = v.getD r d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp

/-- **Plugging a circuit under another one does not disturb it**: the values of the gates of
`shiftCirc |D| C ++ D` are the values of `D` followed by the values of `C`. -/
theorem vals_shiftCirc_append (x : Word) {D : Circuit} :
    ∀ {C : Circuit}, wf C → vals x (shiftCirc D.length C ++ D) = vals x D ++ vals x C := by
  intro C
  induction C with
  | nil => intro _; simp [vals]
  | cons g C ih =>
      rintro ⟨hg, hC⟩
      have hv : vals x (shiftCirc D.length C ++ D) = vals x D ++ vals x C := ih hC
      have hlen : (vals x D).length = D.length := by simp
      have hgate : gateVal x (vals x D ++ vals x C) (shiftGate D.length g)
          = gateVal x (vals x C) g := by
        have hget : ∀ r : ℕ, r < C.length →
            (vals x D ++ vals x C).getD (r + D.length) false = (vals x C).getD r false := by
          intro r _
          rw [← hlen, getD_append_add]
        cases g with
        | inp i => rfl
        | cst b => rfl
        | neg r => rw [shiftGate, gateVal, gateVal, hget r hg]
        | conj r s => rw [shiftGate, gateVal, gateVal, hget r hg.1, hget s hg.2]
        | disj r s => rw [shiftGate, gateVal, gateVal, hget r hg.1, hget s hg.2]
      rw [shiftCirc_cons, List.cons_append, vals, hv, hgate, vals, List.append_assoc]

/-- The output of a relocated circuit plugged on top of another one is its own output. -/
theorem out_shiftCirc_append (x : Word) {D : Circuit} {g : Gate} {C : Circuit}
    (h : wf (g :: C)) :
    out x (shiftCirc D.length (g :: C) ++ D) = out x (g :: C) := by
  have hv : vals x (shiftCirc D.length C ++ D) = vals x D ++ vals x C :=
    vals_shiftCirc_append x h.2
  have hlen : (vals x D).length = D.length := by simp
  have hget : ∀ r : ℕ, r < C.length →
      (vals x D ++ vals x C).getD (r + D.length) false = (vals x C).getD r false := by
    intro r _
    rw [← hlen, getD_append_add]
  rw [shiftCirc_cons, List.cons_append, out, hv, out]
  cases g with
  | inp i => rfl
  | cst b => rfl
  | neg r => rw [shiftGate, gateVal, gateVal, hget r h.1]
  | conj r s => rw [shiftGate, gateVal, gateVal, hget r h.1.1, hget s h.1.2]
  | disj r s => rw [shiftGate, gateVal, gateVal, hget r h.1.1, hget s h.1.2]

/-! ### Relocation on codes -/

/-- The first field of the token, in unary and shifted by one, read off the suffix. -/
def uA1 : Cob := .comp (.app true) [.comp Cob.tail [uFldA]]

/-- The second field of the token, in unary and shifted by one, read off the suffix. -/
def uB1 : Cob := .comp (.app true) [.comp Cob.tail [uFldB]]

@[simp] theorem eval_uA1 (y u p : Word) :
    uA1.eval [y, u, p] = List.replicate (fldA y + 1) true := by
  simp only [uA1, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_tail, eval_uFldA,
    List.tail_replicate, Cob.eval_app, List.getD_cons_zero, ← List.replicate_succ]
  congr 1
  rw [fldA]
  omega

@[simp] theorem eval_uB1 (y u p : Word) :
    uB1.eval [y, u, p] = List.replicate (fldB y + 1) true := by
  simp only [uB1, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_tail, eval_uFldB,
    List.tail_replicate, Cob.eval_app, List.getD_cons_zero, ← List.replicate_succ]
  congr 1
  rw [fldB]
  omega

/-- The term rewriting the token of a gate with its references increased by the parameter. -/
def sblkT (s : ℕ) (b : Bool) : Cob :=
  if b then .empty
  else
    match s with
    | 3 => Cob.catL [Cob.constT [false, true, false], uA1, Cob.constT [false, true]]
    | 4 => Cob.constT (encGate (.cst false))
    | 5 => Cob.constT (encGate (.cst true))
    | 6 => Cob.catL [Cob.constT [false, true, true, true, true, false], uA1, .proj 2,
        Cob.constT [false, true]]
    | 7 => Cob.catL [Cob.constT [false, true, true, true, true, true, false], uA1, .proj 2,
        Cob.constT [false], uB1, .proj 2]
    | 8 => Cob.catL [Cob.constT [false, true, true, true, true, true, true, false], uA1, .proj 2,
        Cob.constT [false], uB1, .proj 2]
    | _ => .empty

/-- The block emitted by the relocation. -/
def sblk (k : ℕ) : ℕ → Bool → Word → ℕ → Word :=
  gblk fun _ g => encGate (shiftGate k g)

theorem eval_sblkT (y : Word) (k : ℕ) (s : ℕ) (b : Bool) (c : ℕ) :
    (sblkT s b).eval [y, List.replicate c true, List.replicate k true] = sblk k s b y c := by
  cases b with
  | true => simp [sblkT, sblk, gblk]
  | false =>
      rcases Nat.lt_or_ge s 9 with h9 | h9
      · interval_cases s
        · simp [sblkT, sblk, gblk, emits]
        · simp [sblkT, sblk, gblk, emits]
        · simp [sblkT, sblk, gblk, emits]
        · rw [show sblkT 3 false = _ from rfl, sblk, gblk, if_pos (by simp [emits]),
            show readGate 3 y = Gate.inp (fldA y) from rfl]
          simp [shiftGate, encGate, tag, fld1, fld2, List.replicate_succ]
        · rw [show sblkT 4 false = _ from rfl, sblk, gblk, if_pos (by simp [emits]),
            show readGate 4 y = Gate.cst false from rfl]
          simp [shiftGate]
        · rw [show sblkT 5 false = _ from rfl, sblk, gblk, if_pos (by simp [emits]),
            show readGate 5 y = Gate.cst true from rfl]
          simp [shiftGate]
        · rw [show sblkT 6 false = _ from rfl, sblk, gblk, if_pos (by simp [emits]),
            show readGate 6 y = Gate.neg (fldA y) from rfl]
          simp [shiftGate, encGate, tag, fld1, fld2, List.replicate_succ, List.replicate_add]
        · rw [show sblkT 7 false = _ from rfl, sblk, gblk, if_pos (by simp [emits]),
            show readGate 7 y = Gate.conj (fldA y) (fldB y) from rfl]
          simp [shiftGate, encGate, tag, fld1, fld2, List.replicate_succ, List.replicate_add]
        · rw [show sblkT 8 false = _ from rfl, sblk, gblk, if_pos (by simp [emits]),
            show readGate 8 y = Gate.disj (fldA y) (fldB y) from rfl]
          simp [shiftGate, encGate, tag, fld1, fld2, List.replicate_succ, List.replicate_add]
      · obtain ⟨n, rfl⟩ : ∃ n, s = n + 9 := ⟨s - 9, by omega⟩
        simp [sblkT, sblk, gblk, emits]

theorem length_sblk (y : Word) (k s : ℕ) (b : Bool) (c : ℕ) :
    (sblk k s b y c).length ≤ 11 * (y.length + (List.replicate k true).length + 1) := by
  rw [sblk, gblk]
  split
  · rw [length_encGate]
    have h1 : fld1 (shiftGate k (readGate s y)) ≤ y.length + k := by
      cases h : readGate s y <;>
        simp only [shiftGate, fld1] <;>
        first
          | omega
          | exact Nat.add_le_add_right (by simpa [h] using fld1_readGate_le y s) k
          | exact le_trans (by simpa [h] using fld1_readGate_le y s) (Nat.le_add_right _ _)
    have h2 : fld2 (shiftGate k (readGate s y)) ≤ y.length + k := by
      cases h : readGate s y <;>
        simp only [shiftGate, fld2] <;>
        first
          | omega
          | exact Nat.add_le_add_right (by simpa [h] using fld2_readGate_le y s) k
          | exact le_trans (by simpa [h] using fld2_readGate_le y s) (Nat.le_add_right _ _)
    have h3 : tag (shiftGate k (readGate s y)) ≤ 6 := (tag_le _).2
    simp only [List.length_replicate]
    omega
  · simp

/-- **The Cobham term relocating a circuit**: it takes the code of a circuit and `1^k` to the code
of the circuit with all its gate references increased by `k`. -/
def shiftCircTerm : Cob := blkRunTerm 10 dstate cinc sblkT 1 11

theorem gmap_shiftGate (k : ℕ) (C : Circuit) :
    gmap (fun _ g => encGate (shiftGate k g)) C = encCirc (shiftCirc k C) := by
  induction C with
  | nil => rfl
  | cons g C ih => rw [gmap, ih, shiftCirc_cons, encCirc]

/-- **Relocation is a Cobham function.** -/
theorem eval_shiftCircTerm (k : ℕ) (C : Circuit) :
    shiftCircTerm.eval [encCirc C, List.replicate k true] = encCirc (shiftCirc k C) := by
  have h := eval_blkRunTerm (m := 10) (Ki := 1) (K := 11) (by norm_num) dstate_lt cinc_le sblkT
    (blk := sblk k) (List.replicate k true) (fun s b y c => eval_sblkT y k s b c)
    (fun s b y c _ => length_sblk y k s b c) (encCirc C)
  rw [shiftCircTerm, h, sblk, brun_gmap, gmap_shiftGate]

end CircCode

end Complexity
