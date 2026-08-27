/-
**Writing gate tokens, and a P-uniform family with a carried accumulator.**

`Start/UniformBlock.lean` supplies the loop rule for P-uniform descriptions: a family of circuits
made of blocks of a fixed size is P-uniform as soon as, for each offset inside the block, a single
Cobham term writes that gate from the block index in unary.  This module makes that rule usable and
then uses it.

Two general tools come first.  `Complexity.CircCode.tokTerm` writes the token of a gate with a fixed
tag and two unary fields, and `Complexity.CircCode.linT` computes `1^{q·i+r}` from `1^i`; between
them they write any gate whose references are affine in the block index.  Next come the semantics
of a layer: the value and the well-formedness of `Complexity.CircCode.layer` are determined gate by
gate, which is what makes a layer-shaped circuit provable at all.

The family built with these is `Complexity.CircCode.pairCirc n`: `n` blocks of four gates,
computing `⋁_{i<n} (x_{2i} ∧ x_{2i+1})`.  Its point is that the blocks are *not* independent — each
block reads the accumulator of the block below it, exactly as the unrolling of a recursion does —
and that the first block is a special case, so the term writing the last gate of a block branches
on whether the block index is zero.

Main definitions:

* `Complexity.CircCode.tokTerm`, `Complexity.CircCode.linT` — the token writer and the affine unary
  index;
* `Complexity.CircCode.lval` — the value of the gate with a given identifier in a layer;
* `Complexity.CircCode.pairT`, `Complexity.CircCode.pairCirc` — the family.

Main results:

* `Complexity.CircCode.eval_tokTerm`, `Complexity.CircCode.eval_linT` — the two tools are Cobham
  functions;
* `Complexity.CircCode.wf_layer`, `Complexity.CircCode.vals_layer_getD`,
  `Complexity.CircCode.out_layer` — the semantics of a layer;
* `Complexity.CircCode.wf_pairCirc`, `Complexity.CircCode.out_pairCirc` — the family is well formed
  and computes what it should;
* `Complexity.codeUniform_pairCirc` — **its descriptions are written by a single Cobham term.**
-/

import Start.UniformBlock

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### Writing a gate token -/

/-- The Cobham term writing the token of a gate with the fixed tag `t` and the two fields
supplied, in unary, by `aT` and `bT`. -/
def tokTerm (t : ℕ) (aT bT : Cob) : Cob :=
  Cob.catL [Cob.constT (false :: (List.replicate t true ++ [false])),
    .comp (.app true) [aT], Cob.constT [false], .comp (.app true) [bT]]

theorem eval_tokTerm (g : Gate) {aT bT : Cob} {args : List Word}
    (ha : aT.eval args = List.replicate (fld1 g) true)
    (hb : bT.eval args = List.replicate (fld2 g) true) :
    (tokTerm (tag g) aT bT).eval args = encGate g := by
  simp [tokTerm, ha, hb, encGate, List.replicate_succ]

/-- The Cobham term computing `1^{q·i+r}` from the word `1^i` sitting in the argument `j`. -/
def linT (j q r : ℕ) : Cob :=
  Cob.pre (List.replicate r true) (.comp .smash [.proj j, Cob.constT (List.replicate q true)])

theorem eval_linT {j q r i v : ℕ} {args : List Word}
    (harg : args.getD j [] = List.replicate i true) (hv : r + i * q = v) :
    (linT j q r).eval args = List.replicate v true := by
  subst hv
  rw [linT]
  simp only [Cob.eval_pre, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash,
    Cob.eval_proj, harg, Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ,
    List.length_replicate]
  rw [← List.replicate_add]

/-! ### The semantics of a layer -/

/-- The value of the gate with identifier `j` of a layer. -/
def lval (x : Word) (tmpl : ℕ → Gate) (j : ℕ) : Bool :=
  gateVal x (vals x (layer tmpl j)) (tmpl j)

theorem vals_layer_getD (x : Word) (tmpl : ℕ → Gate) :
    ∀ N j : ℕ, j < N → (vals x (layer tmpl N)).getD j false = lval x tmpl j := by
  intro N
  induction N with
  | zero => intro j hj; omega
  | succ N ih =>
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · rw [layer, vals_cons_getD_lt x _ _ (by simpa using h)]
        exact ih j h
      · subst h
        have hv := vals_cons_getD_length x (tmpl j) (layer tmpl j)
        rw [length_layer] at hv
        rw [layer]
        exact hv

theorem out_layer (x : Word) (tmpl : ℕ → Gate) (N : ℕ) :
    out x (layer tmpl (N + 1)) = lval x tmpl N := rfl

theorem wf_layer {tmpl : ℕ → Gate} :
    ∀ {N : ℕ}, (∀ j, j < N → gateWf j (tmpl j)) → wf (layer tmpl N)
  | 0, _ => trivial
  | N + 1, h => by
      refine ⟨?_, wf_layer fun j hj => h j (by omega)⟩
      rw [length_layer]
      exact h N (by omega)

/-! ### A family with a carried accumulator -/

/-- The template of the family: the block `i` reads the two input bits `2i` and `2i+1`, conjoins
them, and disjoins the result with the accumulator of the block below. -/
def pairT : ℕ → ℕ → Gate
  | 0, i => .inp (2 * i)
  | 1, i => .inp (2 * i + 1)
  | 2, i => .conj (4 * i) (4 * i + 1)
  | _, 0 => .disj 2 2
  | _, i + 1 => .disj (4 * i + 6) (4 * i + 3)

/-- The gate with identifier `c`: the offset inside its block is `c % 4` and the index of its
block is `c / 4`. -/
def pairF (c : ℕ) : Gate := pairT (c % 4) (c / 4)

/-- The family: `n` blocks of four gates. -/
def pairCirc (n : ℕ) : Circuit := layer pairF (4 * n)

@[simp] theorem length_pairCirc (n : ℕ) : (pairCirc n).length = 4 * n := by
  rw [pairCirc, length_layer]

/-! ### The four gates of a block -/

theorem pairF_zero (i : ℕ) : pairF (4 * i) = .inp (2 * i) := by
  rw [pairF, show 4 * i % 4 = 0 from by omega, show 4 * i / 4 = i from by omega]
  rfl

theorem pairF_one (i : ℕ) : pairF (4 * i + 1) = .inp (2 * i + 1) := by
  rw [pairF, show (4 * i + 1) % 4 = 1 from by omega, show (4 * i + 1) / 4 = i from by omega]
  rfl

theorem pairF_two (i : ℕ) : pairF (4 * i + 2) = .conj (4 * i) (4 * i + 1) := by
  rw [pairF, show (4 * i + 2) % 4 = 2 from by omega, show (4 * i + 2) / 4 = i from by omega]
  rfl

theorem pairF_three_zero : pairF (4 * 0 + 3) = .disj (4 * 0 + 2) (4 * 0 + 2) := by
  rw [pairF, show (4 * 0 + 3) % 4 = 3 from by omega, show (4 * 0 + 3) / 4 = 0 from by omega]
  rfl

theorem pairF_three_succ (i : ℕ) :
    pairF (4 * (i + 1) + 3) = .disj (4 * (i + 1) + 2) (4 * i + 3) := by
  rw [pairF, show (4 * (i + 1) + 3) % 4 = 3 from by omega,
    show (4 * (i + 1) + 3) / 4 = i + 1 from by omega]
  change Gate.disj (4 * i + 6) (4 * i + 3) = _
  congr 1

theorem gateWf_pairF (j : ℕ) : gateWf j (pairF j) := by
  rw [pairF]
  have h4 : j % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hj : 4 * (j / 4) + j % 4 = j := Nat.div_add_mod j 4
  interval_cases h : j % 4
  · exact trivial
  · exact trivial
  · exact ⟨by omega, by omega⟩
  · match hi : j / 4 with
    | 0 => exact ⟨by omega, by omega⟩
    | i + 1 => exact ⟨by omega, by omega⟩

theorem wf_pairCirc (n : ℕ) : wf (pairCirc n) := wf_layer fun j _ => gateWf_pairF j

/-! ### What the family computes -/

/-- Some pair among the first `i + 1` is made of two `true` bits. -/
def pairUpTo (x : Word) : ℕ → Bool
  | 0 => x.getD 0 false && x.getD 1 false
  | i + 1 => pairUpTo x i || (x.getD (2 * (i + 1)) false && x.getD (2 * (i + 1) + 1) false)

theorem lval_pairF_zero (x : Word) (i : ℕ) : lval x pairF (4 * i) = x.getD (2 * i) false := by
  change gateVal x (vals x (layer pairF (4 * i))) (pairF (4 * i)) = _
  rw [pairF_zero]
  rfl

theorem lval_pairF_one (x : Word) (i : ℕ) :
    lval x pairF (4 * i + 1) = x.getD (2 * i + 1) false := by
  change gateVal x (vals x (layer pairF (4 * i + 1))) (pairF (4 * i + 1)) = _
  rw [pairF_one]
  rfl

theorem lval_pairF_two (x : Word) (i : ℕ) :
    lval x pairF (4 * i + 2) = (x.getD (2 * i) false && x.getD (2 * i + 1) false) := by
  have ha := vals_layer_getD x pairF (4 * i + 2) (4 * i) (by omega)
  have hb := vals_layer_getD x pairF (4 * i + 2) (4 * i + 1) (by omega)
  change gateVal x (vals x (layer pairF (4 * i + 2))) (pairF (4 * i + 2)) = _
  rw [pairF_two]
  change ((vals x (layer pairF (4 * i + 2))).getD (4 * i) false &&
    (vals x (layer pairF (4 * i + 2))).getD (4 * i + 1) false) = _
  rw [ha, hb, lval_pairF_zero, lval_pairF_one]

theorem lval_pairF_three (x : Word) : ∀ i : ℕ, lval x pairF (4 * i + 3) = pairUpTo x i
  | 0 => by
      have h2 := vals_layer_getD x pairF (4 * 0 + 3) (4 * 0 + 2) (by omega)
      change gateVal x (vals x (layer pairF (4 * 0 + 3))) (pairF (4 * 0 + 3)) = _
      rw [pairF_three_zero]
      change ((vals x (layer pairF (4 * 0 + 3))).getD (4 * 0 + 2) false ||
        (vals x (layer pairF (4 * 0 + 3))).getD (4 * 0 + 2) false) = _
      rw [h2, lval_pairF_two, Bool.or_self]
      norm_num [pairUpTo]
  | i + 1 => by
      have h2 := vals_layer_getD x pairF (4 * (i + 1) + 3) (4 * (i + 1) + 2) (by omega)
      have h3 := vals_layer_getD x pairF (4 * (i + 1) + 3) (4 * i + 3) (by omega)
      change gateVal x (vals x (layer pairF (4 * (i + 1) + 3))) (pairF (4 * (i + 1) + 3)) = _
      rw [pairF_three_succ]
      change ((vals x (layer pairF (4 * (i + 1) + 3))).getD (4 * (i + 1) + 2) false ||
        (vals x (layer pairF (4 * (i + 1) + 3))).getD (4 * i + 3) false) = _
      rw [h2, h3, lval_pairF_two, lval_pairF_three x i, pairUpTo, Bool.or_comm]

/-- **The family computes the disjunction over the blocks**: its output says that some pair of
adjacent input bits is made of two `true`s. -/
theorem out_pairCirc (x : Word) (n : ℕ) : out x (pairCirc (n + 1)) = pairUpTo x n := by
  have h : 4 * (n + 1) = (4 * n + 3) + 1 := by omega
  rw [pairCirc, h, out_layer, lval_pairF_three]

/-- The same, spelled out as an existential statement. -/
theorem out_pairCirc_iff (x : Word) (n : ℕ) :
    out x (pairCirc (n + 1)) = true ↔
      ∃ i ≤ n, x.getD (2 * i) false = true ∧ x.getD (2 * i + 1) false = true := by
  rw [out_pairCirc]
  induction n with
  | zero =>
      simp only [pairUpTo, Bool.and_eq_true]
      constructor
      · intro h
        exact ⟨0, le_rfl, by simpa using h.1, by simpa using h.2⟩
      · rintro ⟨i, hi, h1, h2⟩
        interval_cases i
        exact ⟨by simpa using h1, by simpa using h2⟩
  | succ n ih =>
      rw [pairUpTo, Bool.or_eq_true]
      constructor
      · rintro (h | h)
        · obtain ⟨i, hi, h1, h2⟩ := ih.1 h
          exact ⟨i, by omega, h1, h2⟩
        · exact ⟨n + 1, le_rfl, (Bool.and_eq_true _ _) ▸ h⟩
      · rintro ⟨i, hi, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hi) with h | h
        · exact Or.inl (ih.2 ⟨i, by omega, h1, h2⟩)
        · subst h
          exact Or.inr (by rw [Bool.and_eq_true]; exact ⟨h1, h2⟩)

/-! ### The family is P-uniform -/

/-- The Cobham term writing the gate at the offset `s` inside its block, from the block index in
unary.  The last gate of a block branches on whether the block is the first one. -/
def pairBlk : ℕ → Cob
  | 0 => tokTerm 1 (linT 1 2 0) (Cob.constT [])
  | 1 => tokTerm 1 (linT 1 2 1) (Cob.constT [])
  | 2 => tokTerm 5 (linT 1 4 0) (linT 1 4 1)
  | _ => tokTerm 6 (linT 1 4 2)
      (.comp Cob.iteC [.proj 1,
        Cob.pre (List.replicate 3 true)
          (.comp .smash [.comp Cob.tail [.proj 1], Cob.constT (List.replicate 4 true)]),
        Cob.constT (List.replicate 2 true)])

theorem eval_pairBlk (n : ℕ) (y : Word) (s c : ℕ) :
    (pairBlk s).eval [y, List.replicate c true, List.replicate n true] = encGate (pairT s c) := by
  have harg : ([y, List.replicate c true, List.replicate n true] : List Word).getD 1 []
      = List.replicate c true := rfl
  match s, c with
  | 0, c =>
      exact eval_tokTerm (pairT 0 c) (eval_linT harg (by change 0 + c * 2 = 2 * c; omega))
        (by simp [pairT, fld2])
  | 1, c =>
      exact eval_tokTerm (pairT 1 c) (eval_linT harg (by change 1 + c * 2 = 2 * c + 1; omega))
        (by simp [pairT, fld2])
  | 2, c =>
      exact eval_tokTerm (pairT 2 c) (eval_linT harg (by change 0 + c * 4 = 4 * c; omega))
        (eval_linT harg (by change 1 + c * 4 = 4 * c + 1; omega))
  | (t + 3), 0 =>
      refine eval_tokTerm (pairT (t + 3) 0)
        (eval_linT harg (by change 2 + 0 * 4 = 2; omega)) ?_
      simp [pairT, fld2, List.replicate_succ]
  | (t + 3), (i + 1) =>
      refine eval_tokTerm (pairT (t + 3) (i + 1))
        (eval_linT harg (by change 2 + (i + 1) * 4 = 4 * (i + 1) + 2; omega)) ?_
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC, Cob.eval_proj,
        List.getD_cons_zero, List.getD_cons_succ, Cob.eval_pre, Cob.eval_smash,
        Cob.eval_tail, Cob.eval_constT, List.tail_replicate, List.length_replicate,
        if_neg (by simp : ¬ List.replicate (i + 1) true = [])]
      rw [← List.replicate_add]
      congr 1
      change 3 + i * 4 = 4 * i + 3
      omega

theorem length_encGate_pairT (n s c l : ℕ) (hc : c ≤ l) :
    (encGate (pairT s c)).length ≤ 20 * (l + n + 1) := by
  rw [length_encGate]
  match s, c with
  | 0, c => simp only [pairT, tag, fld1, fld2]; omega
  | 1, c => simp only [pairT, tag, fld1, fld2]; omega
  | 2, c => simp only [pairT, tag, fld1, fld2]; omega
  | (t + 3), 0 => simp only [pairT, tag, fld1, fld2]; omega
  | (t + 3), (i + 1) => simp only [pairT, tag, fld1, fld2]; omega

theorem eval_pairCnt (x : Word) :
    (Cob.comp .smash [Cob.proj 0, Cob.constT (List.replicate 4 true)]).eval [x]
      = List.replicate (4 * x.length) true := by
  simp [Nat.mul_comm]

end CircCode

/-- **The family with a carried accumulator is P-uniform**: a single Cobham term writes the
description of `Complexity.CircCode.pairCirc n` from any word of length `n`.  The description is
written block by block, with the loop rule of `Start/UniformBlock.lean`. -/
theorem codeUniform_pairCirc : CodeUniform CircCode.pairCirc := by
  have h := codeUniform_blockLayer (K₀ := 4) (K := 20) (by norm_num)
    (tmpl := fun _ s c => CircCode.pairT s c) (k := fun n => 4 * n)
    (cnt := .comp .smash [Cob.proj 0, Cob.constT (List.replicate 4 true)])
    (blkT := CircCode.pairBlk)
    CircCode.eval_pairCnt (fun n y s c => CircCode.eval_pairBlk n y s c)
    CircCode.length_encGate_pairT
  have heq : CircCode.pairCirc
      = fun n => CircCode.layer (fun c => CircCode.pairT (c % 4) (c / 4)) (4 * n) := by
    funext n
    rw [CircCode.pairCirc]
    rfl
  rw [heq]
  exact h

end Complexity
