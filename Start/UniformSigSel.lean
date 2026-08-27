/-
# The selector layer: the compiler's general combinational gadget

`Start/UniformSigLayer.lean` allows the compiler to emit a layer of arbitrary depth, but leaves the
whole bookkeeping of such a layer — its gates, their values, and the Cobham term writing them — to
whoever uses it.  This module carries that bookkeeping out once and for all, for a shape general
enough to express every combinational gadget the compiler needs.

The shape is the **selector layer**.  Three flat gates `A j`, `B j`, `C j` are chosen for each wire
`j` of the output signal, and the wire carries

  `selBit (A j) (B j) (C j) = (A j ∧ B j) ∨ (¬ A j ∧ C j)`,

that is, `B j` if `A j` holds and `C j` otherwise.  Taking `A j` to be a constant recovers a wire
copied verbatim, taking `C j` to be the constant `false` recovers the conjunction `A j ∧ B j`, and
taking `A j` to be the presence bit of a guard word recovers a multiplexer — so a conditional, a
mask, a truncation and a shift are all instances of one rule.

The layer is a grid of seven rows of `2 * m n` gates: the three chosen gates, the negation of the
first, the two conjunctions, and the disjunction, which is the row the interface reads.

Main definitions:

* `Complexity.Tseitin.selBit` — the Boolean function of the layer;
* `Complexity.Tseitin.selTmpl`, `Complexity.Tseitin.selLayerF` — its template, by row and column
  and by gate identifier.

Main results:

* `Complexity.Tseitin.lval_selLayerF_row6` — the topmost row carries `selBit`;
* `Complexity.sigUniform_of_selLayer` — **a selector layer realizes the function its wires
  describe**, as soon as the three chosen gates are written by Cobham terms.
-/

import Start.UniformSigLayer

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### The template -/

/-- The Boolean function of the selector layer: `b` if `a` holds, `c` otherwise. -/
def selBit (a b c : Bool) : Bool := (a && b) || (!a && c)

@[simp] theorem selBit_true (b c : Bool) : selBit true b c = b := by simp [selBit]

@[simp] theorem selBit_false (b c : Bool) : selBit false b c = c := by simp [selBit]

/-- The template of the selector layer, by row and column: the three chosen gates, the negation of
the first, the two conjunctions, and the disjunction. -/
def selTmpl (A B C : ℕ → Gate) (M : ℕ) : ℕ → ℕ → Gate
  | 0, j => A j
  | 1, j => B j
  | 2, j => C j
  | 3, j => .neg j
  | 4, j => .conj j (M + j)
  | 5, j => .conj (3 * M + j) (2 * M + j)
  | _, j => .disj (4 * M + j) (5 * M + j)

/-- The template of the selector layer, by gate identifier: the row is the quotient of the
identifier by the width, the column its remainder. -/
def selLayerF (A B C : ℕ → Gate) (M : ℕ) (c : ℕ) : Gate := selTmpl A B C M (c / M) (c % M)

/-- A layer of width zero degenerates to the first of the three chosen gates. -/
theorem selLayerF_zero (A B C : ℕ → Gate) : selLayerF A B C 0 = A := by
  funext c
  rw [selLayerF, Nat.div_zero, Nat.mod_zero]
  rfl

theorem selLayerF_row {A B C : ℕ → Gate} {M : ℕ} (hM : 0 < M) (i : ℕ) {j : ℕ} (hj : j < M) :
    selLayerF A B C M (i * M + j) = selTmpl A B C M i j := by
  have h1 : (i * M + j) / M = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hj, Nat.zero_add]
  have h2 : (i * M + j) % M = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  rw [selLayerF, h1, h2]

/-! ### The values of the rows -/

theorem gateVal_neg (x : Word) (vs : List Bool) (r : ℕ) :
    gateVal x vs (.neg r) = !(vs.getD r false) := rfl

theorem gateVal_conj (x : Word) (vs : List Bool) (r s : ℕ) :
    gateVal x vs (.conj r s) = (vs.getD r false && vs.getD s false) := rfl

theorem gateVal_disj (x : Word) (vs : List Bool) (r s : ℕ) :
    gateVal x vs (.disj r s) = (vs.getD r false || vs.getD s false) := rfl

variable {x : Word} {A B C : ℕ → Gate} {M : ℕ}

theorem lval_selLayerF_row0 (hM : 0 < M) (hA : ∀ j, flatGate (A j)) {j : ℕ} (hj : j < M) :
    CircCode.lval x (selLayerF A B C M) j = gateVal x [] (A j) := by
  have h := selLayerF_row (A := A) (B := B) (C := C) hM 0 hj
  rw [Nat.zero_mul, Nat.zero_add] at h
  rw [CircCode.lval, h]
  exact gateVal_flat (hA j) _ _ _

theorem lval_selLayerF_row1 (hM : 0 < M) (hB : ∀ j, flatGate (B j)) {j : ℕ} (hj : j < M) :
    CircCode.lval x (selLayerF A B C M) (M + j) = gateVal x [] (B j) := by
  have h := selLayerF_row (A := A) (B := B) (C := C) hM 1 hj
  rw [Nat.one_mul] at h
  rw [CircCode.lval, h]
  exact gateVal_flat (hB j) _ _ _

theorem lval_selLayerF_row2 (hM : 0 < M) (hC : ∀ j, flatGate (C j)) {j : ℕ} (hj : j < M) :
    CircCode.lval x (selLayerF A B C M) (2 * M + j) = gateVal x [] (C j) := by
  have h := selLayerF_row (A := A) (B := B) (C := C) hM 2 hj
  rw [CircCode.lval, h]
  exact gateVal_flat (hC j) _ _ _

theorem lval_selLayerF_row3 (hM : 0 < M) (hA : ∀ j, flatGate (A j)) {j : ℕ} (hj : j < M) :
    CircCode.lval x (selLayerF A B C M) (3 * M + j) = !(gateVal x [] (A j)) := by
  have h := selLayerF_row (A := A) (B := B) (C := C) hM 3 hj
  rw [CircCode.lval, h]
  have hlt : j < 3 * M + j := by omega
  simp only [selTmpl]
  rw [gateVal_neg, CircCode.vals_layer_getD x (selLayerF A B C M) _ _ hlt,
    lval_selLayerF_row0 (B := B) (C := C) hM hA hj]

theorem lval_selLayerF_row4 (hM : 0 < M) (hA : ∀ j, flatGate (A j)) (hB : ∀ j, flatGate (B j))
    {j : ℕ} (hj : j < M) :
    CircCode.lval x (selLayerF A B C M) (4 * M + j)
      = (gateVal x [] (A j) && gateVal x [] (B j)) := by
  have h := selLayerF_row (A := A) (B := B) (C := C) hM 4 hj
  rw [CircCode.lval, h]
  simp only [selTmpl]
  rw [gateVal_conj, CircCode.vals_layer_getD x (selLayerF A B C M) _ _ (by omega),
    CircCode.vals_layer_getD x (selLayerF A B C M) _ _ (by omega),
    lval_selLayerF_row0 (B := B) (C := C) hM hA hj,
    lval_selLayerF_row1 (A := A) (C := C) hM hB hj]

theorem lval_selLayerF_row5 (hM : 0 < M) (hA : ∀ j, flatGate (A j)) (hC : ∀ j, flatGate (C j))
    {j : ℕ} (hj : j < M) :
    CircCode.lval x (selLayerF A B C M) (5 * M + j)
      = (!(gateVal x [] (A j)) && gateVal x [] (C j)) := by
  have h := selLayerF_row (A := A) (B := B) (C := C) hM 5 hj
  rw [CircCode.lval, h]
  simp only [selTmpl]
  rw [gateVal_conj, CircCode.vals_layer_getD x (selLayerF A B C M) _ _ (by omega),
    CircCode.vals_layer_getD x (selLayerF A B C M) _ _ (by omega),
    lval_selLayerF_row3 (B := B) (C := C) hM hA hj,
    lval_selLayerF_row2 (A := A) (B := B) hM hC hj]

/-- **The topmost row of a selector layer carries the selected bit.** -/
theorem lval_selLayerF_row6 (hM : 0 < M) (hA : ∀ j, flatGate (A j)) (hB : ∀ j, flatGate (B j))
    (hC : ∀ j, flatGate (C j)) {j : ℕ} (hj : j < M) :
    CircCode.lval x (selLayerF A B C M) (6 * M + j)
      = selBit (gateVal x [] (A j)) (gateVal x [] (B j)) (gateVal x [] (C j)) := by
  have h := selLayerF_row (A := A) (B := B) (C := C) hM 6 hj
  rw [CircCode.lval, h]
  simp only [selTmpl]
  rw [gateVal_disj, CircCode.vals_layer_getD x (selLayerF A B C M) _ _ (by omega),
    CircCode.vals_layer_getD x (selLayerF A B C M) _ _ (by omega),
    lval_selLayerF_row4 (C := C) hM hA hB, lval_selLayerF_row5 (B := B) hM hA hC]
  · rfl
  · exact hj
  · exact hj

/-! ### Well-formedness and the inputs read -/

theorem gateWf_selLayerF (hA : ∀ j, flatGate (A j)) (hB : ∀ j, flatGate (B j))
    (hC : ∀ j, flatGate (C j)) (c : ℕ) : gateWf c (selLayerF A B C M c) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    rw [selLayerF_zero]
    exact gateWf_flat (hA c) _
  obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < M ∧ c = i * M + j :=
    ⟨c / M, c % M, Nat.mod_lt _ hM, by rw [Nat.mul_comm, Nat.div_add_mod]⟩
  rw [selLayerF_row (A := A) (B := B) (C := C) hM i hj]
  match i with
  | 0 => exact gateWf_flat (hA j) _
  | 1 => exact gateWf_flat (hB j) _
  | 2 => exact gateWf_flat (hC j) _
  | 3 => simp only [selTmpl, gateWf]; omega
  | 4 => simp only [selTmpl, gateWf]; omega
  | 5 => simp only [selTmpl, gateWf]; omega
  | 6 => simp only [selTmpl, gateWf]; omega
  | (i + 7) =>
      simp only [selTmpl, gateWf]
      have h5 : 5 * M < (i + 7) * M := by
        exact Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl M) hM
      have h4 : 4 * M < (i + 7) * M := by
        exact Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl M) hM
      omega

theorem inpLt_selLayerF {w : ℕ} (hM : 0 < M) (hA : ∀ j, j < M → inpLt w (A j))
    (hB : ∀ j, j < M → inpLt w (B j)) (hC : ∀ j, j < M → inpLt w (C j)) (c : ℕ) :
    inpLt w (selLayerF A B C M c) := by
  obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < M ∧ c = i * M + j :=
    ⟨c / M, c % M, Nat.mod_lt _ hM, by rw [Nat.mul_comm, Nat.div_add_mod]⟩
  rw [selLayerF_row (A := A) (B := B) (C := C) hM i hj]
  match i with
  | 0 => exact hA j hj
  | 1 => exact hB j hj
  | 2 => exact hC j hj
  | 3 => exact trivial
  | 4 => exact trivial
  | 5 => exact trivial
  | 6 => exact trivial
  | (i + 7) => exact trivial

end Tseitin

namespace CircCode

open Complexity.Tseitin

/-! ### The Cobham term writing the layer -/

/-- A seven-way case distinction on a row index supplied in unary in the argument `1`. -/
def sel7 (t : ℕ → Cob) : Cob :=
  Cob.iteT (Cob.tailN 0 (.proj 1))
    (Cob.iteT (Cob.tailN 1 (.proj 1))
      (Cob.iteT (Cob.tailN 2 (.proj 1))
        (Cob.iteT (Cob.tailN 3 (.proj 1))
          (Cob.iteT (Cob.tailN 4 (.proj 1))
            (Cob.iteT (Cob.tailN 5 (.proj 1)) (t 6) (t 5)) (t 4)) (t 3)) (t 2)) (t 1)) (t 0)

theorem eval_sel7 (t : ℕ → Cob) {args : List Word} {i : ℕ}
    (hi : args.getD 1 [] = List.replicate i true) :
    (sel7 t).eval args = (t (min i 6)).eval args := by
  have hg : ∀ k : ℕ, (Cob.tailN k (Cob.proj 1)).eval args = List.replicate (i - k) true := by
    intro k
    rw [Cob.eval_tailN, Cob.eval_proj, hi, List.drop_replicate]
  simp only [sel7, eval_iteT_eval, hg, List.replicate_eq_nil_iff]
  match i with
  | 0 => norm_num
  | 1 => norm_num
  | 2 => norm_num
  | 3 => norm_num
  | 4 => norm_num
  | 5 => norm_num
  | (k + 6) =>
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
      norm_num

/-- The branch of the selector layer at row `i`: the three chosen gates, the negation, the two
conjunctions and the disjunction. -/
def selBranch (aT bT cT widT : Cob) : ℕ → Cob
  | 0 => .comp aT [.proj 0, .proj 2, .proj 3]
  | 1 => .comp bT [.proj 0, .proj 2, .proj 3]
  | 2 => .comp cT [.proj 0, .proj 2, .proj 3]
  | 3 => tokTerm 4 (.proj 2) .empty
  | 4 => tokTerm 5 (.proj 2) (Cob.catL [widT, .proj 2])
  | 5 => tokTerm 5 (Cob.catL [widT, widT, widT, .proj 2]) (Cob.catL [widT, widT, .proj 2])
  | _ => tokTerm 6 (Cob.catL [widT, widT, widT, widT, .proj 2])
            (Cob.catL [widT, widT, widT, widT, widT, .proj 2])

/-- **The Cobham term writing the token of the gate of a selector layer** at row `i` and column
`j`.  Its arguments are `[y, 1^i, 1^j, pw]`: `aT`, `bT` and `cT` write the three chosen gates from
`[y, 1^j, pw]`, and `widT` writes the width `1^M` of a row. -/
def selGblk (aT bT cT widT : Cob) : Cob := sel7 (selBranch aT bT cT widT)

/-- **The term writes the token of the gate of the selector layer.** -/
theorem eval_selGblk {A B C : ℕ → Gate} {M : ℕ} {aT bT cT widT : Cob} {y pw : Word} {i j : ℕ}
    (hA : aT.eval [y, List.replicate j true, pw] = encGate (A j))
    (hB : bT.eval [y, List.replicate j true, pw] = encGate (B j))
    (hC : cT.eval [y, List.replicate j true, pw] = encGate (C j))
    (hw : widT.eval [y, List.replicate i true, List.replicate j true, pw]
      = List.replicate M true) :
    (selGblk aT bT cT widT).eval [y, List.replicate i true, List.replicate j true, pw]
      = encGate (selTmpl A B C M i j) := by
  set args : List Word := [y, List.replicate i true, List.replicate j true, pw] with hargs
  have hj2 : (Cob.proj 2).eval args = List.replicate j true := by simp [hargs]
  have habc : ∀ T : Cob, (Cob.comp T [Cob.proj 0, Cob.proj 2, Cob.proj 3]).eval args
      = T.eval [y, List.replicate j true, pw] := by
    intro T
    simp [hargs]
  have hcat : ∀ q : ℕ, (Cob.catL (List.replicate q widT ++ [Cob.proj 2])).eval args
      = List.replicate (q * M + j) true := by
    intro q
    induction q with
    | zero => simpa using hj2
    | succ q ih =>
        rw [List.replicate_succ, List.cons_append]
        rw [show (Cob.catL (widT :: (List.replicate q widT ++ [Cob.proj 2]))).eval args
            = widT.eval args ++ (Cob.catL (List.replicate q widT ++ [Cob.proj 2])).eval args by
          cases hq : List.replicate q widT ++ [Cob.proj 2] with
          | nil => simp at hq
          | cons t ts => simp [Cob.catL]]
        rw [hw, ih, ← List.replicate_add]
        congr 1
        ring
  have htok : ∀ (g : Gate) (p q : ℕ), fld1 g = p * M + j → fld2 g = q * M + j →
      (tokTerm (tag g) (Cob.catL (List.replicate p widT ++ [Cob.proj 2]))
        (Cob.catL (List.replicate q widT ++ [Cob.proj 2]))).eval args = encGate g := by
    intro g p q h1 h2
    exact eval_tokTerm g (by rw [hcat p, h1]) (by rw [hcat q, h2])
  have hzero : (Cob.catL (List.replicate 0 widT ++ [Cob.proj 2])) = Cob.proj 2 := by
    simp [Cob.catL]
  have hone : (Cob.catL (List.replicate 1 widT ++ [Cob.proj 2])) = Cob.catL [widT, Cob.proj 2] := by
    simp [List.replicate_succ]
  have hthree : (Cob.catL (List.replicate 3 widT ++ [Cob.proj 2]))
      = Cob.catL [widT, widT, widT, Cob.proj 2] := by simp [List.replicate_succ]
  have htwo : (Cob.catL (List.replicate 2 widT ++ [Cob.proj 2]))
      = Cob.catL [widT, widT, Cob.proj 2] := by simp [List.replicate_succ]
  have hfour : (Cob.catL (List.replicate 4 widT ++ [Cob.proj 2]))
      = Cob.catL [widT, widT, widT, widT, Cob.proj 2] := by simp [List.replicate_succ]
  have hfive : (Cob.catL (List.replicate 5 widT ++ [Cob.proj 2]))
      = Cob.catL [widT, widT, widT, widT, widT, Cob.proj 2] := by simp [List.replicate_succ]
  rw [selGblk, eval_sel7 (i := i) _ (by simp [hargs])]
  match i with
  | 0 =>
      rw [show min 0 6 = 0 from rfl, selBranch, habc, hA]
      rfl
  | 1 =>
      rw [show min 1 6 = 1 from rfl, selBranch, habc, hB]
      rfl
  | 2 =>
      rw [show min 2 6 = 2 from rfl, selBranch, habc, hC]
      rfl
  | 3 =>
      rw [show min 3 6 = 3 from rfl, selBranch]
      have h := eval_tokTerm (g := Gate.neg j) (aT := Cob.proj 2) (bT := (.empty : Cob))
        (args := args) (by rw [hj2]; rfl) (by simp [fld2])
      rw [show tag (Gate.neg j) = 4 from rfl] at h
      simpa [selTmpl] using h
  | 4 =>
      rw [show min 4 6 = 4 from rfl, selBranch]
      have h := htok (Gate.conj j (M + j)) 0 1 (by simp [fld1]) (by simp [fld2])
      rw [hzero, hone, show tag (Gate.conj j (M + j)) = 5 from rfl] at h
      simpa [selTmpl] using h
  | 5 =>
      rw [show min 5 6 = 5 from rfl, selBranch]
      have h := htok (Gate.conj (3 * M + j) (2 * M + j)) 3 2 (by rfl) (by rfl)
      rw [hthree, htwo, show tag (Gate.conj (3 * M + j) (2 * M + j)) = 5 from rfl] at h
      simpa [selTmpl] using h
  | (k + 6) =>
      have h := htok (Gate.disj (4 * M + j) (5 * M + j)) 4 5 (by rfl) (by rfl)
      rw [hfour, hfive, show tag (Gate.disj (4 * M + j) (5 * M + j)) = 6 from rfl] at h
      rw [show min (k + 6) 6 = 6 by omega, selBranch,
        show selTmpl A B C M (k + 6) j = Gate.disj (4 * M + j) (5 * M + j) from rfl]
      · exact h
      all_goals omega

/-! ### The width, the whole block, and the length of a token -/

/-- `1^(2 * m n)`, read off a parameter word `dmW n (2 * m n)` sitting at the argument `p`: the
leading ones of that word are `1^n`, and `twoT` turns `1^n` into `1^(2 * m n)`. -/
def selWid (twoT : Cob) (p : ℕ) : Cob := .comp twoT [.comp Cob.leadOnes [.proj p]]

theorem eval_selWid {twoT : Cob} {args : List Word} {p n M : ℕ}
    (hp : args.getD p [] = dmW n M) (hw : twoT.eval [List.replicate n true]
      = List.replicate M true) :
    (selWid twoT p).eval args = List.replicate M true := by
  simp only [selWid, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, hp,
    Cob.eval_leadOnes, lead1_dmW]
  exact hw

/-- **The Cobham term writing the gate `c` of a selector layer.**  Its arguments are
`[y, 1^c, dmW n (2 * m n)]`; the row and the column of the gate are the quotient and the remainder
of `c` by the width, and a layer of width zero is the degenerate one made of the gates `A`. -/
def selBlk (aT bT cT twoT : Cob) : Cob :=
  Cob.iteT (selWid twoT 2)
    (.comp (selGblk aT bT cT (selWid twoT 3))
      [.proj 0, Cob.divT (.proj 1) (selWid twoT 2), Cob.modT (.proj 1) (selWid twoT 2), .proj 2])
    aT

/-- **The term writes the token of the gate of the selector layer.** -/
theorem eval_selBlk {A B C : ℕ → Gate} {aT bT cT twoT : Cob} {y : Word} {n M c : ℕ}
    (hA : ∀ j, aT.eval [y, List.replicate j true, dmW n M] = encGate (A j))
    (hB : ∀ j, bT.eval [y, List.replicate j true, dmW n M] = encGate (B j))
    (hC : ∀ j, cT.eval [y, List.replicate j true, dmW n M] = encGate (C j))
    (hw : twoT.eval [List.replicate n true] = List.replicate M true) :
    (selBlk aT bT cT twoT).eval [y, List.replicate c true, dmW n M]
      = encGate (selLayerF A B C M c) := by
  have h2 : (selWid twoT 2).eval [y, List.replicate c true, dmW n M] = List.replicate M true :=
    eval_selWid (by simp) hw
  rw [selBlk, eval_iteT_eval, h2]
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    rw [if_pos (show (List.replicate 0 true : Word) = [] from rfl), selLayerF_zero]
    exact hA c
  rw [if_neg (by simp [List.replicate_eq_nil_iff]; omega)]
  have harg : (Cob.proj 1).eval [y, List.replicate c true, dmW n M] = List.replicate c true := by
    simp
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
    List.getD_cons_succ, Cob.eval_divT hM harg h2, Cob.eval_modT hM harg h2]
  exact eval_selGblk (hA _) (hB _) (hC _) (eval_selWid (by simp) hw)

/-- **A token of a selector layer is short**: linear in the identifier of its gate and in the
length of the parameter word. -/
theorem length_encGate_selLayerF {A B C : ℕ → Gate} {M K L : ℕ}
    (hA : ∀ j, (encGate (A j)).length ≤ K * (j + L + 1))
    (hB : ∀ j, (encGate (B j)).length ≤ K * (j + L + 1))
    (hC : ∀ j, (encGate (C j)).length ≤ K * (j + L + 1))
    (hML : M ≤ L) (c l : ℕ) (hc : c ≤ l) :
    (encGate (selLayerF A B C M c)).length ≤ (K + 11) * (l + L + 1) := by
  have hmono : ∀ j : ℕ, j ≤ l → ∀ g : Gate, (encGate g).length ≤ K * (j + L + 1) →
      (encGate g).length ≤ (K + 11) * (l + L + 1) := by
    intro j hj g hg
    exact hg.trans (Nat.mul_le_mul (by omega) (by omega))
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    rw [selLayerF_zero]
    exact hmono c hc _ (hA c)
  obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < M ∧ c = i * M + j :=
    ⟨c / M, c % M, Nat.mod_lt _ hM, by rw [Nat.mul_comm, Nat.div_add_mod]⟩
  have hjl : j ≤ l := le_trans (by omega) hc
  rw [selLayerF_row (A := A) (B := B) (C := C) hM i hj]
  have hbig : ∀ g : Gate, tag g + fld1 g + fld2 g + 5 ≤ 11 + 9 * M + 2 * j →
      (encGate g).length ≤ (K + 11) * (l + L + 1) := by
    intro g hg
    rw [length_encGate]
    refine hg.trans ?_
    have : 11 + 9 * M + 2 * j ≤ 11 * (l + L + 1) := by omega
    exact this.trans (Nat.mul_le_mul_right _ (by omega))
  match i with
  | 0 => exact hmono j hjl _ (hA j)
  | 1 => exact hmono j hjl _ (hB j)
  | 2 => exact hmono j hjl _ (hC j)
  | 3 => exact hbig _ (by simp only [selTmpl, tag, fld1, fld2]; omega)
  | 4 => exact hbig _ (by simp only [selTmpl, tag, fld1, fld2]; omega)
  | 5 => exact hbig _ (by simp only [selTmpl, tag, fld1, fld2]; omega)
  | (k + 6) => exact hbig _ (by simp only [selTmpl, tag, fld1, fld2]; omega)

end CircCode

open Complexity.Tseitin CircCode in
/-- **A selector layer realizes the function its wires describe.**

The three chosen gates `A n j`, `B n j`, `C n j` are flat and written by the Cobham terms `aT`,
`bT`, `cT`; the layer is then a P-uniform family of circuits whose output wire `j` carries
`selBit (A n j) (B n j) (C n j)`, so any word function whose signal is described that way is
realized. -/
theorem sigUniform_of_selLayer {r : ℕ} {m : ℕ → ℕ} {F : List Word → Word}
    {A B C : ℕ → ℕ → Tseitin.Gate} {mT aT bT cT : Cob} {K : ℕ}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hAf : ∀ n j, Tseitin.flatGate (A n j))
    (hBf : ∀ n j, Tseitin.flatGate (B n j))
    (hCf : ∀ n j, Tseitin.flatGate (C n j))
    (hAi : ∀ n j, j < 2 * m n → Tseitin.inpLt (r * (2 * m n)) (A n j))
    (hBi : ∀ n j, j < 2 * m n → Tseitin.inpLt (r * (2 * m n)) (B n j))
    (hCi : ∀ n j, j < 2 * m n → Tseitin.inpLt (r * (2 * m n)) (C n j))
    (hAt : ∀ (n : ℕ) (y : Word) (j : ℕ),
      aT.eval [y, List.replicate j true, dmW n (2 * m n)] = CircCode.encGate (A n j))
    (hBt : ∀ (n : ℕ) (y : Word) (j : ℕ),
      bT.eval [y, List.replicate j true, dmW n (2 * m n)] = CircCode.encGate (B n j))
    (hCt : ∀ (n : ℕ) (y : Word) (j : ℕ),
      cT.eval [y, List.replicate j true, dmW n (2 * m n)] = CircCode.encGate (C n j))
    (hAb : ∀ n j : ℕ,
      (CircCode.encGate (A n j)).length ≤ K * (j + (dmW n (2 * m n)).length + 1))
    (hBb : ∀ n j : ℕ,
      (CircCode.encGate (B n j)).length ≤ K * (j + (dmW n (2 * m n)).length + 1))
    (hCb : ∀ n j : ℕ,
      (CircCode.encGate (C n j)).length ≤ K * (j + (dmW n (2 * m n)).length + 1))
    (hval : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ m n) →
      (List.range (2 * m n)).map (fun j => Tseitin.selBit
          (Tseitin.gateVal (encArgs (m n) args) [] (A n j))
          (Tseitin.gateVal (encArgs (m n) args) [] (B n j))
          (Tseitin.gateVal (encArgs (m n) args) [] (C n j)))
        = encSig (m n) (F args)) :
    SigUniform r m F := by
  obtain ⟨twoT, htwo⟩ := exists_twiceT hm
  have hw : ∀ n : ℕ, twoT.eval [List.replicate n true] = List.replicate (2 * m n) true := by
    intro n
    rw [htwo, List.length_replicate]
  refine sigUniform_of_layer (m := m) (L := fun n => 6 * (2 * m n)) (mT := mT)
    (lenT := Cob.catL [twoT, twoT, twoT, twoT, twoT, twoT])
    (blkT := CircCode.selBlk aT bT cT twoT) (K := K + 11)
    (tmpl := fun n => selLayerF (A n) (B n) (C n) (2 * m n)) hm ?_ ?_ ?_ ?_ ?_ ?_
  · intro x
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, htwo x, ← List.replicate_add]
    congr 1
    omega
  · intro n c
    exact gateWf_selLayerF (hAf n) (hBf n) (hCf n) c
  · intro n c hc
    have hM : 0 < 2 * m n := by beta_reduce at hc; omega
    exact inpLt_selLayerF hM (hAi n) (hBi n) (hCi n) c
  · intro n y c
    exact CircCode.eval_selBlk (fun j => hAt n y j) (fun j => hBt n y j) (fun j => hCt n y j)
      (hw n)
  · intro n c l hc
    refine CircCode.length_encGate_selLayerF (hAb n) (hBb n) (hCb n) ?_ c l hc
    simp only [length_dmW]
    omega
  · intro n args hlen hle
    refine Eq.trans ?_ (hval n args hlen hle)
    refine List.map_congr_left ?_
    intro j hj
    have hjm : j < 2 * m n := List.mem_range.mp hj
    exact lval_selLayerF_row6 (by omega) (hAf n) (hBf n) (hCf n) hjm

end Complexity
