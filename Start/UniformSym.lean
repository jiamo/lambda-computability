/-
# Every uniform symmetric language is P-uniformly decidable

`Start/UniformMaj.lean` builds the counting grid: a P-uniform family of circuits whose gate at
row `3 * n`, column `j` says that at least `j` of the `n` input bits are `true`.  Majority is read
off one fixed column of the last count row.  This module reads off **all** of them at once.

Fix a predicate `acc : ℕ → ℕ → Bool`, `acc n c` being the verdict on a word of length `n` with `c`
bits `true`, and suppose that a single Cobham term decides it from `1^c` and `1^n`.  The language

`Complexity.SymLang acc = { x | acc |x| (number of `true` bits of x) }`

is then decided by a P-uniform family: on top of the counting grid sits a chain of `n + 1` blocks
of six gates, the block `j` computing "exactly `j` bits are `true`" as
`c(j) ∧ ¬c(j + 1)`, masking it with the constant `acc n j` and disjoining the result into a running
accumulator.  The chain is composed with the grid by `Complexity.Tseitin.reroute`, so its circuit
inputs are the gates of the last count row, and both halves are P-uniform, hence so is the whole
(`Complexity.codeUniform_compose`).

Every *symmetric* language with a Cobham-decidable count predicate is therefore P-uniformly
decidable, and reduces to SAT in polynomial time.  Majority is the instance `acc n c = (n ≤ 2 * c)`,
and two further instances are recorded: the words in which exactly half of the bits are `true`, and
the words whose number of `true` bits is divisible by a fixed `k`.

Main definitions:

* `Complexity.CircCode.symT`, `Complexity.CircCode.symTop` — the selection blocks;
* `Complexity.CircCode.symC` — the deciding family;
* `Complexity.SymLang`, `Complexity.CountUniform` — a symmetric language and the uniformity of its
  count predicate.

Main results:

* `Complexity.CircCode.out_symC` — the family computes `acc n c`;
* `Complexity.codeUniform_symC` — its descriptions are written by a single Cobham term;
* `Complexity.pUniformDecidable_symLang` — **every uniform symmetric language is decided by a
  P-uniform circuit family**;
* `Complexity.polyManyOne_SAT_symLang` — hence it reduces to SAT in polynomial time;
* `Complexity.pUniformDecidable_exactHalf`, `Complexity.pUniformDecidable_countMod` — two
  instances.
-/
import Start.UniformMaj

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### The selection blocks -/

/-- The gate at offset `o` of the block `j` of the selection chain.  The circuit input `i` of the
chain is the gate "at least `i` of the input bits are `true`" of the counting grid.

* offset `0`: the threshold `c(j + 1)`, which is `false` when `j = n`;
* offset `1`: its negation;
* offset `2`: the threshold `c(j)`;
* offset `3`: "exactly `j` bits are `true`";
* offset `4`: the same, masked by the constant verdict `acc n j`;
* offset `5`: the running disjunction of the masked bits. -/
def symT (acc : ℕ → ℕ → Bool) (n : ℕ) : ℕ → ℕ → Gate
  | 0, j => if j < n then .inp (j + 1) else .cst false
  | 1, j => .neg (6 * j)
  | 2, j => .inp j
  | 3, j => .conj (6 * j + 2) (6 * j + 1)
  | 4, j => if acc n j then .conj (6 * j + 3) (6 * j + 3) else .cst false
  | 5, j => if j = 0 then .disj 4 4 else .disj (6 * j + 4) (6 * (j - 1) + 5)
  | _, _ => .cst false

/-- The template of the selection chain as a function of the identifier of the gate. -/
def symF (acc : ℕ → ℕ → Bool) (n c : ℕ) : Gate := symT acc n (c % 6) (c / 6)

/-- The selection chain: `n + 1` blocks of six gates. -/
def symTop (acc : ℕ → ℕ → Bool) (n : ℕ) : Circuit := layer (symF acc n) (6 * (n + 1))

theorem symF_block (acc : ℕ → ℕ → Bool) (n o j : ℕ) (ho : o < 6) :
    symF acc n (6 * j + o) = symT acc n o j := by
  rw [symF, Nat.mul_add_mod, Nat.mod_eq_of_lt ho, Nat.mul_add_div (by norm_num),
    Nat.div_eq_of_lt ho, Nat.add_zero]

/-! ### Well-formedness -/

theorem gateWf_symT (acc : ℕ → ℕ → Bool) (n o j : ℕ) : gateWf (6 * j + o) (symT acc n o j) := by
  match o with
  | 0 => rw [symT]; split_ifs <;> exact trivial
  | 1 => exact (by omega : 6 * j < 6 * j + 1)
  | 2 => exact trivial
  | 3 => exact ⟨by omega, by omega⟩
  | 4 =>
      rw [symT]
      split_ifs
      · exact ⟨by omega, by omega⟩
      · exact trivial
  | 5 =>
      rw [symT]
      split_ifs with h
      · rw [h]; exact ⟨by omega, by omega⟩
      · exact ⟨by omega, by omega⟩
  | (o + 6) => exact trivial

theorem gateWf_symF (acc : ℕ → ℕ → Bool) (n c : ℕ) : gateWf c (symF acc n c) := by
  have h : 6 * (c / 6) + c % 6 = c := by omega
  rw [symF]
  conv_lhs => rw [← h]
  exact gateWf_symT acc n (c % 6) (c / 6)

theorem wf_symTop (acc : ℕ → ℕ → Bool) (n : ℕ) : wf (symTop acc n) :=
  wf_layer fun c _ => gateWf_symF acc n c

theorem inpLt_symT (acc : ℕ → ℕ → Bool) (n o j : ℕ) (hj : j < n + 1) :
    inpLt (n + 1) (symT acc n o j) := by
  match o with
  | 0 =>
      rw [symT]
      split_ifs with h
      · exact (by omega : j + 1 < n + 1)
      · exact trivial
  | 1 => exact trivial
  | 2 => exact hj
  | 3 => exact trivial
  | 4 => rw [symT]; split_ifs <;> exact trivial
  | 5 => rw [symT]; split_ifs <;> exact trivial
  | (o + 6) => exact trivial

theorem inpsLt_symTop (acc : ℕ → ℕ → Bool) (n : ℕ) : inpsLt (n + 1) (symTop acc n) := by
  intro g hg
  obtain ⟨c, hc, rfl⟩ := mem_layer hg
  rw [symF]
  exact inpLt_symT acc n (c % 6) (c / 6) (by omega)

/-! ### The semantics of the chain -/

theorem lval_sym_ref {acc : ℕ → ℕ → Bool} {n c r : ℕ} {z : Word} (hr : r < c) :
    (vals z (layer (symF acc n) c)).getD r false = lval z (symF acc n) r :=
  vals_layer_getD z (symF acc n) c r hr

theorem lval_sym0 (acc : ℕ → ℕ → Bool) (n j : ℕ) (z : Word) :
    lval z (symF acc n) (6 * j) = if j < n then z.getD (j + 1) false else false := by
  have h : 6 * j = 6 * j + 0 := rfl
  rw [h, lval, symF_block acc n 0 j (by norm_num), symT]
  split_ifs with hj <;> rfl

theorem lval_sym1 (acc : ℕ → ℕ → Bool) (n j : ℕ) (z : Word) :
    lval z (symF acc n) (6 * j + 1) = !(if j < n then z.getD (j + 1) false else false) := by
  rw [lval, symF_block acc n 1 j (by norm_num), symT, gateVal,
    lval_sym_ref (acc := acc) (n := n) (z := z) (show 6 * j < 6 * j + 1 by omega),
    lval_sym0]

theorem lval_sym2 (acc : ℕ → ℕ → Bool) (n j : ℕ) (z : Word) :
    lval z (symF acc n) (6 * j + 2) = z.getD j false := by
  rw [lval, symF_block acc n 2 j (by norm_num), symT]
  rfl

theorem lval_sym3 (acc : ℕ → ℕ → Bool) (n j : ℕ) (z : Word) :
    lval z (symF acc n) (6 * j + 3)
      = (z.getD j false && !(if j < n then z.getD (j + 1) false else false)) := by
  rw [lval, symF_block acc n 3 j (by norm_num), symT, gateVal,
    lval_sym_ref (acc := acc) (n := n) (z := z) (show 6 * j + 2 < 6 * j + 3 by omega),
    lval_sym_ref (acc := acc) (n := n) (z := z) (show 6 * j + 1 < 6 * j + 3 by omega),
    lval_sym1, lval_sym2]

/-- On a threshold word the gate at offset `3` says that exactly `j` bits are `true`. -/
theorem lval_sym_exact {acc : ℕ → ℕ → Bool} {n j cnt : ℕ} {z : Word} (hcnt : cnt ≤ n) (hj : j ≤ n)
    (hz : ∀ i, i ≤ n → z.getD i false = decide (i ≤ cnt)) :
    lval z (symF acc n) (6 * j + 3) = decide (j = cnt) := by
  rw [lval_sym3, hz j hj]
  by_cases hjn : j < n
  · rw [if_pos hjn, hz (j + 1) (by omega)]
    by_cases h1 : j ≤ cnt <;> by_cases h2 : j + 1 ≤ cnt <;>
      simp only [h1, h2, decide_true, decide_false, Bool.not_true, Bool.not_false,
        Bool.and_true, Bool.and_false] <;>
      · symm
        first
          | (rw [decide_eq_true_iff]; omega)
          | (rw [decide_eq_false_iff_not]; omega)
  · rw [if_neg hjn]
    have hjn' : j = n := by omega
    subst hjn'
    by_cases h1 : j ≤ cnt <;>
      simp only [h1, decide_true, decide_false, Bool.not_false, Bool.and_true] <;>
      · symm
        first
          | (rw [decide_eq_true_iff]; omega)
          | (rw [decide_eq_false_iff_not]; omega)

theorem lval_sym4 {acc : ℕ → ℕ → Bool} {n j cnt : ℕ} {z : Word} (hcnt : cnt ≤ n) (hj : j ≤ n)
    (hz : ∀ i, i ≤ n → z.getD i false = decide (i ≤ cnt)) :
    lval z (symF acc n) (6 * j + 4) = (acc n j && decide (j = cnt)) := by
  rw [lval, symF_block acc n 4 j (by norm_num), symT]
  by_cases ha : acc n j
  · rw [if_pos ha, ha, gateVal,
      lval_sym_ref (acc := acc) (n := n) (z := z) (show 6 * j + 3 < 6 * j + 4 by omega),
      lval_sym_exact hcnt hj hz, Bool.and_self, Bool.true_and]
  · have ha' : acc n j = false := by simpa using ha
    rw [if_neg ha, ha', Bool.false_and]
    rfl

/-- The accumulator of the block `j` is the verdict, provided the count is at most `j`. -/
theorem lval_sym5 {acc : ℕ → ℕ → Bool} {n cnt : ℕ} {z : Word} (hcnt : cnt ≤ n)
    (hz : ∀ i, i ≤ n → z.getD i false = decide (i ≤ cnt)) :
    ∀ j, j ≤ n → lval z (symF acc n) (6 * j + 5) = (if cnt ≤ j then acc n cnt else false) := by
  intro j
  induction j with
  | zero =>
      intro _
      rw [lval, symF_block acc n 5 0 (by norm_num), symT, if_pos rfl, gateVal]
      have h4 : (4 : ℕ) = 6 * 0 + 4 := by norm_num
      rw [h4, lval_sym_ref (acc := acc) (n := n) (z := z) (show 6 * 0 + 4 < 6 * 0 + 5 by omega),
        lval_sym4 hcnt (by omega) hz, Bool.or_self]
      rcases Nat.eq_zero_or_pos cnt with rfl | hpos
      · simp
      · have e1 : ¬ (0 = cnt) := by omega
        have e2 : ¬ (cnt ≤ 0) := by omega
        simp [e1, e2]
  | succ j ih =>
      intro hj
      rw [lval, symF_block acc n 5 (j + 1) (by norm_num), symT, if_neg (by omega), gateVal]
      have he : 6 * (j + 1 - 1) + 5 = 6 * j + 5 := by omega
      rw [he,
        lval_sym_ref (acc := acc) (n := n) (z := z)
          (show 6 * (j + 1) + 4 < 6 * (j + 1) + 5 by omega),
        lval_sym_ref (acc := acc) (n := n) (z := z)
          (show 6 * j + 5 < 6 * (j + 1) + 5 by omega),
        lval_sym4 hcnt hj hz, ih (by omega)]
      by_cases h1 : cnt ≤ j
      · have e1 : ¬ (j + 1 = cnt) := by omega
        have e2 : cnt ≤ j + 1 := by omega
        simp [h1, e1, e2]
      · by_cases h2 : cnt = j + 1
        · subst h2
          simp [h1]
        · have e1 : ¬ (j + 1 = cnt) := by omega
          have e2 : ¬ (cnt ≤ j + 1) := by omega
          simp [h1, e1, e2]

theorem out_symTop {acc : ℕ → ℕ → Bool} {n cnt : ℕ} {z : Word} (hcnt : cnt ≤ n)
    (hz : ∀ i, i ≤ n → z.getD i false = decide (i ≤ cnt)) :
    out z (symTop acc n) = acc n cnt := by
  have hlen : 6 * (n + 1) = (6 * n + 5) + 1 := by ring
  rw [symTop, hlen, out_layer]
  have h := lval_sym5 (acc := acc) hcnt hz n (le_refl n)
  rw [show 6 * n + 5 = 6 * n + 5 from rfl] at h
  rw [h, if_pos hcnt]

/-! ### Writing the description -/

/-- The Cobham term computing `1^{q·i+r}` from a term evaluating to `1^i`. -/
def mulAddT (q r : ℕ) (t : Cob) : Cob :=
  Cob.pre (List.replicate r true) (.comp .smash [t, Cob.constT (List.replicate q true)])

theorem eval_mulAddT {q r i v : ℕ} {t : Cob} {args : List Word}
    (ht : t.eval args = List.replicate i true) (hv : r + i * q = v) :
    (mulAddT q r t).eval args = List.replicate v true := by
  subst hv
  rw [mulAddT]
  simp only [Cob.eval_pre, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, ht,
    Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ, List.length_replicate]
  rw [← List.replicate_add]

/-- A conditional on whether a term evaluates to the empty word. -/
theorem eval_iteNe {c s t : Cob} {args : List Word} {w a b : Word}
    (hc : c.eval args = w) (hs : s.eval args = a) (ht : t.eval args = b) :
    (Cob.iteT c s t).eval args = if w = [] then b else a := by
  simp only [Cob.iteT, Cob.eval_comp, List.map_cons, List.map_nil, hc, hs, ht, Cob.eval_iteC]

/-- The Cobham term writing the gate at offset `s` of the block `j` of the selection chain, from
`1^j` and `1^n`.  The verdict `acc n j` is decided by `accT` while the description is written. -/
def symBlkT (accT : Cob) : ℕ → Cob
  | 0 =>
      Cob.iteT (.comp Cob.dropU [.proj 1, .proj 2])
        (tokTerm 1 (linT 1 1 1) Cob.empty) (tokTerm 2 Cob.empty Cob.empty)
  | 1 => tokTerm 4 (linT 1 6 0) Cob.empty
  | 2 => tokTerm 1 (.proj 1) Cob.empty
  | 3 => tokTerm 5 (linT 1 6 2) (linT 1 6 1)
  | 4 =>
      Cob.iteT (.comp accT [.proj 1, .proj 2])
        (tokTerm 5 (linT 1 6 3) (linT 1 6 3)) (tokTerm 2 Cob.empty Cob.empty)
  | 5 =>
      Cob.iteT (.proj 1)
        (tokTerm 6 (linT 1 6 4) (mulAddT 6 5 (.comp Cob.tail [.proj 1])))
        (tokTerm 6 (Cob.constT (List.replicate 4 true)) (Cob.constT (List.replicate 4 true)))
  | _ => tokTerm 2 Cob.empty Cob.empty

theorem eval_symBlkT {accT : Cob} {acc : ℕ → ℕ → Bool}
    (hacc : ∀ j n : ℕ, accT.eval [List.replicate j true, List.replicate n true] = bw (acc n j))
    (n : ℕ) (y : Word) (s j : ℕ) :
    (symBlkT accT s).eval [y, List.replicate j true, List.replicate n true]
      = encGate (symT acc n s j) := by
  have hJ : (Cob.proj 1).eval [y, List.replicate j true, List.replicate n true]
      = List.replicate j true := by simp
  have hJa : ([y, List.replicate j true, List.replicate n true] : List Word).getD 1 []
      = List.replicate j true := by simp
  have hnil : ∀ m : ℕ, (List.replicate m true = []) = (m = 0) := by
    intro m; simp
  have hfalse : (tokTerm 2 Cob.empty Cob.empty).eval
      [y, List.replicate j true, List.replicate n true] = encGate (Gate.cst false) :=
    eval_tokTerm (Gate.cst false) (by simp [fld1]) (by simp [fld2])
  match s with
  | 0 =>
      have hcond : (Cob.comp Cob.dropU [Cob.proj 1, Cob.proj 2]).eval
          [y, List.replicate j true, List.replicate n true] = List.replicate (n - j) true := by
        simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
          List.getD_cons_zero, List.getD_cons_succ, Cob.eval_dropU, List.length_replicate,
          List.drop_replicate]
      have hA : (tokTerm 1 (linT 1 1 1) Cob.empty).eval
          [y, List.replicate j true, List.replicate n true] = encGate (Gate.inp (j + 1)) :=
        eval_tokTerm (Gate.inp (j + 1)) (eval_linT hJa (by simp only [fld1]; omega))
          (by simp [fld2])
      rw [symBlkT, eval_iteNe hcond hA hfalse, symT]
      by_cases hj : j < n
      · rw [if_pos hj, if_neg (by rw [hnil]; omega : ¬ List.replicate (n - j) true = [])]
      · rw [if_neg hj, if_pos (by rw [hnil]; omega : List.replicate (n - j) true = [])]
  | 1 =>
      rw [symBlkT, symT]
      exact eval_tokTerm (Gate.neg (6 * j)) (eval_linT hJa (by simp only [fld1]; omega))
        (by simp [fld2])
  | 2 =>
      rw [symBlkT, symT]
      exact eval_tokTerm (Gate.inp j) (by simp [fld1]) (by simp [fld2])
  | 3 =>
      rw [symBlkT, symT]
      exact eval_tokTerm (Gate.conj (6 * j + 2) (6 * j + 1))
        (eval_linT hJa (by simp only [fld1]; omega)) (eval_linT hJa (by simp only [fld2]; omega))
  | 4 =>
      have hcond : (Cob.comp accT [Cob.proj 1, Cob.proj 2]).eval
          [y, List.replicate j true, List.replicate n true] = bw (acc n j) := by
        simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
          List.getD_cons_zero, List.getD_cons_succ]
        exact hacc j n
      have hA : (tokTerm 5 (linT 1 6 3) (linT 1 6 3)).eval
          [y, List.replicate j true, List.replicate n true]
          = encGate (Gate.conj (6 * j + 3) (6 * j + 3)) :=
        eval_tokTerm (Gate.conj (6 * j + 3) (6 * j + 3))
          (eval_linT hJa (by simp only [fld1]; omega)) (eval_linT hJa (by simp only [fld2]; omega))
      rw [symBlkT, eval_iteNe hcond hA hfalse, symT]
      by_cases h : acc n j
      · rw [h]; simp [bw]
      · have h' : acc n j = false := by simpa using h
        rw [h']; simp [bw]
  | 5 =>
      have htl : (Cob.comp Cob.tail [Cob.proj 1]).eval
          [y, List.replicate j true, List.replicate n true] = List.replicate (j - 1) true := by
        simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_tail, hJ,
          List.tail_replicate]
      have hA : (tokTerm 6 (linT 1 6 4) (mulAddT 6 5 (.comp Cob.tail [Cob.proj 1]))).eval
          [y, List.replicate j true, List.replicate n true]
          = encGate (Gate.disj (6 * j + 4) (6 * (j - 1) + 5)) :=
        eval_tokTerm (Gate.disj (6 * j + 4) (6 * (j - 1) + 5))
          (eval_linT hJa (by simp only [fld1]; omega))
          (eval_mulAddT htl (by simp only [fld2]; omega))
      have hB : (tokTerm 6 (Cob.constT (List.replicate 4 true))
            (Cob.constT (List.replicate 4 true))).eval
          [y, List.replicate j true, List.replicate n true] = encGate (Gate.disj 4 4) :=
        eval_tokTerm (Gate.disj 4 4) (by simp [fld1]) (by simp [fld2])
      rw [symBlkT, eval_iteNe hJ hA hB, symT]
      by_cases hj : j = 0
      · rw [if_pos hj, if_pos (by rw [hnil, hj] : List.replicate j true = [])]
      · rw [if_neg hj, if_neg (by rw [hnil]; omega : ¬ List.replicate j true = [])]
  | (s + 6) =>
      have hg : symT acc n (s + 6) j = Gate.cst false := rfl
      have ht : symBlkT accT (s + 6) = tokTerm 2 Cob.empty Cob.empty := rfl
      rw [ht, hg]
      exact hfalse


theorem fld1_symT_le (acc : ℕ → ℕ → Bool) (n s j : ℕ) : fld1 (symT acc n s j) ≤ 6 * j + 5 := by
  match s with
  | 0 => rw [symT]; split_ifs <;> simp only [fld1] <;> omega
  | 1 => simp only [symT, fld1]; omega
  | 2 => simp only [symT, fld1]; omega
  | 3 => simp only [symT, fld1]; omega
  | 4 => rw [symT]; split_ifs <;> simp only [fld1] <;> omega
  | 5 => rw [symT]; split_ifs <;> simp only [fld1] <;> omega
  | (s + 6) => simp only [symT, fld1]; omega

theorem fld2_symT_le (acc : ℕ → ℕ → Bool) (n s j : ℕ) : fld2 (symT acc n s j) ≤ 6 * j + 5 := by
  match s with
  | 0 => rw [symT]; split_ifs <;> simp only [fld2] <;> omega
  | 1 => simp only [symT, fld2]; omega
  | 2 => simp only [symT, fld2]; omega
  | 3 => simp only [symT, fld2]; omega
  | 4 => rw [symT]; split_ifs <;> simp only [fld2] <;> omega
  | 5 => rw [symT]; split_ifs <;> simp only [fld2] <;> omega
  | (s + 6) => simp only [symT, fld2]; omega

theorem length_encGate_symT (acc : ℕ → ℕ → Bool) (n s j l : ℕ) (hj : j ≤ l) :
    (encGate (symT acc n s j)).length ≤ 21 * (l + n + 1) := by
  have h1 := fld1_symT_le acc n s j
  have h2 := fld2_symT_le acc n s j
  have ht := (tag_le (symT acc n s j)).2
  rw [length_encGate]
  omega

/-- The number of gates of the selection chain, in unary, from the instance. -/
theorem eval_symCnt (x : Word) :
    (Cob.pre (List.replicate 6 true)
      (.comp .smash [Cob.proj 0, Cob.constT (List.replicate 6 true)])).eval [x]
      = List.replicate (6 * (x.length + 1)) true := by
  simp only [Cob.eval_pre, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash,
    Cob.eval_proj, List.getD_cons_zero, List.getD_cons_succ, Cob.eval_constT,
    List.length_replicate]
  rw [← List.replicate_add]
  congr 1
  ring

end CircCode

/-- **The selection chain is a P-uniform family.** -/
theorem codeUniform_symTop {acc : ℕ → ℕ → Bool} {accT : Cob}
    (hacc : ∀ j n : ℕ, accT.eval [List.replicate j true, List.replicate n true] = bw (acc n j)) :
    CodeUniform (CircCode.symTop acc) := by
  have h := codeUniform_blockLayer (K₀ := 6) (K := 21) (by norm_num)
    (tmpl := fun n s j => CircCode.symT acc n s j) (k := fun n => 6 * (n + 1))
    (cnt := Cob.pre (List.replicate 6 true)
      (.comp .smash [Cob.proj 0, Cob.constT (List.replicate 6 true)]))
    (blkT := CircCode.symBlkT accT)
    CircCode.eval_symCnt
    (fun n y s c => CircCode.eval_symBlkT hacc n y s c)
    (fun n s c l hc => CircCode.length_encGate_symT acc n s c l hc)
  exact h

/-! ### The deciding family -/

namespace CircCode

open Complexity.Tseitin

/-- The identifier of the first gate of the last count row, in unary, from the instance. -/
theorem eval_symE (x : Word) :
    (Cob.comp .smash [.comp (.app true) [.comp .smash [Cob.proj 0, Cob.constT [true]]],
        .comp .smash [Cob.proj 0, Cob.constT [true, true, true]]]).eval [x]
      = List.replicate ((x.length + 1) * (3 * x.length)) true := by
  simp [Nat.mul_comm]

/-- **The deciding family**: the selection chain composed with the counting grid, its circuit
inputs rewired to the gates of the last count row. -/
def symC (acc : ℕ → ℕ → Bool) (n : ℕ) : Circuit :=
  Tseitin.reroute (majGrid n).length ((n + 1) * (3 * n)) (symTop acc n) ++ majGrid n

theorem cntTo_le (y : Word) : ∀ n : ℕ, cntTo y n ≤ n
  | 0 => le_refl 0
  | n + 1 => by
      rw [cntTo]
      have := cntTo_le y n
      split_ifs <;> omega

theorem getD_drop (l : List Bool) (e i : ℕ) : (l.drop e).getD i false = l.getD (e + i) false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]

theorem symE_le (n : ℕ) : (n + 1) * (3 * n) ≤ (majGrid n).length := by
  rw [length_majGrid]
  exact Nat.mul_le_mul_left _ (by omega)

theorem symE_sub (n : ℕ) : (majGrid n).length - (n + 1) * (3 * n) = n + 1 := by
  have h : (n + 1) * (3 * n + 1) = (n + 1) * (3 * n) + (n + 1) := by ring
  rw [length_majGrid]
  omega

theorem symTop_cons (acc : ℕ → ℕ → Bool) (n : ℕ) :
    symTop acc n = symF acc n (6 * n + 5) :: layer (symF acc n) (6 * n + 5) := by
  rw [symTop, show 6 * (n + 1) = (6 * n + 5) + 1 by ring, layer]

theorem symC_ne_nil (acc : ℕ → ℕ → Bool) (n : ℕ) : symC acc n ≠ [] := by
  rw [symC]
  simp [majGrid, layer, Tseitin.reroute, symTop_cons]

theorem wf_symC (acc : ℕ → ℕ → Bool) (n : ℕ) : wf (symC acc n) :=
  wf_reroute_append (majGrid n) (wf_majGrid n) _ (symE_le n) (symTop acc n) (wf_symTop acc n)
    (by rw [symE_sub]; exact inpsLt_symTop acc n)

/-- **The deciding family computes the verdict on the number of `true` bits.** -/
theorem out_symC (acc : ℕ → ℕ → Bool) (n : ℕ) (y : Word) :
    out y (symC acc n) = acc n (cntTo y n) := by
  have hin : inpsLt ((majGrid n).length - (n + 1) * (3 * n)) (symTop acc n) := by
    rw [symE_sub]; exact inpsLt_symTop acc n
  have hz : ∀ i, i ≤ n →
      ((vals y (majGrid n)).drop ((n + 1) * (3 * n))).getD i false
        = decide (i ≤ cntTo y n) := by
    intro i hi
    have hlt : (n + 1) * (3 * n) + i < (n + 1) * (3 * n + 1) := by
      have h : (n + 1) * (3 * n + 1) = (n + 1) * (3 * n) + (n + 1) := by ring
      omega
    rw [getD_drop, majGrid, vals_layer_getD y (majF n) _ _ hlt,
      lval_maj_count n y n i (by omega)]
  rw [symC]
  have hout := out_reroute_append y (majGrid n) ((n + 1) * (3 * n)) (symE_le n)
    (symF acc n (6 * n + 5)) (layer (symF acc n) (6 * n + 5))
    (by rw [← symTop_cons]; exact wf_symTop acc n) (by rw [← symTop_cons]; exact hin)
  rw [← symTop_cons] at hout
  rw [hout]
  exact out_symTop (cntTo_le y n) hz

end CircCode

/-- **The deciding family is P-uniform.** -/
theorem codeUniform_symC {acc : ℕ → ℕ → Bool} {accT : Cob}
    (hacc : ∀ j n : ℕ, accT.eval [List.replicate j true, List.replicate n true] = bw (acc n j)) :
    CodeUniform (CircCode.symC acc) :=
  codeUniform_compose (codeUniform_symTop hacc) codeUniform_majGrid CircCode.eval_symE

/-! ### Uniform symmetric languages -/

/-- **A symmetric language**: membership depends only on the length of the word and on the number
of its `true` bits. -/
def SymLang (acc : ℕ → ℕ → Bool) : Language := fun x => acc x.length (x.count true) = true

/-- **The count predicate is uniform**: one Cobham term decides `acc n c` from `1^c` and `1^n`. -/
def CountUniform (acc : ℕ → ℕ → Bool) : Prop :=
  ∃ accT : Cob, ∀ j n : ℕ,
    accT.eval [List.replicate j true, List.replicate n true] = bw (acc n j)

/-- **Every symmetric language with a Cobham-decidable count predicate is decided by a P-uniform
circuit family.** -/
theorem pUniformDecidable_symLang {acc : ℕ → ℕ → Bool} (h : CountUniform acc) :
    PUniformDecidable (SymLang acc) := by
  obtain ⟨accT, hacc⟩ := h
  refine ⟨CircCode.symC acc, CircCode.symC_ne_nil acc, CircCode.wf_symC acc, fun n y hy => ?_,
    codeUniform_symC hacc⟩
  rw [CircCode.out_symC acc n y, SymLang, Tseitin.inWord_of_pinned n y hy, count_map_range y n,
    List.length_map, List.length_range]

/-- **Every uniform symmetric language reduces to SAT in polynomial time**, unconditionally. -/
theorem polyManyOne_SAT_symLang {acc : ℕ → ℕ → Bool} (h : CountUniform acc) :
    SymLang acc ≤ₘᵖ Sat.SAT :=
  polyManyOne_SAT_of_pUniformDecidable (pUniformDecidable_symLang h)

/-! ### Instances -/

/-- Comparing `n` with `2 * c` in unary is a Cobham function. -/
theorem countUniform_maj : CountUniform (fun n c => decide (n ≤ 2 * c)) := by
  refine ⟨.comp Cob.notC [.comp Cob.dropU [Cob.catL [.proj 0, .proj 0], .proj 1]], fun j n => ?_⟩
  have hcat : (Cob.catL [Cob.proj 0, Cob.proj 0]).eval
      [List.replicate j true, List.replicate n true] = List.replicate (2 * j) true := by
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, Cob.eval_proj, List.getD_cons_zero]
    rw [← List.replicate_add]
    congr 1
    omega
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
    List.getD_cons_succ, hcat, Cob.eval_dropU, List.length_replicate, List.drop_replicate,
    Cob.eval_notC]
  by_cases h : n ≤ 2 * j
  · rw [if_pos (by simp; omega), decide_eq_true h]
    rfl
  · rw [if_neg (by simp; omega), decide_eq_false h]
    rfl

/-- The majority language is the symmetric language of the predicate `n ≤ 2 * c`. -/
theorem symLang_maj : SymLang (fun n c => decide (n ≤ 2 * c)) = Maj := by
  funext x
  rw [SymLang, Maj]
  simp

/-- **The majority language is P-uniformly decidable**, as an instance of the general theorem. -/
theorem pUniformDecidable_maj' : PUniformDecidable Maj :=
  symLang_maj ▸ pUniformDecidable_symLang countUniform_maj

/-- **The words in which exactly half of the bits are `true`.** -/
def ExactHalf : Language := fun x => x.length = 2 * x.count true

theorem countUniform_exactHalf : CountUniform (fun n c => decide (n = 2 * c)) := by
  refine ⟨Cob.andT (.comp Cob.notC [.comp Cob.dropU [Cob.catL [.proj 0, .proj 0], .proj 1]])
    (.comp Cob.notC [.comp Cob.dropU [.proj 1, Cob.catL [.proj 0, .proj 0]]]), fun j n => ?_⟩
  have hcat : (Cob.catL [Cob.proj 0, Cob.proj 0]).eval
      [List.replicate j true, List.replicate n true] = List.replicate (2 * j) true := by
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, Cob.eval_proj, List.getD_cons_zero]
    rw [← List.replicate_add]
    congr 1
    omega
  have h1 : (Cob.comp Cob.notC [Cob.comp Cob.dropU [Cob.catL [Cob.proj 0, Cob.proj 0],
      Cob.proj 1]]).eval [List.replicate j true, List.replicate n true]
      = bw (decide (n ≤ 2 * j)) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
      List.getD_cons_succ, hcat, Cob.eval_dropU, List.length_replicate, List.drop_replicate,
      Cob.eval_notC]
    by_cases h : n ≤ 2 * j
    · rw [if_pos (by simp; omega), decide_eq_true h]
      rfl
    · rw [if_neg (by simp; omega), decide_eq_false h]
      rfl
  have h2 : (Cob.comp Cob.notC [Cob.comp Cob.dropU [Cob.proj 1,
      Cob.catL [Cob.proj 0, Cob.proj 0]]]).eval [List.replicate j true, List.replicate n true]
      = bw (decide (2 * j ≤ n)) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
      List.getD_cons_succ, hcat, Cob.eval_dropU, List.length_replicate, List.drop_replicate,
      Cob.eval_notC]
    by_cases h : 2 * j ≤ n
    · rw [if_pos (by simp; omega), decide_eq_true h]
      rfl
    · rw [if_neg (by simp; omega), decide_eq_false h]
      rfl
  rw [Cob.eval_andT h1 h2]
  congr 1
  change (decide (n ≤ 2 * j) && decide (2 * j ≤ n)) = decide (n = 2 * j)
  by_cases hle : n ≤ 2 * j
  · by_cases hge : 2 * j ≤ n
    · rw [decide_eq_true hle, decide_eq_true hge, Bool.and_true,
        decide_eq_true (show n = 2 * j by omega)]
    · rw [decide_eq_false hge, Bool.and_false, decide_eq_false (show ¬ n = 2 * j by omega)]
  · rw [decide_eq_false hle, Bool.false_and, decide_eq_false (show ¬ n = 2 * j by omega)]

theorem symLang_exactHalf : SymLang (fun n c => decide (n = 2 * c)) = ExactHalf := by
  funext x
  rw [SymLang, ExactHalf]
  simp

/-- **The words in which exactly half of the bits are `true` form a P-uniformly decidable
language**, and hence reduce to SAT in polynomial time. -/
theorem pUniformDecidable_exactHalf : PUniformDecidable ExactHalf :=
  symLang_exactHalf ▸ pUniformDecidable_symLang countUniform_exactHalf

theorem polyManyOne_SAT_exactHalf : ExactHalf ≤ₘᵖ Sat.SAT :=
  polyManyOne_SAT_of_pUniformDecidable pUniformDecidable_exactHalf

/-- **The words whose number of `true` bits is divisible by `k`.** -/
def CountMod (k : ℕ) : Language := fun x => x.count true % k = 0

theorem countUniform_countMod {k : ℕ} (hk : 0 < k) :
    CountUniform (fun _ c => decide (c % k = 0)) := by
  refine ⟨.comp Cob.notC [Cob.modT (.proj 0) (Cob.constT (List.replicate k true))],
    fun j n => ?_⟩
  have hmod : (Cob.modT (Cob.proj 0) (Cob.constT (List.replicate k true))).eval
      [List.replicate j true, List.replicate n true] = List.replicate (j % k) true :=
    Cob.eval_modT hk (by simp) (by simp)
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, hmod, Cob.eval_notC]
  by_cases h : j % k = 0
  · rw [if_pos (by simp [h]), decide_eq_true h]
    rfl
  · rw [if_neg (by simp [h]), decide_eq_false h]
    rfl

theorem symLang_countMod (k : ℕ) : SymLang (fun _ c => decide (c % k = 0)) = CountMod k := by
  funext x
  rw [SymLang, CountMod]
  simp

/-- **The words whose number of `true` bits is divisible by `k` form a P-uniformly decidable
language.** -/
theorem pUniformDecidable_countMod {k : ℕ} (hk : 0 < k) : PUniformDecidable (CountMod k) :=
  symLang_countMod k ▸ pUniformDecidable_symLang (countUniform_countMod hk)

theorem polyManyOne_SAT_countMod {k : ℕ} (hk : 0 < k) : CountMod k ≤ₘᵖ Sat.SAT :=
  polyManyOne_SAT_of_pUniformDecidable (pUniformDecidable_countMod hk)

/-! ### The class goes past finite-state computation -/

theorem exactHalf_word (a b : ℕ) :
    ExactHalf (List.replicate a true ++ List.replicate b false) ↔ a + b = 2 * a := by
  rw [ExactHalf]
  simp [List.count_replicate]

theorem exactHalf_ne_autoLang_aux {δ : ℕ → Bool → ℕ} {ac : ℕ → Bool}
    (heq : AutoLang δ ac = ExactHalf) {a b : ℕ} (hfe : onesState δ a = onesState δ b)
    (hab : a < b) : False := by
  have key : ∀ c : ℕ, AutoLang δ ac (List.replicate c true ++ List.replicate a false)
      ↔ ac ((List.replicate a false).foldl (fun s bb => δ s bb) (onesState δ c)) = true := by
    intro c
    rw [AutoLang, List.foldl_append, onesState]
  have h1 := key a
  have h2 := key b
  rw [hfe] at h1
  have haA : AutoLang δ ac (List.replicate a true ++ List.replicate a false) := by
    rw [heq]
    exact (exactHalf_word a a).2 (by omega)
  have hbA : AutoLang δ ac (List.replicate b true ++ List.replicate a false) := h2.2 (h1.1 haA)
  rw [heq] at hbA
  exact absurd ((exactHalf_word b a).1 hbA) (by omega)

/-- **The words in which exactly half of the bits are `true` are not the language of any finite
automaton**: this instance of the general theorem is not an instance of
`Complexity.pUniformDecidable_autoLang`. -/
theorem exactHalf_ne_autoLang {m : ℕ} {δ : ℕ → Bool → ℕ} {ac : ℕ → Bool} (hm : 0 < m)
    (hδ : ∀ s b, δ s b < m) : AutoLang δ ac ≠ ExactHalf := by
  intro heq
  obtain ⟨a, -, b, -, hne, hfe⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (m + 1)) (t := Finset.range m)
      (by simp) (fun a _ => Finset.mem_range.2 (onesState_lt hm hδ a))
  rcases Nat.lt_or_ge a b with hab | hba
  · exact exactHalf_ne_autoLang_aux heq hfe hab
  · exact exactHalf_ne_autoLang_aux heq hfe.symm (by omega)

/-- **A regular condition and a uniform count condition may be combined**, by the Boolean closure
of the class. -/
theorem pUniformDecidable_autoLang_and_symLang {m : ℕ} {δ : ℕ → Bool → ℕ} {ac : ℕ → Bool}
    (hm : 0 < m) (hδ : ∀ s b, δ s b < m) {acc : ℕ → ℕ → Bool} (h : CountUniform acc) :
    PUniformDecidable (fun x => AutoLang δ ac x ∧ SymLang acc x) :=
  (pUniformDecidable_autoLang ac hm hδ).and (pUniformDecidable_symLang h)

end Complexity
