/-
# A P-uniform circuit family for a language that is not regular

`Start/UniformAuto.lean` shows that every *regular* language is decided by a P-uniform circuit
family, by a chain of blocks of a size that does not depend on the input length.  This module goes
past finite-state computation: the language

`Complexity.Maj` — the words in which at least half of the bits are `true`

is decided by a P-uniform family whose blocks *grow* with the input length.  The circuit is the
triangular counting grid: the gate of row `3 * t`, column `j` says that at least `j` of the first
`t` bits of the input are `true`, and the row is updated by

`c(t+1, j) = c(t, j) ∨ (c(t, j - 1) ∧ x t)`.

The descriptions of the family are written by a single Cobham term through
`Complexity.codeUniform_gridLayer`, whose Euclidean division in unary is what recovers the row and
the column of a gate from its identifier.
-/
import Start.UniformAuto
import Start.UniformGrid
import Start.UniformDecide

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### The template of the counting grid -/

/-- The gate of the counting grid at row `i`, column `j`, for an input of length `n`.

Row `0` holds the counts of the empty prefix.  The three rows `3 * t + 1`, `3 * t + 2`,
`3 * t + 3` process the bit `t`: the first copies the bit, the second forms the conjunctions
`c(t, j - 1) ∧ x t`, and the third the new counts. -/
def majT (n i j : ℕ) : Gate :=
  if i = 0 then .cst (decide (j = 0))
  else if i % 3 = 1 then .inp (2 * (i / 3) + 1)
  else if i % 3 = 2 then
    (if j = 0 then .cst false
      else .conj ((n + 1) * (i - 2) + (j - 1)) ((n + 1) * (i - 1) + j))
  else
    (if j = 0 then .disj ((n + 1) * (i - 3)) ((n + 1) * (i - 3))
      else .disj ((n + 1) * (i - 3) + j) ((n + 1) * (i - 1) + j))

/-- The template of the grid as a function of the identifier of the gate. -/
def majF (n c : ℕ) : Gate := majT n (c / (n + 1)) (c % (n + 1))

theorem div_col (n i j : ℕ) (hj : j < n + 1) : ((n + 1) * i + j) / (n + 1) = i := by
  rw [Nat.mul_add_div (Nat.succ_pos n), Nat.div_eq_of_lt hj, Nat.add_zero]

theorem mod_col (n i j : ℕ) (hj : j < n + 1) : ((n + 1) * i + j) % (n + 1) = j := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

theorem majF_block (n i j : ℕ) (hj : j < n + 1) : majF n ((n + 1) * i + j) = majT n i j := by
  rw [majF, div_col n i j hj, mod_col n i j hj]

theorem majT_zero (n j : ℕ) : majT n 0 j = .cst (decide (j = 0)) := by rw [majT, if_pos rfl]

theorem majT_bit (n t : ℕ) (j : ℕ) : majT n (3 * t + 1) j = .inp (2 * t + 1) := by
  rw [majT, if_neg (by omega), if_pos (by omega)]
  have e : (3 * t + 1) / 3 = t := by omega
  rw [e]

theorem majT_and_zero (n t : ℕ) : majT n (3 * t + 2) 0 = .cst false := by
  rw [majT, if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos rfl]

theorem majT_and (n t j : ℕ) (hj : 0 < j) :
    majT n (3 * t + 2) j
      = .conj ((n + 1) * (3 * t) + (j - 1)) ((n + 1) * (3 * t + 1) + j) := by
  rw [majT, if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega)]
  have e1 : 3 * t + 2 - 2 = 3 * t := by omega
  have e2 : 3 * t + 2 - 1 = 3 * t + 1 := by omega
  rw [e1, e2]

theorem majT_cnt_zero (n t : ℕ) :
    majT n (3 * t + 3) 0 = .disj ((n + 1) * (3 * t)) ((n + 1) * (3 * t)) := by
  rw [majT, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  have e : 3 * t + 3 - 3 = 3 * t := by omega
  rw [e]

theorem majT_cnt (n t j : ℕ) (hj : 0 < j) :
    majT n (3 * t + 3) j
      = .disj ((n + 1) * (3 * t) + j) ((n + 1) * (3 * t + 2) + j) := by
  rw [majT, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have e1 : 3 * t + 3 - 3 = 3 * t := by omega
  have e2 : 3 * t + 3 - 1 = 3 * t + 2 := by omega
  rw [e1, e2]

theorem majT_mod1 (n i j : ℕ) (h0 : i ≠ 0) (h : i % 3 = 1) :
    majT n i j = .inp (2 * (i / 3) + 1) := by
  rw [majT, if_neg h0, if_pos h]

theorem majT_mod2_zero (n i : ℕ) (h0 : i ≠ 0) (h : i % 3 = 2) : majT n i 0 = .cst false := by
  rw [majT, if_neg h0, if_neg (by omega), if_pos h, if_pos rfl]

theorem majT_mod2 (n i j : ℕ) (h0 : i ≠ 0) (h : i % 3 = 2) (hj : j ≠ 0) :
    majT n i j = .conj ((n + 1) * (i - 2) + (j - 1)) ((n + 1) * (i - 1) + j) := by
  rw [majT, if_neg h0, if_neg (by omega), if_pos h, if_neg hj]

theorem majT_mod0_zero (n i : ℕ) (h0 : i ≠ 0) (h : i % 3 = 0) :
    majT n i 0 = .disj ((n + 1) * (i - 3)) ((n + 1) * (i - 3)) := by
  rw [majT, if_neg h0, if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem majT_mod0 (n i j : ℕ) (h0 : i ≠ 0) (h : i % 3 = 0) (hj : j ≠ 0) :
    majT n i j = .disj ((n + 1) * (i - 3) + j) ((n + 1) * (i - 1) + j) := by
  rw [majT, if_neg h0, if_neg (by omega), if_neg (by omega), if_neg hj]

/-! ### Well-formedness -/

theorem mul_col_lt (n j : ℕ) {a b : ℕ} (hab : a < b) :
    (n + 1) * a + n < (n + 1) * b + j := by
  have h1 : (n + 1) * (a + 1) ≤ (n + 1) * b := Nat.mul_le_mul_left _ (by omega)
  have h2 : (n + 1) * (a + 1) = (n + 1) * a + (n + 1) := by ring
  omega

theorem gateWf_majT (n i j : ℕ) (hj : j < n + 1) :
    gateWf ((n + 1) * i + j) (majT n i j) := by
  rw [majT]
  split_ifs with h0 h1 h2 hz hz
  · exact trivial
  · exact trivial
  · exact trivial
  · have k1 := mul_col_lt n j (show i - 2 < i by omega)
    have k2 := mul_col_lt n j (show i - 1 < i by omega)
    exact ⟨by omega, by omega⟩
  · have k := mul_col_lt n j (show i - 3 < i by omega)
    exact ⟨by omega, by omega⟩
  · have k1 := mul_col_lt n j (show i - 3 < i by omega)
    have k2 := mul_col_lt n j (show i - 1 < i by omega)
    exact ⟨by omega, by omega⟩

theorem gateWf_majF (n c : ℕ) : gateWf c (majF n c) := by
  have h : (n + 1) * (c / (n + 1)) + c % (n + 1) = c := Nat.div_add_mod c (n + 1)
  rw [majF]
  conv_lhs => rw [← h]
  exact gateWf_majT n _ _ (Nat.mod_lt c (Nat.succ_pos n))

/-! ### The semantics of the grid -/

/-- The number of `true` bits among the first `t` bits presented by the input `y`. -/
def cntTo (y : Word) : ℕ → ℕ
  | 0 => 0
  | t + 1 => cntTo y t + (if y.getD (2 * t + 1) false = true then 1 else 0)

theorem lval_maj_ref {n j r : ℕ} {y : Word} (hr : r < j) :
    (vals y (layer (majF n) j)).getD r false = lval y (majF n) r :=
  vals_layer_getD y (majF n) j r hr

theorem lval_maj_bit (n t j : ℕ) (y : Word) (hj : j < n + 1) :
    lval y (majF n) ((n + 1) * (3 * t + 1) + j) = y.getD (2 * t + 1) false := by
  rw [lval, majF_block n (3 * t + 1) j hj, majT_bit]
  rfl

theorem lval_maj_count (n : ℕ) (y : Word) :
    ∀ t j : ℕ, j < n + 1 →
      lval y (majF n) ((n + 1) * (3 * t) + j) = decide (j ≤ cntTo y t) := by
  intro t
  induction t with
  | zero =>
      intro j hj
      have h : (n + 1) * (3 * 0) + j = (n + 1) * 0 + j := by ring
      rw [h, lval, majF_block n 0 j hj, majT_zero]
      simp [gateVal, cntTo]
  | succ t ih =>
      intro j hj
      have hand : ∀ j', 0 < j' → j' < n + 1 →
          lval y (majF n) ((n + 1) * (3 * t + 2) + j')
            = (decide (j' - 1 ≤ cntTo y t) && y.getD (2 * t + 1) false) := by
        intro j' h0 h1
        have r1 : (n + 1) * (3 * t) + (j' - 1) < (n + 1) * (3 * t + 2) + j' := by
          have := mul_col_lt n j' (show 3 * t < 3 * t + 2 by omega)
          omega
        have r2 : (n + 1) * (3 * t + 1) + j' < (n + 1) * (3 * t + 2) + j' := by
          have := mul_col_lt n j' (show 3 * t + 1 < 3 * t + 2 by omega)
          omega
        rw [lval, majF_block n (3 * t + 2) j' h1, majT_and n t j' h0, gateVal,
          lval_maj_ref r1, lval_maj_ref r2, ih (j' - 1) (by omega), lval_maj_bit n t j' y h1]
      have hidx : (n + 1) * (3 * (t + 1)) + j = (n + 1) * (3 * t + 3) + j := by ring
      rw [hidx]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · have r1 : (n + 1) * (3 * t) + 0 < (n + 1) * (3 * t + 3) + 0 := by
          have := mul_col_lt n 0 (show 3 * t < 3 * t + 3 by omega)
          omega
        rw [lval, majF_block n (3 * t + 3) 0 hj, majT_cnt_zero, gateVal]
        rw [show (n + 1) * (3 * t) = (n + 1) * (3 * t) + 0 from rfl, lval_maj_ref r1, ih 0 hj]
        simp
      · have r1 : (n + 1) * (3 * t) + j < (n + 1) * (3 * t + 3) + j := by
          have := mul_col_lt n j (show 3 * t < 3 * t + 3 by omega)
          omega
        have r2 : (n + 1) * (3 * t + 2) + j < (n + 1) * (3 * t + 3) + j := by
          have := mul_col_lt n j (show 3 * t + 2 < 3 * t + 3 by omega)
          omega
        rw [lval, majF_block n (3 * t + 3) j hj, majT_cnt n t j hj0, gateVal,
          lval_maj_ref r1, lval_maj_ref r2, ih j hj, hand j hj0 hj, cntTo]
        cases y.getD (2 * t + 1) false <;>
          by_cases hc : j ≤ cntTo y t <;> by_cases hc2 : j - 1 ≤ cntTo y t <;>
            simp [hc, hc2] <;> omega

/-! ### The circuit -/

/-- The counting grid for inputs of length `n`. -/
def majGrid (n : ℕ) : Circuit := layer (majF n) ((n + 1) * (3 * n + 1))

@[simp] theorem length_majGrid (n : ℕ) : (majGrid n).length = (n + 1) * (3 * n + 1) := by
  simp [majGrid]

theorem wf_majGrid (n : ℕ) : wf (majGrid n) :=
  wf_layer fun c _ => gateWf_majF n c

/-- The identifier of the gate holding the verdict: the count `⌈n/2⌉` after the whole input has
been read. -/
def majIdx (n : ℕ) : ℕ := (n + 1) * (3 * n) + (n + 1) / 2

theorem majIdx_lt (n : ℕ) : majIdx n < (n + 1) * (3 * n + 1) := by
  have h : (n + 1) * (3 * n + 1) = (n + 1) * (3 * n) + (n + 1) := by ring
  have h2 : (n + 1) / 2 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by norm_num)
  rw [majIdx, h]
  omega

/-- The deciding circuit: the counting grid with the selected count on top. -/
def majC (n : ℕ) : Circuit := Gate.disj (majIdx n) (majIdx n) :: majGrid n

theorem majC_ne_nil (n : ℕ) : majC n ≠ [] := by simp [majC]

theorem wf_majC (n : ℕ) : wf (majC n) := by
  refine ⟨?_, wf_majGrid n⟩
  rw [length_majGrid]
  exact ⟨majIdx_lt n, majIdx_lt n⟩

theorem out_majC (n : ℕ) (y : Word) :
    out y (majC n) = decide ((n + 1) / 2 ≤ cntTo y n) := by
  have hhalf : (n + 1) / 2 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by norm_num)
  rw [majC, majGrid, out, gateVal, vals_layer_getD y (majF n) _ _ (majIdx_lt n), majIdx,
    lval_maj_count n y n ((n + 1) / 2) hhalf, Bool.or_self]

/-! ### Uniformity -/

/-- The number of gates of the grid, in unary, from the instance. -/
theorem eval_majCnt (x : Word) :
    (Cob.comp .smash [.comp (.app true) [Cob.comp .smash [Cob.proj 0, Cob.constT [true]]],
        .comp (.app true) [Cob.comp .smash [Cob.proj 0, Cob.constT [true, true, true]]]]).eval [x]
      = List.replicate ((x.length + 1) * (3 * x.length + 1)) true := by
  simp [Nat.mul_comm]

/-- The width of a row, in unary, from the instance. -/
theorem eval_majWid (x : Word) :
    (Cob.comp (.app true) [Cob.comp .smash [Cob.proj 0, Cob.constT [true]]]).eval [x]
      = List.replicate (x.length + 1) true := by
  simp [List.replicate_succ]

/-- The Cobham term for a reference `(n + 1) * (i - k) + col`, from `1^i`, `1^n` and a term for the
column. -/
def tails : ℕ → Cob → Cob
  | 0, t => t
  | k + 1, t => .comp Cob.tail [tails k t]

/-- The Cobham term for a reference `(n + 1) * (i - k) + col`. -/
def majRef (k : ℕ) (col : Cob) : Cob :=
  Cob.catL [.comp .smash [tails k (.proj 1), .comp (.app true) [.proj 3]], col]

/-- The Cobham term writing the gate of the counting grid from its row, its column and the
instance. -/
def majBlk : Cob :=
  .comp Cob.iteC
    [.proj 1,
      .comp Cob.iteC
        [Cob.modT (.proj 1) (Cob.constT [true, true, true]),
          .comp Cob.iteC
            [.comp Cob.tail [Cob.modT (.proj 1) (Cob.constT [true, true, true])],
              .comp Cob.iteC
                [.proj 2,
                  tokTerm 5 (majRef 2 (.comp Cob.tail [.proj 2])) (majRef 1 (.proj 2)),
                  tokTerm 2 (Cob.constT []) (Cob.constT [])],
              tokTerm 1
                (Cob.pre [true]
                  (.comp .smash
                    [Cob.divT (.proj 1) (Cob.constT [true, true, true]),
                      Cob.constT [true, true]]))
                (Cob.constT [])],
          .comp Cob.iteC
            [.proj 2,
              tokTerm 6 (majRef 3 (.proj 2)) (majRef 1 (.proj 2)),
              tokTerm 6 (majRef 3 (Cob.constT [])) (majRef 3 (Cob.constT []))]],
      .comp Cob.iteC
        [.proj 2, tokTerm 2 (Cob.constT []) (Cob.constT []),
          tokTerm 3 (Cob.constT []) (Cob.constT [])]]

theorem eval_tails : ∀ (k : ℕ) {t : Cob} {args : List Word} {i : ℕ},
    t.eval args = List.replicate i true → (tails k t).eval args = List.replicate (i - k) true
  | 0, _, _, _, ht => by simpa [tails] using ht
  | k + 1, t, args, i, ht => by
      rw [tails]
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_tail, eval_tails k ht,
        List.tail_replicate, Nat.sub_sub]

theorem eval_majRef (k : ℕ) {col : Cob} {n i j c : ℕ} {y : Word}
    (hcol : col.eval [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate c true) :
    (majRef k col).eval [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate ((n + 1) * (i - k) + c) true := by
  have hp : (Cob.proj 1).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate i true := by simp
  rw [majRef]
  simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, Cob.eval_comp, Cob.eval_smash, Cob.eval_app, Cob.eval_proj,
    List.getD_cons_zero, List.getD_cons_succ, eval_tails k hp, hcol, List.length_replicate,
    List.length_cons]
  rw [← List.replicate_add]
  congr 1
  ring

theorem eval_majBlk (n i j : ℕ) (y : Word) :
    majBlk.eval [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = encGate (majT n i j) := by
  have hi : (Cob.proj 1).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate i true := by simp
  have hjj : (Cob.proj 2).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate j true := by simp
  have hmod : (Cob.modT (.proj 1) (Cob.constT [true, true, true])).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate (i % 3) true := Cob.eval_modT (by norm_num) hi (by simp)
  have hdiv3 : (Cob.divT (.proj 1) (Cob.constT [true, true, true])).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate (i / 3) true := Cob.eval_divT (by norm_num) hi (by simp)
  have hnil : ∀ m : ℕ, (List.replicate m true = []) = (m = 0) := by
    intro m
    simp
  rw [majBlk]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC, hi, hjj, hmod,
    Cob.eval_tail, List.tail_replicate, hnil]
  by_cases h0 : i = 0
  · subst h0
    by_cases hj0 : j = 0
    · subst hj0
      rw [majT_zero]
      exact eval_tokTerm (Gate.cst true) (by simp [fld1]) (by simp [fld2])
    · simp only [if_neg hj0]
      rw [majT_zero, decide_eq_false hj0]
      exact eval_tokTerm (Gate.cst false) (by simp [fld1]) (by simp [fld2])
  · simp only [if_neg h0]
    have hm3 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases hm3 with hm | hm | hm
    · simp only [hm]
      by_cases hj0 : j = 0
      · subst hj0
        rw [majT_mod0_zero n i h0 hm]
        exact eval_tokTerm (Gate.disj ((n + 1) * (i - 3)) ((n + 1) * (i - 3)))
          (by
            simpa [CircCode.fld1, CircCode.fld2] using
              eval_majRef 3 (n := n) (i := i) (j := 0) (y := y) (c := 0) (by simp))
          (by
            simpa [CircCode.fld1, CircCode.fld2] using
              eval_majRef 3 (n := n) (i := i) (j := 0) (y := y) (c := 0) (by simp))
      · simp only [if_neg hj0]
        rw [majT_mod0 n i j h0 hm hj0]
        exact eval_tokTerm (Gate.disj ((n + 1) * (i - 3) + j) ((n + 1) * (i - 1) + j))
          (eval_majRef 3 hjj) (eval_majRef 1 hjj)
    · simp only [hm, if_neg (by omega : ¬ (1 : ℕ) = 0)]
      rw [majT_mod1 n i j h0 hm]
      refine eval_tokTerm (Gate.inp (2 * (i / 3) + 1)) ?_ (by simp [fld2])
      simp only [Cob.eval_pre, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash,
        hdiv3, Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ,
        List.length_replicate, List.length_cons, List.length_nil, fld1]
      rw [show 2 * (i / 3) + 1 = 1 + i / 3 * 2 by ring, List.replicate_add]
      rfl
    · simp only [hm, if_neg (by omega : ¬ (2 : ℕ) = 0), if_neg (by omega : ¬ (2 - 1 : ℕ) = 0)]
      by_cases hj0 : j = 0
      · subst hj0
        rw [majT_mod2_zero n i h0 hm]
        exact eval_tokTerm (Gate.cst false) (by simp [fld1]) (by simp [fld2])
      · simp only [if_neg hj0]
        rw [majT_mod2 n i j h0 hm hj0]
        refine eval_tokTerm (Gate.conj ((n + 1) * (i - 2) + (j - 1)) ((n + 1) * (i - 1) + j))
          (eval_majRef 2 ?_) (eval_majRef 1 hjj)
        simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_tail, hjj,
          List.tail_replicate]

theorem length_encGate_majT (n i j l : ℕ) (hj : j < n + 1) (hl : (n + 1) * i + j ≤ l) :
    (encGate (majT n i j)).length ≤ 12 * (l + n + 1) := by
  have hm1 : (n + 1) * (i - 1) ≤ (n + 1) * i := Nat.mul_le_mul_left _ (by omega)
  have hm2 : (n + 1) * (i - 2) ≤ (n + 1) * i := Nat.mul_le_mul_left _ (by omega)
  have hm3 : (n + 1) * (i - 3) ≤ (n + 1) * i := Nat.mul_le_mul_left _ (by omega)
  have hi : i ≤ (n + 1) * i := Nat.le_mul_of_pos_left i (Nat.succ_pos n)
  have hdiv : i / 3 ≤ i := Nat.div_le_self i 3
  have htag := (tag_le (majT n i j)).2
  have hf : fld1 (majT n i j) + fld2 (majT n i j) ≤ 2 * l + 1 := by
    rw [majT]
    split_ifs <;> simp only [fld1, fld2] <;> omega
  rw [length_encGate]
  omega

end CircCode

/-- **The counting grid is a P-uniform family.** -/
theorem codeUniform_majGrid : CodeUniform CircCode.majGrid := by
  have h := codeUniform_gridLayer (K := 12) (w := fun n => n + 1)
    (k := fun n => (n + 1) * (3 * n + 1)) (tmpl := CircCode.majT) (gblk := CircCode.majBlk)
    (cnt := .comp .smash [.comp (.app true) [Cob.comp .smash [Cob.proj 0, Cob.constT [true]]],
      .comp (.app true) [Cob.comp .smash [Cob.proj 0, Cob.constT [true, true, true]]]])
    (widT := .comp (.app true) [Cob.comp .smash [Cob.proj 0, Cob.constT [true]]])
    (fun n => Nat.succ_pos n) CircCode.eval_majCnt CircCode.eval_majWid
    CircCode.eval_majBlk CircCode.length_encGate_majT
  exact h

namespace CircCode

/-- The identifier of the selected gate, in unary, from the instance. -/
def majIdxT : Cob :=
  Cob.catL
    [.comp .smash
      [.comp (.app true) [.comp .smash [Cob.proj 0, Cob.constT [true]]],
        .comp .smash [Cob.proj 0, Cob.constT [true, true, true]]],
      Cob.divT (.comp (.app true) [.comp .smash [Cob.proj 0, Cob.constT [true]]])
        (Cob.constT [true, true])]

theorem eval_majIdxT (x : Word) :
    majIdxT.eval [x] = List.replicate (majIdx x.length) true := by
  have hwid : (Cob.comp (.app true) [Cob.comp .smash [Cob.proj 0, Cob.constT [true]]]).eval [x]
      = List.replicate (x.length + 1) true := eval_majWid x
  have hdiv : (Cob.divT (.comp (.app true) [.comp .smash [Cob.proj 0, Cob.constT [true]]])
      (Cob.constT [true, true])).eval [x] = List.replicate ((x.length + 1) / 2) true :=
    Cob.eval_divT (by norm_num) hwid (by simp)
  rw [majIdxT]
  simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, hdiv]
  simp only [Cob.eval_comp, Cob.eval_smash, List.map_cons, List.map_nil, Cob.eval_proj,
    List.getD_cons_zero, List.getD_cons_succ, hwid, List.length_replicate, Cob.eval_constT,
    List.length_cons, List.length_nil]
  rw [← List.replicate_add, majIdx]
  congr 1
  ring

end CircCode

/-- **The deciding circuits of the majority language are a P-uniform family.** -/
theorem codeUniform_majC : CodeUniform CircCode.majC := by
  have hgate : CodeUniform
      (fun n => [Tseitin.Gate.disj (CircCode.majIdx n) (CircCode.majIdx n)]) :=
    codeUniform_gate (t := 6) (aT := CircCode.majIdxT) (bT := CircCode.majIdxT)
      (fun _ => rfl) CircCode.eval_majIdxT CircCode.eval_majIdxT
  exact codeUniform_append hgate codeUniform_majGrid

/-! ### The language -/

/-- **The majority language**: the words at least half of whose bits are `true`. -/
def Maj : Language := fun x => x.length ≤ 2 * x.count true

theorem count_map_range (y : Word) : ∀ n : ℕ,
    ((List.range n).map (fun i => y.getD (2 * i + 1) false)).count true = CircCode.cntTo y n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.count_append, ih, CircCode.cntTo]
      congr 1
      rw [List.getD_eq_getElem?_getD]
      cases hb : y[2 * n + 1]?.getD false <;> simp [hb, List.getD_eq_getElem?_getD]

/-- **The majority language is decided by a P-uniform circuit family**, although it is not
regular: the blocks of this family grow with the length of the input. -/
theorem pUniformDecidable_maj : PUniformDecidable Maj := by
  refine ⟨CircCode.majC, CircCode.majC_ne_nil, CircCode.wf_majC, fun n y hy => ?_,
    codeUniform_majC⟩
  rw [CircCode.out_majC n y, Maj, Tseitin.inWord_of_pinned n y hy, count_map_range y n,
    List.length_map, List.length_range]
  simp only [decide_eq_true_eq]
  omega

/-- **The majority language reduces to SAT in polynomial time**, unconditionally. -/
theorem polyManyOne_SAT_maj : Maj ≤ₘᵖ Sat.SAT :=
  polyManyOne_SAT_of_pUniformDecidable pUniformDecidable_maj

/-! ### The majority language is not regular -/

/-- The state of an automaton after reading `a` bits `true`. -/
def onesState (δ : ℕ → Bool → ℕ) (a : ℕ) : ℕ := (List.replicate a true).foldl (fun s b => δ s b) 0

theorem onesState_lt {m : ℕ} {δ : ℕ → Bool → ℕ} (hm : 0 < m) (hδ : ∀ s b, δ s b < m) (a : ℕ) :
    onesState δ a < m := by
  cases a with
  | zero => exact hm
  | succ a =>
      rw [onesState, List.replicate_succ', List.foldl_append]
      exact hδ _ _

theorem maj_word (a b : ℕ) :
    Maj (List.replicate a true ++ List.replicate b false) ↔ a + b ≤ 2 * a := by
  rw [Maj]
  simp [List.count_replicate]

theorem maj_ne_autoLang_aux {δ : ℕ → Bool → ℕ} {ac : ℕ → Bool} (heq : AutoLang δ ac = Maj)
    {a b : ℕ} (hfe : onesState δ a = onesState δ b) (hab : a < b) : False := by
  have key : ∀ c : ℕ, AutoLang δ ac (List.replicate c true ++ List.replicate b false)
      ↔ ac ((List.replicate b false).foldl (fun s bb => δ s bb) (onesState δ c)) = true := by
    intro c
    rw [AutoLang, List.foldl_append, onesState]
  have h1 := key a
  have h2 := key b
  rw [hfe] at h1
  have hbA : AutoLang δ ac (List.replicate b true ++ List.replicate b false) := by
    rw [heq]
    exact (maj_word b b).2 (by omega)
  have haA : AutoLang δ ac (List.replicate a true ++ List.replicate b false) := h1.2 (h2.1 hbA)
  rw [heq] at haA
  exact absurd ((maj_word a b).1 haA) (by omega)

/-- **The majority language is not the language of any finite automaton**: the counting grid of
this module really goes past finite-state computation. -/
theorem maj_ne_autoLang {m : ℕ} {δ : ℕ → Bool → ℕ} {ac : ℕ → Bool} (hm : 0 < m)
    (hδ : ∀ s b, δ s b < m) : AutoLang δ ac ≠ Maj := by
  intro heq
  obtain ⟨a, -, b, -, hne, hfe⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (m + 1)) (t := Finset.range m)
      (by simp) (fun a _ => Finset.mem_range.2 (onesState_lt hm hδ a))
  -- name the smaller of the two indices
  rcases Nat.lt_or_ge a b with hab | hba
  · exact maj_ne_autoLang_aux heq hfe hab
  · exact maj_ne_autoLang_aux heq hfe.symm (by omega)

end Complexity
