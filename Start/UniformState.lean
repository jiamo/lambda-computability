/-
# P-uniform circuits for automata with polynomially many states

`Start/UniformAuto.lean` compiles a *finite* automaton — a fixed number of states, independent of
the input length — into a P-uniform family of circuits, and `Start/UniformMaj.lean` compiles the
counting grid, which is one particular automaton whose state set grows with the input.  This
module unifies and generalizes both: an automaton whose number of states `M = m n` depends on the
length `n` of the input, whose transition function `δ n` and acceptance predicate `ac n` are
computed in unary by Cobham terms, is compiled into a P-uniform family.

The circuit is a grid of width `M`.  Row `0` holds the one-hot encoding of the initial state.  The
`t`-th input bit is processed by a block of `2 * M + 4` rows: a constant `false`, a constant
`true`, the bit itself, its negation, and then, for every state `s`, a *conjunction* row and an
*accumulator* row, whose column `j` holds

`prev[j] ∧ (δ n j x_t = s)` and `⋁_{j' ≤ j} prev[j'] ∧ (δ n j' x_t = s)`

so that the last column of the accumulator row of `s` holds the one-hot bit of `s` after `t + 1`
bits.  A last row accumulates the one-hot bits of the accepting states, and its last column is the
output gate.

This file builds the grid and proves it correct; `Start/UniformStateCode.lean` writes its
description with a single Cobham term and derives the P-uniform decidability of the language.

Main definitions:

* `Complexity.CircCode.stH`, `Complexity.CircCode.stPrevId`, `Complexity.CircCode.stSelK` — the
  layout of the grid: the height of a block, the identifier of a one-hot bit, and the offset of
  the selector of a transition;
* `Complexity.CircCode.stT`, `Complexity.CircCode.stF`, `Complexity.CircCode.stGrid` — the
  template of the grid, as a function of the row and the column and of the gate identifier, and
  the circuit itself;
* `Complexity.CircCode.stRun` — the state of the automaton after `t` bits.

Main results:

* `Complexity.CircCode.wf_stGrid` — the grid is a well-formed circuit;
* `Complexity.CircCode.lval_st_state` — **the one-hot bits of the grid record the state of the
  automaton**;
* `Complexity.CircCode.out_stGrid` — **the grid accepts exactly the words the automaton
  accepts**.
-/
import Start.UniformAuto
import Start.UniformGrid
import Start.UniformDecide

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### The layout of the grid -/

/-- The height of the block processing one input bit: two constants, the bit, its negation, and a
conjunction row and an accumulator row for each of the `M` states. -/
def stH (M : ℕ) : ℕ := 2 * M + 4

theorem stH_pos (M : ℕ) : 0 < stH M := by simp [stH]

/-- The identifier of the gate holding the one-hot bit of the state `u` after `t` input bits: a
gate of the initial row if `t = 0`, and otherwise the last column of the accumulator row of `u` in
the block of the bit `t - 1`. -/
def stPrevId (M t u : ℕ) : ℕ :=
  if t = 0 then u else M * (6 + stH M * (t - 1) + 2 * u) + (M - 1)

/-- The offset, inside a block, of the gate selecting the transitions into the state `s` from the
state `j`: the constant `true` if both bits move `j` to `s`, the bit if only `true` does, its
negation if only `false` does, and the constant `false` otherwise. -/
def stSelK (δ : ℕ → ℕ → Bool → ℕ) (n s j : ℕ) : ℕ :=
  if δ n j true = s then (if δ n j false = s then 1 else 2)
  else (if δ n j false = s then 3 else 0)

theorem stSelK_lt_four (δ : ℕ → ℕ → Bool → ℕ) (n s j : ℕ) : stSelK δ n s j < 4 := by
  rw [stSelK]; split_ifs <;> omega

/-- **The template of the grid**: the gate at row `i`, column `j`, for an automaton with `M`
states on inputs of length `n`. -/
def stT (δ : ℕ → ℕ → Bool → ℕ) (ac : ℕ → ℕ → Bool) (M n i j : ℕ) : Gate :=
  if i = 0 then .cst (decide (j = 0))
  else if n ≤ (i - 1) / stH M then
    (if j = 0 then
      (if ac n 0 then .disj (stPrevId M n 0) (stPrevId M n 0) else .cst false)
     else .disj (M * i + (j - 1)) (if ac n j then stPrevId M n j else M * i + (j - 1)))
  else if (i - 1) % stH M = 0 then .cst false
  else if (i - 1) % stH M = 1 then .cst true
  else if (i - 1) % stH M = 2 then .inp (2 * ((i - 1) / stH M) + 1)
  else if (i - 1) % stH M = 3 then .neg (M * (i - 1))
  else if ((i - 1) % stH M - 4) % 2 = 0 then
    .conj (stPrevId M ((i - 1) / stH M) j)
      (M * (1 + stH M * ((i - 1) / stH M) + stSelK δ n (((i - 1) % stH M - 4) / 2) j))
  else if j = 0 then .disj (M * (i - 1)) (M * (i - 1))
  else .disj (M * i + (j - 1)) (M * (i - 1) + j)

/-! ### Reading the row and the phase of a gate -/

theorem stDiv (M t p : ℕ) (hp : p < stH M) : (1 + stH M * t + p - 1) / stH M = t := by
  have h : 1 + stH M * t + p - 1 = stH M * t + p := by omega
  rw [h, Nat.mul_add_div (stH_pos M), Nat.div_eq_of_lt hp, Nat.add_zero]

theorem stMod (M t p : ℕ) (hp : p < stH M) : (1 + stH M * t + p - 1) % stH M = p := by
  have h : 1 + stH M * t + p - 1 = stH M * t + p := by omega
  rw [h, Nat.mul_add_mod, Nat.mod_eq_of_lt hp]

variable {δ : ℕ → ℕ → Bool → ℕ} {ac : ℕ → ℕ → Bool} {M n t s j : ℕ}

theorem stT_zero : stT δ ac M n 0 j = .cst (decide (j = 0)) := by rw [stT, if_pos rfl]

/-- The gate of a block row, before the case analysis on the phase. -/
theorem stT_block (ht : t < n) (p : ℕ) (hp : p < stH M) :
    stT δ ac M n (1 + stH M * t + p) j =
      (if p = 0 then .cst false
        else if p = 1 then .cst true
        else if p = 2 then .inp (2 * t + 1)
        else if p = 3 then .neg (M * (1 + stH M * t + p - 1))
        else if (p - 4) % 2 = 0 then
          .conj (stPrevId M t j)
            (M * (1 + stH M * t + stSelK δ n ((p - 4) / 2) j))
        else if j = 0 then .disj (M * (1 + stH M * t + p - 1)) (M * (1 + stH M * t + p - 1))
        else .disj (M * (1 + stH M * t + p) + (j - 1))
          (M * (1 + stH M * t + p - 1) + j)) := by
  rw [stT, if_neg (by omega), stDiv M t p hp, stMod M t p hp, if_neg (by omega)]

theorem stT_cstF (ht : t < n) : stT δ ac M n (1 + stH M * t) j = .cst false := by
  have h := stT_block (δ := δ) (ac := ac) (M := M) (j := j) ht 0 (stH_pos M)
  simpa using h

theorem stT_cstT (ht : t < n) : stT δ ac M n (1 + stH M * t + 1) j = .cst true := by
  have h := stT_block (δ := δ) (ac := ac) (M := M) (j := j) ht 1 (by rw [stH]; omega)
  simpa using h

theorem stT_bit (ht : t < n) : stT δ ac M n (1 + stH M * t + 2) j = .inp (2 * t + 1) := by
  have h := stT_block (δ := δ) (ac := ac) (M := M) (j := j) ht 2 (by rw [stH]; omega)
  simpa using h

theorem stT_neg (ht : t < n) :
    stT δ ac M n (1 + stH M * t + 3) j = .neg (M * (1 + stH M * t + 2)) := by
  have h := stT_block (δ := δ) (ac := ac) (M := M) (j := j) ht 3 (by rw [stH]; omega)
  rw [h]
  norm_num

theorem stT_conj (ht : t < n) (hs : s < M) :
    stT δ ac M n (1 + stH M * t + (4 + 2 * s)) j
      = .conj (stPrevId M t j) (M * (1 + stH M * t + stSelK δ n s j)) := by
  have hp : 4 + 2 * s < stH M := by simp [stH]; omega
  have h := stT_block (δ := δ) (ac := ac) (M := M) (j := j) ht (4 + 2 * s) hp
  have hs2 : (4 + 2 * s - 4) / 2 = s := by omega
  rw [h, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), hs2]

theorem stT_acc (ht : t < n) (hs : s < M) :
    stT δ ac M n (1 + stH M * t + (5 + 2 * s)) j
      = (if j = 0 then
          .disj (M * (1 + stH M * t + (4 + 2 * s))) (M * (1 + stH M * t + (4 + 2 * s)))
        else .disj (M * (1 + stH M * t + (5 + 2 * s)) + (j - 1))
          (M * (1 + stH M * t + (4 + 2 * s)) + j)) := by
  have hp : 5 + 2 * s < stH M := by simp [stH]; omega
  have h := stT_block (δ := δ) (ac := ac) (M := M) (j := j) ht (5 + 2 * s) hp
  rw [h, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]
  have he : 1 + stH M * t + (5 + 2 * s) - 1 = 1 + stH M * t + (4 + 2 * s) := by omega
  rw [he]

theorem stT_final :
    stT δ ac M n (1 + stH M * n) j
      = (if j = 0 then
          (if ac n 0 then .disj (stPrevId M n 0) (stPrevId M n 0) else .cst false)
        else .disj (M * (1 + stH M * n) + (j - 1))
          (if ac n j then stPrevId M n j else M * (1 + stH M * n) + (j - 1))) := by
  have hd : (1 + stH M * n - 1) / stH M = n := by
    have h := stDiv M n 0 (stH_pos M)
    simpa using h
  rw [stT, if_neg (by omega), hd, if_pos (le_refl n)]

/-! ### Well-formedness -/

/-- The gate at row `i`, column `j` sits below every gate of a later row. -/
theorem st_row_lt {a b j' : ℕ} (hab : a < b) (hj' : j' < M) :
    M * a + j' < M * b + j := by
  have h1 : M * (a + 1) ≤ M * b := Nat.mul_le_mul_left _ (by omega)
  have h2 : M * (a + 1) = M * a + M := by ring
  omega

theorem stPrevId_lt (hM : 0 < M) {u i : ℕ} (hu : u < M) (hi : 1 + stH M * t ≤ i) :
    stPrevId M t u < M * i + j := by
  rw [stPrevId]
  split_ifs with h0
  · have : u < M * i + j := by
      have : M ≤ M * i := Nat.le_mul_of_pos_right M (by omega)
      omega
    exact this
  · have hrow : 6 + stH M * (t - 1) + 2 * u < i := by
      have h1 : stH M * (t - 1) + stH M = stH M * t := by
        have : t - 1 + 1 = t := by omega
        calc stH M * (t - 1) + stH M = stH M * (t - 1 + 1) := by ring
          _ = stH M * t := by rw [this]
      have h2 : 2 * u + 6 ≤ stH M := by simp [stH]; omega
      omega
    have : M * (6 + stH M * (t - 1) + 2 * u) + M ≤ M * i := by
      have : M * (6 + stH M * (t - 1) + 2 * u) + M = M * (6 + stH M * (t - 1) + 2 * u + 1) := by
        ring
      rw [this]
      exact Nat.mul_le_mul_left M (by omega)
    omega

theorem gateWf_stT (hM : 0 < M) (hj : j < M) (i : ℕ) :
    gateWf (M * i + j) (stT δ ac M n i j) := by
  have hdm : stH M * ((i - 1) / stH M) + (i - 1) % stH M = i - 1 := Nat.div_add_mod _ _
  have hmul : ∀ a : ℕ, M * a + M = M * (a + 1) := fun a => by ring
  rw [stT]
  split_ifs with h0 hfin hj0 hac hacj hp0 hp1 hp2 hp3 hpar hj0'
  · exact trivial
  · -- the final row, first column, accepting
    have hile : 1 + stH M * n ≤ i := by
      have h := Nat.le_div_iff_mul_le (k := stH M) (stH_pos M) |>.1 hfin
      rw [Nat.mul_comm] at h
      omega
    have h := stPrevId_lt (M := M) (t := n) (j := j) hM (by omega : (0 : ℕ) < M) hile
    exact ⟨h, h⟩
  · exact trivial
  · -- the final row, later columns, accepting
    have hile : 1 + stH M * n ≤ i := by
      have h := Nat.le_div_iff_mul_le (k := stH M) (stH_pos M) |>.1 hfin
      rw [Nat.mul_comm] at h
      omega
    exact ⟨by omega, stPrevId_lt (M := M) (t := n) (j := j) hM hj hile⟩
  · exact ⟨by omega, by omega⟩
  · exact trivial
  · exact trivial
  · exact trivial
  · -- the negation of the bit
    have : M * (i - 1) + M = M * i := by
      rw [hmul]
      congr 1
      omega
    exact (by omega : M * (i - 1) < M * i + j)
  · -- the conjunction row
    have hile : 1 + stH M * ((i - 1) / stH M) ≤ i := by omega
    have hsel : 1 + stH M * ((i - 1) / stH M)
        + stSelK δ n (((i - 1) % stH M - 4) / 2) j < i := by
      have hk := stSelK_lt_four δ n (((i - 1) % stH M - 4) / 2) j
      omega
    refine ⟨stPrevId_lt (M := M) hM hj hile, ?_⟩
    have h := st_row_lt (M := M) (j := j) (j' := 0) hsel hM
    omega
  · -- the accumulator row, first column
    have : M * (i - 1) + M = M * i := by
      rw [hmul]
      congr 1
      omega
    exact ⟨by omega, by omega⟩
  · -- the accumulator row, later columns
    have : M * (i - 1) + M = M * i := by
      rw [hmul]
      congr 1
      omega
    exact ⟨by omega, by omega⟩

/-! ### The circuit -/

/-- The template of the grid, as a function of the identifier of the gate. -/
def stF (δ : ℕ → ℕ → Bool → ℕ) (ac : ℕ → ℕ → Bool) (M n : ℕ) : ℕ → Gate :=
  fun c => stT δ ac M n (c / M) (c % M)

theorem stF_block (hj : j < M) (i : ℕ) : stF δ ac M n (M * i + j) = stT δ ac M n i j := by
  have hM : 0 < M := by omega
  rw [stF, Nat.mul_add_div hM, Nat.div_eq_of_lt hj, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hj]

/-- The number of gates of the grid: `stH M * n + 2` rows of `M` gates. -/
def stCnt (M n : ℕ) : ℕ := M * (stH M * n + 2)

/-- **The grid** deciding the language of the automaton. -/
def stGrid (δ : ℕ → ℕ → Bool → ℕ) (ac : ℕ → ℕ → Bool) (M n : ℕ) : Circuit :=
  layer (stF δ ac M n) (stCnt M n)

theorem stGrid_ne_nil (hM : 0 < M) : stGrid δ ac M n ≠ [] := by
  have h : 0 < stCnt M n := by
    rw [stCnt]
    exact Nat.mul_pos hM (by omega)
  rw [stGrid]
  cases hc : stCnt M n with
  | zero => omega
  | succ k => simp [layer]

theorem wf_stGrid (hM : 0 < M) : wf (stGrid δ ac M n) := by
  refine wf_layer fun c _ => ?_
  have h : M * (c / M) + c % M = c := Nat.div_add_mod c M
  rw [stF]
  conv_lhs => rw [← h]
  exact gateWf_stT hM (Nat.mod_lt c hM) _

/-! ### The semantics of the grid -/

/-- The state of the automaton after the first `t` bits of the word presented by the input. -/
def stRun (δ : ℕ → ℕ → Bool → ℕ) (n : ℕ) (y : Word) : ℕ → ℕ
  | 0 => 0
  | t + 1 => δ n (stRun δ n y t) (abit y t)

theorem stRun_lt (hM : 0 < M) (hδ : ∀ s b, δ n s b < M) (y : Word) (t : ℕ) :
    stRun δ n y t < M := by
  cases t with
  | zero => exact hM
  | succ t => exact hδ _ _

variable {y : Word}

theorem lval_st_ref {r c : ℕ} (h : r < c) :
    (vals y (layer (stF δ ac M n) c)).getD r false = lval y (stF δ ac M n) r :=
  vals_layer_getD y (stF δ ac M n) c r h

theorem lval_st_cstF (ht : t < n) (hj : j < M) :
    lval y (stF δ ac M n) (M * (1 + stH M * t) + j) = false := by
  rw [lval, stF_block hj, stT_cstF ht]
  rfl

theorem lval_st_cstT (ht : t < n) (hj : j < M) :
    lval y (stF δ ac M n) (M * (1 + stH M * t + 1) + j) = true := by
  rw [lval, stF_block hj, stT_cstT ht]
  rfl

theorem lval_st_bit (ht : t < n) (hj : j < M) :
    lval y (stF δ ac M n) (M * (1 + stH M * t + 2) + j) = abit y t := by
  rw [lval, stF_block hj, stT_bit ht]
  rfl

theorem lval_st_neg (hM : 0 < M) (ht : t < n) (hj : j < M) :
    lval y (stF δ ac M n) (M * (1 + stH M * t + 3) + j) = !abit y t := by
  have hr : M * (1 + stH M * t + 2) < M * (1 + stH M * t + 3) + j := by
    simpa using st_row_lt (M := M) (j := j) (a := 1 + stH M * t + 2)
      (b := 1 + stH M * t + 3) (j' := 0) (by omega) hM
  have hb := lval_st_bit (δ := δ) (ac := ac) (M := M) (n := n) (t := t) (j := 0) (y := y) ht hM
  simp only [Nat.add_zero] at hb
  rw [lval, stF_block hj, stT_neg ht, gateVal, lval_st_ref hr, hb]

/-- The value of the selector gate of the pair `(s, j')`: the bit just read moves `j'` to `s`. -/
theorem lval_st_sel (hM : 0 < M) (ht : t < n) (s j' : ℕ) :
    lval y (stF δ ac M n) (M * (1 + stH M * t + stSelK δ n s j'))
      = decide (δ n j' (abit y t) = s) := by
  have hf := lval_st_cstF (δ := δ) (ac := ac) (M := M) (n := n) (t := t) (j := 0) (y := y) ht hM
  have htt := lval_st_cstT (δ := δ) (ac := ac) (M := M) (n := n) (t := t) (j := 0) (y := y) ht hM
  have hb := lval_st_bit (δ := δ) (ac := ac) (M := M) (n := n) (t := t) (j := 0) (y := y) ht hM
  have hng := lval_st_neg (δ := δ) (ac := ac) (M := M) (n := n) (t := t) (j := 0) (y := y)
    hM ht hM
  simp only [Nat.add_zero] at hf htt hb hng
  rw [stSelK]
  split_ifs with h1 h2 h2
  · rw [htt]
    cases hbit : abit y t <;> simp [h1, h2]
  · rw [hb]
    cases hbit : abit y t <;> simp [h1, h2]
  · rw [hng]
    cases hbit : abit y t <;> simp [h1, h2]
  · rw [Nat.add_zero, hf]
    cases hbit : abit y t <;> simp [h1, h2]

/-- The conjunction row: the previous state was `j`, and the bit just read moves `j` to `s`. -/
theorem lval_st_conj (hM : 0 < M) (ht : t < n) (hs : s < M) (hj : j < M)
    (hprev : ∀ u, u < M → lval y (stF δ ac M n) (stPrevId M t u) = decide (u = stRun δ n y t)) :
    lval y (stF δ ac M n) (M * (1 + stH M * t + (4 + 2 * s)) + j)
      = (decide (j = stRun δ n y t) && decide (δ n j (abit y t) = s)) := by
  have hk := stSelK_lt_four δ n s j
  have hr1 : stPrevId M t j < M * (1 + stH M * t + (4 + 2 * s)) + j :=
    stPrevId_lt hM hj (by omega)
  have hr2 : M * (1 + stH M * t + stSelK δ n s j) < M * (1 + stH M * t + (4 + 2 * s)) + j := by
    simpa using st_row_lt (M := M) (j := j) (a := 1 + stH M * t + stSelK δ n s j)
      (b := 1 + stH M * t + (4 + 2 * s)) (j' := 0) (by omega) hM
  rw [lval, stF_block hj, stT_conj ht hs, gateVal, lval_st_ref hr1, lval_st_ref hr2,
    hprev j hj, lval_st_sel hM ht s j]

/-- The accumulator row: the disjunction of the conjunctions of the columns `j' ≤ j`. -/
theorem lval_st_acc (hM : 0 < M) (ht : t < n) (hs : s < M)
    (hprev : ∀ u, u < M → lval y (stF δ ac M n) (stPrevId M t u) = decide (u = stRun δ n y t)) :
    ∀ j, j < M →
      lval y (stF δ ac M n) (M * (1 + stH M * t + (5 + 2 * s)) + j)
        = decide (stRun δ n y t ≤ j ∧ δ n (stRun δ n y t) (abit y t) = s) := by
  intro j
  induction j with
  | zero =>
      intro h0
      have hr : M * (1 + stH M * t + (4 + 2 * s)) < M * (1 + stH M * t + (5 + 2 * s)) + 0 := by
        simpa using st_row_lt (M := M) (j := 0) (a := 1 + stH M * t + (4 + 2 * s))
          (b := 1 + stH M * t + (5 + 2 * s)) (j' := 0) (by omega) hM
      have hc := lval_st_conj (δ := δ) (ac := ac) (M := M) (n := n) (t := t) (s := s) (j := 0)
        (y := y) hM ht hs hM hprev
      simp only [Nat.add_zero] at hc
      rw [lval, stF_block h0, stT_acc ht hs, if_pos rfl, gateVal, lval_st_ref hr, Bool.or_self,
        hc]
      cases hst : stRun δ n y t with
      | zero => simp
      | succ k => simp
  | succ j ih =>
      intro hj
      have hjM : j < M := by omega
      have hr1 : M * (1 + stH M * t + (5 + 2 * s)) + j
          < M * (1 + stH M * t + (5 + 2 * s)) + (j + 1) := by omega
      have hr2 : M * (1 + stH M * t + (4 + 2 * s)) + (j + 1)
          < M * (1 + stH M * t + (5 + 2 * s)) + (j + 1) :=
        st_row_lt (M := M) (j := j + 1) (by omega) hj
      rw [lval, stF_block hj, stT_acc ht hs, if_neg (by omega), gateVal]
      simp only [Nat.add_sub_cancel]
      rw [lval_st_ref hr1, lval_st_ref hr2, ih hjM,
        lval_st_conj (j := j + 1) hM ht hs hj hprev]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨by omega, h2⟩
        · refine ⟨by omega, ?_⟩
          rw [← h1]
          exact h2
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge j (stRun δ n y t) with h | h
        · refine Or.inr ⟨by omega, ?_⟩
          rw [show j + 1 = stRun δ n y t by omega]
          exact h2
        · exact Or.inl ⟨h, h2⟩

/-- **The one-hot bits of the grid record the state of the automaton** after the bits read so
far. -/
theorem lval_st_state (hM : 0 < M) (hδ : ∀ s b, δ n s b < M) :
    ∀ t, t ≤ n → ∀ u, u < M →
      lval y (stF δ ac M n) (stPrevId M t u) = decide (u = stRun δ n y t) := by
  intro t
  induction t with
  | zero =>
      intro _ u hu
      have hF : stF δ ac M n u = stT δ ac M n 0 u := by
        simpa using stF_block (δ := δ) (ac := ac) (M := M) (n := n) (j := u) hu 0
      rw [stPrevId, if_pos rfl, lval, hF, stT_zero]
      rfl
  | succ t ih =>
      intro ht u hu
      have hprev := ih (by omega)
      have hid : stPrevId M (t + 1) u = M * (1 + stH M * t + (5 + 2 * u)) + (M - 1) := by
        rw [stPrevId, if_neg (by omega), Nat.add_sub_cancel]
        congr 2
        omega
      have hlt : stRun δ n y t < M := stRun_lt hM hδ y t
      rw [hid, lval_st_acc hM (by omega : t < n) hu hprev (M - 1) (by omega)]
      have hiff : (stRun δ n y t ≤ M - 1 ∧ δ n (stRun δ n y t) (abit y t) = u)
          ↔ (u = stRun δ n y (t + 1)) := by
        rw [stRun]
        constructor
        · rintro ⟨-, h⟩
          exact h.symm
        · intro h
          exact ⟨by omega, h.symm⟩
      exact decide_eq_decide.2 hiff

/-- The final row accumulates the one-hot bits of the accepting states. -/
theorem lval_st_final (hM : 0 < M) (hδ : ∀ s b, δ n s b < M) :
    ∀ j, j < M →
      lval y (stF δ ac M n) (M * (1 + stH M * n) + j)
        = (decide (stRun δ n y n ≤ j) && ac n (stRun δ n y n)) := by
  have hstate := lval_st_state (δ := δ) (ac := ac) (y := y) hM hδ n (le_refl n)
  intro j
  induction j with
  | zero =>
      intro h0
      have hr : stPrevId M n 0 < M * (1 + stH M * n) + 0 := stPrevId_lt hM hM (by omega)
      rw [lval, stF_block h0, stT_final, if_pos rfl]
      by_cases hac0 : ac n 0
      · rw [if_pos hac0, gateVal, lval_st_ref hr, Bool.or_self, hstate 0 hM]
        cases hst : stRun δ n y n with
        | zero => simp [hac0]
        | succ k => simp
      · have hac0' : ac n 0 = false := by simpa using hac0
        rw [if_neg hac0, gateVal]
        cases hst : stRun δ n y n with
        | zero => simp [hac0']
        | succ k => simp
  | succ j ih =>
      intro hj
      have hjM : j < M := by omega
      have hr1 : M * (1 + stH M * n) + j < M * (1 + stH M * n) + (j + 1) := by omega
      have hr2 : stPrevId M n (j + 1) < M * (1 + stH M * n) + (j + 1) :=
        stPrevId_lt hM hj (by omega)
      rw [lval, stF_block hj, stT_final, if_neg (by omega)]
      simp only [Nat.add_sub_cancel]
      by_cases hacj : ac n (j + 1)
      · rw [if_pos hacj, gateVal, lval_st_ref hr1, lval_st_ref hr2, ih hjM, hstate (j + 1) hj]
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨h1, h2⟩ | h1)
          · exact ⟨by omega, h2⟩
          · refine ⟨by omega, ?_⟩
            rw [← h1]
            exact hacj
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_or_ge j (stRun δ n y n) with h | h
          · exact Or.inr (by omega)
          · exact Or.inl ⟨h, h2⟩
      · have hacj' : ac n (j + 1) = false := by simpa using hacj
        rw [if_neg hacj, gateVal, lval_st_ref hr1, ih hjM, Bool.or_self]
        rw [Bool.eq_iff_iff]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          rcases Nat.lt_or_ge j (stRun δ n y n) with h | h
          · rw [show stRun δ n y n = j + 1 by omega, hacj'] at h2
            exact absurd h2 (by simp)
          · exact h

/-- **The grid accepts exactly the words accepted by the automaton.** -/
theorem out_stGrid (hM : 0 < M) (hδ : ∀ s b, δ n s b < M) :
    out y (stGrid δ ac M n) = ac n (stRun δ n y n) := by
  have hlast : stCnt M n = (M * (1 + stH M * n) + (M - 1)) + 1 := by
    rw [stCnt]
    have : M * (1 + stH M * n) = M + M * (stH M * n) := by ring
    have h2 : M * (stH M * n + 2) = M * (stH M * n) + 2 * M := by ring
    omega
  rw [stGrid, hlast, out_layer,
    lval_st_final (δ := δ) (ac := ac) hM hδ (M - 1) (by omega)]
  have hlt : stRun δ n y n < M := stRun_lt hM hδ y n
  rw [decide_eq_true (by omega : stRun δ n y n ≤ M - 1), Bool.true_and]

end CircCode

end Complexity
