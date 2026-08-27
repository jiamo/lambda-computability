/-
# P-uniform circuits for cellular automata: the tableau

`Start/UniformState.lean` compiles an automaton with polynomially many states into a P-uniform
family of circuits.  Such an automaton reads its input once, so what it can decide is limited by
the number of configurations it can distinguish.  This module compiles the other standard device,
and the one that Cook–Levin really rests on: a **cellular automaton** over a fixed finite alphabet,
run for polynomially many steps on a tape of polynomial length.  Its computation is a *tableau*,
and the circuit is that tableau.

The circuit is a grid of width `W`, one column per tape cell.  Row `0` is the constant `false`,
row `1` the constant `true`, row `2` holds the input bit of the column, and the `K` rows
`3, …, K + 2` hold the one-hot encoding of the initial contents of the tape.  Each step of the
automaton is then a block of `caHb K` rows: for every triple `(a, b, c)` of symbols a pair of
conjunction rows computes

`prev_a[j-1] ∧ prev_b[j] ∧ prev_c[j+1]`,

and for every symbol `d` an accumulator runs through the triples, collecting those whose local rule
gives `d`.  The last accumulator row of `d` is the one-hot bit of `d` at the next time step.  After
the last block, `K` rows accumulate the accepting symbols of the cell `0`, and a final row
broadcasts the answer to the last column, which is the output gate.

Because the alphabet is fixed, the height of a block is a constant, and every gate of the grid is
determined by simple arithmetic on its row and column; `Start/UniformCACode.lean` writes that
arithmetic as a Cobham term.

Main definitions:

* `Complexity.CellAuto` — a cellular automaton over a fixed finite alphabet;
* `Complexity.CircCode.caCell` — the contents of the tape cell `j` at time `t`;
* `Complexity.CircCode.caT`, `Complexity.CircCode.caGrid` — the template of the tableau and the
  circuit itself.

Main results:

* `Complexity.CircCode.wf_caGrid` — the tableau is a well-formed circuit;
* `Complexity.CircCode.lval_ca_state` — **the one-hot bits of the tableau record the contents of
  the tape**;
* `Complexity.CircCode.out_caGrid` — **the tableau accepts exactly the words the automaton
  accepts**.
-/
import Start.UniformState

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-- **A cellular automaton over a fixed finite alphabet.**  The symbols are the naturals below
`K`; `blk` is the blank, carried by every cell outside the tape; `ini f b` is the symbol written
initially in a cell holding the input bit `b`, the flag `f` telling whether the cell is the first
one; `stp a b c` is the local rule, and `ac` marks the accepting symbols. -/
structure CellAuto where
  /-- The number of symbols of the alphabet. -/
  K : ℕ
  /-- The blank symbol, carried by the cells outside the tape. -/
  blk : ℕ
  /-- The initial contents of a cell, from its input bit and the flag telling whether it is the
  first cell. -/
  ini : Bool → Bool → ℕ
  /-- The local rule: the new symbol of a cell, from its left neighbour, itself and its right
  neighbour. -/
  stp : ℕ → ℕ → ℕ → ℕ
  /-- The accepting symbols. -/
  ac : ℕ → Bool
  /-- The alphabet is not empty. -/
  Kpos : 0 < K
  /-- The blank is a symbol. -/
  blk_lt : blk < K
  /-- The initial contents are symbols. -/
  ini_lt : ∀ f b, ini f b < K
  /-- The local rule produces symbols. -/
  stp_lt : ∀ a b c, stp a b c < K

namespace CircCode

open Complexity.Tseitin

/-! ### The layout of the tableau -/

/-- The number of triples of symbols. -/
def caTri (K : ℕ) : ℕ := K * K * K

/-- The height of the block of one time step: two conjunction rows per triple, and one
accumulator row per triple and per target symbol. -/
def caHb (K : ℕ) : ℕ := caTri K * (K + 2)

/-- The number of rows before the first block: the two constants, the input row, and the `K`
one-hot rows of the initial tape. -/
def caB (K : ℕ) : ℕ := 3 + K

/-- The first row after the last block. -/
def caP (K H : ℕ) : ℕ := caB K + caHb K * H

/-- The number of rows of the tableau. -/
def caRows (K H : ℕ) : ℕ := caP K H + K + 1

/-- The number of gates of the tableau. -/
def caCnt (K W H : ℕ) : ℕ := W * caRows K H

/-- The first component of the triple with index `m`. -/
def triA (K m : ℕ) : ℕ := m / (K * K)

/-- The second component of the triple with index `m`. -/
def triB (K m : ℕ) : ℕ := m / K % K

/-- The third component of the triple with index `m`. -/
def triC (K m : ℕ) : ℕ := m % K

/-- The index of the triple `(a, b, c)`. -/
def triIdx (K a b c : ℕ) : ℕ := (a * K + b) * K + c

/-- The row holding the one-hot bit of the symbol `s` at time `t`: an initial row if `t = 0`, and
otherwise the last accumulator row of `s` in the block of the step `t - 1`. -/
def caStRow (K t s : ℕ) : ℕ :=
  if t = 0 then 3 + s
  else caB K + caHb K * (t - 1) + 2 * caTri K + s * caTri K + (caTri K - 1)

/-- The identifier of the one-hot bit of the symbol `s` in the cell `j` at time `t`. -/
def caStId (K W t s j : ℕ) : ℕ := W * caStRow K t s + j

/-- The identifier of the one-hot bit of the symbol `s` in the cell to the *left* of `j`: the
constant `true` or `false` when that cell falls outside the tape. -/
def caRefL (K W blk t s j : ℕ) : ℕ :=
  if j = 0 then (if s = blk then W else 0) else caStId K W t s (j - 1)

/-- The identifier of the one-hot bit of the symbol `s` in the cell to the *right* of `j`: the
constant `true` or `false` when that cell falls outside the tape. -/
def caRefR (K W blk t s j : ℕ) : ℕ :=
  if j + 1 < W then caStId K W t s (j + 1) else (if s = blk then W else 0)

/-! ### The three kinds of row -/

/-- The one-hot row of the symbol `s` in the initial tape. -/
def caInitG (blk : ℕ) (ini : Bool → Bool → ℕ) (W n s j : ℕ) : Gate :=
  if j < n then
    (if ini (decide (j = 0)) true = s then
      (if ini (decide (j = 0)) false = s then .cst true else .disj (W * 2 + j) (W * 2 + j))
     else (if ini (decide (j = 0)) false = s then .neg (W * 2 + j) else .cst false))
  else .cst (decide (blk = s))

/-- The row of phase `p` in the block of the step `t`. -/
def caBlockG (K blk : ℕ) (stp : ℕ → ℕ → ℕ → ℕ) (W t p j : ℕ) : Gate :=
  if p < 2 * caTri K then
    (if p % 2 = 0 then
      .conj (caRefL K W blk t (triA K (p / 2)) j) (caStId K W t (triB K (p / 2)) j)
     else
      .conj (W * (caB K + caHb K * t + p - 1) + j)
        (caRefR K W blk t (triC K (p / 2)) j))
  else
    .disj (if (p - 2 * caTri K) % caTri K = 0 then 0
      else W * (caB K + caHb K * t + p - 1) + j)
      (if stp (triA K ((p - 2 * caTri K) % caTri K)) (triB K ((p - 2 * caTri K) % caTri K))
            (triC K ((p - 2 * caTri K) % caTri K)) = (p - 2 * caTri K) / caTri K then
        W * (caB K + caHb K * t + 2 * ((p - 2 * caTri K) % caTri K) + 1) + j
      else 0)

/-- The accumulator row of the accepting symbol `e`, read off the cell `0` at the last time
step. -/
def caFinG (K : ℕ) (ac : ℕ → Bool) (W H e j : ℕ) : Gate :=
  .disj (if e = 0 then 0 else W * (caP K H + e - 1) + j)
    (if ac e then caStId K W H e j else 0)

/-- The row holding the input bit of the column: the columns beyond the input are blank, so they
hold the constant `false`. -/
def caBitG (n j : ℕ) : Gate := if j < n then .inp (2 * j + 1) else .cst false

/-- **The template of the tableau**: the gate at row `i`, column `j`. -/
def caT (A : CellAuto) (W H n i j : ℕ) : Gate :=
  if i = 0 then .cst false
  else if i = 1 then .cst true
  else if i = 2 then caBitG n j
  else if i < caB A.K then caInitG A.blk A.ini W n (i - 3) j
  else if i < caP A.K H then
    caBlockG A.K A.blk A.stp W ((i - caB A.K) / caHb A.K) ((i - caB A.K) % caHb A.K) j
  else if i < caP A.K H + A.K then caFinG A.K A.ac W H (i - caP A.K H) j
  else .disj (W * (caP A.K H + A.K - 1)) (W * (caP A.K H + A.K - 1))

/-- The template of the tableau, as a function of the identifier of the gate. -/
def caF (A : CellAuto) (W H n : ℕ) : ℕ → Gate :=
  fun c => caT A W H n (c / W) (c % W)

/-- **The tableau** deciding the language of the cellular automaton. -/
def caGrid (A : CellAuto) (W H n : ℕ) : Circuit :=
  layer (caF A W H n) (caCnt A.K W H)

/-! ### The computation of the automaton -/

/-- The contents of the cell `j` at time `t`: the initial tape carries the symbol `ini` of the
input bit in its first `n` cells and the blank elsewhere, and each later step applies the local
rule to the cell and its two neighbours, the cells outside the tape being blank. -/
def caCell (A : CellAuto) (W n : ℕ) (bit : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, j => if j < n then A.ini (decide (j = 0)) (bit j) else A.blk
  | t + 1, j =>
      A.stp (if j = 0 then A.blk else caCell A W n bit t (j - 1)) (caCell A W n bit t j)
        (if j + 1 < W then caCell A W n bit t (j + 1) else A.blk)

/-- The symbol of the cell to the left of `j` at time `t`, the blank outside the tape. -/
def caCellL (A : CellAuto) (W n : ℕ) (bit : ℕ → Bool) (t j : ℕ) : ℕ :=
  if j = 0 then A.blk else caCell A W n bit t (j - 1)

/-- The symbol of the cell to the right of `j` at time `t`, the blank outside the tape. -/
def caCellR (A : CellAuto) (W n : ℕ) (bit : ℕ → Bool) (t j : ℕ) : ℕ :=
  if j + 1 < W then caCell A W n bit t (j + 1) else A.blk

theorem caCell_succ (A : CellAuto) (W n : ℕ) (bit : ℕ → Bool) (t j : ℕ) :
    caCell A W n bit (t + 1) j
      = A.stp (caCellL A W n bit t j) (caCell A W n bit t j) (caCellR A W n bit t j) := rfl

theorem caCell_lt (A : CellAuto) (W n : ℕ) (bit : ℕ → Bool) (t j : ℕ) :
    caCell A W n bit t j < A.K := by
  cases t with
  | zero =>
      rw [caCell]
      split
      · exact A.ini_lt _ _
      · exact A.blk_lt
  | succ t => exact A.stp_lt _ _ _

theorem caCellL_lt (A : CellAuto) (W n : ℕ) (bit : ℕ → Bool) (t j : ℕ) :
    caCellL A W n bit t j < A.K := by
  rw [caCellL]
  split
  · exact A.blk_lt
  · exact caCell_lt A W n bit t _

theorem caCellR_lt (A : CellAuto) (W n : ℕ) (bit : ℕ → Bool) (t j : ℕ) :
    caCellR A W n bit t j < A.K := by
  rw [caCellR]
  split
  · exact caCell_lt A W n bit t _
  · exact A.blk_lt

/-- The computation depends only on the input bits inside the tape. -/
theorem caCell_congr (A : CellAuto) (W n : ℕ) {b₁ b₂ : ℕ → Bool} (h : ∀ j, j < n → b₁ j = b₂ j) :
    ∀ t j, caCell A W n b₁ t j = caCell A W n b₂ t j := by
  intro t
  induction t with
  | zero =>
      intro j
      rw [caCell, caCell]
      by_cases hj : j < n
      · rw [if_pos hj, if_pos hj, h j hj]
      · rw [if_neg hj, if_neg hj]
  | succ t ih => intro j; rw [caCell, caCell, ih, ih, ih]

/-! ### The arithmetic of triples -/

theorem caTri_pos {K : ℕ} (hK : 0 < K) : 0 < caTri K := by
  rw [caTri]; positivity

theorem triIdx_lt {K a b c : ℕ} (ha : a < K) (hb : b < K) (hc : c < K) :
    triIdx K a b c < caTri K := by
  rw [triIdx, caTri]
  calc (a * K + b) * K + c < (a * K + b) * K + K := by omega
    _ = (a * K + b + 1) * K := by ring
    _ ≤ (a * K + K) * K := by
        have : a * K + b + 1 ≤ a * K + K := by omega
        exact Nat.mul_le_mul_right _ this
    _ = ((a + 1) * K) * K := by ring
    _ ≤ (K * K) * K := by
        have : (a + 1) * K ≤ K * K := Nat.mul_le_mul_right _ (by omega)
        exact Nat.mul_le_mul_right _ this

theorem triA_triIdx {K a b c : ℕ} (hb : b < K) (hc : c < K) : triA K (triIdx K a b c) = a := by
  have hK : 0 < K := by omega
  have h : triIdx K a b c = (b * K + c) + (K * K) * a := by rw [triIdx]; ring
  have hlt : b * K + c < K * K := by nlinarith
  rw [triA, h, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, Nat.zero_add]

theorem triB_triIdx {K a b c : ℕ} (hb : b < K) (hc : c < K) : triB K (triIdx K a b c) = b := by
  have hK : 0 < K := by omega
  have h : triIdx K a b c = c + K * (a * K + b) := by rw [triIdx]; ring
  have h2 : a * K + b = b + K * a := by ring
  rw [triB, h, Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hc, Nat.zero_add, h2,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

theorem triC_triIdx {K a b c : ℕ} (hc : c < K) : triC K (triIdx K a b c) = c := by
  have h : triIdx K a b c = c + K * (a * K + b) := by rw [triIdx]; ring
  rw [triC, h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

theorem triA_lt {K m : ℕ} (hm : m < caTri K) : triA K m < K := by
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h, caTri] at hm; omega
    · exact h
  rw [caTri] at hm
  rw [triA, Nat.div_lt_iff_lt_mul (by positivity)]
  calc m < K * K * K := hm
    _ = K * (K * K) := by ring

theorem triB_lt {K m : ℕ} (hK : 0 < K) : triB K m < K := Nat.mod_lt _ hK

theorem triC_lt {K m : ℕ} (hK : 0 < K) : triC K m < K := Nat.mod_lt _ hK

theorem triIdx_tri {K m : ℕ} (hm : m < caTri K) :
    triIdx K (triA K m) (triB K m) (triC K m) = m := by
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h, caTri] at hm; omega
    · exact h
  have h1 : K * (m / K / K) + m / K % K = m / K := Nat.div_add_mod (m / K) K
  have h2 : K * (m / K) + m % K = m := Nat.div_add_mod m K
  have h3 : m / (K * K) = m / K / K := by rw [Nat.div_div_eq_div_mul]
  rw [triIdx, triA, triB, triC, h3]
  calc (m / K / K * K + m / K % K) * K + m % K
      = K * (K * (m / K / K) + m / K % K) + m % K := by ring
    _ = K * (m / K) + m % K := by rw [h1]
    _ = m := h2

/-! ### The layout is coherent -/

theorem caStRow_lt_base {K t s : ℕ} (hs : s < K) : caStRow K t s < caB K + caHb K * t := by
  have hK : 0 < K := by omega
  have hT : 0 < caTri K := caTri_pos hK
  rw [caStRow]
  split_ifs with h
  · subst h; simp only [caB]; omega
  · have hst : s * caTri K + caTri K ≤ K * caTri K := by
      calc s * caTri K + caTri K = (s + 1) * caTri K := by ring
        _ ≤ K * caTri K := Nat.mul_le_mul_right _ (by omega)
    have hHb : caHb K = 2 * caTri K + K * caTri K := by rw [caHb]; ring
    have ht : caHb K * (t - 1) + caHb K = caHb K * t := by
      have h1 : t - 1 + 1 = t := by omega
      calc caHb K * (t - 1) + caHb K = caHb K * (t - 1 + 1) := by ring
        _ = caHb K * t := by rw [h1]
    simp only [caB]
    omega

theorem caStRow_lt_caP {K H t s : ℕ} (hs : s < K) (ht : t ≤ H) : caStRow K t s < caP K H := by
  have h := caStRow_lt_base (K := K) (t := t) hs
  have : caHb K * t ≤ caHb K * H := Nat.mul_le_mul_left _ ht
  rw [caP]
  omega

/-! ### The tableau is a well-formed circuit -/

theorem ca_row_lt {W i i' j j' : ℕ} (h : i' < i) (hj' : j' < W) : W * i' + j' < W * i + j := by
  have h1 : W * (i' + 1) ≤ W * i := Nat.mul_le_mul_left _ (by omega)
  have h2 : W * (i' + 1) = W * i' + W := by ring
  omega

theorem gateWf_caInitG {W n i j : ℕ} (hj : j < W) (hi : 2 < i) (blk s : ℕ)
    (ini : Bool → Bool → ℕ) : gateWf (W * i + j) (caInitG blk ini W n s j) := by
  have href : W * 2 + j < W * i + j := ca_row_lt hi hj
  rw [caInitG]
  split_ifs <;> simp only [gateWf] <;> first | exact ⟨href, href⟩ | exact href

theorem gateWf_caFinG {A : CellAuto} {W H i j e : ℕ} (hW : 0 < W) (hj : j < W) (he : e < A.K)
    (hi : caP A.K H + e = i) : gateWf (W * i + j) (caFinG A.K A.ac W H e j) := by
  have hP : 3 ≤ caP A.K H := by
    have : caP A.K H = 3 + A.K + caHb A.K * H := by rw [caP, caB]
    omega
  have h1 : W * (caP A.K H + e - 1) + j < W * i + j := ca_row_lt (by omega) hj
  have h2 : caStId A.K W H e j < W * i + j := by
    have hrow := caStRow_lt_caP (K := A.K) (H := H) (t := H) he le_rfl
    rw [caStId]
    exact ca_row_lt (by omega) hj
  have h0 : 0 < W * i + j := by
    have : W * 1 ≤ W * i := Nat.mul_le_mul_left _ (by omega)
    omega
  rw [caFinG]
  simp only [gateWf]
  refine ⟨?_, ?_⟩
  · split_ifs
    · exact h0
    · exact h1
  · split_ifs
    · exact h2
    · exact h0

theorem gateWf_caBlockG {A : CellAuto} {W t p j i : ℕ} (hW : 0 < W) (hj : j < W)
    (hi : caB A.K + caHb A.K * t + p = i) :
    gateWf (W * i + j) (caBlockG A.K A.blk A.stp W t p j) := by
  have hK := A.Kpos
  have hT : 0 < caTri A.K := caTri_pos hK
  have hi3 : 3 ≤ caB A.K := by simp [caB]
  have h0 : 0 < W * i + j := by
    have : W * 1 ≤ W * i := Nat.mul_le_mul_left _ (by omega)
    omega
  have hWlt : W < W * i + j := by
    have h := ca_row_lt (W := W) (i := i) (i' := 1) (j := j) (j' := 0) (by omega) hW
    omega
  have hprev : ∀ s : ℕ, s < A.K → ∀ j' : ℕ, j' < W → caStId A.K W t s j' < W * i + j := by
    intro s hs j' hj'
    have hrow := caStRow_lt_base (K := A.K) (t := t) hs
    rw [caStId]
    exact ca_row_lt (by omega) hj'
  have hrefl : ∀ s : ℕ, s < A.K → caRefL A.K W A.blk t s j < W * i + j := by
    intro s hs
    rw [caRefL]
    split_ifs with hj0 hs0
    · exact hWlt
    · exact h0
    · exact hprev s hs (j - 1) (by omega)
  have hrefr : ∀ s : ℕ, s < A.K → caRefR A.K W A.blk t s j < W * i + j := by
    intro s hs
    rw [caRefR]
    split_ifs with hjw hs0
    · exact hprev s hs (j + 1) hjw
    · exact hWlt
    · exact h0
  have hbelow : W * (caB A.K + caHb A.K * t + p - 1) + j < W * i + j :=
    ca_row_lt (by omega) hj
  have hY : ∀ q : ℕ, q < caTri A.K → ¬ p < 2 * caTri A.K →
      W * (caB A.K + caHb A.K * t + 2 * q + 1) + j < W * i + j := by
    intro q hq hpq
    exact ca_row_lt (by omega) hj
  rw [caBlockG]
  split_ifs with hplt hpar
  · exact ⟨hrefl _ (triA_lt (by omega)), hprev _ (triB_lt hK) j hj⟩
  · exact ⟨hbelow, hrefr _ (triC_lt hK)⟩
  · exact ⟨h0, hY _ (Nat.mod_lt _ hT) hplt⟩
  · exact ⟨h0, h0⟩
  · exact ⟨hbelow, hY _ (Nat.mod_lt _ hT) hplt⟩
  · exact ⟨hbelow, h0⟩

theorem gateWf_caT {A : CellAuto} {W H n j : ℕ} (hW : 0 < W) (hj : j < W) (i : ℕ) :
    gateWf (W * i + j) (caT A W H n i j) := by
  have hK := A.Kpos
  have hHb : 0 < caHb A.K := by
    rw [caHb]
    exact Nat.mul_pos (caTri_pos hK) (by omega)
  rw [caT]
  split_ifs with h0 h1 h2 h3 h4 h5
  · trivial
  · trivial
  · rw [caBitG]
    split <;> trivial
  · exact gateWf_caInitG hj (by omega) _ _ _
  · refine gateWf_caBlockG hW hj ?_
    have hdm := Nat.div_add_mod (i - caB A.K) (caHb A.K)
    have hge : caB A.K ≤ i := by simp only [caB] at h3 ⊢; omega
    omega
  · exact gateWf_caFinG hW hj (by omega) (by omega)
  · have hP : 3 ≤ caP A.K H := by
      have : caP A.K H = 3 + A.K + caHb A.K * H := by rw [caP, caB]
      omega
    have href : W * (caP A.K H + A.K - 1) + 0 < W * i + j := ca_row_lt (by omega) hW
    exact ⟨by omega, by omega⟩

theorem wf_caGrid {A : CellAuto} {W H n : ℕ} (hW : 0 < W) : wf (caGrid A W H n) := by
  refine wf_layer fun c _ => ?_
  have h : W * (c / W) + c % W = c := Nat.div_add_mod c W
  rw [caF]
  conv_lhs => rw [← h]
  exact gateWf_caT hW (Nat.mod_lt c hW) _

theorem caGrid_ne_nil {A : CellAuto} {W H n : ℕ} (hW : 0 < W) : caGrid A W H n ≠ [] := by
  have h : 0 < caCnt A.K W H := by
    rw [caCnt, caRows]
    exact Nat.mul_pos hW (by omega)
  rw [caGrid]
  cases hc : caCnt A.K W H with
  | zero => omega
  | succ k => simp [layer]

/-! ### Reading the rows of the tableau -/

section Sem

variable {A : CellAuto} {W H n t s i j j' p m d : ℕ} {y : Word}

theorem caF_block (hj : j < W) (i : ℕ) : caF A W H n (W * i + j) = caT A W H n i j := by
  have hW : 0 < W := by omega
  rw [caF, Nat.mul_add_div hW, Nat.div_eq_of_lt hj, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hj]

theorem lval_ca_ref {r c : ℕ} (h : r < c) :
    (vals y (layer (caF A W H n) c)).getD r false = lval y (caF A W H n) r :=
  vals_layer_getD y (caF A W H n) c r h

theorem lval_ca_false (hW : 0 < W) : lval y (caF A W H n) 0 = false := by
  have h : caF A W H n (W * 0 + 0) = caT A W H n 0 0 := caF_block hW 0
  simp only [Nat.mul_zero, Nat.add_zero] at h
  rw [lval, h, caT, if_pos rfl]
  rfl

theorem lval_ca_true (hW : 0 < W) : lval y (caF A W H n) W = true := by
  have h : caF A W H n (W * 1 + 0) = caT A W H n 1 0 := caF_block hW 1
  simp only [Nat.mul_one, Nat.add_zero] at h
  rw [lval, h, caT, if_neg one_ne_zero, if_pos rfl]
  rfl

theorem lval_ca_bit (hj : j < W) (hjn : j < n) :
    lval y (caF A W H n) (W * 2 + j) = abit y j := by
  rw [lval, caF_block hj 2, caT, if_neg (by omega), if_neg (by omega), if_pos rfl, caBitG,
    if_pos hjn]
  rfl

/-! ### The initial rows -/

theorem caT_init (hs : s < A.K) : caT A W H n (3 + s) j = caInitG A.blk A.ini W n s j := by
  rw [caT, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by simp [caB]; omega)]
  congr 1
  omega

theorem lval_ca_init (hj : j < W) (hs : s < A.K) :
    lval y (caF A W H n) (caStId A.K W 0 s j) = decide (caCell A W n (abit y) 0 j = s) := by
  have hid : caStId A.K W 0 s j = W * (3 + s) + j := by rw [caStId, caStRow, if_pos rfl]
  have href : W * 2 + j < W * (3 + s) + j := ca_row_lt (by omega) hj
  rw [hid, lval, caF_block hj, caT_init hs, caInitG, caCell]
  by_cases hjn : j < n
  · rw [if_pos hjn, if_pos hjn]
    have hbit : (vals y (layer (caF A W H n) (W * (3 + s) + j))).getD (W * 2 + j) false
        = abit y j := by rw [lval_ca_ref href, lval_ca_bit hj hjn]
    by_cases h1 : A.ini (decide (j = 0)) true = s
    · by_cases h2 : A.ini (decide (j = 0)) false = s
      · rw [if_pos h1, if_pos h2]
        cases hb : abit y j <;> simp [gateVal, h1, h2]
      · rw [if_pos h1, if_neg h2, gateVal, hbit]
        cases hb : abit y j <;> simp [h1, h2]
    · by_cases h2 : A.ini (decide (j = 0)) false = s
      · rw [if_neg h1, if_pos h2, gateVal, hbit]
        cases hb : abit y j <;> simp [h1, h2]
      · rw [if_neg h1, if_neg h2]
        cases hb : abit y j <;> simp [gateVal, h1, h2]
  · rw [if_neg hjn, if_neg hjn]
    rfl

/-! ### The rows of a block -/

theorem caT_block (hp : p < caHb A.K) (ht : t < H) :
    caT A W H n (caB A.K + caHb A.K * t + p) j = caBlockG A.K A.blk A.stp W t p j := by
  have hb : 3 ≤ caB A.K := by simp [caB]
  have hHt : caHb A.K * t + caHb A.K ≤ caHb A.K * H := by
    have h1 : caHb A.K * (t + 1) ≤ caHb A.K * H := Nat.mul_le_mul_left _ (by omega)
    have h2 : caHb A.K * (t + 1) = caHb A.K * t + caHb A.K := by ring
    omega
  have hlt : caB A.K + caHb A.K * t + p < caP A.K H := by rw [caP]; omega
  have hHb : 0 < caHb A.K := by omega
  have hd : (caB A.K + caHb A.K * t + p - caB A.K) / caHb A.K = t := by
    have h : caB A.K + caHb A.K * t + p - caB A.K = caHb A.K * t + p := by omega
    rw [h, Nat.mul_add_div hHb, Nat.div_eq_of_lt hp, Nat.add_zero]
  have hm : (caB A.K + caHb A.K * t + p - caB A.K) % caHb A.K = p := by
    have h : caB A.K + caHb A.K * t + p - caB A.K = caHb A.K * t + p := by omega
    rw [h, Nat.mul_add_mod, Nat.mod_eq_of_lt hp]
  rw [caT, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos hlt, hd, hm]

theorem caBlockG_conj1 (hm : m < caTri A.K) :
    caBlockG A.K A.blk A.stp W t (2 * m) j
      = .conj (caRefL A.K W A.blk t (triA A.K m) j) (caStId A.K W t (triB A.K m) j) := by
  rw [caBlockG, if_pos (by omega), if_pos (by omega),
    show 2 * m / 2 = m from by omega]

theorem caBlockG_conj2 (hm : m < caTri A.K) :
    caBlockG A.K A.blk A.stp W t (2 * m + 1) j
      = .conj (W * (caB A.K + caHb A.K * t + 2 * m) + j)
          (caRefR A.K W A.blk t (triC A.K m) j) := by
  rw [caBlockG, if_pos (by omega), if_neg (by omega),
    show (2 * m + 1) / 2 = m from by omega,
    show caB A.K + caHb A.K * t + (2 * m + 1) - 1 = caB A.K + caHb A.K * t + 2 * m from by omega]

theorem caBlockG_acc (hm : m < caTri A.K) :
    caBlockG A.K A.blk A.stp W t (2 * caTri A.K + d * caTri A.K + m) j
      = .disj (if m = 0 then 0
          else W * (caB A.K + caHb A.K * t + 2 * caTri A.K + d * caTri A.K + m - 1) + j)
        (if A.stp (triA A.K m) (triB A.K m) (triC A.K m) = d then
          W * (caB A.K + caHb A.K * t + 2 * m + 1) + j else 0) := by
  have hT : 0 < caTri A.K := by omega
  have hq : 2 * caTri A.K + d * caTri A.K + m - 2 * caTri A.K = d * caTri A.K + m := by omega
  have hmod : (d * caTri A.K + m) % caTri A.K = m := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hm]
  have hdiv : (d * caTri A.K + m) / caTri A.K = d := by
    rw [Nat.mul_comm, Nat.mul_add_div hT, Nat.div_eq_of_lt hm, Nat.add_zero]
  have harg : caB A.K + caHb A.K * t + (2 * caTri A.K + d * caTri A.K + m) - 1
      = caB A.K + caHb A.K * t + 2 * caTri A.K + d * caTri A.K + m - 1 := by omega
  rw [caBlockG, if_neg (by omega), hq, hmod, hdiv, harg]

/-! ### Reading the previous time step -/

theorem lval_ca_center (hs : s < A.K)
    (hrow : caB A.K + caHb A.K * t ≤ i) (hj' : j' < W)
    (hprev : ∀ u, u < A.K → ∀ v, v < W →
      lval y (caF A W H n) (caStId A.K W t u v) = decide (caCell A W n (abit y) t v = u)) :
    (vals y (layer (caF A W H n) (W * i + j))).getD (caStId A.K W t s j') false
      = decide (caCell A W n (abit y) t j' = s) := by
  have hrowlt := caStRow_lt_base (K := A.K) (t := t) hs
  have hlt : caStId A.K W t s j' < W * i + j := by
    rw [caStId]
    exact ca_row_lt (by omega) hj'
  rw [lval_ca_ref hlt, hprev s hs j' hj']

theorem lval_ca_refL (hW : 0 < W) (hj : j < W) (hs : s < A.K)
    (hrow : caB A.K + caHb A.K * t ≤ i)
    (hprev : ∀ u, u < A.K → ∀ v, v < W →
      lval y (caF A W H n) (caStId A.K W t u v) = decide (caCell A W n (abit y) t v = u)) :
    (vals y (layer (caF A W H n) (W * i + j))).getD (caRefL A.K W A.blk t s j) false
      = decide (caCellL A W n (abit y) t j = s) := by
  have hb : 3 ≤ caB A.K := by simp [caB]
  have hWlt : W < W * i + j := by
    have h := ca_row_lt (W := W) (i := i) (i' := 1) (j := j) (j' := 0) (by omega) hW
    omega
  have h0 : 0 < W * i + j := by
    have h := ca_row_lt (W := W) (i := i) (i' := 0) (j := j) (j' := 0) (by omega) hW
    omega
  rw [caRefL, caCellL]
  by_cases hj0 : j = 0
  · rw [if_pos hj0, if_pos hj0]
    by_cases hsb : s = A.blk
    · rw [if_pos hsb, lval_ca_ref hWlt, lval_ca_true hW, hsb]
      simp
    · rw [if_neg hsb, lval_ca_ref h0, lval_ca_false hW]
      simp [Ne.symm hsb]
  · rw [if_neg hj0, if_neg hj0]
    exact lval_ca_center hs hrow (by omega) hprev

theorem lval_ca_refR (hW : 0 < W) (hs : s < A.K)
    (hrow : caB A.K + caHb A.K * t ≤ i)
    (hprev : ∀ u, u < A.K → ∀ v, v < W →
      lval y (caF A W H n) (caStId A.K W t u v) = decide (caCell A W n (abit y) t v = u)) :
    (vals y (layer (caF A W H n) (W * i + j))).getD (caRefR A.K W A.blk t s j) false
      = decide (caCellR A W n (abit y) t j = s) := by
  have hb : 3 ≤ caB A.K := by simp [caB]
  have hWlt : W < W * i + j := by
    have h := ca_row_lt (W := W) (i := i) (i' := 1) (j := j) (j' := 0) (by omega) hW
    omega
  have h0 : 0 < W * i + j := by
    have h := ca_row_lt (W := W) (i := i) (i' := 0) (j := j) (j' := 0) (by omega) hW
    omega
  rw [caRefR, caCellR]
  by_cases hjw : j + 1 < W
  · rw [if_pos hjw, if_pos hjw]
    exact lval_ca_center hs hrow hjw hprev
  · rw [if_neg hjw, if_neg hjw]
    by_cases hsb : s = A.blk
    · rw [if_pos hsb, lval_ca_ref hWlt, lval_ca_true hW, hsb]
      simp
    · rw [if_neg hsb, lval_ca_ref h0, lval_ca_false hW]
      simp [Ne.symm hsb]

/-! ### The value of the rows of a block -/

theorem two_caTri_le_caHb (K : ℕ) : 2 * caTri K ≤ caHb K := by
  rw [caHb]
  calc 2 * caTri K = caTri K * 2 := by ring
    _ ≤ caTri K * (K + 2) := Nat.mul_le_mul_left _ (by omega)

theorem accP_lt_caHb {K d m : ℕ} (hd : d < K) (hm : m < caTri K) :
    2 * caTri K + d * caTri K + m < caHb K := by
  have h : d * caTri K + caTri K ≤ K * caTri K := by
    calc d * caTri K + caTri K = (d + 1) * caTri K := by ring
      _ ≤ K * caTri K := Nat.mul_le_mul_right _ (by omega)
  have hHb : caHb K = 2 * caTri K + K * caTri K := by rw [caHb]; ring
  omega

variable (hprev : ∀ u, u < A.K → ∀ v, v < W →
  lval y (caF A W H n) (caStId A.K W t u v) = decide (caCell A W n (abit y) t v = u))

include hprev

theorem lval_ca_conj1 (hW : 0 < W) (hj : j < W) (ht : t < H) (hm : m < caTri A.K) :
    lval y (caF A W H n) (W * (caB A.K + caHb A.K * t + 2 * m) + j)
      = (decide (caCellL A W n (abit y) t j = triA A.K m) &&
        decide (caCell A W n (abit y) t j = triB A.K m)) := by
  have hK := A.Kpos
  have hle := two_caTri_le_caHb A.K
  rw [lval, caF_block hj, caT_block (by omega) ht, caBlockG_conj1 hm, gateVal,
    lval_ca_refL hW hj (triA_lt hm) (by omega) hprev,
    lval_ca_center (triB_lt hK) (by omega) hj hprev]

theorem lval_ca_conj2 (hW : 0 < W) (hj : j < W) (ht : t < H) (hm : m < caTri A.K) :
    lval y (caF A W H n) (W * (caB A.K + caHb A.K * t + (2 * m + 1)) + j)
      = decide (triIdx A.K (caCellL A W n (abit y) t j) (caCell A W n (abit y) t j)
          (caCellR A W n (abit y) t j) = m) := by
  have hK := A.Kpos
  have hle := two_caTri_le_caHb A.K
  have hC := caCell_lt A W n (abit y) t j
  have hL := caCellL_lt A W n (abit y) t j
  have hR := caCellR_lt A W n (abit y) t j
  have href : W * (caB A.K + caHb A.K * t + 2 * m) + j
      < W * (caB A.K + caHb A.K * t + (2 * m + 1)) + j := ca_row_lt (by omega) hj
  rw [lval, caF_block hj, caT_block (by omega) ht, caBlockG_conj2 hm, gateVal,
    lval_ca_ref href, lval_ca_conj1 hprev hW hj ht hm,
    lval_ca_refR hW (triC_lt hK) (by omega) hprev]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rw [h1, h2, h3]
    exact triIdx_tri hm
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← h, triA_triIdx hC hR]
    · rw [← h, triB_triIdx hC hR]
    · rw [← h, triC_triIdx hR]

theorem lval_ca_acc (hW : 0 < W) (hj : j < W) (ht : t < H) (hd : d < A.K) :
    ∀ m, m < caTri A.K →
      lval y (caF A W H n)
          (W * (caB A.K + caHb A.K * t + (2 * caTri A.K + d * caTri A.K + m)) + j)
        = decide (triIdx A.K (caCellL A W n (abit y) t j) (caCell A W n (abit y) t j)
              (caCellR A W n (abit y) t j) ≤ m ∧
            A.stp (caCellL A W n (abit y) t j) (caCell A W n (abit y) t j)
              (caCellR A W n (abit y) t j) = d) := by
  have hK := A.Kpos
  have hC := caCell_lt A W n (abit y) t j
  have hL := caCellL_lt A W n (abit y) t j
  have hR := caCellR_lt A W n (abit y) t j
  have hidx : ∀ q : ℕ, q < caTri A.K →
      (triIdx A.K (caCellL A W n (abit y) t j) (caCell A W n (abit y) t j)
        (caCellR A W n (abit y) t j) = q) →
      A.stp (triA A.K q) (triB A.K q) (triC A.K q)
        = A.stp (caCellL A W n (abit y) t j) (caCell A W n (abit y) t j)
            (caCellR A W n (abit y) t j) := by
    intro q hq h
    rw [← h, triA_triIdx hC hR, triB_triIdx hC hR, triC_triIdx hR]
  intro m
  induction m with
  | zero =>
      intro hm
      have hp : 2 * caTri A.K + d * caTri A.K + 0 < caHb A.K := accP_lt_caHb hd hm
      have h0 : 0 < W * (caB A.K + caHb A.K * t + (2 * caTri A.K + d * caTri A.K + 0)) + j := by
        have h := ca_row_lt (W := W) (i := caB A.K + caHb A.K * t
          + (2 * caTri A.K + d * caTri A.K + 0)) (i' := 0) (j := j) (j' := 0)
          (by simp [caB]) hW
        omega
      have hY : W * (caB A.K + caHb A.K * t + (2 * 0 + 1)) + j
          < W * (caB A.K + caHb A.K * t + (2 * caTri A.K + d * caTri A.K + 0)) + j :=
        ca_row_lt (by omega) hj
      rw [lval, caF_block hj, caT_block hp ht, caBlockG_acc hm, gateVal, if_pos rfl,
        lval_ca_ref h0, lval_ca_false hW]
      by_cases hs : A.stp (triA A.K 0) (triB A.K 0) (triC A.K 0) = d
      · rw [if_pos hs]
        have hrw : W * (caB A.K + caHb A.K * t + 2 * 0 + 1) + j
            = W * (caB A.K + caHb A.K * t + (2 * 0 + 1)) + j := by ring_nf
        rw [hrw, lval_ca_ref hY, lval_ca_conj2 hprev hW hj ht hm, Bool.false_or]
        rw [Bool.eq_iff_iff]
        simp only [decide_eq_true_eq, Nat.le_zero]
        constructor
        · intro h
          exact ⟨h, by rw [← hidx 0 hm h]; exact hs⟩
        · rintro ⟨h, -⟩
          exact h
      · rw [if_neg hs, lval_ca_ref h0, lval_ca_false hW, Bool.false_or]
        rw [Bool.eq_iff_iff]
        simp only [decide_eq_true_eq, Nat.le_zero]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨h1, h2⟩
          rw [hidx 0 hm h1] at hs
          exact absurd h2 hs
  | succ m ih =>
      intro hm
      have hmlt : m < caTri A.K := by omega
      have hp : 2 * caTri A.K + d * caTri A.K + (m + 1) < caHb A.K := accP_lt_caHb hd hm
      have h0 : 0 < W * (caB A.K + caHb A.K * t
          + (2 * caTri A.K + d * caTri A.K + (m + 1))) + j := by
        have h := ca_row_lt (W := W) (i := caB A.K + caHb A.K * t
          + (2 * caTri A.K + d * caTri A.K + (m + 1))) (i' := 0) (j := j) (j' := 0)
          (by simp [caB]) hW
        omega
      have hprevrow : W * (caB A.K + caHb A.K * t + (2 * caTri A.K + d * caTri A.K + m)) + j
          < W * (caB A.K + caHb A.K * t + (2 * caTri A.K + d * caTri A.K + (m + 1))) + j :=
        ca_row_lt (by omega) hj
      have hY : W * (caB A.K + caHb A.K * t + (2 * (m + 1) + 1)) + j
          < W * (caB A.K + caHb A.K * t + (2 * caTri A.K + d * caTri A.K + (m + 1))) + j :=
        ca_row_lt (by omega) hj
      have hrw1 : W * (caB A.K + caHb A.K * t + 2 * caTri A.K + d * caTri A.K + (m + 1) - 1) + j
          = W * (caB A.K + caHb A.K * t + (2 * caTri A.K + d * caTri A.K + m)) + j := by
        congr 2
        omega
      have hrw2 : W * (caB A.K + caHb A.K * t + 2 * (m + 1) + 1) + j
          = W * (caB A.K + caHb A.K * t + (2 * (m + 1) + 1)) + j := by
        congr 2
      rw [lval, caF_block hj, caT_block hp ht, caBlockG_acc hm, gateVal, if_neg (by omega),
        hrw1, lval_ca_ref hprevrow, ih hmlt]
      by_cases hs : A.stp (triA A.K (m + 1)) (triB A.K (m + 1)) (triC A.K (m + 1)) = d
      · rw [if_pos hs, hrw2, lval_ca_ref hY, lval_ca_conj2 hprev hW hj ht hm]
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨h1, h2⟩ | h1)
          · exact ⟨by omega, h2⟩
          · exact ⟨by omega, by rw [← hidx (m + 1) hm h1]; exact hs⟩
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_or_ge (triIdx A.K (caCellL A W n (abit y) t j)
            (caCell A W n (abit y) t j) (caCellR A W n (abit y) t j)) (m + 1) with h | h
          · exact Or.inl ⟨by omega, h2⟩
          · exact Or.inr (by omega)
      · rw [if_neg hs, lval_ca_ref h0, lval_ca_false hW, Bool.or_false]
        rw [Bool.eq_iff_iff]
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          rcases Nat.lt_or_ge (triIdx A.K (caCellL A W n (abit y) t j)
            (caCell A W n (abit y) t j) (caCellR A W n (abit y) t j)) (m + 1) with h | h
          · omega
          · have heq : triIdx A.K (caCellL A W n (abit y) t j) (caCell A W n (abit y) t j)
                (caCellR A W n (abit y) t j) = m + 1 := by omega
            rw [hidx (m + 1) hm heq] at hs
            exact absurd h2 hs

theorem lval_ca_step (hW : 0 < W) (hj : j < W) (ht : t < H) (hd : d < A.K) :
    lval y (caF A W H n) (caStId A.K W (t + 1) d j)
      = decide (caCell A W n (abit y) (t + 1) j = d) := by
  have hK := A.Kpos
  have hT : 0 < caTri A.K := caTri_pos hK
  have hC := caCell_lt A W n (abit y) t j
  have hL := caCellL_lt A W n (abit y) t j
  have hR := caCellR_lt A W n (abit y) t j
  have hidlt : triIdx A.K (caCellL A W n (abit y) t j) (caCell A W n (abit y) t j)
      (caCellR A W n (abit y) t j) < caTri A.K := triIdx_lt hL hC hR
  have hid : caStId A.K W (t + 1) d j
      = W * (caB A.K + caHb A.K * t + (2 * caTri A.K + d * caTri A.K + (caTri A.K - 1))) + j := by
    rw [caStId, caStRow, if_neg (by omega), Nat.add_sub_cancel]
    congr 2
    omega
  rw [hid, lval_ca_acc hprev hW hj ht hd _ (by omega), caCell_succ]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨by omega, h⟩

omit hprev

theorem lval_ca_state (hW : 0 < W) : ∀ t, t ≤ H → ∀ s, s < A.K → ∀ j, j < W →
    lval y (caF A W H n) (caStId A.K W t s j) = decide (caCell A W n (abit y) t j = s) := by
  intro t
  induction t with
  | zero => intro _ s hs j hj; exact lval_ca_init hj hs
  | succ t ih =>
      intro ht s hs j hj
      exact lval_ca_step (fun u hu v hv => ih (by omega) u hu v hv) hW hj (by omega) hs

/-! ### The final rows and the output -/

theorem caP_ge (K H : ℕ) : 3 ≤ caP K H := by
  have : caP K H = 3 + K + caHb K * H := by rw [caP, caB]
  omega

theorem caT_fin {e : ℕ} (he : e < A.K) :
    caT A W H n (caP A.K H + e) j = caFinG A.K A.ac W H e j := by
  have hP := caP_ge A.K H
  have hcaB : caB A.K = 3 + A.K := rfl
  have hle : caB A.K ≤ caP A.K H := by
    have : caP A.K H = caB A.K + caHb A.K * H := rfl
    omega
  rw [caT, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

theorem caT_last (hi : caP A.K H + A.K ≤ i) :
    caT A W H n i j = .disj (W * (caP A.K H + A.K - 1)) (W * (caP A.K H + A.K - 1)) := by
  have hP := caP_ge A.K H
  have hle : caB A.K ≤ caP A.K H := by
    have : caP A.K H = caB A.K + caHb A.K * H := rfl
    omega
  rw [caT, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

theorem lval_ca_fin (hW : 0 < W) : ∀ e, e < A.K → ∀ j, j < W →
    lval y (caF A W H n) (W * (caP A.K H + e) + j)
      = (decide (caCell A W n (abit y) H j ≤ e) && A.ac (caCell A W n (abit y) H j)) := by
  have hP := caP_ge A.K H
  intro e
  induction e with
  | zero =>
      intro he j hj
      have h0 : 0 < W * (caP A.K H + 0) + j := by
        have h := ca_row_lt (W := W) (i := caP A.K H + 0) (i' := 0) (j := j) (j' := 0)
          (by omega) hW
        omega
      have hst : caStId A.K W H 0 j < W * (caP A.K H + 0) + j := by
        have hrow := caStRow_lt_caP (K := A.K) (H := H) (t := H) he le_rfl
        rw [caStId]
        exact ca_row_lt (by omega) hj
      rw [lval, caF_block hj, caT_fin he, caFinG, gateVal, if_pos rfl, lval_ca_ref h0,
        lval_ca_false hW]
      by_cases hac : A.ac 0
      · rw [if_pos hac, lval_ca_ref hst, lval_ca_state hW H le_rfl 0 he j hj, Bool.false_or]
        cases hc : caCell A W n (abit y) H j with
        | zero => simp [hac]
        | succ k => simp
      · have hac' : A.ac 0 = false := by simpa using hac
        rw [if_neg hac, lval_ca_ref h0, lval_ca_false hW, Bool.false_or]
        cases hc : caCell A W n (abit y) H j with
        | zero => simp [hac']
        | succ k => simp
  | succ e ih =>
      intro he j hj
      have hprevrow : W * (caP A.K H + e) + j < W * (caP A.K H + (e + 1)) + j :=
        ca_row_lt (by omega) hj
      have h0 : 0 < W * (caP A.K H + (e + 1)) + j := by
        have h := ca_row_lt (W := W) (i := caP A.K H + (e + 1)) (i' := 0) (j := j) (j' := 0)
          (by omega) hW
        omega
      have hst : caStId A.K W H (e + 1) j < W * (caP A.K H + (e + 1)) + j := by
        have hrow := caStRow_lt_caP (K := A.K) (H := H) (t := H) he le_rfl
        rw [caStId]
        exact ca_row_lt (by omega) hj
      have hrw : W * (caP A.K H + (e + 1) - 1) + j = W * (caP A.K H + e) + j := by
        congr 2
      rw [lval, caF_block hj, caT_fin he, caFinG, gateVal, if_neg (by omega), hrw,
        lval_ca_ref hprevrow, ih (by omega) j hj]
      by_cases hac : A.ac (e + 1)
      · rw [if_pos hac, lval_ca_ref hst, lval_ca_state hW H le_rfl (e + 1) he j hj]
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨h1, h2⟩ | h1)
          · exact ⟨by omega, h2⟩
          · exact ⟨by omega, by rw [h1]; exact hac⟩
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_or_ge (caCell A W n (abit y) H j) (e + 1) with h | h
          · exact Or.inl ⟨by omega, h2⟩
          · exact Or.inr (by omega)
      · have hac' : A.ac (e + 1) = false := by simpa using hac
        rw [if_neg hac, lval_ca_ref h0, lval_ca_false hW, Bool.or_false]
        rw [Bool.eq_iff_iff]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          rcases Nat.lt_or_ge (caCell A W n (abit y) H j) (e + 1) with h | h
          · omega
          · rw [show caCell A W n (abit y) H j = e + 1 by omega, hac'] at h2
            exact absurd h2 (by simp)

/-- **The tableau accepts exactly the words the automaton accepts**: the output gate holds the
acceptance bit of the cell `0` after `H` steps. -/
theorem out_caGrid (hW : 0 < W) :
    out y (caGrid A W H n) = A.ac (caCell A W n (abit y) H 0) := by
  have hK := A.Kpos
  have hP := caP_ge A.K H
  have hcell := caCell_lt A W n (abit y) H 0
  have hlast : caCnt A.K W H = (W * (caP A.K H + A.K) + (W - 1)) + 1 := by
    rw [caCnt, caRows]
    have h : W * (caP A.K H + A.K + 1) = W * (caP A.K H + A.K) + W := by ring
    omega
  have hrefrow : W * (caP A.K H + A.K - 1) = W * (caP A.K H + (A.K - 1)) + 0 := by
    congr 2
    omega
  have href : W * (caP A.K H + (A.K - 1)) + 0 < W * (caP A.K H + A.K) + (W - 1) :=
    ca_row_lt (by omega) hW
  rw [caGrid, hlast, out_layer, lval, caF_block (by omega), caT_last (by omega), gateVal,
    hrefrow, lval_ca_ref href, lval_ca_fin hW (A.K - 1) (by omega) 0 hW, Bool.or_self,
    decide_eq_true (by omega : caCell A W n (abit y) H 0 ≤ A.K - 1), Bool.true_and]

end Sem



end CircCode

end Complexity
