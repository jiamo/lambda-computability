/-
**Finite automata as P-uniform circuit families.**

`Start/UniformDecide.lean` exhibits two languages decided by P-uniform circuit families, the
all-ones words and the words with at least one `true`.  Both are recognised by a two-state
automaton, and this module proves the general statement they are instances of: **the language of
every finite automaton is decided by a P-uniform family of circuits**, hence reduces to SAT in
polynomial time with no hypothesis left over.

The circuits are a chain of `n` identical blocks, one per input bit, carrying the state of the
automaton in one-hot form.  A block of `K = 4 + 2 * m ^ 2 + m` gates holds

* the four constants and literals `false`, `true`, `x_{2i+1}` and its negation;
* for every pair of states `(s, t)`, the conjunction of "the previous state was `t`" with the
  selector saying that `t` moves to `s` on the bit just read, and the running disjunction of those
  conjunctions over `t`, whose last member is the one-hot bit "the new state is `s`";
* the running disjunction, over the accepting states `s`, of the new one-hot bits, whose last
  member is "the automaton accepts the prefix read so far".

Every reference of a block is either inside the block or at a fixed offset of the block below, so
the description is written block by block by the loop rule
`Complexity.codeUniform_blockLayer`, with one Cobham term per offset.

Main definitions:

* `Complexity.CircCode.autoT`, `Complexity.CircCode.autoCirc` — the block template and the family;
* `Complexity.CircCode.runTo` — the state of the automaton after the first `i` bits;
* `Complexity.AutoLang` — the language of an automaton.

Main results:

* `Complexity.CircCode.wf_autoCirc`, `Complexity.CircCode.out_autoCirc` — the family is well
  formed and its output is the acceptance of the word read off the input;
* `Complexity.codeUniform_autoCirc` — **its descriptions are written by a single Cobham term**;
* `Complexity.pUniformDecidable_autoLang` — **the language of a finite automaton is decided by a
  P-uniform circuit family**;
* `Complexity.polyManyOne_SAT_autoLang` — hence it reduces to SAT in polynomial time.
-/

import Start.UniformDecide

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### The layout of a block -/

/-- The number of gates of one block: four constants and literals, two gates for each ordered pair
of states, and one accumulator for each state. -/
def autoK (m : ℕ) : ℕ := 4 + 2 * (m * m) + m

theorem autoK_pos {m : ℕ} : 0 < autoK m := by
  rw [autoK]; omega

/-- The offset of the conjunction gate of the pair `(s, t)` inside a block. -/
def cjOff (m s t : ℕ) : ℕ := 4 + 2 * (s * m + t)

/-- The offset of the accumulator gate of the pair `(s, t)` inside a block. -/
def acOff (m s t : ℕ) : ℕ := 4 + 2 * (s * m + t) + 1

/-- The offset of the one-hot bit of the state `s`: the last accumulator of its row. -/
def stOff (m s : ℕ) : ℕ := acOff m s (m - 1)

/-- The offset of the `s`-th gate of the final acceptance chain. -/
def fnOff (m s : ℕ) : ℕ := 4 + 2 * (m * m) + s

theorem mul_add_lt {m s t : ℕ} (hs : s < m) (ht : t < m) : s * m + t < m * m := by
  have h : s * m + m ≤ m * m := by
    have : (s + 1) * m ≤ m * m := Nat.mul_le_mul_right m hs
    simpa [Nat.succ_mul] using this
  omega

theorem cjOff_lt {m s t : ℕ} (hs : s < m) (ht : t < m) : cjOff m s t < 4 + 2 * (m * m) := by
  have := mul_add_lt hs ht
  rw [cjOff]; omega

theorem acOff_lt {m s t : ℕ} (hs : s < m) (ht : t < m) : acOff m s t < 4 + 2 * (m * m) := by
  have := mul_add_lt hs ht
  rw [acOff]; omega

theorem stOff_lt {m s : ℕ} (hm : 0 < m) (hs : s < m) : stOff m s < 4 + 2 * (m * m) :=
  acOff_lt hs (by omega)

theorem fnOff_lt {m s : ℕ} (hs : s < m) : fnOff m s < autoK m := by
  rw [fnOff, autoK]; omega

/-! ### The template of a block -/

/-- The selector of the pair `(s, t)`: the offset, inside the block, of the gate saying that the
state `t` moves to the state `s` on the bit just read.  It is the constant `false` when no bit
does, the constant `true` when both do, the bit itself or its negation otherwise. -/
def autoSel (δ : ℕ → Bool → ℕ) (s t : ℕ) : ℕ :=
  if δ t false = s then (if δ t true = s then 1 else 3)
  else (if δ t true = s then 2 else 0)

/-- The identifier of the gate holding the one-hot bit of the state `t` before the block `i`: the
initial state in the first block, the state gate of the block below afterwards. -/
def autoPrev (m : ℕ) : ℕ → ℕ → ℕ
  | 0, t => if t = 0 then 1 else 0
  | i + 1, t => autoK m * i + stOff m t

/-- The accumulator gate of the pair `(s, t)` in the block `i`. -/
def autoAcc (m i s t : ℕ) : Gate :=
  if t = 0 then .disj (autoK m * i + cjOff m s 0) (autoK m * i + cjOff m s 0)
  else .disj (autoK m * i + acOff m s (t - 1)) (autoK m * i + cjOff m s t)

/-- The identifier contributed to the acceptance chain by the state `s`: its one-hot bit if `s` is
accepting, the constant `false` otherwise. -/
def autoX (m : ℕ) (ac : ℕ → Bool) (i s : ℕ) : ℕ :=
  if ac s then autoK m * i + stOff m s else autoK m * i

/-- The `s`-th gate of the acceptance chain in the block `i`. -/
def autoFin (m : ℕ) (ac : ℕ → Bool) (i s : ℕ) : Gate :=
  if s = 0 then .disj (autoX m ac i 0) (autoX m ac i 0)
  else .disj (autoK m * i + fnOff m (s - 1)) (autoX m ac i s)

/-- **The template of the family**: the gate at the offset `o` of the block `i`. -/
def autoT (m : ℕ) (δ : ℕ → Bool → ℕ) (ac : ℕ → Bool) (o i : ℕ) : Gate :=
  if o = 0 then .cst false
  else if o = 1 then .cst true
  else if o = 2 then .inp (2 * i + 1)
  else if o = 3 then .neg (autoK m * i + 2)
  else if o < 4 + 2 * (m * m) then
    (if (o - 4) % 2 = 0 then
        Gate.conj (autoPrev m i ((o - 4) / 2 % m))
          (autoK m * i + autoSel δ ((o - 4) / 2 / m) ((o - 4) / 2 % m))
      else autoAcc m i ((o - 4) / 2 / m) ((o - 4) / 2 % m))
  else if o < autoK m then autoFin m ac i (o - 4 - 2 * (m * m))
  else .cst false

/-- The gate with identifier `c`: the offset inside its block is `c % K` and the index of its
block is `c / K`. -/
def autoF (m : ℕ) (δ : ℕ → Bool → ℕ) (ac : ℕ → Bool) (c : ℕ) : Gate :=
  autoT m δ ac (c % autoK m) (c / autoK m)

/-- **The family**: `n` blocks, one per input bit. -/
def autoCirc (m : ℕ) (δ : ℕ → Bool → ℕ) (ac : ℕ → Bool) (n : ℕ) : Circuit :=
  layer (autoF m δ ac) (autoK m * n)

@[simp] theorem length_autoCirc (m : ℕ) (δ : ℕ → Bool → ℕ) (ac : ℕ → Bool) (n : ℕ) :
    (autoCirc m δ ac n).length = autoK m * n := by
  rw [autoCirc, length_layer]

/-! ### Reading the template off an offset -/

section Template

variable {m : ℕ} {δ : ℕ → Bool → ℕ} {ac : ℕ → Bool}

theorem div_pair {s t : ℕ} (hm : 0 < m) (ht : t < m) : (s * m + t) / m = s := by
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt ht, Nat.zero_add]

theorem mod_pair {s t : ℕ} (ht : t < m) : (s * m + t) % m = t := by
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

theorem autoT_zero (i : ℕ) : autoT m δ ac 0 i = .cst false := by
  rw [autoT, if_pos rfl]

theorem autoT_one (i : ℕ) : autoT m δ ac 1 i = .cst true := by
  rw [autoT, if_neg (by omega), if_pos rfl]

theorem autoT_two (i : ℕ) : autoT m δ ac 2 i = .inp (2 * i + 1) := by
  rw [autoT, if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem autoT_three (i : ℕ) : autoT m δ ac 3 i = .neg (autoK m * i + 2) := by
  rw [autoT, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem autoT_cj {s t : ℕ} (hm : 0 < m) (hs : s < m) (ht : t < m) (i : ℕ) :
    autoT m δ ac (cjOff m s t) i
      = .conj (autoPrev m i t) (autoK m * i + autoSel δ s t) := by
  have h4 : cjOff m s t - 4 = 2 * (s * m + t) := by rw [cjOff]; omega
  rw [autoT, if_neg (by rw [cjOff]; omega), if_neg (by rw [cjOff]; omega),
    if_neg (by rw [cjOff]; omega), if_neg (by rw [cjOff]; omega),
    if_pos (cjOff_lt hs ht), h4]
  rw [Nat.mul_mod_right, if_pos rfl, Nat.mul_div_cancel_left _ (by omega : 0 < 2),
    div_pair hm ht, mod_pair ht]

theorem autoT_ac {s t : ℕ} (hm : 0 < m) (hs : s < m) (ht : t < m) (i : ℕ) :
    autoT m δ ac (acOff m s t) i = autoAcc m i s t := by
  have h4 : acOff m s t - 4 = 2 * (s * m + t) + 1 := by rw [acOff]; omega
  have hodd : (2 * (s * m + t) + 1) % 2 = 1 := by omega
  have hdiv : (2 * (s * m + t) + 1) / 2 = s * m + t := by omega
  rw [autoT, if_neg (by rw [acOff]; omega), if_neg (by rw [acOff]; omega),
    if_neg (by rw [acOff]; omega), if_neg (by rw [acOff]; omega),
    if_pos (acOff_lt hs ht), h4, hodd, if_neg (by omega), hdiv, div_pair hm ht, mod_pair ht]

theorem autoT_fn {s : ℕ} (hs : s < m) (i : ℕ) :
    autoT m δ ac (fnOff m s) i = autoFin m ac i s := by
  have h4 : fnOff m s - 4 - 2 * (m * m) = s := by rw [fnOff]; omega
  rw [autoT, if_neg (by rw [fnOff]; omega), if_neg (by rw [fnOff]; omega),
    if_neg (by rw [fnOff]; omega), if_neg (by rw [fnOff]; omega),
    if_neg (by rw [fnOff]; omega), if_pos (fnOff_lt hs), h4]

/-- The gate with identifier `autoK m * i + o`, for an offset `o` inside the block. -/
theorem autoF_block {o : ℕ} (ho : o < autoK m) (i : ℕ) :
    autoF m δ ac (autoK m * i + o) = autoT m δ ac o i := by
  have hK : 0 < autoK m := autoK_pos
  have hdiv : (autoK m * i + o) / autoK m = i := by
    rw [Nat.mul_add_div hK, Nat.div_eq_of_lt ho, Nat.add_zero]
  have hmod : (autoK m * i + o) % autoK m = o := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ho]
  rw [autoF, hdiv, hmod]

end Template

/-! ### Well-formedness -/

section Wf

variable {m : ℕ} {δ : ℕ → Bool → ℕ} {ac : ℕ → Bool}

theorem stOff_lt_autoK {s : ℕ} (hm : 0 < m) (hs : s < m) : stOff m s < autoK m := by
  have := stOff_lt hm hs
  rw [autoK]
  omega

theorem autoPrev_lt {t : ℕ} (hm : 0 < m) (ht : t < m) (i : ℕ) :
    autoPrev m i t < autoK m * i + 4 := by
  cases i with
  | zero =>
      rw [autoPrev]
      split <;> omega
  | succ i =>
      rw [autoPrev]
      have h := stOff_lt_autoK (m := m) (s := t) hm ht
      have : autoK m * (i + 1) = autoK m * i + autoK m := by ring
      omega

theorem autoSel_le (δ : ℕ → Bool → ℕ) (s t : ℕ) : autoSel δ s t ≤ 3 := by
  rw [autoSel]
  split_ifs <;> omega

/-- Every offset inside the block, other than the four first and the acceptance chain, is the
conjunction or the accumulator of a pair of states. -/
theorem exists_pair_of_offset {o : ℕ} (h4 : 4 ≤ o) (hlt : o < 4 + 2 * (m * m)) :
    ∃ s t, s < m ∧ t < m ∧ (o = cjOff m s t ∨ o = acOff m s t) := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega
    · exact h
  refine ⟨(o - 4) / 2 / m, (o - 4) / 2 % m, ?_, Nat.mod_lt _ hm, ?_⟩
  · have hq : (o - 4) / 2 < m * m := by omega
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hq; exact hq)
  · have hqm : (o - 4) / 2 / m * m + (o - 4) / 2 % m = (o - 4) / 2 := by
      have h := Nat.div_add_mod ((o - 4) / 2) m
      rw [Nat.mul_comm] at h
      exact h
    rcases Nat.even_or_odd (o - 4) with he | ho
    · left
      rw [cjOff, hqm]
      have : (o - 4) % 2 = 0 := Nat.even_iff.mp he
      omega
    · right
      rw [acOff, hqm]
      have : (o - 4) % 2 = 1 := Nat.odd_iff.mp ho
      omega

theorem gateWf_autoT {o i : ℕ} (ho : o < autoK m) :
    gateWf (autoK m * i + o) (autoT m δ ac o i) := by
  rcases Nat.lt_or_ge o 4 with hsmall | h4
  · interval_cases o
    · rw [autoT_zero]; trivial
    · rw [autoT_one]; trivial
    · rw [autoT_two]; trivial
    · rw [autoT_three]
      change autoK m * i + 2 < autoK m * i + 3
      omega
  rcases Nat.lt_or_ge o (4 + 2 * (m * m)) with hmid | hfin
  · have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; omega
      · exact h
    obtain ⟨s, t, hs, ht, hcase⟩ := exists_pair_of_offset (m := m) h4 hmid
    rcases hcase with rfl | rfl
    · rw [autoT_cj hm hs ht]
      have h1 := autoPrev_lt (m := m) (t := t) hm ht i
      have h2 := autoSel_le δ s t
      have h3 : 4 ≤ cjOff m s t := by rw [cjOff]; omega
      exact ⟨by omega, by omega⟩
    · rw [autoT_ac hm hs ht, autoAcc]
      split_ifs with h0
      · subst h0
        have : cjOff m s 0 + 1 = acOff m s 0 := by rw [cjOff, acOff]
        exact ⟨by omega, by omega⟩
      · have h1 : cjOff m s t + 1 = acOff m s t := by rw [cjOff, acOff]
        have h2 : acOff m s (t - 1) + 2 = acOff m s t := by
          rw [acOff, acOff]
          have : t - 1 + 1 = t := by omega
          have hmul : s * m + (t - 1) + 1 = s * m + t := by omega
          omega
        exact ⟨by omega, by omega⟩
  · have hs : o - (4 + 2 * (m * m)) < m := by rw [autoK] at ho; omega
    have hm : 0 < m := by omega
    have hofn : o = fnOff m (o - (4 + 2 * (m * m))) := by rw [fnOff]; omega
    rw [hofn, autoT_fn hs, autoFin]
    set s := o - (4 + 2 * (m * m)) with hsdef
    have hX : autoX m ac i s < autoK m * i + fnOff m s := by
      rw [autoX]
      split
      · have := stOff_lt hm hs
        rw [fnOff]
        omega
      · rw [fnOff]; omega
    have hX0 : autoX m ac i 0 < autoK m * i + fnOff m s := by
      rw [autoX]
      split
      · have := stOff_lt hm (show 0 < m from hm)
        rw [fnOff]
        omega
      · rw [fnOff]; omega
    split_ifs with h0
    · exact ⟨hX0, hX0⟩
    · refine ⟨?_, hX⟩
      have : fnOff m (s - 1) < fnOff m s := by rw [fnOff, fnOff]; omega
      omega

theorem gateWf_autoF (j : ℕ) : gateWf j (autoF m δ ac j) := by
  have hK : 0 < autoK m := autoK_pos
  have hj : autoK m * (j / autoK m) + j % autoK m = j := Nat.div_add_mod _ _
  have ho : j % autoK m < autoK m := Nat.mod_lt _ hK
  have h := gateWf_autoT (m := m) (δ := δ) (ac := ac) (i := j / autoK m) ho
  rw [hj] at h
  rw [autoF]
  exact h

theorem wf_autoCirc (m : ℕ) (δ : ℕ → Bool → ℕ) (ac : ℕ → Bool) (n : ℕ) :
    wf (autoCirc m δ ac n) :=
  wf_layer fun j _ => gateWf_autoF j

end Wf

/-! ### What the family computes -/

section Semantics

variable {m : ℕ} {δ : ℕ → Bool → ℕ} {ac : ℕ → Bool} {x : Word}

/-- The `i`-th bit of the word presented by the circuit input. -/
def abit (x : Word) (i : ℕ) : Bool := x.getD (2 * i + 1) false

/-- The state of the automaton after the first `i` bits. -/
def runTo (δ : ℕ → Bool → ℕ) (x : Word) : ℕ → ℕ
  | 0 => 0
  | i + 1 => δ (runTo δ x i) (abit x i)

theorem runTo_lt {m : ℕ} {δ : ℕ → Bool → ℕ} (hm : 0 < m) (hδ : ∀ s b, δ s b < m) (x : Word)
    (i : ℕ) : runTo δ x i < m := by
  cases i with
  | zero => exact hm
  | succ i => exact hδ _ _

/-- The value of the conjunction gate of the pair `(s, t)` in the block `i`. -/
def cjv (δ : ℕ → Bool → ℕ) (x : Word) (i s t : ℕ) : Bool :=
  decide (runTo δ x i = t) && decide (δ t (abit x i) = s)

/-- The value of the accumulator of the pair `(s, t)`: the disjunction of the conjunctions of the
pairs `(s, t')` with `t' ≤ t`. -/
def orUpTo (δ : ℕ → Bool → ℕ) (x : Word) (i s : ℕ) : ℕ → Bool
  | 0 => cjv δ x i s 0
  | t + 1 => orUpTo δ x i s t || cjv δ x i s (t + 1)

/-- The value of the `s`-th gate of the acceptance chain of the block `i`. -/
def fnUpTo (δ : ℕ → Bool → ℕ) (ac : ℕ → Bool) (x : Word) (i : ℕ) : ℕ → Bool
  | 0 => ac 0 && decide (runTo δ x (i + 1) = 0)
  | s + 1 => fnUpTo δ ac x i s || (ac (s + 1) && decide (runTo δ x (i + 1) = s + 1))

/-- Looking up the value of a gate below the one being evaluated. -/
theorem lval_ref {j r : ℕ} (hr : r < j) :
    (vals x (layer (autoF m δ ac) j)).getD r false = lval x (autoF m δ ac) r :=
  vals_layer_getD x (autoF m δ ac) j r hr

theorem lval_zero (i : ℕ) : lval x (autoF m δ ac) (autoK m * i) = false := by
  have h : autoK m * i = autoK m * i + 0 := rfl
  rw [lval, h, autoF_block autoK_pos i, autoT_zero]
  rfl

theorem lval_one (i : ℕ) : lval x (autoF m δ ac) (autoK m * i + 1) = true := by
  have h1 : (1 : ℕ) < autoK m := by rw [autoK]; omega
  rw [lval, autoF_block h1 i, autoT_one]
  rfl

theorem lval_two (i : ℕ) : lval x (autoF m δ ac) (autoK m * i + 2) = abit x i := by
  have h2 : (2 : ℕ) < autoK m := by rw [autoK]; omega
  rw [lval, autoF_block h2 i, autoT_two]
  rfl

theorem lval_three (i : ℕ) : lval x (autoF m δ ac) (autoK m * i + 3) = !abit x i := by
  have h3 : (3 : ℕ) < autoK m := by rw [autoK]; omega
  rw [lval, autoF_block h3 i, autoT_three, gateVal, lval_ref (by omega), lval_two]

/-- The value of the selector gate of the pair `(s, t)`: the bit just read moves `t` to `s`. -/
theorem lval_sel (i s t : ℕ) :
    lval x (autoF m δ ac) (autoK m * i + autoSel δ s t) = decide (δ t (abit x i) = s) := by
  rw [autoSel]
  split_ifs with h0 h1 h2
  · rw [lval_one]
    cases abit x i <;> simp [h0, h1]
  · rw [lval_three]
    cases abit x i <;> simp [h0, h1]
  · rw [lval_two]
    cases abit x i <;> simp [h0, h2]
  · rw [Nat.add_zero, lval_zero]
    cases abit x i <;> simp [h0, h2]

/-! ### The value of a block, given the block below -/

/-- The conjunction gate of the pair `(s, t)` holds "the previous state was `t`, and `t` moves to
`s` on the bit just read". -/
theorem lval_cj (hm : 0 < m) {i : ℕ}
    (hprev : ∀ t, t < m →
      lval x (autoF m δ ac) (autoPrev m i t) = decide (runTo δ x i = t))
    {s t : ℕ} (hs : s < m) (ht : t < m) :
    lval x (autoF m δ ac) (autoK m * i + cjOff m s t) = cjv δ x i s t := by
  have hlt : cjOff m s t < autoK m := by
    have := cjOff_lt hs ht
    rw [autoK]
    omega
  have h4 : 4 ≤ cjOff m s t := by rw [cjOff]; omega
  have hp := autoPrev_lt (m := m) (t := t) hm ht i
  have hsel := autoSel_le δ s t
  rw [lval, autoF_block hlt i, autoT_cj hm hs ht, gateVal,
    lval_ref (by omega), lval_ref (by omega), hprev t ht, lval_sel, cjv]

/-- The accumulator of the pair `(s, t)` holds the disjunction over `t' ≤ t`. -/
theorem lval_acc (hm : 0 < m) {i : ℕ}
    (hprev : ∀ t, t < m →
      lval x (autoF m δ ac) (autoPrev m i t) = decide (runTo δ x i = t))
    {s : ℕ} (hs : s < m) :
    ∀ t, t < m → lval x (autoF m δ ac) (autoK m * i + acOff m s t) = orUpTo δ x i s t := by
  intro t
  induction t with
  | zero =>
      intro ht
      have hlt : acOff m s 0 < autoK m := by
        have := acOff_lt hs ht
        rw [autoK]
        omega
      have hcj : cjOff m s 0 + 1 = acOff m s 0 := by rw [cjOff, acOff]
      rw [lval, autoF_block hlt i, autoT_ac hm hs ht, autoAcc, if_pos rfl, gateVal,
        lval_ref (by omega), lval_cj hm hprev hs ht, orUpTo, Bool.or_self]
  | succ t ih =>
      intro ht
      have htm : t < m := by omega
      have hlt : acOff m s (t + 1) < autoK m := by
        have := acOff_lt hs ht
        rw [autoK]
        omega
      have hcj : cjOff m s (t + 1) + 1 = acOff m s (t + 1) := by rw [cjOff, acOff]
      have hac : acOff m s t + 2 = acOff m s (t + 1) := by
        rw [acOff, acOff]
        have : s * m + (t + 1) = s * m + t + 1 := by omega
        omega
      rw [lval, autoF_block hlt i, autoT_ac hm hs ht, autoAcc, if_neg (by omega),
        show t + 1 - 1 = t from rfl, gateVal, lval_ref (by omega), lval_ref (by omega),
        ih htm, lval_cj hm hprev hs ht, orUpTo]

/-- Below the current state the accumulated disjunction is still empty. -/
theorem orUpTo_of_lt (i s : ℕ) : ∀ t, t < runTo δ x i → orUpTo δ x i s t = false := by
  intro t
  induction t with
  | zero =>
      intro ht
      rw [orUpTo, cjv, decide_eq_false (by omega), Bool.false_and]
  | succ t ih =>
      intro ht
      rw [orUpTo, ih (by omega), cjv, decide_eq_false (by omega), Bool.false_and,
        Bool.or_self]

/-- Once the current state has been passed, the accumulated disjunction is the transition. -/
theorem orUpTo_eq (i s : ℕ) :
    ∀ t, runTo δ x i ≤ t →
      orUpTo δ x i s t = decide (δ (runTo δ x i) (abit x i) = s) := by
  intro t
  induction t with
  | zero =>
      intro ht
      have h0 : runTo δ x i = 0 := by omega
      rw [orUpTo, cjv, h0]
      simp
  | succ t ih =>
      intro ht
      rcases Nat.lt_or_ge t (runTo δ x i) with hlt | hge
      · have heq : runTo δ x i = t + 1 := by omega
        rw [orUpTo, orUpTo_of_lt i s t hlt, cjv, heq]
        simp
      · rw [orUpTo, ih hge, cjv, decide_eq_false (by omega : ¬ runTo δ x i = t + 1),
          Bool.false_and, Bool.or_false]

/-- The one-hot bit of the state `s` in the block `i`. -/
theorem lval_state_step (hm : 0 < m) (hδ : ∀ s b, δ s b < m) {i : ℕ}
    (hprev : ∀ t, t < m →
      lval x (autoF m δ ac) (autoPrev m i t) = decide (runTo δ x i = t))
    {s : ℕ} (hs : s < m) :
    lval x (autoF m δ ac) (autoK m * i + stOff m s) = decide (runTo δ x (i + 1) = s) := by
  have hr : runTo δ x i < m := runTo_lt hm hδ x i
  rw [stOff, lval_acc hm hprev hs (m - 1) (by omega), orUpTo_eq i s (m - 1) (by omega), runTo]

/-- The one-hot bits of the block below, or the initial state in the first block. -/
theorem lval_prev (hm : 0 < m) (hδ : ∀ s b, δ s b < m) :
    ∀ (i t : ℕ), t < m →
      lval x (autoF m δ ac) (autoPrev m i t) = decide (runTo δ x i = t) := by
  intro i
  induction i with
  | zero =>
      intro t ht
      rw [autoPrev]
      split_ifs with h0
      · subst h0
        rw [show (1 : ℕ) = autoK m * 0 + 1 by omega, lval_one]
        simp [runTo]
      · rw [show (0 : ℕ) = autoK m * 0 by omega, lval_zero]
        simp [runTo, Ne.symm h0]
  | succ i ih =>
      intro t ht
      rw [autoPrev]
      exact lval_state_step hm hδ (fun t' ht' => ih t' ht') ht

/-- **The one-hot bits of a block record the state of the automaton** after the bits read so
far. -/
theorem lval_state (hm : 0 < m) (hδ : ∀ s b, δ s b < m) (i : ℕ) {s : ℕ} (hs : s < m) :
    lval x (autoF m δ ac) (autoK m * i + stOff m s) = decide (runTo δ x (i + 1) = s) :=
  lval_state_step hm hδ (lval_prev hm hδ i) hs

/-! ### The acceptance chain -/

theorem lval_fin (hm : 0 < m) (hδ : ∀ s b, δ s b < m) (i : ℕ) :
    ∀ s, s < m →
      lval x (autoF m δ ac) (autoK m * i + fnOff m s) = fnUpTo δ ac x i s := by
  intro s
  induction s with
  | zero =>
      intro hs
      have hX : autoX m ac i 0 < autoK m * i + fnOff m 0 := by
        rw [autoX]
        split
        · have := stOff_lt hm hs
          rw [fnOff]
          omega
        · rw [fnOff]; omega
      rw [lval, autoF_block (fnOff_lt hs) i, autoT_fn hs, autoFin, if_pos rfl, gateVal,
        lval_ref hX, Bool.or_self, autoX]
      split_ifs with hac
      · rw [lval_state hm hδ i hs, fnUpTo, hac]
        simp
      · rw [lval_zero, fnUpTo]
        simp [hac]
  | succ s ih =>
      intro hs
      have hsm : s < m := by omega
      have hX : autoX m ac i (s + 1) < autoK m * i + fnOff m (s + 1) := by
        rw [autoX]
        split
        · have := stOff_lt hm hs
          rw [fnOff]
          omega
        · rw [fnOff]; omega
      have hfn : fnOff m s < fnOff m (s + 1) := by rw [fnOff, fnOff]; omega
      rw [lval, autoF_block (fnOff_lt hs) i, autoT_fn hs, autoFin, if_neg (by omega),
        show s + 1 - 1 = s from rfl, gateVal, lval_ref (by omega), lval_ref hX, ih hsm,
        fnUpTo, autoX]
      split_ifs with hac
      · rw [lval_state hm hδ i hs, hac]
        simp
      · rw [lval_zero]
        simp [hac]

theorem fnUpTo_of_lt (i : ℕ) : ∀ s, s < runTo δ x (i + 1) → fnUpTo δ ac x i s = false := by
  intro s
  induction s with
  | zero =>
      intro hs
      rw [fnUpTo, decide_eq_false (by omega), Bool.and_false]
  | succ s ih =>
      intro hs
      rw [fnUpTo, ih (by omega), decide_eq_false (by omega), Bool.and_false, Bool.or_self]

theorem fnUpTo_eq (i : ℕ) :
    ∀ s, runTo δ x (i + 1) ≤ s → fnUpTo δ ac x i s = ac (runTo δ x (i + 1)) := by
  intro s
  induction s with
  | zero =>
      intro hs
      have h0 : runTo δ x (i + 1) = 0 := by omega
      rw [fnUpTo, h0]
      simp
  | succ s ih =>
      intro hs
      rcases Nat.lt_or_ge s (runTo δ x (i + 1)) with hlt | hge
      · have heq : runTo δ x (i + 1) = s + 1 := by omega
        rw [fnUpTo, fnUpTo_of_lt i s hlt, heq]
        simp
      · rw [fnUpTo, ih hge, decide_eq_false (by omega : ¬ runTo δ x (i + 1) = s + 1),
          Bool.and_false, Bool.or_false]

/-- **The family accepts exactly the words accepted by the automaton.** -/
theorem out_autoCirc (hm : 0 < m) (hδ : ∀ s b, δ s b < m) (n : ℕ) :
    out x (autoCirc m δ ac (n + 1)) = ac (runTo δ x (n + 1)) := by
  have hK : autoK m * (n + 1) = (autoK m * n + fnOff m (m - 1)) + 1 := by
    have h1 : autoK m * (n + 1) = autoK m * n + autoK m := by ring
    have h2 : autoK m = fnOff m (m - 1) + 1 := by rw [autoK, fnOff]; omega
    omega
  have hr : runTo δ x (n + 1) < m := runTo_lt hm hδ x (n + 1)
  rw [autoCirc, hK, out_layer, lval_fin hm hδ n (m - 1) (by omega),
    fnUpTo_eq n (m - 1) (by omega)]

end Semantics

/-! ### The descriptions are written by a Cobham term -/

section Uniform

variable {m : ℕ} {δ : ℕ → Bool → ℕ} {ac : ℕ → Bool}

/-- The offset, inside a block, of the gate contributed to the acceptance chain by the state
`s`. -/
def xOff (m : ℕ) (ac : ℕ → Bool) (s : ℕ) : ℕ := if ac s then stOff m s else 0

theorem autoX_eq (m : ℕ) (ac : ℕ → Bool) (i s : ℕ) :
    autoX m ac i s = autoK m * i + xOff m ac s := by
  rw [autoX, xOff]
  split <;> omega

/-- The Cobham term writing, in unary, the reference to the state gate of the block below. -/
def prevT (m t : ℕ) : Cob :=
  .comp Cob.iteC [.proj 1,
    Cob.pre (List.replicate (stOff m t) true)
      (.comp .smash [.comp Cob.tail [.proj 1], Cob.constT (List.replicate (autoK m) true)]),
    Cob.constT (List.replicate (if t = 0 then 1 else 0) true)]

theorem eval_prevT (m t : ℕ) (y : Word) (c n : ℕ) :
    (prevT m t).eval [y, List.replicate c true, List.replicate n true]
      = List.replicate (autoPrev m c t) true := by
  cases c with
  | zero =>
      simp only [prevT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC,
        Cob.eval_proj, List.getD_cons_zero, List.getD_cons_succ, Cob.eval_constT,
        List.replicate_zero]
      simp [autoPrev]
  | succ i =>
      simp only [prevT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC,
        Cob.eval_proj, List.getD_cons_zero, List.getD_cons_succ, Cob.eval_constT,
        Cob.eval_pre, Cob.eval_smash, Cob.eval_tail, List.tail_replicate,
        List.length_replicate,
        if_neg (by simp : ¬ (List.replicate (i + 1) true = ([] : Word)))]
      rw [← List.replicate_add, autoPrev]
      congr 1
      have h : i + 1 - 1 = i := by omega
      rw [h, Nat.mul_comm, Nat.add_comm]

/-- The Cobham term writing the accumulator gate of the pair `(s, t)`. -/
def accT (m s t : ℕ) : Cob :=
  if t = 0 then
    tokTerm 6 (linT 1 (autoK m) (cjOff m s 0)) (linT 1 (autoK m) (cjOff m s 0))
  else
    tokTerm 6 (linT 1 (autoK m) (acOff m s (t - 1))) (linT 1 (autoK m) (cjOff m s t))

/-- The Cobham term writing the `s`-th gate of the acceptance chain. -/
def finT (m : ℕ) (ac : ℕ → Bool) (s : ℕ) : Cob :=
  if s = 0 then
    tokTerm 6 (linT 1 (autoK m) (xOff m ac 0)) (linT 1 (autoK m) (xOff m ac 0))
  else
    tokTerm 6 (linT 1 (autoK m) (fnOff m (s - 1))) (linT 1 (autoK m) (xOff m ac s))

/-- **The Cobham term writing the gate at a given offset of a block**, from the block index in
unary. -/
def autoBlk (m : ℕ) (δ : ℕ → Bool → ℕ) (ac : ℕ → Bool) (o : ℕ) : Cob :=
  if o = 0 then tokTerm 2 (Cob.constT []) (Cob.constT [])
  else if o = 1 then tokTerm 3 (Cob.constT []) (Cob.constT [])
  else if o = 2 then tokTerm 1 (linT 1 2 1) (Cob.constT [])
  else if o = 3 then tokTerm 4 (linT 1 (autoK m) 2) (Cob.constT [])
  else if o < 4 + 2 * (m * m) then
    (if (o - 4) % 2 = 0 then
        tokTerm 5 (prevT m ((o - 4) / 2 % m))
          (linT 1 (autoK m) (autoSel δ ((o - 4) / 2 / m) ((o - 4) / 2 % m)))
      else accT m ((o - 4) / 2 / m) ((o - 4) / 2 % m))
  else if o < autoK m then finT m ac (o - 4 - 2 * (m * m))
  else tokTerm 2 (Cob.constT []) (Cob.constT [])

theorem eval_autoBlk (n : ℕ) (y : Word) (o c : ℕ) :
    (autoBlk m δ ac o).eval [y, List.replicate c true, List.replicate n true]
      = encGate (autoT m δ ac o c) := by
  have harg : ([y, List.replicate c true, List.replicate n true] : List Word).getD 1 []
      = List.replicate c true := rfl
  rw [autoBlk, autoT]
  have hf1 : ∀ a b : ℕ, fld1 (Gate.disj a b) = a := fun _ _ => rfl
  have hf2 : ∀ a b : ℕ, fld2 (Gate.disj a b) = b := fun _ _ => rfl
  split_ifs with h0 h1 h2 h3 h4 h5 h6
  · exact eval_tokTerm (.cst false) (by simp [fld1]) (by simp [fld2])
  · exact eval_tokTerm (.cst true) (by simp [fld1]) (by simp [fld2])
  · exact eval_tokTerm (.inp (2 * c + 1)) (eval_linT harg (by simp only [fld1]; ring))
      (by simp [fld2])
  · exact eval_tokTerm (.neg (autoK m * c + 2)) (eval_linT harg (by simp only [fld1]; ring))
      (by simp [fld2])
  · exact eval_tokTerm (.conj (autoPrev m c ((o - 4) / 2 % m))
      (autoK m * c + autoSel δ ((o - 4) / 2 / m) ((o - 4) / 2 % m)))
      (eval_prevT m _ y c n) (eval_linT harg (by simp only [fld2]; ring))
  · rw [accT, autoAcc]
    split_ifs with ht
    · exact eval_tokTerm (.disj (autoK m * c + cjOff m ((o - 4) / 2 / m) 0)
        (autoK m * c + cjOff m ((o - 4) / 2 / m) 0))
        (eval_linT harg (by rw [hf1]; ring)) (eval_linT harg (by rw [hf2]; ring))
    · exact eval_tokTerm (.disj (autoK m * c + acOff m ((o - 4) / 2 / m) ((o - 4) / 2 % m - 1))
        (autoK m * c + cjOff m ((o - 4) / 2 / m) ((o - 4) / 2 % m)))
        (eval_linT harg (by rw [hf1]; ring)) (eval_linT harg (by rw [hf2]; ring))
  · rw [finT, autoFin]
    split_ifs with hs
    · exact eval_tokTerm (.disj (autoX m ac c 0) (autoX m ac c 0))
        (eval_linT harg (by rw [hf1, autoX_eq]; ring))
        (eval_linT harg (by rw [hf2, autoX_eq]; ring))
    · exact eval_tokTerm (.disj (autoK m * c + fnOff m (o - 4 - 2 * (m * m) - 1))
        (autoX m ac c (o - 4 - 2 * (m * m))))
        (eval_linT harg (by rw [hf1]; ring))
        (eval_linT harg (by rw [hf2, autoX_eq]; ring))
  · exact eval_tokTerm (.cst false) (by simp [fld1]) (by simp [fld2])

/-! ### The size of a token -/

theorem autoT_fld_le (o c : ℕ) :
    fld1 (autoT m δ ac o c) + fld2 (autoT m δ ac o c)
      ≤ 2 * (autoK m * c + autoK m) + 2 * c + 1 := by
  have hA : 4 ≤ autoK m := by rw [autoK]; omega
  rcases Nat.lt_or_ge o 4 with hsmall | h4
  · interval_cases o
    · rw [autoT_zero]; simp [fld1, fld2]
    · rw [autoT_one]; simp [fld1, fld2]
    · rw [autoT_two]
      simp only [fld1, fld2]
      omega
    · rw [autoT_three]
      simp only [fld1, fld2]
      omega
  rcases Nat.lt_or_ge o (4 + 2 * (m * m)) with hmid | hfin
  · have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; omega
      · exact h
    obtain ⟨s, t, hs, ht, hcase⟩ := exists_pair_of_offset (m := m) h4 hmid
    have hst : stOff m t < autoK m := stOff_lt_autoK hm ht
    have hcj : cjOff m s t < autoK m := by
      have := cjOff_lt hs ht
      rw [autoK]
      omega
    have hcj0 : cjOff m s 0 < autoK m := by
      have := cjOff_lt hs hm
      rw [autoK]
      omega
    have hac : acOff m s t < autoK m := by
      have := acOff_lt hs ht
      rw [autoK]
      omega
    rcases hcase with rfl | rfl
    · rw [autoT_cj hm hs ht]
      simp only [fld1, fld2]
      have hp : autoPrev m c t ≤ autoK m * c + autoK m := by
        cases c with
        | zero =>
            rw [autoPrev]
            split <;> omega
        | succ i =>
            rw [autoPrev]
            have : autoK m * (i + 1) = autoK m * i + autoK m := by ring
            omega
      have hsel := autoSel_le δ s t
      omega
    · rw [autoT_ac hm hs ht, autoAcc]
      split_ifs with h0
      · simp only [fld1, fld2]
        omega
      · have hac' : acOff m s (t - 1) < autoK m := by
          have := acOff_lt hs (show t - 1 < m by omega)
          rw [autoK]
          omega
        simp only [fld1, fld2]
        omega
  rcases Nat.lt_or_ge o (autoK m) with hlt | hge
  · have hs : o - (4 + 2 * (m * m)) < m := by rw [autoK] at hlt; omega
    have hm : 0 < m := by omega
    have hofn : o = fnOff m (o - (4 + 2 * (m * m))) := by rw [fnOff]; omega
    rw [hofn, autoT_fn hs, autoFin]
    have hX : ∀ s', s' < m → autoX m ac c s' ≤ autoK m * c + autoK m := by
      intro s' hs'
      rw [autoX]
      split
      · have := stOff_lt_autoK hm hs'
        omega
      · omega
    have hfn : ∀ s', s' < m → fnOff m s' < autoK m := fun s' hs' => fnOff_lt hs'
    split_ifs with h0
    · simp only [fld1, fld2]
      have := hX 0 hm
      omega
    · simp only [fld1, fld2]
      have h1 := hX _ hs
      have h2 := hfn (o - (4 + 2 * (m * m)) - 1) (by omega)
      omega
  · rw [autoT, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
    simp [fld1, fld2]

theorem length_encGate_autoT (n o c l : ℕ) (hc : c ≤ l) :
    (encGate (autoT m δ ac o c)).length ≤ (2 * autoK m + 14) * (l + n + 1) := by
  have hfld := autoT_fld_le (m := m) (δ := δ) (ac := ac) o c
  have htag := (tag_le (autoT m δ ac o c)).2
  rw [length_encGate]
  have hstep : (2 * autoK m + 14) * (l + n + 1) ≥ (2 * autoK m + 14) * (l + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hexp : (2 * autoK m + 14) * (l + 1) = 2 * (autoK m * l) + 2 * autoK m + 14 * l + 14 := by
    ring
  have hcl : autoK m * c ≤ autoK m * l := Nat.mul_le_mul_left _ hc
  omega

theorem eval_autoCnt (m : ℕ) (x : Word) :
    (Cob.comp .smash [Cob.proj 0, Cob.constT (List.replicate (autoK m) true)]).eval [x]
      = List.replicate (autoK m * x.length) true := by
  simp [Nat.mul_comm]

end Uniform

end CircCode

/-- **The descriptions of the automaton family are written by a single Cobham term.** -/
theorem codeUniform_autoCirc (m : ℕ) (δ : ℕ → Bool → ℕ) (ac : ℕ → Bool) :
    CodeUniform (CircCode.autoCirc m δ ac) := by
  have h := codeUniform_blockLayer (K₀ := CircCode.autoK m) (K := 2 * CircCode.autoK m + 14)
    CircCode.autoK_pos
    (tmpl := fun _ o c => CircCode.autoT m δ ac o c) (k := fun n => CircCode.autoK m * n)
    (cnt := .comp .smash [Cob.proj 0, Cob.constT (List.replicate (CircCode.autoK m) true)])
    (blkT := CircCode.autoBlk m δ ac)
    (CircCode.eval_autoCnt m) (fun n y o c => CircCode.eval_autoBlk n y o c)
    (fun n o c l hc => CircCode.length_encGate_autoT n o c l hc)
  exact h

/-! ### The language of an automaton -/

/-- The language of the automaton with transition `δ`, initial state `0` and accepting states
`ac`. -/
def AutoLang (δ : ℕ → Bool → ℕ) (ac : ℕ → Bool) : Language :=
  fun x => ac (x.foldl (fun s b => δ s b) 0) = true

namespace CircCode

/-- The run of the automaton on the word presented by the circuit input. -/
theorem runTo_eq_foldl (δ : ℕ → Bool → ℕ) (y : Word) : ∀ n,
    runTo δ y n
      = ((List.range n).map (fun i => y.getD (2 * i + 1) false)).foldl (fun s b => δ s b) 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [runTo, ih, List.range_succ, List.map_append, List.foldl_append]
      simp [abit]

/-- The circuits deciding the language of an automaton: the chain of blocks, with a constant gate
underneath so that the circuit is never empty and the empty word is decided by the initial
state. -/
def autoDec (m : ℕ) (δ : ℕ → Bool → ℕ) (ac : ℕ → Bool) (n : ℕ) : Tseitin.Circuit :=
  Tseitin.stackC (autoCirc m δ ac n) [.cst (ac 0)]

@[simp] theorem length_autoDec (m : ℕ) (δ : ℕ → Bool → ℕ) (ac : ℕ → Bool) (n : ℕ) :
    (autoDec m δ ac n).length = autoK m * n + 1 := by
  simp [autoDec]

theorem autoDec_ne_nil (m : ℕ) (δ : ℕ → Bool → ℕ) (ac : ℕ → Bool) (n : ℕ) :
    autoDec m δ ac n ≠ [] := by
  intro h
  have := length_autoDec m δ ac n
  rw [h] at this
  simp at this

theorem wf_autoDec (m : ℕ) (δ : ℕ → Bool → ℕ) (ac : ℕ → Bool) (n : ℕ) :
    Tseitin.wf (autoDec m δ ac n) :=
  Tseitin.wf_stackC (wf_autoCirc m δ ac n) ⟨trivial, trivial⟩

theorem out_autoDec {m : ℕ} {δ : ℕ → Bool → ℕ} {ac : ℕ → Bool}
    (hm : 0 < m) (hδ : ∀ s b, δ s b < m) (n : ℕ) (y : Word) :
    Tseitin.out y (autoDec m δ ac n) = ac (runTo δ y n) := by
  cases n with
  | zero => rfl
  | succ n =>
      have hne : autoCirc m δ ac (n + 1) ≠ [] := by
        intro h
        have hlen := length_autoCirc m δ ac (n + 1)
        rw [h] at hlen
        have hK : 0 < autoK m := autoK_pos
        simp only [List.length_nil] at hlen
        have : 0 < autoK m * (n + 1) := Nat.mul_pos hK (by omega)
        omega
      rw [autoDec, Tseitin.out_stackC y _ (wf_autoCirc m δ ac (n + 1)) hne,
        out_autoCirc hm hδ n]

end CircCode

/-- **The language of a finite automaton is decided by a P-uniform circuit family.** -/
theorem pUniformDecidable_autoLang {m : ℕ} {δ : ℕ → Bool → ℕ} (ac : ℕ → Bool) (hm : 0 < m)
    (hδ : ∀ s b, δ s b < m) : PUniformDecidable (AutoLang δ ac) := by
  refine ⟨CircCode.autoDec m δ ac, CircCode.autoDec_ne_nil m δ ac, CircCode.wf_autoDec m δ ac,
    fun n y hy => ?_, ?_⟩
  · rw [CircCode.out_autoDec hm hδ n y, CircCode.runTo_eq_foldl, AutoLang,
      Tseitin.inWord_of_pinned n y hy]
  · exact codeUniform_stack (codeUniform_autoCirc m δ ac)
      (codeUniform_const [Tseitin.Gate.cst (ac 0)])

/-- **The language of a finite automaton reduces to SAT in polynomial time**, unconditionally. -/
theorem polyManyOne_SAT_autoLang {m : ℕ} {δ : ℕ → Bool → ℕ} (ac : ℕ → Bool) (hm : 0 < m)
    (hδ : ∀ s b, δ s b < m) : AutoLang δ ac ≤ₘᵖ Sat.SAT :=
  polyManyOne_SAT_of_pUniformDecidable (pUniformDecidable_autoLang ac hm hδ)

end Complexity
