/-
**Binary arithmetic as Cobham terms.**

Natural numbers are written as binary words, least significant bit first (`Complexity.nv`), with
no normalization: leading (high) zeros are allowed.  This module writes addition, comparison and
maximum of such words as Cobham terms.

Each operation is a bounded recursion on notation over a *counter* word whose length is the
number of positions to process.  Because the recursion computes its value on the shorter suffix
of the counter first, it naturally handles the positions from the lowest upwards, which is the
direction in which a carry (for addition) or the comparison of the lower bits (for `≤`) flows.

Main definitions:

* `Complexity.nv` — the value of a binary word;
* `Complexity.addW`, `Complexity.leW`, `Complexity.maxW` — addition, comparison and maximum of
  binary words;
* `Complexity.Cob.addT`, `Complexity.Cob.leT`, `Complexity.Cob.maxT` — the Cobham terms;
* `Complexity.Cob.nzT` — whether a word has a nonzero value.

Main results:

* `Complexity.nv_addW`, `Complexity.leW_iff`, `Complexity.nv_maxW` — correctness;
* `Complexity.length_addW`, `Complexity.length_maxW_le` — lengths;
* `Complexity.Cob.eval_addT`, `Complexity.Cob.eval_leT`, `Complexity.Cob.eval_maxT` — the terms
  compute the operations.
-/

import Start.ShamirCob

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Values of binary words -/

/-- The value of a binary word, least significant bit first. -/
def nv : Word → ℕ
  | [] => 0
  | b :: w => b.toNat + 2 * nv w

@[simp] theorem nv_nil : nv [] = 0 := rfl

@[simp] theorem nv_cons (b : Bool) (w : Word) : nv (b :: w) = b.toNat + 2 * nv w := rfl

theorem nv_append (u v : Word) : nv (u ++ v) = nv u + 2 ^ u.length * nv v := by
  induction u with
  | nil => simp
  | cons b u ih => simp [ih, pow_succ]; ring

theorem nv_lt (w : Word) : nv w < 2 ^ w.length := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp [pow_succ] <;> omega

theorem nv_take_succ (a : Word) (j : ℕ) :
    nv (a.take (j + 1)) = nv (a.take j) + 2 ^ j * (a.getD j false).toNat := by
  induction a generalizing j with
  | nil => simp
  | cons b a ih =>
      cases j with
      | zero => simp
      | succ j =>
          rw [List.take_succ_cons, List.take_succ_cons, nv_cons, nv_cons, ih]
          simp [pow_succ]; ring

theorem nv_take_of_le (a : Word) {j : ℕ} (h : a.length ≤ j) : nv (a.take j) = nv a := by
  rw [List.take_of_length_le h]

@[simp] theorem nv_bw (b : Bool) : nv (bw b) = b.toNat := by cases b <;> rfl

/-- `nv w` is nonzero iff `w` contains a `true`. -/
theorem nv_pos_iff (w : Word) : 0 < nv w ↔ true ∈ w := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp [ih]

/-! ### Addition -/

/-- The recursion behind addition: `addRec a b j = c :: S`, where `S` lists the bits `j - 1, …, 0`
of the sum of the lowest `j` bits of `a` and `b` (highest first) and `c` is the carry out. -/
def addRec (a b : Word) : ℕ → Word
  | 0 => [false]
  | j + 1 =>
      let r := addRec a b j
      let x := a.getD j false
      let y := b.getD j false
      let c := r.headD false
      (x && y || x && c || y && c) :: (Bool.xor (Bool.xor x y) c) :: r.tail

theorem length_addRec (a b : Word) : ∀ j, (addRec a b j).length = j + 1
  | 0 => rfl
  | j + 1 => by
      simp only [addRec, List.length_cons, List.length_tail, length_addRec a b j]
      omega

theorem addRec_ne_nil (a b : Word) (j : ℕ) : addRec a b j ≠ [] := by
  intro h; have := length_addRec a b j; rw [h] at this; simp at this

theorem nv_addRec (a b : Word) : ∀ j,
    nv (addRec a b j).reverse = nv (a.take j) + nv (b.take j)
  | 0 => by simp [addRec]
  | j + 1 => by
      have ih := nv_addRec a b j
      obtain ⟨c, S, hcs⟩ : ∃ c S, addRec a b j = c :: S := by
        cases h : addRec a b j with
        | nil => exact absurd h (addRec_ne_nil a b j)
        | cons c S => exact ⟨c, S, rfl⟩
      have hS : S.length = j := by
        have := length_addRec a b j; rw [hcs] at this; simpa using this
      rw [hcs] at ih
      simp only [List.reverse_cons, nv_append, List.length_reverse, hS, nv_cons, nv_nil] at ih
      simp only [addRec, hcs, List.headD_cons, List.tail_cons, List.reverse_cons, nv_append,
        List.length_append, List.length_reverse, hS, List.length_singleton, nv_cons, nv_nil,
        nv_take_succ]
      generalize a.getD j false = x at *
      generalize b.getD j false = y at *
      have key : (Bool.xor (Bool.xor x y) c).toNat + 2 * (x && y || x && c || y && c).toNat
          = x.toNat + y.toNat + c.toNat := by
        cases x <;> cases y <;> cases c <;> rfl
      have h3 : 2 ^ j * (Bool.xor (Bool.xor x y) c).toNat
          + 2 ^ j * 2 * (x && y || x && c || y && c).toNat
          = 2 ^ j * x.toNat + 2 ^ j * y.toNat + 2 ^ j * c.toNat := by
        rw [mul_assoc, ← mul_add, key]; ring
      rw [pow_succ]
      simp only [mul_zero, add_zero] at ih ⊢
      linarith [h3, ih]

/-- **Binary addition.** -/
def addW (a b : Word) : Word := (addRec a b (max a.length b.length)).reverse

theorem nv_addW (a b : Word) : nv (addW a b) = nv a + nv b := by
  rw [addW, nv_addRec, nv_take_of_le _ (le_max_left _ _), nv_take_of_le _ (le_max_right _ _)]

theorem length_addW (a b : Word) : (addW a b).length = max a.length b.length + 1 := by
  rw [addW, List.length_reverse, length_addRec]

/-! ### Comparison and maximum -/

/-- The recursion behind comparison: whether the lowest `j` bits of `a` give a value at most that
of the lowest `j` bits of `b`. -/
def leRec (a b : Word) : ℕ → Bool
  | 0 => true
  | j + 1 => if a.getD j false = b.getD j false then leRec a b j else b.getD j false

theorem leRec_iff (a b : Word) : ∀ j, leRec a b j = decide (nv (a.take j) ≤ nv (b.take j))
  | 0 => by simp [leRec]
  | j + 1 => by
      have ih := leRec_iff a b j
      have ha := nv_lt (a.take j)
      have hb := nv_lt (b.take j)
      have hla : (a.take j).length ≤ j := by simp
      have hlb : (b.take j).length ≤ j := by simp
      have hpa : 2 ^ (a.take j).length ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hla
      have hpb : 2 ^ (b.take j).length ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hlb
      simp only [leRec, nv_take_succ]
      generalize a.getD j false = x
      generalize b.getD j false = y
      generalize nv (a.take j) = A at *
      generalize nv (b.take j) = B at *
      have h2 : 0 < 2 ^ j := by positivity
      cases x <;> cases y <;> simp [ih] <;> omega

/-- **Comparison of binary words.** -/
def leW (a b : Word) : Bool := leRec a b (max a.length b.length)

theorem leW_iff (a b : Word) : leW a b = decide (nv a ≤ nv b) := by
  rw [leW, leRec_iff, nv_take_of_le _ (le_max_left _ _), nv_take_of_le _ (le_max_right _ _)]

/-- **Maximum of binary words.** -/
def maxW (a b : Word) : Word := if leW a b then b else a

theorem nv_maxW (a b : Word) : nv (maxW a b) = max (nv a) (nv b) := by
  rw [maxW, leW_iff]
  by_cases h : nv a ≤ nv b
  · simp [h]
  · simp [h]; omega

theorem length_maxW_le (a b : Word) : (maxW a b).length ≤ max a.length b.length := by
  rw [maxW]; split <;> omega

/-! ### Cobham terms -/

/-- Selection among eight terms by three Boolean-valued (empty / nonempty) conditions. -/
def Cob.case3 (cx cy cc : Cob) (f : Bool → Bool → Bool → Cob) : Cob :=
  Cob.iteT cx
    (Cob.iteT cy (Cob.iteT cc (f true true true) (f true true false))
      (Cob.iteT cc (f true false true) (f true false false)))
    (Cob.iteT cy (Cob.iteT cc (f false true true) (f false true false))
      (Cob.iteT cc (f false false true) (f false false false)))

theorem Cob.eval_case3 (cx cy cc : Cob) (f : Bool → Bool → Bool → Cob) (args : List Word)
    (x y c : Bool) (hx : cx.eval args = bw x) (hy : cy.eval args = bw y)
    (hc : cc.eval args = bw c) :
    (Cob.case3 cx cy cc f).eval args = (f x y c).eval args := by
  cases x <;> cases y <;> cases c <;> simp [Cob.case3, Cob.eval_iteT_word, hx, hy, hc, bw]

/-- The bit at position `|z|` of `a`, where `z` is argument `0` and `a` argument `i`. -/
def Cob.bitAtLen (i : ℕ) : Cob := Cob.nthBit 0 (Cob.dropBy (.proj 0) (.proj i))

theorem Cob.eval_bitAtLen (i : ℕ) (args : List Word) :
    (Cob.bitAtLen i).eval args = bw ((args.getD i []).getD (args.getD 0 []).length false) := by
  simp only [Cob.bitAtLen, Cob.eval_nthBit, Cob.eval_dropBy, Cob.eval_proj]
  congr 1
  simp [List.getD_eq_getElem?_getD]

/-- The step of the addition recursion, on `[z, ih, a, b]`. -/
def Cob.addStep : Cob :=
  Cob.case3 (Cob.bitAtLen 2) (Cob.bitAtLen 3) (Cob.nthBit 0 (.proj 1))
    (fun x y c => Cob.pre [x && y || x && c || y && c, Bool.xor (Bool.xor x y) c]
      (Cob.tailN 1 (.proj 1)))

/-- The addition recursion over a counter, on `[z, a, b]`. -/
def Cob.addCore : Cob :=
  .bRec (Cob.constT [false]) Cob.addStep Cob.addStep (.comp (.app true) [.proj 0])

theorem Cob.eval_addCore (a b : Word) : ∀ z : Word,
    Cob.addCore.eval [z, a, b] = addRec a b z.length
  | [] => by simp [Cob.addCore, addRec]
  | bit :: z => by
      have ih := Cob.eval_addCore a b z
      have hstep : Cob.addStep.eval [z, addRec a b z.length, a, b] = addRec a b (z.length + 1) := by
        rw [Cob.addStep, Cob.eval_case3 _ _ _ _ _ (a.getD z.length false) (b.getD z.length false)
          ((addRec a b z.length).headD false)]
        · simp [addRec, Cob.eval_tailN]
        · simp [Cob.eval_bitAtLen]
        · simp [Cob.eval_bitAtLen]
        · rw [Cob.eval_nthBit]
          simp [List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_eq_getElem?]
      rw [Cob.addCore, Cob.eval_bRec_cons, ← Cob.addCore, ih]
      have hlen : (addRec a b (z.length + 1)).length ≤ z.length + 1 + 1 := by
        rw [length_addRec]
      cases bit <;> simp only [hstep, Bool.false_eq_true, ite_false, ite_true] <;>
        simp [List.take_of_length_le, length_addRec]

/-- The word `1^{max(|a|, |b|)}` for the values of two terms. -/
def Cob.maxOnes (ta tb : Cob) : Cob := Cob.iteT (Cob.leU ta tb) (Cob.onesOf tb) (Cob.onesOf ta)

theorem Cob.eval_maxOnes (ta tb : Cob) (args : List Word) :
    (Cob.maxOnes ta tb).eval args =
      List.replicate (max (ta.eval args).length (tb.eval args).length) true := by
  rw [Cob.maxOnes, Cob.eval_iteT_word, Cob.eval_leU]
  by_cases h : (ta.eval args).length ≤ (tb.eval args).length
  · simp [h, bw]
  · simp [h, bw, max_eq_left (le_of_lt (not_le.1 h))]

/-- **Addition as a Cobham term.** -/
def Cob.addT (ta tb : Cob) : Cob :=
  .comp Cob.revTerm [.comp Cob.addCore [Cob.maxOnes ta tb, ta, tb]]

@[simp] theorem Cob.eval_addT (ta tb : Cob) (args : List Word) :
    (Cob.addT ta tb).eval args = addW (ta.eval args) (tb.eval args) := by
  simp only [Cob.addT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_revTerm,
    Cob.eval_addCore, Cob.eval_maxOnes, List.length_replicate, addW]

/-- The step of the comparison recursion, on `[z, ih, a, b]`. -/
def Cob.leStep : Cob :=
  Cob.case3 (Cob.bitAtLen 2) (Cob.bitAtLen 3) (.proj 1)
    (fun x y c => Cob.constT (bw (if x = y then c else y)))

/-- The comparison recursion over a counter, on `[z, a, b]`. -/
def Cob.leCore : Cob := .bRec (Cob.constT [true]) Cob.leStep Cob.leStep Cob.trueC

theorem Cob.eval_leCore (a b : Word) : ∀ z : Word,
    Cob.leCore.eval [z, a, b] = bw (leRec a b z.length)
  | [] => by simp [Cob.leCore, leRec, bw]
  | bit :: z => by
      have ih := Cob.eval_leCore a b z
      have hstep : Cob.leStep.eval [z, bw (leRec a b z.length), a, b] =
          bw (leRec a b (z.length + 1)) := by
        rw [Cob.leStep, Cob.eval_case3 _ _ _ _ _ (a.getD z.length false) (b.getD z.length false)
          (leRec a b z.length)]
        · simp [leRec]
        · simp [Cob.eval_bitAtLen]
        · simp [Cob.eval_bitAtLen]
        · simp
      rw [Cob.leCore, Cob.eval_bRec_cons, ← Cob.leCore, ih]
      have hlen : (bw (leRec a b (z.length + 1))).length ≤ 1 := by
        cases leRec a b (z.length + 1) <;> simp [bw]
      cases bit <;> simp only [hstep, Bool.false_eq_true, ite_false, ite_true] <;>
        simp [List.take_of_length_le hlen]

/-- **Comparison as a Cobham term.** -/
def Cob.leT (ta tb : Cob) : Cob := .comp Cob.leCore [Cob.maxOnes ta tb, ta, tb]

@[simp] theorem Cob.eval_leT (ta tb : Cob) (args : List Word) :
    (Cob.leT ta tb).eval args = bw (leW (ta.eval args) (tb.eval args)) := by
  simp only [Cob.leT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_leCore,
    Cob.eval_maxOnes, List.length_replicate, leW]

/-- **Maximum as a Cobham term.** -/
def Cob.maxT (ta tb : Cob) : Cob := Cob.iteT (Cob.leT ta tb) tb ta

@[simp] theorem Cob.eval_maxT (ta tb : Cob) (args : List Word) :
    (Cob.maxT ta tb).eval args = maxW (ta.eval args) (tb.eval args) := by
  rw [Cob.maxT, Cob.eval_iteT_word, Cob.eval_leT, maxW]
  cases leW (ta.eval args) (tb.eval args) <;> simp [bw]

/-! ### Nonzero test -/

/-- Whether a word contains a `true`. -/
def Cob.nzCore : Cob :=
  .bRec .empty (.proj 1) Cob.trueC Cob.trueC

theorem Cob.eval_nzCore : ∀ w : Word, Cob.nzCore.eval [w] = bw (decide (true ∈ w))
  | [] => by simp [Cob.nzCore, bw]
  | b :: w => by
      have ih := Cob.eval_nzCore w
      rw [Cob.nzCore, Cob.eval_bRec_cons, ← Cob.nzCore, ih]
      have hlen : (bw (decide (true ∈ w))).length ≤ 1 := by
        cases decide (true ∈ w) <;> simp [bw]
      cases b
      · simp only [Bool.false_eq_true, ite_false, Cob.eval_proj]
        rw [List.take_of_length_le (by simpa using hlen)]
        simp
      · simp [bw]

/-- The test `2 ^ |c| ≤ 2 · nv w` for the values `w` of `tw` and `c` of `tc`. -/
def Cob.thrT (tw tc : Cob) : Cob :=
  .comp Cob.nzCore [Cob.dropBy (Cob.tailN 1 tc) tw]

/-- `2 ^ C ≤ 2 · nv w` iff some bit of `w` at a position `≥ C - 1` is set. -/
theorem two_pow_le_two_mul_nv_iff (w : Word) (C : ℕ) :
    2 ^ C ≤ 2 * nv w ↔ true ∈ w.drop (C - 1) := by
  rw [← nv_pos_iff]
  have hsplit := nv_append (w.take (C - 1)) (w.drop (C - 1))
  rw [List.take_append_drop] at hsplit
  have hlt := nv_lt (w.take (C - 1))
  have hlen : (w.take (C - 1)).length ≤ C - 1 := by simp
  rcases Nat.eq_zero_or_pos C with hC | hC
  · subst hC; simp at hsplit ⊢; omega
  · obtain ⟨k, rfl⟩ : ∃ k, C = k + 1 := ⟨C - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hsplit hlen hlt ⊢
    rcases Nat.lt_or_ge (w.take k).length k with hl | hl
    · -- `w` is shorter than `k`: the high part is empty and `nv w < 2 ^ k`
      have hw : w.length < k := by
        rw [List.length_take] at hl; omega
      have hd : w.drop k = [] := List.drop_eq_nil_of_le (by omega)
      have hnv := nv_lt w
      have : 2 ^ w.length < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hw
      rw [hd]; simp [pow_succ]; omega
    · have hle : (w.take k).length = k := le_antisymm hlen hl
      rw [hle] at hsplit hlt
      constructor
      · intro h
        by_contra h0
        push Not at h0
        have : nv (w.drop k) = 0 := by omega
        rw [this] at hsplit; simp [pow_succ] at h; omega
      · intro h
        have : 2 ^ k ≤ 2 ^ k * nv (w.drop k) := Nat.le_mul_of_pos_right _ h
        rw [pow_succ]; omega

theorem Cob.eval_thrT (tw tc : Cob) (args : List Word) :
    (Cob.thrT tw tc).eval args =
      bw (decide (2 ^ (tc.eval args).length ≤ 2 * nv (tw.eval args))) := by
  simp only [Cob.thrT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_dropBy,
    Cob.eval_tailN, List.length_drop, Cob.eval_nzCore]
  congr 2
  exact propext (two_pow_le_two_mul_nv_iff _ _).symm

/-! ### Word equality -/

theorem nv_inj : ∀ {u v : Word}, u.length = v.length → nv u = nv v → u = v
  | [], [], _, _ => rfl
  | b :: u, c :: v, hl, hv => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [nv_cons] at hv
      have hbc : b = c := by cases b <;> cases c <;> simp at hv ⊢ <;> omega
      subst hbc
      rw [nv_inj hl (by omega)]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- **Equality of words as a Cobham term.** -/
def Cob.eqW (ta tb : Cob) : Cob := Cob.andT (Cob.eqU ta tb) (Cob.andT (Cob.leT ta tb) (Cob.leT tb ta))

@[simp] theorem Cob.eval_eqW (ta tb : Cob) (args : List Word) :
    (Cob.eqW ta tb).eval args = bw (decide (ta.eval args = tb.eval args)) := by
  rw [Cob.eqW, Cob.eval_andT (Cob.eval_eqU ta tb args)
    (Cob.eval_andT (Cob.eval_leT ta tb args) (Cob.eval_leT tb ta args))]
  congr 1
  simp only [leW_iff]
  by_cases h : ta.eval args = tb.eval args
  · simp [h]
  · have : ¬ ((ta.eval args).length = (tb.eval args).length ∧
        nv (ta.eval args) ≤ nv (tb.eval args) ∧ nv (tb.eval args) ≤ nv (ta.eval args)) :=
      fun ⟨h1, h2, h3⟩ => h (nv_inj h1 (le_antisymm h2 h3))
    simp only [h, decide_false]
    simpa using this

end Complexity
