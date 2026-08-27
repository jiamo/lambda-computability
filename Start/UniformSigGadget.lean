/-
# The gadgets a loop is built from

`Start/UniformSigWire.lean` compiles a description of three wires into a P-uniform family of
circuits realizing the selector `Complexity.Tseitin.selBit` of their values.  This module writes
down the descriptions of the five gadgets a bounded recursion needs, and proves that each of them
means what it should:

* the tail of a word, and the word obtained by putting the head of one word in front of another —
  the two halves of *moving one bit* from a word being consumed to a word being built;
* the head bit of a word, presented as a word, and the multiplexer choosing between two words
  according to whether a third is empty — the two halves of a *test*;
* the truncation of a word to the length of another — the *bound* of a bounded recursion.

Every one of them is a single selector layer over wires of the argument signals, so each costs a
constant number of gates per output wire.

Main definitions:

* `Complexity.consHeadW`, `Complexity.headBitW`, `Complexity.muxW` — the word functions.

Main results:

* `Complexity.sigUniform_tail`, `Complexity.sigUniform_consHead`,
  `Complexity.sigUniform_headBit`, `Complexity.sigUniform_mux`,
  `Complexity.sigUniform_takeLen` — **each gadget is realized**.
-/

import Start.UniformSigWire

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Complexity.Tseitin

/-! ### The word functions -/

/-- The head of `a` put in front of `b`, or `b` itself if `a` is empty. -/
def consHeadW (a b : Word) : Word :=
  match a with
  | [] => b
  | c :: _ => c :: b

/-- The head bit of `a`, as a word: `[true]` if `a` starts with `true`, and `[]` otherwise. -/
def headBitW (a : Word) : Word := if a.headD false then [true] else []

/-- The multiplexer: `u` if the guard `g` is nonempty, and `v` otherwise. -/
def muxW (g u v : Word) : Word := if g = [] then v else u

/-! ### Reading a wire -/

theorem gateVal_inp_arg {m : ℕ} {args : List Word} {i p k : ℕ} (hi : i < args.length)
    (hp : p < 2 * m) (hk : k = i * (2 * m) + p) :
    gateVal (encArgs m args) [] (Gate.inp k)
      = (encSig m (args.getD i [])).getD p false := by
  subst hk
  exact getD_encArgs m args hi hp

theorem selBit_true_false (a : Bool) : selBit a true false = a := by cases a <;> rfl

theorem selBit_and (a b : Bool) : selBit a b false = (a && b) := by cases a <;> cases b <;> rfl

theorem consHeadW_eq (a b : Word) : consHeadW a b = if a = [] then b else a.getD 0 false :: b := by
  cases a <;> simp [consHeadW]

theorem headBitW_eq (a : Word) : headBitW a = if a.getD 0 false then [true] else [] := by
  cases a <;> simp [headBitW]

theorem getD_encSig_headBitW {mm j : ℕ} (a : Word) (hj : j < 2 * mm) :
    (encSig mm (headBitW a)).getD j false
      = if j = 0 ∨ j = mm then a.getD 0 false else false := by
  have hmm : 0 < mm := by omega
  have hlen : (headBitW a).length = if a.getD 0 false then 1 else 0 := by
    rw [headBitW_eq]
    cases a.getD 0 false <;> simp
  have hget : ∀ p, (headBitW a).getD p false = if p = 0 then a.getD 0 false else false := by
    intro p
    rw [headBitW_eq]
    cases hb : a.getD 0 false <;> cases p <;> simp
  rcases lt_or_ge j mm with h | h
  · rw [getD_encSig_lt _ h, hlen]
    by_cases hj0 : j = 0
    · rw [if_pos (Or.inl hj0), hj0]
      cases a.getD 0 false <;> simp
    · rw [if_neg (show ¬ (j = 0 ∨ j = mm) by omega)]
      have hle1 : (if a.getD 0 false then 1 else 0 : ℕ) ≤ 1 := by split <;> omega
      simp only [decide_eq_false_iff_not, Nat.not_lt]
      omega
  · rw [getD_encSig_ge _ h hj, hget]
    by_cases hjm : j = mm
    · rw [if_pos (Or.inr hjm), hjm, Nat.sub_self, if_pos rfl]
    · rw [if_neg (by omega), if_neg (by omega)]

theorem and_getD_zero (a : Word) :
    (decide (0 < a.length) && a.getD 0 false) = a.getD 0 false := by
  cases a <;> simp

theorem getD_take (u : Word) (k p : ℕ) :
    (u.take k).getD p false = if p < k then u.getD p false else false := by
  by_cases h : p < k
  · rw [if_pos h]
    rcases lt_or_ge p u.length with h2 | h2
    · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h2]
      simp [List.getElem_take]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ h2]
  · rw [if_neg h, List.getD_eq_default _ _ (by simp; omega)]

theorem getD_tail (u : Word) (p : ℕ) : u.tail.getD p false = u.getD (p + 1) false := by
  cases u with
  | nil => simp
  | cons b u => simp

/-! ### The tail -/

/-- The wire of the tail of a word: the wire above it, except at the top of each block. -/
def tailA : GateE :=
  .iteE (.ne (.add .col (.lit 1)) .half)
    (.iteE (.ne (.add .col (.lit 1)) .width) (.inpE (.add .col (.lit 1))) (.cstE false))
    (.cstE false)

theorem gate_tailA (j mm M : ℕ) :
    tailA.gate j mm M
      = if j + 1 = mm then Gate.cst false
        else if j + 1 = M then Gate.cst false else Gate.inp (j + 1) := by
  simp only [tailA, GateE.gate, CondE.holds, IdxE.val, ne_eq]
  by_cases h0 : j + 1 = mm
  · simp [h0]
  · by_cases h1 : j + 1 = M <;> simp [h0, h1]

theorem bnd_tailA (j mm M : ℕ) :
    tailA.bnd j mm M = if j + 1 = mm then 0 else if j + 1 = M then 0 else j + 1 := by
  simp only [tailA, GateE.bnd, CondE.holds, IdxE.val, ne_eq]
  by_cases h0 : j + 1 = mm
  · simp [h0]
  · by_cases h1 : j + 1 = M <;> simp [h0, h1]

/-- **The tail of a word is realized.** -/
theorem sigUniform_tail {r : ℕ} {m : ℕ → ℕ} {mT : Cob} (hr : 0 < r)
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigUniform r m (fun args => (args.getD 0 []).tail) := by
  refine sigUniform_of_selLayerE (K := 8) (ea := tailA) (eb := .cstE true) (ec := .cstE false)
    hm ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro n j hj
    have h1 : 1 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
    rw [bnd_tailA]
    split_ifs <;> omega
  · intro n j hj
    have h1 : 1 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
    simp only [GateE.bnd]
    omega
  · intro n j hj
    have h1 : 1 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
    simp only [GateE.bnd]
    omega
  · intro n j
    rw [bnd_tailA]
    split_ifs <;> omega
  · intro n j
    simp only [GateE.bnd]
    omega
  · intro n j
    simp only [GateE.bnd]
    omega
  · intro n args hlen hle
    have hmem : args.getD 0 [] ∈ args := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    set u : Word := args.getD 0 [] with hu
    have hul : u.length ≤ m n := by rw [hu]; exact hle _ hmem
    have h0 : (0 : ℕ) < args.length := by omega
    refine List.ext_getElem (by simp) ?_
    intro j h1 h2
    have hj : j < 2 * m n := by simpa using h1
    have hrhs : (encSig (m n) u.tail)[j] = (encSig (m n) u.tail).getD j false :=
      (List.getD_eq_getElem _ _ (by simpa using h2)).symm
    simp only [List.getElem_map, List.getElem_range, hrhs]
    rw [show gateVal (encArgs (m n) args) [] ((GateE.cstE true).gate j (m n) (2 * m n)) = true from
      rfl, show gateVal (encArgs (m n) args) [] ((GateE.cstE false).gate j (m n) (2 * m n))
      = false from rfl, selBit_true_false, gate_tailA]
    rcases lt_or_ge j (m n) with hjm | hjm
    · -- a presence wire
      rw [getD_encSig_lt _ hjm]
      by_cases h3 : j + 1 = m n
      · rw [if_pos h3]
        have hnt : ¬ (j < u.tail.length) := by
          simp only [List.length_tail]
          omega
        simp only [gateVal]
        exact (decide_eq_false hnt).symm
      · rw [if_neg h3, if_neg (by omega)]
        rw [gateVal_inp_arg (i := 0) (p := j + 1) h0 (by omega) (by omega),
          getD_encSig_lt _ (by omega), ← hu]
        simp only [List.length_tail, decide_eq_decide]
        omega
    · -- a value wire
      rw [getD_encSig_ge _ hjm hj, getD_tail]
      by_cases h3 : j + 1 = 2 * m n
      · rw [if_neg (by omega), if_pos h3]
        have : u.getD (j - m n + 1) false = false := by
          rw [List.getD_eq_default]
          omega
        simp only [gateVal]
        exact this.symm
      · rw [if_neg (by omega), if_neg h3]
        rw [gateVal_inp_arg (i := 0) (p := j + 1) h0 (by omega) (by omega),
          getD_encSig_ge _ (by omega) (by omega), ← hu]
        congr 1
        omega

/-! ### Putting the head of a word in front of another -/

/-- The first wire of `consHeadW a b`: the presence bit of the head of `a`. -/
def consHeadA : GateE := .inpE (.lit 0)

/-- The wire of `consHeadW a b` when `a` is nonempty: the signal of `b` shifted by one place,
with the head bit of `a` written at the bottom of the value block. -/
def consHeadB : GateE :=
  .iteE (.ne .col (.lit 0))
    (.iteE (.ne .col .half) (.inpE (.sub (.add .width .col) (.lit 1))) (.inpE .half))
    (.cstE true)

/-- The wire of `consHeadW a b` when `a` is empty: the signal of `b`. -/
def consHeadC : GateE := .inpE (.add .width .col)

theorem gate_consHeadB (j mm M : ℕ) :
    consHeadB.gate j mm M
      = if j = 0 then Gate.cst true
        else if j = mm then Gate.inp mm else Gate.inp (M + j - 1) := by
  simp only [consHeadB, GateE.gate, CondE.holds, IdxE.val, ne_eq]
  by_cases h0 : j = 0
  · simp [h0]
  · by_cases h1 : j = mm <;> simp [h0, h1]

theorem bnd_consHeadB (j mm M : ℕ) :
    consHeadB.bnd j mm M = if j = 0 then 0 else if j = mm then mm else M + j - 1 := by
  simp only [consHeadB, GateE.bnd, CondE.holds, IdxE.val, ne_eq]
  by_cases h0 : j = 0
  · simp [h0]
  · by_cases h1 : j = mm <;> simp [h0, h1]

/-- **Putting the head of a word in front of another is realized.** -/
theorem sigUniform_consHead {r : ℕ} {m : ℕ → ℕ} {mT : Cob} (hr : 2 ≤ r)
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigUniform r m (fun args => consHeadW (args.getD 0 []) (args.getD 1 [])) := by
  refine sigUniform_of_selLayerE (K := 8) (ea := consHeadA) (eb := consHeadB) (ec := consHeadC)
    hm ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro n j hj
    have h1 : 2 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
    simp only [consHeadA, GateE.bnd, IdxE.val]
    omega
  · intro n j hj
    have h1 : 2 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
    rw [bnd_consHeadB]
    split_ifs <;> omega
  · intro n j hj
    have h1 : 2 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
    simp only [consHeadC, GateE.bnd, IdxE.val]
    omega
  · intro n j
    simp only [consHeadA, GateE.bnd, IdxE.val]
    omega
  · intro n j
    rw [bnd_consHeadB]
    split_ifs <;> omega
  · intro n j
    simp only [consHeadC, GateE.bnd, IdxE.val]
    omega
  · intro n args hlen hle
    have h0 : (0 : ℕ) < args.length := by omega
    have h1' : (1 : ℕ) < args.length := by omega
    refine List.ext_getElem (by simp) ?_
    intro j hj1 hj2
    have hj : j < 2 * m n := by simpa using hj1
    have hmm : 0 < m n := by omega
    have hrhs : (encSig (m n) (consHeadW (args.getD 0 []) (args.getD 1 [])))[j]
        = (encSig (m n) (consHeadW (args.getD 0 []) (args.getD 1 []))).getD j false :=
      (List.getD_eq_getElem _ _ (by simpa using hj2)).symm
    simp only [List.getElem_map, List.getElem_range, hrhs]
    have hA : gateVal (encArgs (m n) args) [] (consHeadA.gate j (m n) (2 * m n))
        = decide (0 < (args.getD 0 []).length) := by
      rw [show consHeadA.gate j (m n) (2 * m n) = Gate.inp 0 from rfl,
        gateVal_inp_arg (i := 0) (p := 0) h0 (by omega) (by omega), getD_encSig_lt _ hmm]
    have hC : gateVal (encArgs (m n) args) [] (consHeadC.gate j (m n) (2 * m n))
        = (encSig (m n) (args.getD 1 [])).getD j false := by
      rw [show consHeadC.gate j (m n) (2 * m n) = Gate.inp (2 * m n + j) from rfl,
        gateVal_inp_arg (i := 1) (p := j) h1' hj (by ring)]
    rw [hA, hC, gate_consHeadB, consHeadW_eq]
    by_cases hg : args.getD 0 [] = []
    · rw [if_pos hg, hg]
      simp
    · have hpos : 0 < (args.getD 0 []).length := by
        rcases hh : args.getD 0 [] with _ | ⟨c, t⟩
        · exact absurd hh hg
        · simp
      rw [if_neg hg, decide_eq_true hpos, selBit_true]
      by_cases hj0 : j = 0
      · rw [if_pos hj0, hj0, getD_encSig_lt _ hmm]
        simp [gateVal]
      · rw [if_neg hj0]
        by_cases hjm : j = m n
        · rw [if_pos hjm, gateVal_inp_arg (i := 0) (p := m n) h0 (by omega) (by omega),
            getD_encSig_ge _ (le_refl _) (by omega), getD_encSig_ge _ (by omega) (by omega)]
          simp [hjm]
        · rw [if_neg hjm, gateVal_inp_arg (i := 1) (p := j - 1) h1' (by omega) (by omega)]
          rcases lt_or_ge j (m n) with hlt | hge
          · rw [getD_encSig_lt _ (by omega), getD_encSig_lt _ hlt]
            simp only [List.length_cons, decide_eq_decide]
            omega
          · rw [getD_encSig_ge _ (by omega) (by omega), getD_encSig_ge _ hge hj,
              show j - m n = (j - m n - 1) + 1 by omega, List.getD_cons_succ]
            congr 1
            omega

/-! ### The head bit -/

/-- The wire of `headBitW a` when `a` is nonempty: the head bit of `a` at the bottom of each
block. -/
def headBitB : GateE :=
  .iteE (.ne .col (.lit 0)) (.iteE (.ne .col .half) (.cstE false) (.inpE .half)) (.inpE .half)

theorem gate_headBitB (j mm M : ℕ) :
    headBitB.gate j mm M = if j = 0 ∨ j = mm then Gate.inp mm else Gate.cst false := by
  simp only [headBitB, GateE.gate, CondE.holds, IdxE.val, ne_eq]
  by_cases h0 : j = 0
  · simp [h0]
  · by_cases h1 : j = mm <;> simp [h0, h1]

theorem bnd_headBitB (j mm M : ℕ) :
    headBitB.bnd j mm M = if j = 0 ∨ j = mm then mm else 0 := by
  simp only [headBitB, GateE.bnd, CondE.holds, IdxE.val, ne_eq]
  by_cases h0 : j = 0
  · simp [h0]
  · by_cases h1 : j = mm <;> simp [h0, h1]

/-- **The head bit of a word is realized.** -/
theorem sigUniform_headBit {r : ℕ} {m : ℕ → ℕ} {mT : Cob} (hr : 0 < r)
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigUniform r m (fun args => headBitW (args.getD 0 [])) := by
  refine sigUniform_of_selLayerE (K := 8) (ea := consHeadA) (eb := headBitB) (ec := .cstE false)
    hm ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro n j hj
    have h1 : 1 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
    simp only [consHeadA, GateE.bnd, IdxE.val]
    omega
  · intro n j hj
    have h1 : 1 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
    rw [bnd_headBitB]
    split_ifs <;> omega
  · intro n j hj
    have h1 : 1 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
    simp only [GateE.bnd]
    omega
  · intro n j
    simp only [consHeadA, GateE.bnd, IdxE.val]
    omega
  · intro n j
    rw [bnd_headBitB]
    split_ifs <;> omega
  · intro n j
    simp only [GateE.bnd]
    omega
  · intro n args hlen hle
    have h0 : (0 : ℕ) < args.length := by omega
    refine List.ext_getElem (by simp) ?_
    intro j hj1 hj2
    have hj : j < 2 * m n := by simpa using hj1
    have hmm : 0 < m n := by omega
    have hrhs : (encSig (m n) (headBitW (args.getD 0 [])))[j]
        = (encSig (m n) (headBitW (args.getD 0 []))).getD j false :=
      (List.getD_eq_getElem _ _ (by simpa using hj2)).symm
    simp only [List.getElem_map, List.getElem_range, hrhs]
    have hA : gateVal (encArgs (m n) args) [] (consHeadA.gate j (m n) (2 * m n))
        = decide (0 < (args.getD 0 []).length) := by
      rw [show consHeadA.gate j (m n) (2 * m n) = Gate.inp 0 from rfl,
        gateVal_inp_arg (i := 0) (p := 0) h0 (by omega) (by omega), getD_encSig_lt _ hmm]
    have hBv : gateVal (encArgs (m n) args) [] (Gate.inp (m n))
        = (args.getD 0 []).getD 0 false := by
      rw [gateVal_inp_arg (i := 0) (p := m n) h0 (by omega) (by omega),
        getD_encSig_ge _ (le_refl _) (by omega)]
      simp
    rw [hA, gate_headBitB,
      show gateVal (encArgs (m n) args) [] ((GateE.cstE false).gate j (m n) (2 * m n)) = false
        from rfl]
    rw [getD_encSig_headBitW _ hj]
    by_cases hjc : j = 0 ∨ j = m n
    · rw [if_pos hjc, if_pos hjc, hBv, selBit_and, and_getD_zero]
    · rw [if_neg hjc, if_neg hjc,
        show gateVal (encArgs (m n) args) [] (Gate.cst false) = false from rfl, selBit_and,
        Bool.and_false]

/-! ### The multiplexer -/

/-- The wire of `muxW g u v` when the guard is nonempty: the signal of `u`. -/
def muxB : GateE := .inpE (.add .width .col)

/-- The wire of `muxW g u v` when the guard is empty: the signal of `v`. -/
def muxC : GateE := .inpE (.add (.add .width .width) .col)

/-- **The multiplexer is realized.** -/
theorem sigUniform_mux {r : ℕ} {m : ℕ → ℕ} {mT : Cob} (hr : 3 ≤ r)
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigUniform r m (fun args => muxW (args.getD 0 []) (args.getD 1 []) (args.getD 2 [])) := by
  refine sigUniform_of_selLayerE (K := 8) (ea := consHeadA) (eb := muxB) (ec := muxC)
    hm ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro n j hj
    have h1 : 3 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
    simp only [consHeadA, GateE.bnd, IdxE.val]
    omega
  · intro n j hj
    have h1 : 3 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
    simp only [muxB, GateE.bnd, IdxE.val]
    omega
  · intro n j hj
    have h1 : 3 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
    simp only [muxC, GateE.bnd, IdxE.val]
    omega
  · intro n j
    simp only [consHeadA, GateE.bnd, IdxE.val]
    omega
  · intro n j
    simp only [muxB, GateE.bnd, IdxE.val]
    omega
  · intro n j
    simp only [muxC, GateE.bnd, IdxE.val]
    omega
  · intro n args hlen hle
    have h0 : (0 : ℕ) < args.length := by omega
    have h1' : (1 : ℕ) < args.length := by omega
    have h2' : (2 : ℕ) < args.length := by omega
    refine List.ext_getElem (by simp) ?_
    intro j hj1 hj2
    have hj : j < 2 * m n := by simpa using hj1
    have hmm : 0 < m n := by omega
    have hrhs : (encSig (m n) (muxW (args.getD 0 []) (args.getD 1 []) (args.getD 2 [])))[j]
        = (encSig (m n) (muxW (args.getD 0 []) (args.getD 1 []) (args.getD 2 []))).getD j false :=
      (List.getD_eq_getElem _ _ (by simpa using hj2)).symm
    simp only [List.getElem_map, List.getElem_range, hrhs]
    rw [show consHeadA.gate j (m n) (2 * m n) = Gate.inp 0 from rfl,
      show muxB.gate j (m n) (2 * m n) = Gate.inp (2 * m n + j) from rfl,
      show muxC.gate j (m n) (2 * m n) = Gate.inp (2 * m n + 2 * m n + j) from rfl,
      gateVal_inp_arg (i := 0) (p := 0) h0 (by omega) (by omega),
      gateVal_inp_arg (i := 1) (p := j) h1' hj (by ring),
      gateVal_inp_arg (i := 2) (p := j) h2' hj (by ring),
      getD_encSig_lt _ hmm, muxW]
    by_cases hg : args.getD 0 [] = []
    · rw [if_pos hg, hg]
      simp
    · have hpos : 0 < (args.getD 0 []).length := by
        rcases hh : args.getD 0 [] with _ | ⟨c, t⟩
        · exact absurd hh hg
        · simp
      rw [if_neg hg, decide_eq_true hpos, selBit_true]

/-! ### The truncation -/

/-- The wire of `u.take |w|` selecting on the presence bit of `w` at the same place inside its
block. -/
def takeLenA : GateE := .inpE (.add .width (.mod .col .half))

/-- The wire of `u.take |w|` carrying the wire of `u`. -/
def takeLenB : GateE := .inpE .col

/-- **The truncation of a word to the length of another is realized.** -/
theorem sigUniform_takeLen {r : ℕ} {m : ℕ → ℕ} {mT : Cob} (hr : 2 ≤ r)
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigUniform r m (fun args => (args.getD 0 []).take (args.getD 1 []).length) := by
  refine sigUniform_of_selLayerE (K := 8) (ea := takeLenA) (eb := takeLenB) (ec := .cstE false)
    hm ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro n j hj
    have h1 : 2 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
    have h2 : j % m n < m n := Nat.mod_lt _ (by omega)
    simp only [takeLenA, GateE.bnd, IdxE.val]
    omega
  · intro n j hj
    have h1 : 2 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
    simp only [takeLenB, GateE.bnd, IdxE.val]
    omega
  · intro n j hj
    have h1 : 2 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
    simp only [GateE.bnd]
    omega
  · intro n j
    have h2 : j % m n ≤ j := Nat.mod_le _ _
    simp only [takeLenA, GateE.bnd, IdxE.val]
    omega
  · intro n j
    simp only [takeLenB, GateE.bnd, IdxE.val]
    omega
  · intro n j
    simp only [GateE.bnd]
    omega
  · intro n args hlen hle
    have h0 : (0 : ℕ) < args.length := by omega
    have h1' : (1 : ℕ) < args.length := by omega
    refine List.ext_getElem (by simp) ?_
    intro j hj1 hj2
    have hj : j < 2 * m n := by simpa using hj1
    have hmm : 0 < m n := by omega
    have hmod : j % m n < m n := Nat.mod_lt _ hmm
    have hrhs : (encSig (m n) ((args.getD 0 []).take (args.getD 1 []).length))[j]
        = (encSig (m n) ((args.getD 0 []).take (args.getD 1 []).length)).getD j false :=
      (List.getD_eq_getElem _ _ (by simpa using hj2)).symm
    simp only [List.getElem_map, List.getElem_range, hrhs]
    rw [show takeLenA.gate j (m n) (2 * m n) = Gate.inp (2 * m n + j % m n) from rfl,
      show takeLenB.gate j (m n) (2 * m n) = Gate.inp j from rfl,
      show gateVal (encArgs (m n) args) [] ((GateE.cstE false).gate j (m n) (2 * m n)) = false
        from rfl,
      gateVal_inp_arg (i := 1) (p := j % m n) h1' (by omega) (by ring),
      gateVal_inp_arg (i := 0) (p := j) h0 hj (by ring),
      getD_encSig_lt _ hmod, selBit_and]
    rcases lt_or_ge j (m n) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt, getD_encSig_lt _ hlt, getD_encSig_lt _ hlt, List.length_take]
      simp
    · have hmods : j % m n = j - m n := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      rw [hmods, getD_encSig_ge _ hge hj, getD_encSig_ge _ hge hj, getD_take]
      split_ifs with h
      · rw [decide_eq_true h, Bool.true_and]
      · rw [decide_eq_false h, Bool.false_and]

end Complexity
