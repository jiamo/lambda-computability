/-
Representing binary **words** by wires of a Boolean circuit.

A word `u` of length at most `M` is represented by two lists of `M` wires: a *presence* vector,
whose `i`-th wire says whether `i < |u|`, and a *bit* vector, whose `i`-th wire carries `u i` (and
is `false` beyond the end of `u`).  Since the wires of a circuit are functions of the circuit
input, what a signal represents is a *function* `Word → Word` of the circuit input, which is what
`Complexity.Tseitin.WHolds` states.

This module provides the word-level gadgets that the compiler of `Start/CobhamCircuit.lean` needs:
constants, resizing, dropping a prefix (free of charge), multiplexing, truncation to the length of
another word, prepending a bit, the smash function, and reading a word off the circuit input.

Main definitions:

* `Complexity.Tseitin.WHolds` — a pair of wire vectors represents a word-valued function;
* `Complexity.Tseitin.inWord` — the word a circuit input encodes on a block of input positions.

Main results:

* `Complexity.Tseitin.WHolds.mono`, `Complexity.Tseitin.WHolds.drop` — free operations;
* `Complexity.Tseitin.exists_emptySig`, `exists_constSig`, `exists_resize`, `exists_iteSig`,
  `exists_takeSig`, `exists_consSig`, `exists_smashSig`, `exists_inputSig` — the gadgets;
* `Complexity.Tseitin.exists_inWord` — every short enough word is read off some circuit input.
-/

import Start.CircuitBuild

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### Word signals -/

/-- The wire vectors `ps` (presence) and `bs` (bits), each of length `M`, represent the
word-valued function `f` of the circuit input. -/
structure WHolds (C : Circuit) (M : ℕ) (ps bs : List ℕ) (f : Word → Word) : Prop where
  lenP : ps.length = M
  lenB : bs.length = M
  bnd : ∀ x, (f x).length ≤ M
  pres : ∀ i, i < M → Holds C (ps.getD i 0) (fun x => decide (i < (f x).length))
  bit : ∀ i, i < M → Holds C (bs.getD i 0) (fun x => (f x).getD i false)

theorem WHolds.mono {C C' : Circuit} {M : ℕ} {ps bs : List ℕ} {f : Word → Word}
    (h : WHolds C M ps bs f) (he : Ext C C') : WHolds C' M ps bs f :=
  ⟨h.lenP, h.lenB, h.bnd, fun i hi => (h.pres i hi).mono he, fun i hi => (h.bit i hi).mono he⟩

theorem WHolds.congr {C : Circuit} {M : ℕ} {ps bs : List ℕ} {f g : Word → Word}
    (h : WHolds C M ps bs f) (hfg : ∀ x, f x = g x) : WHolds C M ps bs g := by
  refine ⟨h.lenP, h.lenB, fun x => by rw [← hfg]; exact h.bnd x, fun i hi => ?_, fun i hi => ?_⟩
  · exact (h.pres i hi).congr (fun x => by rw [hfg])
  · exact (h.bit i hi).congr (fun x => by rw [hfg])

/-- Dropping a prefix of a word costs no gates at all: it is a shift of the wire vectors. -/
theorem WHolds.drop {C : Circuit} {M : ℕ} {ps bs : List ℕ} {f : Word → Word}
    (h : WHolds C M ps bs f) (j : ℕ) :
    WHolds C (M - j) (ps.drop j) (bs.drop j) (fun x => (f x).drop j) := by
  have hgetP : ∀ i, (ps.drop j).getD i 0 = ps.getD (j + i) 0 := by
    intro i
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
  have hgetB : ∀ i, (bs.drop j).getD i 0 = bs.getD (j + i) 0 := by
    intro i
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
  refine ⟨by simp [h.lenP], by simp [h.lenB], fun x => by
    have := h.bnd x
    simp only [List.length_drop]
    omega, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hgetP]
    refine ((h.pres (j + i) (by omega)).congr fun x => ?_)
    simp only [List.length_drop, decide_eq_decide]
    omega
  · rw [hgetB]
    refine ((h.bit (j + i) (by omega)).congr fun x => ?_)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-! ### Constants -/

/-- The signal of a fixed word. -/
theorem exists_constSig (C : Circuit) (hC : wf C) (u : Word) (M : ℕ) (hM : u.length ≤ M) :
    ∃ (C' : Circuit) (ps bs : List ℕ), Ext C C' ∧ wf C' ∧ C'.length ≤ C.length + 2 ∧
      WHolds C' M ps bs (fun _ => u) := by
  obtain ⟨C₁, e₁, w₁, l₁, h₁⟩ := exists_cst C hC false
  obtain ⟨C₂, e₂, w₂, l₂, h₂⟩ := exists_cst C₁ w₁ true
  set wF := C.length with hwF
  set wT := C₁.length with hwT
  have hF : Holds C₂ wF (fun _ => false) := h₁.mono e₂
  have hT : Holds C₂ wT (fun _ => true) := h₂
  have hsel : ∀ c : Bool, Holds C₂ (if c then wT else wF) (fun _ => c) := by
    intro c
    cases c
    · exact hF
    · exact hT
  refine ⟨C₂, (List.range M).map (fun i => if decide (i < u.length) then wT else wF),
    (List.range M).map (fun i => if u.getD i false then wT else wF),
    e₁.trans e₂, w₂, by omega, by simp, by simp, fun _ => hM, fun i hi => ?_, fun i hi => ?_⟩
  · have hget :
        ((List.range M).map (fun i => if decide (i < u.length) then wT else wF)).getD i 0 =
        if decide (i < u.length) then wT else wF := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
      rfl
    rw [hget]
    exact hsel (decide (i < u.length))
  · have hget : ((List.range M).map (fun i => if u.getD i false then wT else wF)).getD i 0 =
        if u.getD i false then wT else wF := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
      rfl
    rw [hget]
    exact hsel (u.getD i false)

/-- The signal of the empty word. -/
theorem exists_emptySig (C : Circuit) (hC : wf C) (M : ℕ) :
    ∃ (C' : Circuit) (ps bs : List ℕ), Ext C C' ∧ wf C' ∧ C'.length ≤ C.length + 2 ∧
      WHolds C' M ps bs (fun _ => []) :=
  exists_constSig C hC [] M (by simp)

/-! ### Resizing -/

/-- Changing the width of a signal, provided the represented word still fits. -/
theorem exists_resize {C : Circuit} (hC : wf C) {M : ℕ} {ps bs : List ℕ} {f : Word → Word}
    (h : WHolds C M ps bs f) (M' : ℕ) (hM' : ∀ x, (f x).length ≤ M') :
    ∃ (C' : Circuit) (ps' bs' : List ℕ), Ext C C' ∧ wf C' ∧ C'.length ≤ C.length + 1 ∧
      WHolds C' M' ps' bs' f := by
  obtain ⟨C₁, e₁, w₁, l₁, h₁⟩ := exists_cst C hC false
  set wF := C.length with hwF
  have hgen : ∀ (ws : List ℕ) (i : ℕ), i < M' →
      ((ws ++ List.replicate M' wF).take M').getD i 0 =
        if i < ws.length then ws.getD i 0 else wF := by
    intro ws i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
    by_cases hlt : i < ws.length
    · rw [List.getElem?_append_left hlt, if_pos hlt, List.getD_eq_getElem?_getD]
    · rw [List.getElem?_append_right (by omega), if_neg hlt]
      have : (List.replicate M' wF)[i - ws.length]? = some wF := by
        apply List.getElem?_replicate_of_lt
        omega
      rw [this]
      rfl
  refine ⟨C₁, (ps ++ List.replicate M' wF).take M', (bs ++ List.replicate M' wF).take M',
    e₁, w₁, by omega, by simp [h.lenP], by simp [h.lenB], hM', fun i hi => ?_, fun i hi => ?_⟩
  · rw [hgen ps i hi, h.lenP]
    by_cases hlt : i < M
    · rw [if_pos hlt]
      exact (h.pres i hlt).mono e₁
    · rw [if_neg hlt]
      refine h₁.congr fun x => ?_
      have := h.bnd x
      have hfalse : ¬ (i < (f x).length) := by omega
      simp [hfalse]
  · rw [hgen bs i hi, h.lenB]
    by_cases hlt : i < M
    · rw [if_pos hlt]
      exact (h.bit i hlt).mono e₁
    · rw [if_neg hlt]
      refine h₁.congr fun x => ?_
      have := h.bnd x
      rw [List.getD_eq_default _ _ (by omega)]

/-! ### Multiplexing -/

/-- Choosing between two words according to a wire. -/
theorem exists_iteSig {C : Circuit} (hC : wf C) {c : ℕ} {fc : Word → Bool} (hc : Holds C c fc)
    {M : ℕ} {ps₁ bs₁ ps₂ bs₂ : List ℕ} {f₁ f₂ : Word → Word}
    (h₁ : WHolds C M ps₁ bs₁ f₁) (h₂ : WHolds C M ps₂ bs₂ f₂) :
    ∃ (C' : Circuit) (ps bs : List ℕ), Ext C C' ∧ wf C' ∧ C'.length ≤ C.length + 8 * M ∧
      WHolds C' M ps bs (fun x => if fc x then f₁ x else f₂ x) := by
  obtain ⟨C₁, pws, e₁, w₁, hlenp, hszp, hp⟩ :=
    exists_wire_list hC M 4
      (fun i x => if fc x then decide (i < (f₁ x).length) else decide (i < (f₂ x).length))
      (fun D hD he i hi =>
        exists_ite hD (hc.mono he) ((h₁.pres i hi).mono he) ((h₂.pres i hi).mono he))
  obtain ⟨C₂, bws, e₂, w₂, hlenb, hszb, hb⟩ :=
    exists_wire_list w₁ M 4
      (fun i x => if fc x then (f₁ x).getD i false else (f₂ x).getD i false)
      (fun D hD he i hi =>
        exists_ite hD (hc.mono (e₁.trans he)) ((h₁.bit i hi).mono (e₁.trans he))
          ((h₂.bit i hi).mono (e₁.trans he)))
  refine ⟨C₂, pws, bws, e₁.trans e₂, w₂, by
    have := e₁.length_le
    omega, hlenp, hlenb, fun x => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · cases hfc : fc x
    · simpa [hfc] using h₂.bnd x
    · simpa [hfc] using h₁.bnd x
  · refine ((hp i hi).mono e₂).congr fun x => ?_
    cases fc x <;> simp
  · refine (hb i hi).congr fun x => ?_
    cases fc x <;> simp

/-! ### Truncation -/

/-- Truncating a word to the length of another word. -/
theorem exists_takeSig {C : Circuit} (hC : wf C) {M : ℕ} {ps₁ bs₁ ps₂ bs₂ : List ℕ}
    {f₁ f₂ : Word → Word} (h₁ : WHolds C M ps₁ bs₁ f₁) (h₂ : WHolds C M ps₂ bs₂ f₂) :
    ∃ (C' : Circuit) (ps bs : List ℕ), Ext C C' ∧ wf C' ∧ C'.length ≤ C.length + 2 * M ∧
      WHolds C' M ps bs (fun x => (f₁ x).take (f₂ x).length) := by
  obtain ⟨C₁, pws, e₁, w₁, hlenp, hszp, hp⟩ :=
    exists_wire_list hC M 1
      (fun i x => decide (i < (f₁ x).length) && decide (i < (f₂ x).length))
      (fun D hD he i hi => by
        obtain ⟨D', e, hw, hs, hh⟩ :=
          exists_conj hD ((h₁.pres i hi).mono he) ((h₂.pres i hi).mono he)
        exact ⟨D', D.length, e, hw, by omega, hh⟩)
  obtain ⟨C₂, bws, e₂, w₂, hlenb, hszb, hb⟩ :=
    exists_wire_list w₁ M 1
      (fun i x => (f₁ x).getD i false &&
        (decide (i < (f₁ x).length) && decide (i < (f₂ x).length)))
      (fun D hD he i hi => by
        obtain ⟨D', e, hw, hs, hh⟩ :=
          exists_conj hD ((h₁.bit i hi).mono (e₁.trans he)) ((hp i hi).mono he)
        exact ⟨D', D.length, e, hw, by omega, hh⟩)
  have hlen : ∀ x, ((f₁ x).take (f₂ x).length).length = min (f₁ x).length (f₂ x).length := by
    intro x
    simp [Nat.min_comm]
  have hgetD_take : ∀ (l : Word) (n i : ℕ),
      (l.take n).getD i false = (l.getD i false && decide (i < n)) := by
    intro l n i
    by_cases hin : i < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hin, ← List.getD_eq_getElem?_getD]
      simp [hin]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp [hin]
  refine ⟨C₂, pws, bws, e₁.trans e₂, w₂, by
    have := e₁.length_le
    omega, hlenp, hlenb, fun x => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have := h₁.bnd x
    rw [hlen x]
    omega
  · refine ((hp i hi).mono e₂).congr fun x => ?_
    rw [hlen x]
    by_cases k₁ : i < (f₁ x).length <;> by_cases k₂ : i < (f₂ x).length <;>
      simp [k₁, k₂]
  · refine (hb i hi).congr fun x => ?_
    rw [hgetD_take]
    by_cases k₁ : i < (f₁ x).length
    · simp [k₁]
    · rw [List.getD_eq_default _ _ (by omega)]
      simp

/-! ### Prepending a bit -/

/-- Prepending a fixed bit to a word. -/
theorem exists_consSig {C : Circuit} (hC : wf C) (b : Bool) {M : ℕ} {ps bs : List ℕ}
    {f : Word → Word} (h : WHolds C M ps bs f) (M' : ℕ) (hM' : ∀ x, (f x).length + 1 ≤ M') :
    ∃ (C' : Circuit) (ps' bs' : List ℕ), Ext C C' ∧ wf C' ∧ C'.length ≤ C.length + 3 ∧
      WHolds C' M' ps' bs' (fun x => b :: f x) := by
  have hM'pos : 1 ≤ M' := le_trans (Nat.le_add_left 1 _) (hM' [])
  obtain ⟨C₁, ps₁, bs₁, e₁, w₁, l₁, h₁⟩ :=
    exists_resize hC h (M' - 1) (fun x => by have := hM' x; omega)
  obtain ⟨C₂, e₂, w₂, l₂, hT⟩ := exists_cst C₁ w₁ true
  obtain ⟨C₃, e₃, w₃, l₃, hB⟩ := exists_cst C₂ w₂ b
  refine ⟨C₃, C₁.length :: ps₁, C₂.length :: bs₁, e₁.trans (e₂.trans e₃), w₃, by omega,
    by simp [h₁.lenP]; omega, by simp [h₁.lenB]; omega, fun x => by
      have := hM' x
      simp only [List.length_cons]
      omega, fun i hi => ?_, fun i hi => ?_⟩
  · match i with
    | 0 => exact (hT.mono e₃).congr fun x => by simp
    | (i + 1) =>
        refine ((h₁.pres i (by omega)).mono (e₂.trans e₃)).congr fun x => ?_
        simp
  · match i with
    | 0 => exact hB.congr fun x => by simp
    | (i + 1) =>
        refine ((h₁.bit i (by omega)).mono (e₂.trans e₃)).congr fun x => ?_
        simp

/-! ### The smash function -/

/-- The pairs `(a, b)` with `a < M₁`, `b < M₂` and `i < (a + 1) * (b + 1)`. -/
def smashPairs (M₁ M₂ i : ℕ) : List (ℕ × ℕ) :=
  (((List.range M₁).flatMap fun a => (List.range M₂).map fun b => (a, b))).filter
    fun ab => decide (i < (ab.1 + 1) * (ab.2 + 1))

theorem mem_smashPairs {M₁ M₂ i a b : ℕ} :
    (a, b) ∈ smashPairs M₁ M₂ i ↔ a < M₁ ∧ b < M₂ ∧ i < (a + 1) * (b + 1) := by
  simp only [smashPairs, List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map,
    Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a', ha', b', hb', rfl, rfl⟩, h⟩
    exact ⟨ha', hb', h⟩
  · rintro ⟨ha, hb, h⟩
    exact ⟨⟨a, ha, b, hb, rfl, rfl⟩, h⟩

theorem length_smashPairs_le (M₁ M₂ i : ℕ) : (smashPairs M₁ M₂ i).length ≤ M₁ * M₂ := by
  refine le_trans (List.length_filter_le _ _) ?_
  simp

/-- The disjunction defining `i < L₁ * L₂` in terms of the presence vectors. -/
theorem any_smashPairs (M₁ M₂ i L₁ L₂ : ℕ) (h₁ : L₁ ≤ M₁) (h₂ : L₂ ≤ M₂) :
    (List.range (smashPairs M₁ M₂ i).length).any
        (fun j => decide (((smashPairs M₁ M₂ i).getD j (0, 0)).1 < L₁) &&
          decide (((smashPairs M₁ M₂ i).getD j (0, 0)).2 < L₂)) =
      decide (i < L₁ * L₂) := by
  by_cases hi : i < L₁ * L₂
  · have hL₁ : 0 < L₁ := by
      rcases Nat.eq_zero_or_pos L₁ with rfl | h
      · simp at hi
      · exact h
    have hL₂ : 0 < L₂ := by
      rcases Nat.eq_zero_or_pos L₂ with rfl | h
      · simp at hi
      · exact h
    have hmem : (L₁ - 1, L₂ - 1) ∈ smashPairs M₁ M₂ i := by
      rw [mem_smashPairs]
      refine ⟨by omega, by omega, ?_⟩
      have : L₁ - 1 + 1 = L₁ := by omega
      rw [this]
      have : L₂ - 1 + 1 = L₂ := by omega
      rw [this]
      exact hi
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.1 hmem
    rw [show decide (i < L₁ * L₂) = true from by simp [hi]]
    simp only [List.any_eq_true, List.mem_range]
    refine ⟨j, hj, ?_⟩
    rw [List.getD_eq_getElem _ _ hj, hget]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  · simp only [hi, decide_false]
    by_contra hcon
    rw [Bool.not_eq_false, List.any_eq_true] at hcon
    obtain ⟨j, hjmem, hj⟩ := hcon
    rw [List.mem_range] at hjmem
    have hmem : (smashPairs M₁ M₂ i).getD j (0, 0) ∈ smashPairs M₁ M₂ i := by
      rw [List.getD_eq_getElem _ _ hjmem]
      exact List.getElem_mem hjmem
    have hpair := mem_smashPairs (M₁ := M₁) (M₂ := M₂) (i := i)
      (a := ((smashPairs M₁ M₂ i).getD j (0, 0)).1)
      (b := ((smashPairs M₁ M₂ i).getD j (0, 0)).2)
    obtain ⟨-, -, hlt⟩ := hpair.1 (by simpa using hmem)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    exact hi (lt_of_lt_of_le hlt (Nat.mul_le_mul (by omega) (by omega)))

theorem getD_replicate_true (k i : ℕ) :
    (List.replicate k true).getD i false = decide (i < k) := by
  by_cases h : i < k
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [h]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt h)]
    simp [h]

/-- The signal of the smash `x # y = 1^{|x| · |y|}`. -/
theorem exists_smashSig {C : Circuit} (hC : wf C) {M₁ M₂ : ℕ} {ps₁ bs₁ ps₂ bs₂ : List ℕ}
    {f₁ f₂ : Word → Word} (h₁ : WHolds C M₁ ps₁ bs₁ f₁) (h₂ : WHolds C M₂ ps₂ bs₂ f₂)
    (M : ℕ) (hM : ∀ x, (f₁ x).length * (f₂ x).length ≤ M) :
    ∃ (C' : Circuit) (ps bs : List ℕ), Ext C C' ∧ wf C' ∧
      C'.length ≤ C.length + M * (2 * (M₁ * M₂) + 2) ∧
      WHolds C' M ps bs (fun x => List.replicate ((f₁ x).length * (f₂ x).length) true) := by
  obtain ⟨C₁, ws, e₁, w₁, hlen, hsz, hws⟩ :=
    exists_wire_list hC M (2 * (M₁ * M₂) + 2)
      (fun i x => decide (i < (f₁ x).length * (f₂ x).length))
      (fun D hD he i _ => by
        set P := smashPairs M₁ M₂ i with hP
        have hple : P.length ≤ M₁ * M₂ := by
          rw [hP]; exact length_smashPairs_le M₁ M₂ i
        obtain ⟨D₁, cws, d₁, u₁, hlen₁, hsz₁, hcw⟩ :=
          exists_wire_list hD P.length 1
            (fun j x => decide ((P.getD j (0, 0)).1 < (f₁ x).length) &&
              decide ((P.getD j (0, 0)).2 < (f₂ x).length))
            (fun E hE heE j hj => by
              have hmem : P.getD j (0, 0) ∈ P := by
                rw [List.getD_eq_getElem _ _ hj]
                exact List.getElem_mem hj
              have hpair : ((P.getD j (0, 0)).1, (P.getD j (0, 0)).2) ∈ P := by simpa using hmem
              obtain ⟨ha, hb, -⟩ := mem_smashPairs.1 hpair
              obtain ⟨E', e, hw, hs, hh⟩ :=
                exists_conj hE ((h₁.pres _ ha).mono (he.trans heE))
                  ((h₂.pres _ hb).mono (he.trans heE))
              exact ⟨E', E.length, e, hw, by omega, hh⟩)
        obtain ⟨D₂, w, d₂, u₂, hsz₂, hh₂⟩ :=
          exists_bigOr u₁ P.length cws
            (fun j x => decide ((P.getD j (0, 0)).1 < (f₁ x).length) &&
              decide ((P.getD j (0, 0)).2 < (f₂ x).length)) hcw
        refine ⟨D₂, w, d₁.trans d₂, u₂, by omega, hh₂.congr fun x => ?_⟩
        exact any_smashPairs M₁ M₂ i _ _ (h₁.bnd x) (h₂.bnd x))
  refine ⟨C₁, ws, ws, e₁, w₁, by simpa using hsz, hlen, hlen, fun x => by
    simpa using hM x, fun i hi => ?_, fun i hi => ?_⟩
  · exact (hws i hi).congr fun x => by simp
  · exact (hws i hi).congr fun x => (getD_replicate_true _ _).symm

/-! ### Reading a word off the circuit input -/

/-- The word encoded by the first `2 * N` positions of the circuit input: the input is read as a
list of pairs, the first component saying whether a further bit follows and the second carrying
that bit. -/
def inWord : ℕ → Word → Word
  | 0, _ => []
  | N + 1, x => if x.getD 0 false then x.getD 1 false :: inWord N (x.drop 2) else []

theorem getD_drop_two (x : Word) (k : ℕ) : (x.drop 2).getD k false = x.getD (k + 2) false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
  congr 1
  omega

theorem length_inWord_le : ∀ (N : ℕ) (x : Word), (inWord N x).length ≤ N := by
  intro N
  induction N with
  | zero => intro x; rw [inWord]; simp
  | succ N ih =>
      intro x
      by_cases h : x.getD 0 false = true
      · rw [inWord, if_pos h, List.length_cons]
        have := ih (x.drop 2)
        omega
      · rw [inWord, if_neg h]
        simp

theorem inWord_pres : ∀ (N i : ℕ) (x : Word), i < N →
    decide (i < (inWord N x).length) =
      (List.range (i + 1)).all (fun j => x.getD (2 * j) false) := by
  intro N
  induction N with
  | zero => intro i x hi; omega
  | succ N ih =>
      intro i x hi
      have hsplit : (List.range (i + 1)).all (fun j => x.getD (2 * j) false)
          = (x.getD 0 false && (List.range i).all (fun j => x.getD (2 * (j + 1)) false)) := by
        rw [List.range_succ_eq_map, List.all_cons]
        simp [List.all_map, Function.comp_def]
      by_cases h : x.getD 0 false = true
      · rw [hsplit, h, Bool.true_and, inWord, if_pos h, List.length_cons]
        match i with
        | 0 => simp
        | (i + 1) =>
            have hrec := ih i (x.drop 2) (by omega)
            rw [show decide (i + 1 < (inWord N (x.drop 2)).length + 1)
                  = decide (i < (inWord N (x.drop 2)).length) by simp, hrec]
            simp only [getD_drop_two, Nat.mul_succ]
      · simp only [Bool.not_eq_true] at h
        rw [hsplit, h, inWord, if_neg (by rw [h]; simp)]
        simp

theorem inWord_bit : ∀ (N i : ℕ) (x : Word),
    (inWord N x).getD i false =
      (x.getD (2 * i + 1) false && decide (i < (inWord N x).length)) := by
  intro N
  induction N with
  | zero => intro i x; rw [inWord]; simp
  | succ N ih =>
      intro i x
      by_cases h : x.getD 0 false = true
      · rw [inWord, if_pos h]
        match i with
        | 0 => simp
        | (i + 1) =>
            rw [List.getD_cons_succ, ih i (x.drop 2), getD_drop_two, List.length_cons,
              show decide (i + 1 < (inWord N (x.drop 2)).length + 1)
                  = decide (i < (inWord N (x.drop 2)).length) by simp]
            congr 2
      · rw [inWord, if_neg h]
        simp

/-- **Every short enough word is read off some circuit input.** -/
theorem exists_inWord : ∀ (N : ℕ) (u : Word), u.length ≤ N → ∃ x : Word, inWord N x = u := by
  intro N
  induction N with
  | zero =>
      intro u hu
      refine ⟨[], ?_⟩
      rw [inWord, List.eq_nil_of_length_eq_zero (by omega : u.length = 0)]
  | succ N ih =>
      intro u hu
      match u with
      | [] =>
          refine ⟨[false], ?_⟩
          rw [inWord, if_neg (by simp)]
      | (b :: u) =>
          obtain ⟨x, hx⟩ := ih u (by simpa using Nat.le_of_succ_le_succ (by simpa using hu))
          refine ⟨true :: b :: x, ?_⟩
          rw [inWord, if_pos (by simp)]
          simp only [List.getD_cons_succ, List.getD_cons_zero]
          rw [show (true :: b :: x).drop 2 = x from rfl, hx]

/-- The signal reading a word off the circuit input. -/
theorem exists_inputSig (C : Circuit) (hC : wf C) (N : ℕ) :
    ∃ (C' : Circuit) (ps bs : List ℕ), Ext C C' ∧ wf C' ∧
      C'.length ≤ C.length + 2 * N + N * (N + 2) + N ∧ WHolds C' N ps bs (inWord N) := by
  obtain ⟨C₁, iws, e₁, w₁, hleni, hszi, hiw⟩ :=
    exists_wire_list hC (2 * N) 1 (fun k x => x.getD k false)
      (fun D hD _ k _ => by
        obtain ⟨D', e, hw, hl, hh⟩ := exists_inp D hD k
        exact ⟨D', D.length, e, hw, by omega, hh⟩)
  obtain ⟨C₂, pws, e₂, w₂, hlenp, hszp, hpw⟩ :=
    exists_wire_list w₁ N (N + 2) (fun i x => decide (i < (inWord N x).length))
      (fun D hD he i hi => by
        obtain ⟨D', w, e, hw, hs, hh⟩ :=
          exists_bigAnd hD (i + 1) ((List.range (i + 1)).map (fun j => iws.getD (2 * j) 0))
            (fun j x => x.getD (2 * j) false) (fun j hj => by
              have hget : ((List.range (i + 1)).map (fun j => iws.getD (2 * j) 0)).getD j 0
                  = iws.getD (2 * j) 0 := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
                rfl
              rw [hget]
              exact (hiw (2 * j) (by omega)).mono he)
        exact ⟨D', w, e, hw, by omega, hh.congr fun x => (inWord_pres N i x hi).symm⟩)
  obtain ⟨C₃, bws, e₃, w₃, hlenb, hszb, hbw⟩ :=
    exists_wire_list w₂ N 1 (fun i x => (inWord N x).getD i false)
      (fun D hD he i hi => by
        obtain ⟨D', e, hw, hl, hh⟩ :=
          exists_conj hD ((hiw (2 * i + 1) (by omega)).mono (e₂.trans he))
            ((hpw i hi).mono he)
        exact ⟨D', D.length, e, hw, by omega, hh.congr fun x => (inWord_bit N i x).symm⟩)
  refine ⟨C₃, pws, bws, e₁.trans (e₂.trans e₃), w₃, ?_, hlenp, hlenb,
    fun x => length_inWord_le N x, fun i hi => (hpw i hi).mono e₃, fun i hi => hbw i hi⟩
  have h₁ := e₁.length_le
  have h₂ := e₂.length_le
  omega

end Tseitin

end Complexity
