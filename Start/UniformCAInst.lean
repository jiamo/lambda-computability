/-
# An instance of the tableau rule: a spreading cellular automaton

`Start/UniformCACode.lean` proves that the language of a cellular automaton over a fixed finite
alphabet, run on a Cobham-computable tape for a Cobham-computable number of steps, is decided by a
P-uniform circuit family.  This module exercises that rule on a concrete automaton, so that the
rule is visibly not vacuous: the automaton whose local rule is the disjunction of a cell and its
two neighbours.  A `true` bit of the input spreads one cell per step in both directions, so after
enough steps the first cell carries the disjunction of the whole input.

Main definitions:

* `Complexity.orCA` — the spreading cellular automaton;
* `Complexity.orW` — the tape and the running time, one more than the length of the input.

Main results:

* `Complexity.caCell_orCA` — **the contents of a cell are the disjunction of the window it can
  see**;
* `Complexity.caLang_orCA_eq_someOne` — the language of the automaton is
  `Complexity.SomeOne`;
* `Complexity.pUniformDecidable_someOne_of_ca` — a second proof, through the tableau, that
  `Complexity.SomeOne` is decided by a P-uniform circuit family.
-/
import Start.UniformCACode

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-- **The spreading cellular automaton**: two symbols, the blank `0` and the mark `1`; a cell is
marked at the next step exactly when it or one of its neighbours is marked now. -/
def orCA : CellAuto where
  K := 2
  blk := 0
  ini := fun _ b => if b then 1 else 0
  stp := fun a b c => if a = 1 ∨ b = 1 ∨ c = 1 then 1 else 0
  ac := fun s => decide (s = 1)
  Kpos := by norm_num
  blk_lt := by norm_num
  ini_lt := by intro _ b; cases b <;> norm_num
  stp_lt := by intro a b c; split <;> norm_num

/-- The tape and the running time: one more than the length of the input, so that the tape is
never empty and the mark has time to reach the first cell. -/
def orW (n : ℕ) : ℕ := n + 1

/-- **The contents of a cell are the disjunction of the window it can see**: the cell `j` is
marked at time `t` exactly when some input bit inside the tape at distance at most `t` is
`true`. -/
theorem caCell_orCA (W n : ℕ) (bit : ℕ → Bool) : ∀ t j, j < W →
    (CircCode.caCell orCA W n bit t j = 1
      ↔ ∃ k, k < W ∧ k < n ∧ bit k = true ∧ j ≤ k + t ∧ k ≤ j + t) := by
  intro t
  induction t with
  | zero =>
      intro j hj
      have hval : CircCode.caCell orCA W n bit 0 j = if j < n ∧ bit j = true then 1 else 0 := by
        rw [CircCode.caCell]
        by_cases hjn : j < n
        · rw [if_pos hjn]
          cases bit j <;> simp [orCA, hjn]
        · rw [if_neg hjn]
          simp [orCA, hjn]
      rw [hval]
      constructor
      · intro hc
        by_cases hp : j < n ∧ bit j = true
        · exact ⟨j, hj, hp.1, hp.2, by omega, by omega⟩
        · rw [if_neg hp] at hc
          exact absurd hc (by norm_num)
      · rintro ⟨k, -, hkn, hbk, h1, h2⟩
        have hkj : k = j := by omega
        subst hkj
        rw [if_pos ⟨hkn, hbk⟩]
  | succ t ih =>
      intro j hj
      have hstp : ∀ a b c : ℕ, orCA.stp a b c = 1 ↔ (a = 1 ∨ b = 1 ∨ c = 1) := by
        intro a b c
        by_cases hh : a = 1 ∨ b = 1 ∨ c = 1 <;> simp [orCA, hh]
      have hL : (if j = 0 then orCA.blk else CircCode.caCell orCA W n bit t (j - 1)) = 1
          ↔ (j ≠ 0 ∧ ∃ k, k < W ∧ k < n ∧ bit k = true ∧ j - 1 ≤ k + t ∧ k ≤ j - 1 + t) := by
        by_cases h0 : j = 0
        · rw [if_pos h0]
          simp [orCA, h0]
        · rw [if_neg h0, ih (j - 1) (by omega)]
          simp [h0]
      have hR : (if j + 1 < W then CircCode.caCell orCA W n bit t (j + 1) else orCA.blk) = 1
          ↔ (j + 1 < W ∧ ∃ k, k < W ∧ k < n ∧ bit k = true ∧ j + 1 ≤ k + t ∧ k ≤ j + 1 + t) := by
        by_cases hw : j + 1 < W
        · rw [if_pos hw, ih (j + 1) hw]
          simp [hw]
        · rw [if_neg hw]
          simp [orCA, hw]
      rw [CircCode.caCell, hstp, hL, ih j hj, hR]
      constructor
      · rintro (⟨-, k, hkW, hkn, hbk, h1, h2⟩ | ⟨k, hkW, hkn, hbk, h1, h2⟩
          | ⟨-, k, hkW, hkn, hbk, h1, h2⟩) <;>
          exact ⟨k, hkW, hkn, hbk, by omega, by omega⟩
      · rintro ⟨k, hkW, hkn, hbk, h1, h2⟩
        rcases Nat.lt_or_ge (j + t) k with hgt | hle
        · exact Or.inr (Or.inr ⟨by omega, k, hkW, hkn, hbk, by omega, by omega⟩)
        · rcases Nat.lt_or_ge (k + t) j with hlt | hge
          · exact Or.inl ⟨by omega, k, hkW, hkn, hbk, by omega, by omega⟩
          · exact Or.inr (Or.inl ⟨k, hkW, hkn, hbk, by omega, by omega⟩)

/-- The tape and the running time are computed in unary by a Cobham term. -/
theorem caUniform_orW : CAUniform orW orW := by
  refine ⟨Cob.pre [true] (Cob.unary (.proj 0)), Cob.pre [true] (Cob.unary (.proj 0)),
    fun n => by rw [orW]; omega, ?_, ?_⟩ <;>
  · intro x
    rw [Cob.eval_pre, Cob.eval_unary, orW, List.replicate_succ]
    simp

/-- The language of the spreading automaton is exactly the language of the words with a `true`
bit. -/
theorem caLang_orCA_eq_someOne : CALang orCA orW orW = SomeOne := by
  funext x
  rw [CALang, SomeOne]
  have hac : ∀ s : ℕ, (orCA.ac s = true) = (s = 1) := by
    intro s
    simp [orCA]
  rw [hac, caCell_orCA _ _ _ _ 0 (by rw [orW]; omega)]
  apply propext
  constructor
  · rintro ⟨k, -, hkn, hbk, -, -⟩
    rw [List.any_eq_true]
    exact ⟨x.getD k false, by rw [List.getD_eq_getElem x false hkn]; exact List.getElem_mem hkn,
      hbk⟩
  · intro hx
    rw [List.any_eq_true] at hx
    obtain ⟨b, hb, hbt⟩ := hx
    obtain ⟨k, hk, hkb⟩ := List.getElem_of_mem hb
    exact ⟨k, by rw [orW]; omega, hk,
      by rw [List.getD_eq_getElem x false hk, hkb]; exact hbt, by omega, by rw [orW]; omega⟩

/-- **A second proof, through the tableau, that `Complexity.SomeOne` is decided by a P-uniform
circuit family.** -/
theorem pUniformDecidable_someOne_of_ca : PUniformDecidable SomeOne := by
  rw [← caLang_orCA_eq_someOne]
  exact pUniformDecidable_caLang caUniform_orW

end Complexity
