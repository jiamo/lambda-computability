import Start.KolmogorovCond
import Start.Sqrt

/-!
# Description-cost audit for `kolm` and `kolmCond` (task `M19-DESCRIPTION-COST-AUDIT`)

`Lambda.kolm` and `Lambda.kolmCond` measure programs by the raw syntax size `Lambda.size`
(a de Bruijn index `i` costs `i + 1`), not by the length of a binary program.  Binary-string
counting facts ("at most `2^m` descriptions of length `< m`") therefore do not apply verbatim.
This module proves the counting facts that *do* hold for the actual measure, through an explicit
comparison with a binary prefix code.

* `Lambda.sizeBits` — a prefix-free binary code of terms:
  `var i ↦ 1^(i+1) 0`, `lam t ↦ 0 1 · sizeBits t`, `app a b ↦ 0 0 · sizeBits a · sizeBits b`.
* `Lambda.sizeBits_append_inj` — prefix-freeness (unique decoding).
* `Lambda.size_le_length_sizeBits`, `Lambda.length_sizeBits_le` — the comparison maps
  `size t ≤ |sizeBits t| ≤ 2 · size t`.
* `Lambda.card_size_le` — at most `4^m` terms have size `≤ m`.
* `Lambda.card_kolm_le`, `Lambda.card_kolmCond_le` — at most `4^m` numbers have (conditional)
  complexity `≤ m`.
* `Lambda.exists_le_four_pow_kolm_gt`, `Lambda.exists_le_four_pow_kolmCond_gt` — quantitative
  incompressibility: among `0, …, 4^m` some number has (conditional) complexity `> m`.
* `Lambda.kolmBits` with `Lambda.kolm_le_kolmBits`, `Lambda.kolmBits_le_two_mul_kolm` — the
  bit-length description complexity of the same programs is within a factor two of `kolm`.

So the raw size measure counts with base `4` rather than base `2`: every additive
"`log₂` of a count" step in an information inequality becomes a `2 · log₂` step for `kolm`
(equivalently, a `log₄` step), and transfers to the bit measure only up to the factor two of
`kolmBits`.  These are this library's own definitions and proofs.
-/

set_option autoImplicit false

noncomputable section

namespace Lambda

/-- A prefix-free binary code of lambda terms. -/
def sizeBits : Lambda → List Bool
  | var i => List.replicate (i + 1) Bool.true ++ [Bool.false]
  | lam t => Bool.false :: Bool.true :: sizeBits t
  | app a b => Bool.false :: Bool.false :: (sizeBits a ++ sizeBits b)

theorem replicate_true_append_false_inj (i j : ℕ) (r r' : List Bool)
    (h : List.replicate (i + 1) Bool.true ++ Bool.false :: r = List.replicate (j + 1) Bool.true ++ Bool.false :: r') :
    i = j ∧ r = r' := by
  induction i generalizing j with
  | zero =>
      cases j with
      | zero => simpa using h
      | succ j => simp [List.replicate_succ] at h
  | succ i ih =>
      cases j with
      | zero => simp [List.replicate_succ] at h
      | succ j =>
          rw [List.replicate_succ (n := i + 1), List.replicate_succ (n := j + 1)] at h
          simp only [List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨h1, h2⟩ := ih j h
          exact ⟨by omega, h2⟩

/-- **Unique decoding**: the code is prefix-free. -/
theorem sizeBits_append_inj : ∀ (t t' : Lambda) (r r' : List Bool),
    sizeBits t ++ r = sizeBits t' ++ r' → t = t' ∧ r = r'
  | var i, var j, r, r', h => by
      simp only [sizeBits, List.append_assoc, List.singleton_append] at h
      obtain ⟨h1, h2⟩ := replicate_true_append_false_inj i j r r' h
      exact ⟨by rw [h1], h2⟩
  | var i, lam _, r, r', h => by simp [sizeBits, List.replicate_succ] at h
  | var i, app _ _, r, r', h => by simp [sizeBits, List.replicate_succ] at h
  | lam _, var j, r, r', h => by simp [sizeBits, List.replicate_succ] at h
  | lam t, lam t', r, r', h => by
      simp only [sizeBits, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := sizeBits_append_inj t t' r r' h
      exact ⟨by rw [h1], h2⟩
  | lam _, app _ _, r, r', h => by simp [sizeBits] at h
  | app _ _, var j, r, r', h => by simp [sizeBits, List.replicate_succ] at h
  | app _ _, lam _, r, r', h => by simp [sizeBits] at h
  | app a b, app a' b', r, r', h => by
      simp only [sizeBits, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨h1, h2⟩ := sizeBits_append_inj a a' _ _ h
      obtain ⟨h3, h4⟩ := sizeBits_append_inj b b' r r' h2
      exact ⟨by rw [h1, h3], h4⟩

theorem sizeBits_injective : Function.Injective sizeBits := fun t t' h =>
  (sizeBits_append_inj t t' [] [] (by simpa using h)).1

/-- Comparison map, lower half: the raw size is at most the binary code length. -/
theorem size_le_length_sizeBits : ∀ t : Lambda, size t ≤ (sizeBits t).length
  | var i => by simp [sizeBits]
  | lam t => by have := size_le_length_sizeBits t; simp [sizeBits]; omega
  | app a b => by
      have := size_le_length_sizeBits a; have := size_le_length_sizeBits b; simp [sizeBits]; omega

/-- Comparison map, upper half: the binary code length is at most twice the raw size. -/
theorem length_sizeBits_le : ∀ t : Lambda, (sizeBits t).length ≤ 2 * size t
  | var i => by simp [sizeBits]
  | lam t => by have := length_sizeBits_le t; simp [sizeBits]; omega
  | app a b => by
      have := length_sizeBits_le a; have := length_sizeBits_le b; simp [sizeBits]; omega

/-- Pad the code of a term of size `≤ m` to exactly `2m` sizeBits. -/
def padBits (m : ℕ) (t : {t : Lambda // size t ≤ m}) : List.Vector Bool (2 * m) :=
  ⟨sizeBits t.1 ++ List.replicate (2 * m - (sizeBits t.1).length) Bool.false, by
    have := length_sizeBits_le t.1; have := t.2; simp; omega⟩

theorem padBits_injective (m : ℕ) : Function.Injective (padBits m) := by
  intro t t' h
  have h' := congrArg Subtype.val h
  simp only [padBits] at h'
  exact Subtype.ext (sizeBits_append_inj _ _ _ _ h').1

/-- **Counting terms by raw size**: at most `4^m` terms have size `≤ m`. -/
theorem card_size_le (m : ℕ) : Nat.card {t : Lambda // size t ≤ m} ≤ 4 ^ m := by
  have := Nat.card_le_card_of_injective _ (padBits_injective m)
  · simpa [pow_mul] using this

instance finite_size_le (m : ℕ) : Finite {t : Lambda // size t ≤ m} :=
  Finite.of_injective (padBits m) (padBits_injective m)

/-- A minimal program, as an element of the terms of size `≤ m`. -/
def minSizeProg (m : ℕ) (s : {s : ℕ // kolm s ≤ m}) : {t : Lambda // size t ≤ m} :=
  ⟨(exists_program_of_kolm s.1).choose, by
    rw [(exists_program_of_kolm s.1).choose_spec.2]; exact s.2⟩

theorem minProg_injective (m : ℕ) : Function.Injective (minSizeProg m) := by
  intro s s' h
  have h1 := (exists_program_of_kolm s.1).choose_spec.1.2
  have h2 := (exists_program_of_kolm s'.1).choose_spec.1.2
  have h' := congrArg Subtype.val h
  simp only [minSizeProg] at h'
  rw [h'] at h1
  exact Subtype.ext (Lambda.unique_church_reduct h1 h2)

/-- **Counting numbers by complexity**: at most `4^m` numbers have `kolm s ≤ m`. -/
theorem card_kolm_le (m : ℕ) : Nat.card {s : ℕ // kolm s ≤ m} ≤ 4 ^ m :=
  (Nat.card_le_card_of_injective _ (minProg_injective m)).trans (card_size_le m)

/-- A minimal conditional program, as an element of the terms of size `≤ m`. -/
def minCondSizeProg (m y : ℕ) (s : {s : ℕ // kolmCond s y ≤ m}) : {t : Lambda // size t ≤ m} :=
  ⟨(exists_condProgram_of_kolmCond s.1 y).choose, by
    rw [(exists_condProgram_of_kolmCond s.1 y).choose_spec.2]; exact s.2⟩

theorem minCondProg_injective (m y : ℕ) : Function.Injective (minCondSizeProg m y) := by
  intro s s' h
  have h1 := (exists_condProgram_of_kolmCond s.1 y).choose_spec.1.2
  have h2 := (exists_condProgram_of_kolmCond s'.1 y).choose_spec.1.2
  have h' := congrArg Subtype.val h
  simp only [minCondSizeProg] at h'
  rw [h'] at h1
  exact Subtype.ext (Lambda.unique_church_reduct h1 h2)

/-- **Conditional counting**: for every `y`, at most `4^m` numbers have `kolmCond s y ≤ m`. -/
theorem card_kolmCond_le (m y : ℕ) : Nat.card {s : ℕ // kolmCond s y ≤ m} ≤ 4 ^ m :=
  (Nat.card_le_card_of_injective _ (minCondProg_injective m y)).trans (card_size_le m)

/-- Pigeonhole helper: if at most `N` numbers satisfy `P`, some number `≤ N` fails `P`. -/
theorem exists_le_not_of_card_le (P : ℕ → Prop) (N : ℕ) [Finite {s : ℕ // P s}]
    (h : Nat.card {s : ℕ // P s} ≤ N) : ∃ s ≤ N, ¬ P s := by
  by_contra hc
  push Not at hc
  have hinj : Function.Injective (fun i : Fin (N + 1) => (⟨i.1, hc i.1 (by omega)⟩ : {s // P s})) := by
    intro i j hij
    exact Fin.ext (congrArg Subtype.val hij)
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

instance finite_kolm_le (m : ℕ) : Finite {s : ℕ // kolm s ≤ m} :=
  Finite.of_injective (minSizeProg m) (minProg_injective m)

instance finite_kolmCond_le (m y : ℕ) : Finite {s : ℕ // kolmCond s y ≤ m} :=
  Finite.of_injective (minCondSizeProg m y) (minCondProg_injective m y)

/-- **Quantitative incompressibility** for the raw size measure: some `s ≤ 4^m` has
`kolm s > m`. -/
theorem exists_le_four_pow_kolm_gt (m : ℕ) : ∃ s ≤ 4 ^ m, m < kolm s := by
  obtain ⟨s, hs, h⟩ := exists_le_not_of_card_le (fun s => kolm s ≤ m) _ (card_kolm_le m)
  exact ⟨s, hs, by omega⟩

/-- **Conditional quantitative incompressibility**: for every `y`, some `s ≤ 4^m` has
`kolmCond s y > m`. -/
theorem exists_le_four_pow_kolmCond_gt (m y : ℕ) : ∃ s ≤ 4 ^ m, m < kolmCond s y := by
  obtain ⟨s, hs, h⟩ :=
    exists_le_not_of_card_le (fun s => kolmCond s y ≤ m) _ (card_kolmCond_le m y)
  exact ⟨s, hs, by omega⟩

/-- Bit-length description complexity: the least binary code length `|sizeBits t|` of a program. -/
def kolmBits (s : ℕ) : ℕ := sInf {n | ∃ t : Lambda, IsProgramFor t s ∧ (sizeBits t).length = n}

theorem kolm_le_kolmBits (s : ℕ) : kolm s ≤ kolmBits s := by
  have hne : {n | ∃ t : Lambda, IsProgramFor t s ∧ (sizeBits t).length = n}.Nonempty :=
    ⟨(sizeBits (church s)).length, church s, isProgramFor_church s, rfl⟩
  obtain ⟨t, ht, hl⟩ := Nat.sInf_mem hne
  rw [kolmBits, ← hl]
  exact (kolm_le_of_isProgramFor ht).trans (size_le_length_sizeBits t)

theorem kolmBits_le_two_mul_kolm (s : ℕ) : kolmBits s ≤ 2 * kolm s := by
  obtain ⟨t, ht, hs⟩ := exists_program_of_kolm s
  rw [← hs]
  have : kolmBits s ≤ (sizeBits t).length :=
    Nat.sInf_le (s := {n | ∃ t : Lambda, IsProgramFor t s ∧ (sizeBits t).length = n}) ⟨t, ht, rfl⟩
  exact this.trans (length_sizeBits_le t)

end Lambda

end
