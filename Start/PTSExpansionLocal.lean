/-
**Expansion postponement and syntax-directed completeness for level assignments without a bound
(M29-EP-LOCAL).**

`expansionPostponement_of_stratification` and `sd_complete_of_stratification` assume a
`Stratification`, whose levels are bounded.  This module removes the bound.

* `HasTypeR.monotone`, `HasTypeSD.monotone`: both systems are monotone in the specification.
* `Functional.restrict`: functionality passes to finite restrictions.
* `levelsStratification`: on a finite restriction `P.restrict A R`, the truncated levels
  `fun s => min (level s) N` form a `Stratification`.
* `expansionPostponement_of_levels`, `sd_complete_of_levels`: the unbounded theorems.  A typing
  derivation uses finitely many axioms and rules (`HasType.finite_support`); the bounded
  theorems apply to that restriction, and the results are transported back by monotonicity.
* Poll's Open Problem 6 for every specification with expansion postponement:
  `HasTypeR.weak_subject_reduction` and `HasTypeR.correctness_of_types`.
* `NatHierarchy.natHier`: sorts `ℕ`, axioms `n : n+1`, rules `(m, n, n)` for `n ≤ m`.  It has
  infinitely many sorts, no `Stratification`, and satisfies all of the above.
-/

import Start.PTSSyntaxDirected

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

universe u

/-! ### Monotonicity -/

namespace HasTypeR

variable {S : Type u} {P Q : Specification S}

theorem monotone {Γ : List (Expr S)} {M A : Expr S} (h : HasTypeR P Γ M A)
    (ha : ∀ s t, P.axioms s t → Q.axioms s t)
    (hr : ∀ a b c, P.rule a b c → Q.rule a b c) : HasTypeR Q Γ M A := by
  induction h with
  | ax h => exact .ax (ha _ _ h)
  | var _ ih => exact .var ih
  | weaken _ _ ihM ihA => exact .weaken ihM ihA
  | product _ _ h ihA ihB => exact .product ihA ihB (hr _ _ _ h)
  | abstraction _ _ ihb ihPi => exact .abstraction ihb ihPi
  | application _ _ ihf iha => exact .application ihf iha
  | reduction _ hb ih => exact .reduction ih hb

end HasTypeR

namespace HasTypeSD

variable {S : Type u} {P Q : Specification S}

theorem monotone {Γ : List (Expr S)} {M A : Expr S} (h : HasTypeSD P Γ M A)
    (ha : ∀ s t, P.axioms s t → Q.axioms s t)
    (hr : ∀ a b c, P.rule a b c → Q.rule a b c) : HasTypeSD Q Γ M A := by
  induction h with
  | ax h => exact .ax (ha _ _ h)
  | var _ hs ih => exact .var ih hs
  | weaken_var _ _ hs ih ihA => exact .weaken_var ih ihA hs
  | weaken_sort _ _ hs ih ihA => exact .weaken_sort ih ihA hs
  | product _ h1 _ h2 h ihA ihB => exact .product ihA h1 ihB h2 (hr _ _ _ h)
  | abstraction _ _ hs ihb ihPi => exact .abstraction ihb ihPi hs
  | application _ hw _ hc ihf iha => exact .application ihf hw iha hc

end HasTypeSD

/-! ### Restrictions -/

theorem Functional.restrict {S : Type u} {P : Specification S} (hf : Functional P)
    (A : Finset (S × S)) (R : Finset (S × S × S)) : Functional (P.restrict A R) :=
  ⟨fun s t t' h h' => hf.1 s t t' h.1 h'.1,
    fun s₁ s₂ s₃ s₃' h h' => hf.2 s₁ s₂ s₃ s₃' h.1 h'.1⟩

section Levels

variable {S : Type u} {P : Specification S}

/-- The largest level occurring in the finite sets of axioms `A` and rules `R`. -/
def levelsBound (level : S → ℕ) (A : Finset (S × S)) (R : Finset (S × S × S)) : ℕ :=
  max (A.sup fun p => max (level p.1) (level p.2))
    (R.sup fun r => max (level r.1) (max (level r.2.1) (level r.2.2)))

theorem levelsBound_axiom (level : S → ℕ) {A : Finset (S × S)} (R : Finset (S × S × S))
    {s t : S} (h : (s, t) ∈ A) :
    level s ≤ levelsBound level A R ∧ level t ≤ levelsBound level A R := by
  have := Finset.le_sup (f := fun p : S × S => max (level p.1) (level p.2)) h
  simp only at this
  unfold levelsBound
  constructor <;> omega

theorem levelsBound_rule (level : S → ℕ) (A : Finset (S × S)) {R : Finset (S × S × S)}
    {a b c : S} (h : (a, b, c) ∈ R) :
    level a ≤ levelsBound level A R ∧ level b ≤ levelsBound level A R ∧
      level c ≤ levelsBound level A R := by
  have := Finset.le_sup
    (f := fun r : S × S × S => max (level r.1) (max (level r.2.1) (level r.2.2))) h
  simp only at this
  unfold levelsBound
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- On a finite restriction, truncating an unbounded level assignment at the largest level that
occurs gives a `Stratification`. -/
def levelsStratification (level : S → ℕ)
    (hax : ∀ s t, P.axioms s t → level t = level s + 1)
    (hrule : ∀ s₁ s₂ s₃, P.rule s₁ s₂ s₃ → level s₃ = level s₂ ∧ level s₂ ≤ level s₁)
    (A : Finset (S × S)) (R : Finset (S × S × S)) : Stratification (P.restrict A R) where
  level s := min (level s) (levelsBound level A R)
  bound := levelsBound level A R
  level_le _ := min_le_right _ _
  axiom_level s t h := by
    have hb := levelsBound_axiom level R h.2
    have := hax s t h.1
    show min _ _ = min _ _ + 1
    omega
  rule_level a b c h := by
    have hb := levelsBound_rule level A h.2
    have := hrule a b c h.1
    show min _ _ = min _ _ ∧ min _ _ ≤ min _ _
    omega

/-- **Expansion postponement for level assignments without a bound.**  If axioms go up exactly
one level and no product has its codomain above its domain, expansion postponement holds.  No
bound on the levels and no normalization hypothesis. -/
theorem expansionPostponement_of_levels (level : S → ℕ)
    (hax : ∀ s t, P.axioms s t → level t = level s + 1)
    (hrule : ∀ s₁ s₂ s₃, P.rule s₁ s₂ s₃ → level s₃ = level s₂ ∧ level s₂ ≤ level s₁) :
    ExpansionPostponement P := by
  intro Γ M T h
  obtain ⟨A, R, hAR⟩ := h.finite_support
  obtain ⟨B, hB, hR⟩ :=
    expansionPostponement_of_stratification (levelsStratification level hax hrule A R) Γ M T hAR
  exact ⟨B, hB, hR.monotone (fun _ _ h => h.1) (fun _ _ _ h => h.1)⟩

/-- **Completeness of Pollack's syntax-directed system for functional specifications with a level
assignment without a bound.** -/
theorem sd_complete_of_levels (hf : Functional P) (level : S → ℕ)
    (hax : ∀ s t, P.axioms s t → level t = level s + 1)
    (hrule : ∀ s₁ s₂ s₃, P.rule s₁ s₂ s₃ → level s₃ = level s₂ ∧ level s₂ ≤ level s₁)
    {Γ : List (Expr S)} {M T : Expr S} (h : HasType P Γ M T) :
    ∃ T', HasTypeSD P Γ M T' ∧ Converts T' T := by
  obtain ⟨A, R, hAR⟩ := h.finite_support
  obtain ⟨T', hT', hc⟩ :=
    sd_complete_of_stratification (hf.restrict A R) (levelsStratification level hax hrule A R) hAR
  exact ⟨T', hT'.monotone (fun _ _ h => h.1) (fun _ _ _ h => h.1), hc⟩

end Levels

/-! ### Poll's Open Problem 6 under expansion postponement -/

namespace HasTypeR

variable {S : Type u} {P : Specification S}

/-- **Weak subject reduction** for the reduction-only system (Poll's Open Problem 6, first half),
for every specification with expansion postponement. -/
theorem weak_subject_reduction (hep : ExpansionPostponement P) {Γ : List (Expr S)}
    {a a' A : Expr S} (h : HasTypeR P Γ a A) (hr : Reduces a a') :
    ∃ A', Reduces A A' ∧ HasTypeR P Γ a' A' :=
  hep Γ a' A (h.toHasType.subject_reduces hr)

/-- **Correctness of types** for the reduction-only system (Poll's Open Problem 6, second half),
for every specification with expansion postponement. -/
theorem correctness_of_types (hep : ExpansionPostponement P) {Γ : List (Expr S)}
    {a A : Expr S} (h : HasTypeR P Γ a A) :
    (∃ s, A = .sort s) ∨ ∃ s, HasTypeR P Γ A (.sort s) := by
  rcases h.toHasType.regularity with hs | ⟨s, hA⟩
  · exact .inl hs
  · obtain ⟨B, hB, hR⟩ := hep Γ A (.sort s) hA
    rw [HasTypeR.sort_reduces hB] at hR
    exact .inr ⟨s, hR⟩

end HasTypeR

/-! ### An infinite hierarchy -/

namespace NatHierarchy

/-- Sorts `ℕ`, axioms `n : n+1`, rules `(m, n, n)` for `n ≤ m`. -/
def natHier : Specification ℕ where
  axioms n m := m = n + 1
  rule a b c := c = b ∧ b ≤ a

theorem natHier_functional : Functional natHier :=
  ⟨fun _ _ _ h h' => h.trans h'.symm, fun _ _ _ _ h h' => h.1.trans h'.1.symm⟩

theorem natHier_axiom_level : ∀ s t, natHier.axioms s t → id t = id s + 1 :=
  fun _ _ h => h

theorem natHier_rule_level :
    ∀ s₁ s₂ s₃, natHier.rule s₁ s₂ s₃ → id s₃ = id s₂ ∧ id s₂ ≤ id s₁ :=
  fun _ _ _ h => h

/-- `natHier` has infinitely many sorts, all of them used by axioms. -/
theorem natHier_infinite : Infinite ℕ ∧ ∀ n : ℕ, natHier.axioms n (n + 1) :=
  ⟨inferInstance, fun _ => rfl⟩

/-- `natHier` has no `Stratification`: the levels of a stratification are bounded. -/
theorem natHier_not_stratified (L : Stratification natHier) : False := by
  have h : ∀ n, n ≤ L.level n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => have := L.axiom_level n (n + 1) rfl; omega
  have := h (L.bound + 1)
  have := L.level_le (L.bound + 1)
  omega

theorem natHier_expansionPostponement : ExpansionPostponement natHier :=
  expansionPostponement_of_levels id natHier_axiom_level natHier_rule_level

theorem natHier_sd_complete {Γ : List (Expr ℕ)} {M T : Expr ℕ} (h : HasType natHier Γ M T) :
    ∃ T', HasTypeSD natHier Γ M T' ∧ Converts T' T :=
  sd_complete_of_levels natHier_functional id natHier_axiom_level natHier_rule_level h

/-- Poll's Open Problem 6 for `natHier`: weak subject reduction for `HasTypeR`. -/
theorem natHier_weak_subject_reduction {Γ : List (Expr ℕ)} {a a' A : Expr ℕ}
    (h : HasTypeR natHier Γ a A) (hr : Reduces a a') :
    ∃ A', Reduces A A' ∧ HasTypeR natHier Γ a' A' :=
  h.weak_subject_reduction natHier_expansionPostponement hr

/-- Poll's Open Problem 6 for `natHier`: correctness of types for `HasTypeR`. -/
theorem natHier_correctness_of_types {Γ : List (Expr ℕ)} {a A : Expr ℕ}
    (h : HasTypeR natHier Γ a A) :
    (∃ s, A = .sort s) ∨ ∃ s, HasTypeR natHier Γ A (.sort s) :=
  h.correctness_of_types natHier_expansionPostponement

end NatHierarchy

end PureTypeSystem
