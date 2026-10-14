/-
**Expansion postponement for stratified pure type systems.**

A `Stratification P` assigns to every sort a level in `0, …, bound`, such that every axiom
`s : t` goes up exactly one level and every rule `(s₁, s₂, s₃)` has `s₃` at the level of `s₂`
and `s₂` not above `s₁` (no dependent products).

* `Stratification.TypeLevel Γ T k`: `T` is a type whose inhabitants live at level `k`, i.e.
  either `T` is a sort `t` with `k = level t + 1`, or `Γ ⊢ T : s` with `level s = k`.
* `Stratification.level_unique`: the level of the types of a term is unique.
* `Stratification.conv_level`: convertible types have the same level.
* `Stratification.core`: in a context valid for the reduction-only system, every judgement
  `Γ ⊢ M : T` gives `Γ ⊢R M : T'` for some reduct `T'` of `T`.  The proof is a well-founded
  induction on `(bound + 2 − level, M)`, lexicographically; the only call on a subject that is not
  a subterm is the call on `Π A B'` in the abstraction case, and it is one level higher.
* `expansionPostponement_of_stratification`: expansion postponement for every stratified
  specification.  No normalization hypothesis.
* `uMinus_stratified`: System U⁻ is stratified.
* `cube_stratified`, `cube_expansionPostponement`: the cube corners without the rule `(∗,□)`
  (`λ→`, `λ2`, `λω̲`, `λω`) are stratified.  `cube_not_stratified`: the corners with `(∗,□)`
  are not.  `lambdaStar_not_stratified`: `λ*` (`∗ : ∗`) is not.
-/

import Start.PTSExpansion
import Start.PTSHurkens

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

universe u

/-- Bounded levels for the sorts of a specification: axioms go up exactly one level, and no
product has its codomain above its domain. -/
structure Stratification {S : Type u} (P : Specification S) where
  level : S → ℕ
  bound : ℕ
  level_le : ∀ s, level s ≤ bound
  axiom_level : ∀ s t, P.axioms s t → level t = level s + 1
  rule_level : ∀ s₁ s₂ s₃, P.rule s₁ s₂ s₃ → level s₃ = level s₂ ∧ level s₂ ≤ level s₁

section Aux

variable {S : Type u} {P : Specification S}

theorem Converts.reduces_sort {T : Expr S} {t : S} (hc : Converts T (.sort t)) :
    Reduces T (.sort t) := by
  obtain ⟨K, h1, h2⟩ := hc.join
  rw [HasTypeR.sort_reduces h2] at h1
  exact h1

theorem HasType.axiom_of_sort {Γ : List (Expr S)} {t s : S}
    (h : HasType P Γ (.sort t) (.sort s)) : P.axioms t s := by
  obtain ⟨r, hr, hc⟩ := h.generation
  obtain rfl := hc.sort_inj
  exact hr

theorem HasTypeR.close {Γ : List (Expr S)} {M T U : Expr S} (hc : Converts T U)
    (h : HasTypeR P Γ M U) : ∃ T', Reduces T T' ∧ HasTypeR P Γ M T' := by
  obtain ⟨K, h1, h2⟩ := hc.join
  exact ⟨K, h1, h.reduces h2⟩

end Aux

namespace Stratification

variable {S : Type u} {P : Specification S} (L : Stratification P)

/-- `T` is a type at level `k`: a sort `t` with `level t + 1 = k`, or a type of sort level `k`. -/
def TypeLevel (Γ : List (Expr S)) (T : Expr S) (k : ℕ) : Prop :=
  (∃ t, T = .sort t ∧ L.level t + 1 = k) ∨ (∃ s, HasType P Γ T (.sort s) ∧ L.level s = k)

variable {L}

theorem TypeLevel.le {Γ : List (Expr S)} {T : Expr S} {k : ℕ} (h : L.TypeLevel Γ T k) :
    k ≤ L.bound + 1 := by
  rcases h with ⟨t, -, rfl⟩ | ⟨s, -, rfl⟩
  · have := L.level_le t; omega
  · have := L.level_le s; omega

variable (L) in
theorem TypeLevel.sort (Γ : List (Expr S)) (t : S) : L.TypeLevel Γ (.sort t) (L.level t + 1) :=
  .inl ⟨t, rfl, rfl⟩

/-- Convertible types have the same level, given uniqueness of sort levels at the level of the
first type. -/
theorem conv_level_of {Γ : List (Expr S)} {T T' : Expr S} {k k' : ℕ}
    (hU : ∀ (C : Expr S) (s s' : S), HasType P Γ C (.sort s) → HasType P Γ C (.sort s') →
      L.level s = k → L.level s = L.level s')
    (hc : Converts T T') (hT : L.TypeLevel Γ T k) (hT' : L.TypeLevel Γ T' k') : k = k' := by
  rcases hT with ⟨t, rfl, rfl⟩ | ⟨s, hs, rfl⟩ <;>
    rcases hT' with ⟨t', rfl, rfl⟩ | ⟨s', hs', rfl⟩
  · obtain rfl := hc.sort_inj
    rfl
  · have h := hs'.subject_reduces (Converts.reduces_sort (.symm _ _ hc))
    exact (L.axiom_level _ _ h.axiom_of_sort).symm
  · have h := hs.subject_reduces (Converts.reduces_sort hc)
    exact L.axiom_level _ _ h.axiom_of_sort
  · obtain ⟨C, h1, h2⟩ := hc.join
    exact hU C s s' (hs.subject_reduces h1) (hs'.subject_reduces h2) rfl

theorem level_unique_aux (n : ℕ) : ∀ (M : Expr S) (Γ : List (Expr S)) (T T' : Expr S)
    (k k' : ℕ), L.bound + 2 - k ≤ n → HasType P Γ M T → HasType P Γ M T' →
    L.TypeLevel Γ T k → L.TypeLevel Γ T' k' → k = k' := by
  induction n with
  | zero =>
      intro M Γ T T' k k' hn _ _ hT _
      have := hT.le
      omega
  | succ n ihn =>
      have hconv : ∀ (Γ : List (Expr S)) (T T' : Expr S) (k k' : ℕ),
          L.bound + 2 - k ≤ n + 1 → Converts T T' → L.TypeLevel Γ T k →
          L.TypeLevel Γ T' k' → k = k' := by
        intro Γ T T' k k' hn hc hT hT'
        refine conv_level_of (fun C s s' hs hs' hsk => ?_) hc hT hT'
        have := ihn C Γ _ _ _ _ (by omega) hs hs' (TypeLevel.sort L Γ s)
          (TypeLevel.sort L Γ s')
        omega
      intro M
      induction M with
      | var m =>
          intro Γ T T' k k' hn ht ht' hT hT'
          obtain ⟨A, hA, hc⟩ := ht.generation
          obtain ⟨A', hA', hc'⟩ := ht'.generation
          obtain rfl := hA.unique hA'
          exact hconv Γ T T' k k' hn (.trans _ _ _ hc (.symm _ _ hc')) hT hT'
      | sort t =>
          intro Γ T T' k k' hn ht ht' hT hT'
          obtain ⟨r, hr, hc⟩ := ht.generation
          obtain ⟨r', hr', hc'⟩ := ht'.generation
          have h1 := hconv Γ T _ k _ hn hc hT (TypeLevel.sort L Γ r)
          have e1 := L.axiom_level _ _ hr
          have e2 := L.axiom_level _ _ hr'
          have h2 := hconv Γ _ T' _ k' (by omega) (.symm _ _ hc') (TypeLevel.sort L Γ r') hT'
          omega
      | app f a ihf _ =>
          intro Γ T T' k k' hn ht ht' hT hT'
          obtain ⟨D, E, hf, ha, hc⟩ := ht.generation_app
          obtain ⟨D', E', hf', ha', hc'⟩ := ht'.generation_app
          obtain ⟨r, hPi⟩ := hf.product_type_sorted
          obtain ⟨r', hPi'⟩ := hf'.product_type_sorted
          obtain ⟨r₁, r₂, r₃, -, hE, hr, hrc⟩ := hPi.generation_pi
          obtain ⟨r₁', r₂', r₃', -, hE', hr', hrc'⟩ := hPi'.generation_pi
          obtain rfl := hrc.sort_inj
          obtain rfl := hrc'.sort_inj
          have l1 := L.rule_level _ _ _ hr
          have l2 := L.rule_level _ _ _ hr'
          have hEa : HasType P Γ (E.instantiate a) (.sort r₂) := hE.instantiate ha
          have hEa' : HasType P Γ (E'.instantiate a) (.sort r₂') := hE'.instantiate ha'
          have h1 := hconv Γ T _ k _ hn hc hT (.inr ⟨r₂, hEa, rfl⟩)
          have h2 := ihf Γ _ _ _ _ (by omega) hf hf' (.inr ⟨r, hPi, rfl⟩)
            (.inr ⟨r', hPi', rfl⟩)
          have h3 := hconv Γ _ T' _ k' (by omega) (.symm _ _ hc') (.inr ⟨r₂', hEa', rfl⟩) hT'
          omega
      | lam A b _ ihb =>
          intro Γ T T' k k' hn ht ht' hT hT'
          obtain ⟨B, s, hb, hPi, hc⟩ := ht.generation_lam
          obtain ⟨B', s', hb', hPi', hc'⟩ := ht'.generation_lam
          obtain ⟨s₁, s₂, s₃, -, hB, hr, hsc⟩ := hPi.generation_pi
          obtain ⟨s₁', s₂', s₃', -, hB', hr', hsc'⟩ := hPi'.generation_pi
          obtain rfl := hsc.sort_inj
          obtain rfl := hsc'.sort_inj
          have l1 := L.rule_level _ _ _ hr
          have l2 := L.rule_level _ _ _ hr'
          have h1 := hconv Γ T _ k _ hn hc hT (.inr ⟨_, hPi, rfl⟩)
          have h2 := ihb (A :: Γ) _ _ _ _ (by omega) hb hb' (.inr ⟨s₂, hB, rfl⟩)
            (.inr ⟨s₂', hB', rfl⟩)
          have h3 := hconv Γ _ T' _ k' (by omega) (.symm _ _ hc') (.inr ⟨_, hPi', rfl⟩) hT'
          omega
      | pi A B _ ihB =>
          intro Γ T T' k k' hn ht ht' hT hT'
          obtain ⟨s₁, s₂, s₃, -, hB, hr, hc⟩ := ht.generation_pi
          obtain ⟨s₁', s₂', s₃', -, hB', hr', hc'⟩ := ht'.generation_pi
          have l1 := L.rule_level _ _ _ hr
          have l2 := L.rule_level _ _ _ hr'
          have h1 := hconv Γ T _ k _ hn hc hT (TypeLevel.sort L Γ s₃)
          have h2 := ihB (A :: Γ) _ _ _ _ (by omega) hB hB' (TypeLevel.sort L _ s₂)
            (TypeLevel.sort L _ s₂')
          have h3 := hconv Γ _ T' _ k' (by omega) (.symm _ _ hc') (TypeLevel.sort L Γ s₃') hT'
          omega

/-- **Uniqueness of levels.**  All types of a term have the same level. -/
theorem level_unique {Γ : List (Expr S)} {M T T' : Expr S} {k k' : ℕ}
    (ht : HasType P Γ M T) (ht' : HasType P Γ M T') (hT : L.TypeLevel Γ T k)
    (hT' : L.TypeLevel Γ T' k') : k = k' :=
  level_unique_aux (L.bound + 2) M Γ T T' k k' (by omega) ht ht' hT hT'

/-- **Convertible types have the same level.** -/
theorem conv_level {Γ : List (Expr S)} {T T' : Expr S} {k k' : ℕ}
    (hc : Converts T T') (hT : L.TypeLevel Γ T k) (hT' : L.TypeLevel Γ T' k') : k = k' := by
  refine conv_level_of (fun C s s' hs hs' _ => ?_) hc hT hT'
  have := level_unique hs hs' (TypeLevel.sort L Γ s) (TypeLevel.sort L Γ s')
  omega

theorem core_aux (n : ℕ) : ∀ (M : Expr S) (Γ : List (Expr S)) (T : Expr S) (k : ℕ),
    L.bound + 2 - k ≤ n → ValidContextR P Γ → HasType P Γ M T → L.TypeLevel Γ T k →
    ∃ T', Reduces T T' ∧ HasTypeR P Γ M T' := by
  induction n with
  | zero =>
      intro M Γ T k hn _ _ hT
      have := hT.le
      omega
  | succ n ihn =>
      intro M
      induction M with
      | var m =>
          intro Γ T k _ hΓ ht _
          obtain ⟨A, hA, hc⟩ := ht.generation
          exact HasTypeR.close hc (HasTypeR.lookup hΓ hA)
      | sort t =>
          intro Γ T k _ hΓ ht _
          obtain ⟨r, hr, hc⟩ := ht.generation
          exact HasTypeR.close hc (HasTypeR.sort_of_valid hΓ hr)
      | pi A B ihA ihB =>
          intro Γ T k hn hΓ ht hT
          obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := ht.generation_pi
          have l := L.rule_level _ _ _ hr
          have hk := conv_level hc hT (TypeLevel.sort L Γ s₃)
          obtain ⟨T₁, hT₁, hA'⟩ := ihA Γ _ _ (by omega) hΓ hA (TypeLevel.sort L Γ s₁)
          rw [HasTypeR.sort_reduces hT₁] at hA'
          obtain ⟨T₂, hT₂, hB'⟩ := ihB (A :: Γ) _ _ (by omega) (.cons hΓ hA') hB
            (TypeLevel.sort L _ s₂)
          rw [HasTypeR.sort_reduces hT₂] at hB'
          exact HasTypeR.close hc (.product hA' hB' hr)
      | app f a ihf iha =>
          intro Γ T k hn hΓ ht hT
          obtain ⟨D, E, hf, ha, hc⟩ := ht.generation_app
          obtain ⟨r, hPi⟩ := hf.product_type_sorted
          obtain ⟨r₁, r₂, r₃, hD, hE, hr, hrc⟩ := hPi.generation_pi
          obtain rfl := hrc.sort_inj
          have l := L.rule_level _ _ _ hr
          have hEa : HasType P Γ (E.instantiate a) (.sort r₂) := hE.instantiate ha
          have hk := conv_level hc hT (.inr ⟨r₂, hEa, rfl⟩)
          obtain ⟨F, hF, hf'⟩ := ihf Γ _ _ (by omega) hΓ hf (.inr ⟨_, hPi, rfl⟩)
          obtain ⟨D₂, hD₂, ha'⟩ := iha Γ _ _ (by omega) hΓ ha (.inr ⟨r₁, hD, rfl⟩)
          obtain ⟨D₁, E₁, rfl, hD₁, hE₁⟩ := Reduces.pi_inv hF
          obtain ⟨G, hG₁, hG₂⟩ := Reduces.confluent hD₁ hD₂
          have happ := HasTypeR.application (hf'.reduces (Reduces.pi hG₁ .refl))
            (ha'.reduces hG₂)
          exact HasTypeR.close
            (.trans _ _ _ hc (Reduces.converts (Reduces.subst hE₁ (Expr.single a)))) happ
      | lam A b ihA ihb =>
          intro Γ T k hn hΓ ht hT
          obtain ⟨B, s, hb, hPi, hc⟩ := ht.generation_lam
          obtain ⟨s₁, s₂, s₃, hA, hB, hr, hsc⟩ := hPi.generation_pi
          obtain rfl := hsc.sort_inj
          have l := L.rule_level _ _ _ hr
          have hk := conv_level hc hT (.inr ⟨_, hPi, rfl⟩)
          have hs := L.level_le s
          obtain ⟨T₁, hT₁, hA'⟩ := ihA Γ _ _ (by omega) hΓ hA (TypeLevel.sort L Γ s₁)
          rw [HasTypeR.sort_reduces hT₁] at hA'
          obtain ⟨B', hBB', hb'⟩ := ihb (A :: Γ) _ _ (by omega) (.cons hΓ hA') hb
            (.inr ⟨s₂, hB, rfl⟩)
          have hred : Reduces (Expr.pi A B) (Expr.pi A B') := Reduces.pi .refl hBB'
          have hPi' := hPi.subject_reduces hred
          obtain ⟨U, hU, hPiR⟩ := ihn _ Γ _ _ (by omega) hΓ hPi' (TypeLevel.sort L Γ s)
          rw [HasTypeR.sort_reduces hU] at hPiR
          exact HasTypeR.close (.trans _ _ _ hc (Reduces.converts hred))
            (.abstraction hb' hPiR)

/-- **Core lemma.**  In a context that is valid for the reduction-only system, every typing
judgement has a reduction-only derivation at a reduct of its type. -/
theorem core (L : Stratification P) {Γ : List (Expr S)} {M T : Expr S} (hΓ : ValidContextR P Γ)
    (h : HasType P Γ M T) : ∃ T', Reduces T T' ∧ HasTypeR P Γ M T' := by
  obtain ⟨t, rfl⟩ | ⟨s, hs⟩ := h.regularity
  · exact core_aux (L := L) (L.bound + 2) M Γ _ _ (by omega) hΓ h (TypeLevel.sort L Γ t)
  · exact core_aux (L := L) (L.bound + 2) M Γ _ _ (by omega) hΓ h (.inr ⟨s, hs, rfl⟩)

theorem validContextR (L : Stratification P) {Γ : List (Expr S)} (hΓ : ValidContext P Γ) : ValidContextR P Γ := by
  induction hΓ with
  | nil => exact .nil
  | cons _ hA ih =>
      obtain ⟨U, hU, hA'⟩ := core L ih hA
      rw [HasTypeR.sort_reduces hU] at hA'
      exact .cons ih hA'

end Stratification

/-- **Expansion postponement for stratified specifications.**  If the sorts carry bounded levels,
axioms go up exactly one level and no product has its codomain above its domain, then every
typing judgement has a derivation without expansion steps at a reduct of its type.  No
normalization hypothesis. -/
theorem expansionPostponement_of_stratification {S : Type u} {P : Specification S}
    (L : Stratification P) : ExpansionPostponement P := by
  intro Γ M A h
  exact Stratification.core L (Stratification.validContextR L h.valid) h

namespace Hurkens

/-- System U⁻ is stratified: `∗ ↦ 0`, `□ ↦ 1`, `△ ↦ 2`. -/
def uMinus_stratified : Stratification uMinus where
  level
    | .star => 0
    | .box => 1
    | .tri => 2
  bound := 2
  level_le s := by cases s <;> decide
  axiom_level s t h := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  rule_level s₁ s₂ s₃ h := by
    obtain ⟨rfl, h⟩ := h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Expansion postponement holds for System U⁻. -/
theorem uMinus_expansionPostponement : ExpansionPostponement uMinus :=
  expansionPostponement_of_stratification uMinus_stratified

end Hurkens

/-! ### Which standard systems are stratified -/

section Examples

/-- The cube corners without dependent types (`λ→`, `λ2`, `λω̲`, `λω`) are stratified:
`∗ ↦ 0`, `□ ↦ 1`. -/
def cube_stratified (f : CubeFeatures) (hf : f.dep = false) : Stratification (cubeSpec f) where
  level
    | .star => 0
    | .box => 1
  bound := 1
  level_le s := by cases s <;> decide
  axiom_level a b h := by
    obtain ⟨rfl, rfl⟩ := h
    rfl
  rule_level s₁ s₂ s₃ h := by
    obtain ⟨h1, h⟩ := h
    subst h1
    cases s₁ <;> cases s₃ <;> simp_all [CubeFeatures.allows]

/-- Expansion postponement for the four cube corners without dependent types. -/
theorem cube_expansionPostponement (f : CubeFeatures) (hf : f.dep = false) :
    ExpansionPostponement (cubeSpec f) :=
  expansionPostponement_of_stratification (cube_stratified f hf)

/-- A specification with an axiom `s : t` and a rule `(s, t, r)` is not stratified. -/
theorem not_stratified_of_dependent_rule {S : Type u} {P : Specification S} {s t r : S}
    (hst : P.axioms s t) (hr : P.rule s t r) (L : Stratification P) : False := by
  have h1 := L.axiom_level _ _ hst
  have h2 := (L.rule_level _ _ _ hr).2
  omega

/-- A specification with an axiom `s : s` is not stratified. -/
theorem not_stratified_of_axiom_self {S : Type u} {P : Specification S} {s : S}
    (hs : P.axioms s s) (L : Stratification P) : False := by
  have := L.axiom_level _ _ hs
  omega

/-- The cube corners with dependent types (`λP`, `λP2`, `λPω̲`, `λC`) are not stratified,
because of the rule `(∗, □)`. -/
theorem cube_not_stratified (f : CubeFeatures) (hf : f.dep = true)
    (L : Stratification (cubeSpec f)) : False :=
  not_stratified_of_dependent_rule (P := cubeSpec f) (s := .star) (t := .box) (r := .box)
    ⟨rfl, rfl⟩ ⟨rfl, hf⟩ L

/-- `λ*`: one sort `∗`, axiom `∗ : ∗`, rule `(∗, ∗, ∗)`. -/
def lambdaStar : Specification Unit where
  axioms _ _ := True
  rule _ _ _ := True

/-- `λ*` is not stratified. -/
theorem lambdaStar_not_stratified (L : Stratification lambdaStar) : False :=
  not_stratified_of_axiom_self (P := lambdaStar) (s := ()) trivial L

end Examples

end PureTypeSystem
