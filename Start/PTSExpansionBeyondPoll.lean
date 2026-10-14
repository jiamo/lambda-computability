/-
**Expansion postponement beyond Poll's hypothesis.**

`W` is System U⁻ moved up one level, with an extra sort `o` at the bottom that has two types
`t` and `t'`:

* sorts `o, t, t', k, u` at levels `0, 1, 1, 2, 3`;
* axioms `o : t`, `o : t'`, `t : k`, `k : u`;
* rules `(o,o,o)`, `(t,t,t)`, `(k,t,t)`, `(k,k,k)`, `(u,k,k)`.

Results:
* `W_stratified`, hence `W_expansionPostponement` (by `expansionPostponement_of_stratification`).
* `W_not_functional`: `o : t` and `o : t'`.
* `W_hurkens_typed`: Hurkens' term, moved up one level, has type `Π x : t. x` in `W`.
* `W_not_wn`: `W` is not weakly normalizing.
* `W_closed_normal_not_o`: no closed normal term has type `o`.
* `W_type_not_wn`: the closed type `A := L o` (with `L` Hurkens' term) has type `o` and no
  normal form; so `x : A ⊢ x : A` is a judgement whose type has no normal form
  (`W_typed_type_not_wn`).  Hence `W` lies outside Poll's hypothesis (normalising types).
-/

import Start.PTSExpansionLevels
import Start.PTSRestriction

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

namespace BeyondPoll

open Hurkens

/-- The sorts of `W`. -/
inductive WSort | o | t | t' | k | u
  deriving DecidableEq, Repr

/-- System U⁻ shifted up one level, with an extra bottom sort `o` typed by both `t` and `t'`. -/
def W : Specification WSort where
  axioms a b := (a = .o ∧ b = .t) ∨ (a = .o ∧ b = .t') ∨ (a = .t ∧ b = .k) ∨ (a = .k ∧ b = .u)
  rule s₁ s₂ s₃ := s₃ = s₂ ∧
    ((s₁ = .o ∧ s₂ = .o) ∨ (s₁ = .t ∧ s₂ = .t) ∨ (s₁ = .k ∧ s₂ = .t) ∨
      (s₁ = .k ∧ s₂ = .k) ∨ (s₁ = .u ∧ s₂ = .k))

/-- Levels `o ↦ 0`, `t, t' ↦ 1`, `k ↦ 2`, `u ↦ 3`. -/
def W_stratified : Stratification W where
  level
    | .o => 0
    | .t => 1
    | .t' => 1
    | .k => 2
    | .u => 3
  bound := 3
  level_le s := by cases s <;> decide
  axiom_level a b h := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  rule_level s₁ s₂ s₃ h := by
    obtain ⟨rfl, h⟩ := h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- `W` is not functional: `o : t` and `o : t'`. -/
theorem W_not_functional : ¬ ∀ s a b, W.axioms s a → W.axioms s b → a = b := by
  intro h
  have := h .o .t .t' (Or.inl ⟨rfl, rfl⟩) (Or.inr (Or.inl ⟨rfl, rfl⟩))
  cases this

/-- The embedding of U⁻ into `W`: `∗ ↦ t`, `□ ↦ k`, `△ ↦ u`. -/
def shift : USort → WSort
  | .star => .t
  | .box => .k
  | .tri => .u

/-- Hurkens' term moved up one level. -/
def hurkensW : Expr WSort := hurkens.mapSort shift

/-- Hurkens' term moved up one level proves `Π x : t. x` in `W`. -/
theorem W_hurkens_typed : HasType W ([]) hurkensW (.pi (.sort .t) (.var 0)) := by
  have h := hurkens_typed.mapSort shift (Q := W)
    (by
      intro a b h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    (by
      intro a b c h
      obtain ⟨rfl, h⟩ := h
      refine ⟨rfl, ?_⟩
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  exact h

/-- **`W` is not weakly normalizing.** -/
theorem W_not_wn : ¬ SystemWeaklyNormalizing W := fun h =>
  not_wn_of_closed_bot W_hurkens_typed
    (h ([]) .nil hurkensW ⟨_, .inl W_hurkens_typed⟩)

/-- The closed type `L o`, with `L` Hurkens' term in `W`. -/
def typeA : Expr WSort := .app hurkensW (.sort .o)

theorem typeA_typed : HasType W ([]) typeA (.sort .o) :=
  HasType.application W_hurkens_typed (.ax (Or.inl ⟨rfl, rfl⟩))

/-- **No closed normal term has type `o`.**  No sort is typed by `o`, and the only rule with
third component `o` is `(o,o,o)`. -/
theorem W_closed_normal_not_o {N : Expr WSort} (h : HasType W ([]) N (.sort .o))
    (hn : Normal N) : False := by
  induction N with
  | var n => exact neutral_nil_untyped (.var n) h
  | sort s =>
      obtain ⟨r, hr, hc⟩ := h.generation
      obtain rfl := hc.sort_inj
      rcases hr with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  | app f a _ _ =>
      obtain ⟨s, h'⟩ | hne | ⟨A, B, h'⟩ | ⟨A, b, h'⟩ := h.normal_shape hn
      · cases h'
      · exact neutral_nil_untyped hne h
      · cases h'
      · cases h'
  | lam A b _ _ => exact h.lambda_cannot_have_sort_type
  | pi A B ihA _ =>
      obtain ⟨s₁, s₂, s₃, hA, -, hr, hc⟩ := h.generation_pi
      obtain rfl := hc.sort_inj
      obtain ⟨rfl, hr⟩ := hr
      rcases hr with ⟨rfl, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · exact ihA hA hn.pi_domain
      all_goals cases h

/-- **A well-typed closed type with no normal form.** -/
theorem W_type_not_wn : HasType W ([]) typeA (.sort .o) ∧ ¬ WeaklyNormalizing typeA := by
  refine ⟨typeA_typed, ?_⟩
  rintro ⟨N, hr, hn⟩
  exact W_closed_normal_not_o (typeA_typed.subject_reduces hr) hn

theorem typeA_rename : typeA.rename Nat.succ = typeA := by decide +kernel

/-- **`W` has a typing judgement whose type has no normal form**: `x : A ⊢ x : A`.  So `W` does
not have normalising types, and lies outside the hypothesis of Poll's theorem. -/
theorem W_typed_type_not_wn :
    ∃ Γ a T, HasType W Γ a T ∧ ¬ WeaklyNormalizing T := by
  refine ⟨[typeA], .var 0, typeA, ?_, W_type_not_wn.2⟩
  have h := HasType.var typeA_typed
  rwa [typeA_rename] at h

/-- **Expansion postponement holds for `W`.** -/
theorem W_expansionPostponement : ExpansionPostponement W :=
  expansionPostponement_of_stratification W_stratified

/-- **`W` is in the stratified class**, is not weakly normalizing, and is not functional
(hence not injective in any sense that implies functionality). -/
theorem W_in_class : Nonempty (Stratification W) ∧ ¬ SystemWeaklyNormalizing W ∧
    ¬ (∀ s a b, W.axioms s a → W.axioms s b → a = b) :=
  ⟨⟨W_stratified⟩, W_not_wn, W_not_functional⟩

/-! ### A Stage C test case: `W` with the dependent rule `(o, t, t)` -/

/-- `W` plus the dependent rule `(o, t, t)`: a dependent, non-normalizing system. -/
def Wdep : Specification WSort where
  axioms := W.axioms
  rule s₁ s₂ s₃ := W.rule s₁ s₂ s₃ ∨ (s₁ = .o ∧ s₂ = .t ∧ s₃ = .t)

/-- `Wdep` is not stratified. -/
theorem Wdep_not_stratified (L : Stratification Wdep) : False :=
  not_stratified_of_dependent_rule (P := Wdep) (s := .o) (t := .t) (r := .t)
    (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl, rfl⟩) L

/-- `Wdep` is not weakly normalizing. -/
theorem Wdep_not_wn : ¬ SystemWeaklyNormalizing Wdep := fun h =>
  have hL : HasType Wdep ([]) hurkensW (.pi (.sort .t) (.var 0)) :=
    W_hurkens_typed.monotone (fun _ _ h => h) (fun _ _ _ h => Or.inl h)
  not_wn_of_closed_bot hL (h ([]) .nil hurkensW ⟨_, .inl hL⟩)

end BeyondPoll

end PureTypeSystem
