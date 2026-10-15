/-
**Functionality is necessary for completeness of Pollack's syntax-directed system, even with
expansion postponement (M29-SD-FUNCTIONAL).**

* `HasTypeSD.sort_inv`: in the syntax-directed system a sort is typed only by an axiom.
* `NonFunctional.F`: sorts `o, a, a', b, b'` (levels `0, 1, 1, 2, 2`), axioms `o : a`, `o : a'`,
  `a : b`, `a' : b'`, rules `(b, a, a)` and `(b', b', b')`.  It has finitely many sorts, a
  `Stratification` (`F_stratified`), hence expansion postponement (`F_expansionPostponement`),
  and it is not functional (`F_not_functional`).
* `F_hasType`: in the context `z : a', x : (λy:a'. o) z`, the term `λw:a. x` has type `Πw:a. o`.
* `F_not_sd`: it has no syntax-directed type at all.
* `sd_incomplete_stratified`: the packaged statement.
-/

import Start.PTSSyntaxDirected

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

universe u

namespace HasTypeSD

variable {S : Type u} {P : Specification S}

/-- A sort is typed in the syntax-directed system only by an axiom. -/
theorem sort_inv {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeSD P Γ M T) :
    ∀ t, M = .sort t → ∃ t', T = .sort t' ∧ P.axioms t t' := by
  induction h with
  | ax h => intro t heq; cases heq; exact ⟨_, rfl, h⟩
  | var => intro t heq; cases heq
  | weaken_var => intro t heq; cases heq
  | weaken_sort _ _ _ ih _ =>
      intro t heq
      cases heq
      obtain ⟨t', rfl, h⟩ := ih _ rfl
      exact ⟨t', rfl, h⟩
  | product => intro t heq; cases heq
  | abstraction => intro t heq; cases heq
  | application => intro t heq; cases heq

end HasTypeSD

theorem WhReduces.pi_eq {S : Type u} {A B X : Expr S} (h : WhReduces (.pi A B) X) :
    X = .pi A B := by
  unfold WhReduces at h
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; cases hs

namespace NonFunctional

inductive FSort | o | a | a' | b | b'
  deriving DecidableEq, Repr

open FSort

def F : Specification FSort where
  axioms s t := (s = .o ∧ t = .a) ∨ (s = .o ∧ t = .a') ∨ (s = .a ∧ t = .b) ∨ (s = .a' ∧ t = .b')
  rule s₁ s₂ s₃ := (s₁ = .b ∧ s₂ = .a ∧ s₃ = .a) ∨ (s₁ = .b' ∧ s₂ = .b' ∧ s₃ = .b')

/-- `(λy:a'. o) z` -/
def R : Expr FSort := .app (.lam (.sort .a') (.sort .o)) (.var 0)
/-- `z : a', x : R` (newest first). -/
def Γ : List (Expr FSort) := [R, .sort .a']
/-- `λw:a. x` -/
def M : Expr FSort := .lam (.sort .a) (.var 1)
/-- `Πw:a. o` -/
def A : Expr FSort := .pi (.sort .a) (.sort .o)

def level : FSort → ℕ
  | .o => 0
  | .a => 1
  | .a' => 1
  | .b => 2
  | .b' => 2

def F_stratified : Stratification F where
  level := level
  bound := 2
  level_le s := by cases s <;> decide
  axiom_level s t h := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  rule_level s₁ s₂ s₃ h := by
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide

theorem F_expansionPostponement : ExpansionPostponement F :=
  expansionPostponement_of_stratification F_stratified

theorem F_not_functional : ¬ Functional F := by
  intro h
  have := h.1 .o .a .a' (Or.inl ⟨rfl, rfl⟩) (Or.inr (Or.inl ⟨rfl, rfl⟩))
  cases this

def toFin : FSort → Fin 5
  | .o => 0
  | .a => 1
  | .a' => 2
  | .b => 3
  | .b' => 4

theorem F_finite : Finite FSort :=
  Finite.of_injective toFin (by intro x y h; cases x <;> cases y <;> first | rfl | cases h)

theorem ax_oa : F.axioms .o .a := Or.inl ⟨rfl, rfl⟩
theorem ax_oa' : F.axioms .o .a' := Or.inr (Or.inl ⟨rfl, rfl⟩)
theorem ax_ab : F.axioms .a .b := Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
theorem ax_a'b' : F.axioms .a' .b' := Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

/-- `[a']` -/
abbrev c1 : List (Expr FSort) := Expr.sort FSort.a' :: List.nil
/-- `[a', a']` -/
abbrev c2 : List (Expr FSort) := Expr.sort FSort.a' :: c1

theorem F_hasType : HasType F Γ M A := by
  -- `z : a'`
  have h1 : HasType F ([]) (.sort .a') (.sort .b') := .ax ax_a'b'
  -- in context `[a']`
  have h2 : HasType F c1 (.sort .a') (.sort .b') := .weaken h1 h1
  have h3 : HasType F c2 (.sort .a') (.sort .b') := .weaken h2 h2
  have ho : HasType F ([]) (.sort .o) (.sort .a') := .ax ax_oa'
  have ho1 : HasType F c1 (.sort .o) (.sort .a') := .weaken ho h1
  have ho2 : HasType F c2 (.sort .o) (.sort .a') := .weaken ho1 h2
  have hpi : HasType F c1 (.pi (.sort .a') (.sort .a')) (.sort .b') :=
    .product h2 h3 (Or.inr ⟨rfl, rfl, rfl⟩)
  have hlam : HasType F c1 (.lam (.sort .a') (.sort .o)) (.pi (.sort .a') (.sort .a')) :=
    .abstraction ho2 hpi
  have hz : HasType F c1 (.var 0) (.sort .a') := .var h1
  have hR : HasType F c1 R (.sort .a') := .application hlam hz
  -- in context `Γ`
  have hxR : HasType F Γ (.var 0) (R.rename Nat.succ) := .var hR
  have hoa : HasType F c1 (.sort .o) (.sort .a) := .weaken (.ax ax_oa) h1
  have hoaΓ : HasType F Γ (.sort .o) (.sort .a) := .weaken hoa hR
  have hconv : Converts (R.rename Nat.succ) (.sort .o : Expr FSort) :=
    .rel _ _ (Beta.head _ _ _)
  have hx : HasType F Γ (.var 0) (.sort .o) := .conversion hxR hoaΓ hconv
  have ha : HasType F Γ (.sort .a) (.sort .b) := .weaken (.weaken (.ax ax_ab) h1) hR
  have hx1 : HasType F (.sort .a :: Γ) (.var 1) (.sort .o) := .weaken hx ha
  have hoa2 : HasType F (.sort .a :: Γ) (.sort .o) (.sort .a) := .weaken hoaΓ ha
  have hpiA : HasType F Γ A (.sort .a) := .product ha hoa2 (Or.inl ⟨rfl, rfl, rfl⟩)
  exact .abstraction hx1 hpiA

theorem sort_eq_of_reduces {s t : FSort} (h : Reduces (.sort s : Expr FSort) (.sort t)) : t = s := by
  have := HasTypeR.sort_reduces h
  cases this
  rfl

/-- The judgement `F_hasType` has no syntax-directed derivation, at any type. -/
theorem F_not_sd : ¬ ∃ T, HasTypeSD F Γ M T := by
  rintro ⟨T, h⟩
  unfold M Γ at h
  cases h with
  | abstraction hb hpi hs =>
    cases hb with
    | weaken_var hv _ _ =>
      cases hv with
      | var _ _ =>
        simp only [R, Expr.rename] at hpi
        cases hpi with
        | @product _ _ _ _ _ s₁ s₂ s₃ hA hTA hB hTB hrule =>
          obtain ⟨t₁, rfl, h₁⟩ := hA.sort_inv _ rfl
          obtain rfl : t₁ = .b := by
            rcases h₁ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ <;> first | exact h | cases h
          obtain rfl : s₁ = .b := sort_eq_of_reduces hTA
          obtain rfl : s₂ = .a := by
            rcases hrule with ⟨-, h, -⟩ | ⟨h, -⟩ <;> first | exact h | cases h
          cases hB with
          | application hf hw harg hc =>
            cases hf with
            | abstraction hbody hpi2 hs2 =>
              obtain ⟨t, rfl, ht⟩ := hbody.sort_inv _ rfl
              obtain ⟨rfl, rfl⟩ := Expr.pi.inj (WhReduces.pi_eq hw)
              obtain rfl := sort_eq_of_reduces hTB
              cases hpi2 with
              | product hA2 hTA2 hB2 hTB2 hrule2 =>
                obtain ⟨u, rfl, hu⟩ := hA2.sort_inv _ rfl
                obtain ⟨v, rfl, hv⟩ := hB2.sort_inv _ rfl
                obtain rfl := sort_eq_of_reduces hTA2
                obtain rfl := sort_eq_of_reduces hTB2
                rcases hv with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨h, -⟩ <;> try cases h
                rcases hrule2 with ⟨h, -⟩ | ⟨-, h, -⟩ <;> cases h
                rcases hu with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ <;> cases h

/-- The reduction-only system types the same judgement (at a reduct of `Πw:a. o`, which is
normal, hence at `Πw:a. o` itself). -/
theorem F_hasTypeR : HasTypeR F Γ M A := by
  obtain ⟨B, hB, hR⟩ := F_expansionPostponement Γ M A F_hasType
  have hn : Normal A := by
    intro N h
    cases h with
    | pi_domain h => cases h
    | pi_body h => cases h
  rwa [← hn.reduces_eq hB] at hR

/-- **Pollack's syntax-directed system is incomplete for a stratified non-functional PTS.**
`F` has finitely many sorts and a `Stratification`; the judgement `Γ ⊢ λw:a. x : Πw:a. o` is
derivable, but `λw:a. x` has no syntax-directed type in `Γ`. -/
theorem sd_incomplete_stratified :
    Finite FSort ∧ Nonempty (Stratification F) ∧ HasType F Γ M A ∧
      ¬ ∃ T, HasTypeSD F Γ M T :=
  ⟨F_finite, ⟨F_stratified⟩, F_hasType, F_not_sd⟩

/-- Consequence: expansion postponement does not imply completeness of `HasTypeSD`. -/
theorem sd_complete_not_of_expansionPostponement :
    ¬ ∀ (P : Specification FSort), ExpansionPostponement P →
      ∀ Γ M A, HasType P Γ M A → ∃ T, HasTypeSD P Γ M T :=
  fun h => F_not_sd (h F F_expansionPostponement Γ M A F_hasType)

end NonFunctional

end PureTypeSystem
