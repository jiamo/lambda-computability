/-
**Expansion postponement for pure type systems (TLCA open problem 23): the statement.**

* `HasTypeR P Γ M A`: the typing rules of `HasType` (`Start/PTSBasic.lean`) with the conversion
  rule replaced by one-step beta-reduction of the type (rule `reduction`).
* `ExpansionPostponement P`: every `HasType` judgement `Γ ⊢ M : A` has a reduction-only derivation
  `Γ ⊢R M : B` at some reduct `B` of `A`.
* `HasTypeR.toHasType`: soundness of the reduction-only system.
* Metatheory of `HasTypeR`: validity of contexts, typed substitution (`HasTypeR.subst`,
  `HasTypeR.instantiate`, `HasTypeR.weaken_under`) and generation for products and abstractions.
* `expansionPostponement_iff_sortedSubjectReductionR`: for every specification, expansion
  postponement is equivalent to closure of `HasTypeR` under one-step reduction of a subject typed
  by a sort.

Poll's theorem (expansion postponement for normalizing specifications) is not proved here; see
`docs/goal/evidence/M29-EP.md` for the missing lemma.
-/

import Start.PTSTyping
import Start.PTSNormalization

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

universe u

/-- Typing with the conversion rule replaced by beta-reduction of the type. -/
inductive HasTypeR {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Prop
  | ax {s t} : P.axioms s t → HasTypeR P [] (.sort s) (.sort t)
  | var {Γ A s} : HasTypeR P Γ A (.sort s) →
      HasTypeR P (A :: Γ) (.var 0) (A.rename Nat.succ)
  | weaken {Γ M B A s} : HasTypeR P Γ M B → HasTypeR P Γ A (.sort s) →
      HasTypeR P (A :: Γ) (M.rename Nat.succ) (B.rename Nat.succ)
  | product {Γ A B s₁ s₂ s₃} : HasTypeR P Γ A (.sort s₁) →
      HasTypeR P (A :: Γ) B (.sort s₂) → P.rule s₁ s₂ s₃ →
      HasTypeR P Γ (.pi A B) (.sort s₃)
  | abstraction {Γ A b B s} : HasTypeR P (A :: Γ) b B →
      HasTypeR P Γ (.pi A B) (.sort s) →
      HasTypeR P Γ (.lam A b) (.pi A B)
  | application {Γ f a A B} : HasTypeR P Γ f (.pi A B) →
      HasTypeR P Γ a A → HasTypeR P Γ (.app f a) (B.instantiate a)
  | reduction {Γ M A B} : HasTypeR P Γ M A → Beta A B → HasTypeR P Γ M B

/-- Expansion postponement (TLCA open problem 23): every typing judgement has a derivation
without expansion steps, at a reduct of the type. -/
def ExpansionPostponement {S : Type u} (P : Specification S) : Prop :=
  ∀ Γ M A, HasType P Γ M A →
    ∃ B, Relation.ReflTransGen Beta A B ∧ HasTypeR P Γ M B

/-- Contexts whose declarations are typed by sorts in the reduction-only system. -/
inductive ValidContextR {S : Type u} (P : Specification S) : List (Expr S) → Prop
  | nil : ValidContextR P []
  | cons {Γ A s} : ValidContextR P Γ → HasTypeR P Γ A (.sort s) →
      ValidContextR P (A :: Γ)

namespace HasTypeR

variable {S : Type u} {P : Specification S}

/-- Soundness: the reduction-only system derives only `HasType` judgements. -/
theorem toHasType {Γ : List (Expr S)} {M A : Expr S} (h : HasTypeR P Γ M A) :
    HasType P Γ M A := by
  induction h with
  | ax h => exact .ax h
  | var _ ih => exact .var ih
  | weaken _ _ ihM ihA => exact .weaken ihM ihA
  | product _ _ hr ihA ihB => exact .product ihA ihB hr
  | abstraction _ _ ihb ihP => exact .abstraction ihb ihP
  | application _ _ ihf iha => exact .application ihf iha
  | @reduction Γ M A B _ hAB ih =>
      rcases ih.regularity with ⟨s, rfl⟩ | ⟨s, hA⟩
      · exact absurd hAB (Normal.sort s B)
      · exact .conversion ih (hA.subject_reduction hAB) (.rel _ _ hAB)

theorem reduces {Γ : List (Expr S)} {M A B : Expr S} (h : HasTypeR P Γ M A)
    (hr : Reduces A B) : HasTypeR P Γ M B := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact .reduction ih hs

theorem valid {Γ : List (Expr S)} {M A : Expr S} (h : HasTypeR P Γ M A) :
    ValidContextR P Γ := by
  induction h with
  | ax _ => exact .nil
  | var h ih => exact .cons ih h
  | weaken _ h _ ih => exact .cons ih h
  | product _ _ _ ih _ => exact ih
  | abstraction _ _ _ ih => exact ih
  | application _ _ ih _ => exact ih
  | reduction _ _ ih => exact ih

theorem sort_of_valid {Γ : List (Expr S)} (hΓ : ValidContextR P Γ)
    {s t : S} (hst : P.axioms s t) : HasTypeR P Γ (.sort s) (.sort t) := by
  induction hΓ with
  | nil => exact .ax hst
  | cons _ hA ih => exact .weaken ih hA

/-- A type that reduces from a sort is that sort. -/
theorem sort_reduces {s : S} {T : Expr S} (h : Reduces (.sort s) T) : T = .sort s :=
  ((Normal.sort s).reduces_eq h).symm

theorem product_domain {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeR P Γ M T) :
    ∀ A B, M = .pi A B → ∃ s, HasTypeR P Γ A (.sort s) := by
  induction h with
  | ax h => intro A B heq; cases heq
  | var h ih => intro A B heq; cases heq
  | @weaken Γ M T C s hM hC ihM ihC =>
      intro A B heq
      cases M with
      | var n => cases heq
      | sort t => cases heq
      | app f a => cases heq
      | lam D b => cases heq
      | pi D E =>
          obtain ⟨rfl, rfl⟩ := Expr.pi.inj heq
          obtain ⟨t, ht⟩ := ihM D E rfl
          exact ⟨t, .weaken ht hC⟩
  | product hA hB hr ihA ihB =>
      intro A B heq
      cases heq
      exact ⟨_, hA⟩
  | abstraction hb hT ihb ihT => intro A B heq; cases heq
  | application hf ha ihf iha => intro A B heq; cases heq
  | reduction hM hB ihM => exact ihM

end HasTypeR

/-- Exactly typed simultaneous substitution for the reduction-only system. -/
def TypedSubstitutionR {S : Type u} (P : Specification S)
    (Γ Δ : List (Expr S)) (σ : Nat → Expr S) : Prop :=
  ∀ n A, Lookup Γ n A → HasTypeR P Δ (σ n) (A.subst σ)

namespace TypedSubstitutionR

variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}
    {σ : Nat → Expr S}

theorem tail {A : Expr S} (hσ : TypedSubstitutionR P (A :: Γ) Δ σ) :
    TypedSubstitutionR P Γ Δ (σ ∘ Nat.succ) := by
  intro n B hB
  have h := hσ (n + 1) (B.rename Nat.succ) (.succ A hB)
  simpa only [Expr.subst_rename, Function.comp_def] using h

theorem lift {A : Expr S} {s : S} (hσ : TypedSubstitutionR P Γ Δ σ)
    (hA : HasTypeR P Δ (A.subst σ) (.sort s)) :
    TypedSubstitutionR P (A :: Γ) (A.subst σ :: Δ) (Expr.liftSub σ) := by
  intro n B hn
  cases hn with
  | zero =>
      have ht := HasTypeR.var hA
      simpa only [Expr.liftSub_zero, Expr.subst_rename, Expr.rename_subst,
        Expr.liftSub_succ, Function.comp_def] using ht
  | succ C hn =>
      have ht := HasTypeR.weaken (hσ _ _ hn) hA
      simpa only [Expr.liftSub_succ, Expr.rename_subst, Expr.subst_rename,
        Function.comp_def] using ht

end TypedSubstitutionR

namespace HasTypeR

variable {S : Type u} {P : Specification S}

theorem subst {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeR P Γ M T) {Δ : List (Expr S)}
    (hΔ : ValidContextR P Δ) (σ : Nat → Expr S) (hσ : TypedSubstitutionR P Γ Δ σ) :
    HasTypeR P Δ (M.subst σ) (T.subst σ) := by
  induction h generalizing Δ σ with
  | ax h => exact sort_of_valid hΔ h
  | var h ih => exact hσ _ _ (.zero _ _)
  | weaken hM hA ihM ihA =>
      simpa only [Expr.subst_rename] using ihM hΔ (σ ∘ Nat.succ) hσ.tail
  | product hA hB hr ihA ihB =>
      have hA' := ihA hΔ σ hσ
      exact .product hA' (ihB (.cons hΔ hA') _ (hσ.lift hA')) hr
  | @abstraction Γ A b B s hb hprod ihb ihprod =>
      have hprod' := ihprod hΔ σ hσ
      obtain ⟨t, hA'⟩ := hprod'.product_domain _ _ rfl
      exact .abstraction (ihb (.cons hΔ hA') _ (hσ.lift hA')) hprod'
  | application hf ha ihf iha =>
      simpa only [Expr.subst, Expr.instantiate_subst] using
        (HasTypeR.application (ihf hΔ σ hσ) (iha hΔ σ hσ))
  | reduction hM hB ihM =>
      exact .reduction (ihM hΔ σ hσ) (hB.subst σ)

theorem lookup {Γ : List (Expr S)} (hΓ : ValidContextR P Γ)
    {n : Nat} {A : Expr S} (hn : Lookup Γ n A) : HasTypeR P Γ (.var n) A := by
  induction hΓ generalizing n A with
  | nil => cases hn
  | cons hΓ hB ih =>
      cases hn with
      | zero => exact .var hB
      | succ _ hn => exact .weaken (ih hn) hB

theorem instantiate {Γ : List (Expr S)} {A b B a : Expr S}
    (hb : HasTypeR P (A :: Γ) b B) (ha : HasTypeR P Γ a A) :
    HasTypeR P Γ (b.instantiate a) (B.instantiate a) := by
  have hσ : TypedSubstitutionR P (A :: Γ) Γ (Expr.single a) := by
    intro n D hn
    cases hn with
    | zero => simpa only [Expr.single, Expr.subst_lift_single] using ha
    | succ _ hn =>
        simpa only [Expr.single, Expr.subst_lift_single] using lookup ha.valid hn
  exact hb.subst ha.valid _ hσ

theorem weaken_under {Γ : List (Expr S)} {A D b B : Expr S} {s t : S}
    (hb : HasTypeR P (A :: Γ) b B) (hA : HasTypeR P Γ A (.sort s))
    (hD : HasTypeR P Γ D (.sort t)) :
    HasTypeR P (A.rename Nat.succ :: D :: Γ)
      (b.rename (Expr.liftRen Nat.succ)) (B.rename (Expr.liftRen Nat.succ)) := by
  have hA' : HasTypeR P (D :: Γ) (A.subst (Expr.var ∘ Nat.succ)) (.sort s) := by
    simpa only [Expr.subst_var_rename, Expr.rename] using HasTypeR.weaken hA hD
  have hσw : TypedSubstitutionR P Γ (D :: Γ) (Expr.var ∘ Nat.succ) := by
    intro n B hn
    simpa only [Expr.subst_var_rename, Function.comp_apply, Expr.rename] using
      (HasTypeR.weaken (lookup hD.valid hn) hD)
  have hσ := hσw.lift hA'
  have h := hb.subst (.cons (.cons hD.valid hD) hA') _ hσ
  have heq : Expr.liftSub (Expr.var ∘ Nat.succ : Nat → Expr S) =
      Expr.var ∘ Expr.liftRen Nat.succ := by
    funext n
    cases n <;> rfl
  simpa only [heq, Expr.subst_var_rename] using h

/-- Generation for products in the reduction-only system. -/
theorem generation_pi {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeR P Γ M T) :
    ∀ A B, M = .pi A B → ∃ s₁ s₂ s₃, HasTypeR P Γ A (.sort s₁) ∧
      HasTypeR P (A :: Γ) B (.sort s₂) ∧ P.rule s₁ s₂ s₃ ∧ T = .sort s₃ := by
  induction h with
  | ax h => intro A B heq; cases heq
  | var h ih => intro A B heq; cases heq
  | @weaken Γ M T C s hM hC ihM ihC =>
      intro A B heq
      cases M with
      | var n => cases heq
      | sort t => cases heq
      | app f a => cases heq
      | lam D b => cases heq
      | pi D E =>
          obtain ⟨rfl, rfl⟩ := Expr.pi.inj heq
          obtain ⟨t₁, t₂, t₃, hD, hE, hr, rfl⟩ := ihM D E rfl
          exact ⟨t₁, t₂, t₃, .weaken hD hC, hE.weaken_under hD hC, hr, rfl⟩
  | product hA hB hr ihA ihB =>
      intro A B heq
      cases heq
      exact ⟨_, _, _, hA, hB, hr, rfl⟩
  | abstraction hb hT ihb ihT => intro A B heq; cases heq
  | application hf ha ihf iha => intro A B heq; cases heq
  | reduction hM hB ihM =>
      intro A B heq
      obtain ⟨t₁, t₂, t₃, hA, hB', hr, rfl⟩ := ihM A B heq
      exact absurd hB (Normal.sort t₃ _)

/-- Generation for abstractions in the reduction-only system. -/
theorem generation_lam {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeR P Γ M T) :
    ∀ A b, M = .lam A b → ∃ B s, HasTypeR P (A :: Γ) b B ∧
      HasTypeR P Γ (.pi A B) (.sort s) ∧ Reduces (.pi A B) T := by
  induction h with
  | ax h => intro A b heq; cases heq
  | var h ih => intro A b heq; cases heq
  | @weaken Γ M T C s hM hC ihM ihC =>
      intro A b heq
      cases M with
      | var n => cases heq
      | sort t => cases heq
      | app f a => cases heq
      | pi D E => cases heq
      | lam D c =>
          obtain ⟨rfl, rfl⟩ := Expr.lam.inj heq
          obtain ⟨B, t, hc, hPi, hr⟩ := ihM D c rfl
          obtain ⟨r, hD⟩ := hPi.product_domain _ _ rfl
          exact ⟨_, t, hc.weaken_under hD hC, .weaken hPi hC, hr.rename Nat.succ⟩
  | product hA hB hr ihA ihB => intro A b heq; cases heq
  | abstraction hb hT ihb ihT =>
      intro A b heq
      cases heq
      exact ⟨_, _, hb, hT, .refl⟩
  | application hf ha ihf iha => intro A b heq; cases heq
  | reduction hM hB ihM =>
      intro A b heq
      obtain ⟨B', t, hb, hPi, hr⟩ := ihM A b heq
      exact ⟨B', t, hb, hPi, hr.tail hB⟩

end HasTypeR

/-- Closure of the reduction-only system under one-step reduction of a subject typed by a sort.
By `expansionPostponement_iff_sortedSubjectReductionR` this is equivalent to
`ExpansionPostponement P`. -/
def SortedSubjectReductionR {S : Type u} (P : Specification S) : Prop :=
  ∀ Γ M M' s, HasTypeR P Γ M (.sort s) → Beta M M' → HasTypeR P Γ M' (.sort s)

namespace SortedSubjectReductionR

variable {S : Type u} {P : Specification S}

theorem reduces (h : SortedSubjectReductionR P) {Γ : List (Expr S)} {M M' : Expr S} {s : S}
    (hM : HasTypeR P Γ M (.sort s)) (hr : Reduces M M') : HasTypeR P Γ M' (.sort s) := by
  induction hr with
  | refl => exact hM
  | tail _ hs ih => exact h _ _ _ _ ih hs

end SortedSubjectReductionR

/-- Expansion postponement from closure of the reduction-only system under reduction of
sort-typed subjects.  No normalization or functionality hypothesis. -/
theorem expansionPostponement_of_sortedSubjectReductionR {S : Type u} {P : Specification S}
    (hsr : SortedSubjectReductionR P) : ExpansionPostponement P := by
  intro Γ M A h
  induction h with
  | ax h => exact ⟨_, .refl, .ax h⟩
  | var _ ih =>
      obtain ⟨B, hB, hA⟩ := ih
      rw [HasTypeR.sort_reduces hB] at hA
      exact ⟨_, .refl, .var hA⟩
  | weaken _ _ ihM ihA =>
      obtain ⟨B', hB', hM⟩ := ihM
      obtain ⟨T, hT, hA⟩ := ihA
      rw [HasTypeR.sort_reduces hT] at hA
      exact ⟨_, Reduces.rename hB' Nat.succ, .weaken hM hA⟩
  | product _ _ hr ihA ihB =>
      obtain ⟨T₁, hT₁, hA⟩ := ihA
      obtain ⟨T₂, hT₂, hB⟩ := ihB
      rw [HasTypeR.sort_reduces hT₁] at hA
      rw [HasTypeR.sort_reduces hT₂] at hB
      exact ⟨_, .refl, .product hA hB hr⟩
  | @abstraction Γ A b B s _ _ ihb ihP =>
      obtain ⟨B', hB', hb⟩ := ihb
      obtain ⟨T, hT, hP⟩ := ihP
      rw [HasTypeR.sort_reduces hT] at hP
      obtain ⟨s₁, s₂, s₃, hA, hBs, hr, hs⟩ := hP.generation_pi A B rfl
      have hB's := hsr.reduces hBs hB'
      exact ⟨_, Reduces.pi .refl hB', .abstraction hb (.product hA hB's hr)⟩
  | @application Γ f a A B _ _ ihf iha =>
      obtain ⟨D, hD, hf⟩ := ihf
      obtain ⟨A₂, hA₂, ha⟩ := iha
      obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Reduces.pi_inv hD
      obtain ⟨E, hE₁, hE₂⟩ := Reduces.confluent hA₁ hA₂
      have hf' := hf.reduces (Reduces.pi hE₁ .refl)
      have ha' := ha.reduces hE₂
      exact ⟨_, Reduces.subst hB₁ (Expr.single a), .application hf' ha'⟩
  | conversion _ _ hc ihM _ =>
      obtain ⟨A', hA', hM⟩ := ihM
      obtain ⟨K, hK₁, hK₂⟩ := hc.join
      obtain ⟨E, hE₁, hE₂⟩ := Reduces.confluent hA' hK₁
      exact ⟨E, hK₂.trans hE₂, hM.reduces hE₁⟩

/-- Expansion postponement is equivalent to closure of the reduction-only system under
reduction of sort-typed subjects, for every specification. -/
theorem expansionPostponement_iff_sortedSubjectReductionR {S : Type u}
    (P : Specification S) :
    ExpansionPostponement P ↔ SortedSubjectReductionR P := by
  refine ⟨fun hep => ?_, expansionPostponement_of_sortedSubjectReductionR⟩
  intro Γ M M' s hM hr
  obtain ⟨B, hB, h⟩ := hep Γ M' (.sort s) (hM.toHasType.subject_reduction hr)
  rwa [HasTypeR.sort_reduces hB] at h

end PureTypeSystem
