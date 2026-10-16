/-
**Toward expansion postponement for λPω̲ (M29-EP-CUBE-REST): the canonical judgement.**

Step 1 of the plan for λPω̲.  `HasTypeNW P Γ M T` is the canonical judgement: the rules of
`HasTypeR` without the reduction rule; subjects, types and contexts are β-normal
(`HasTypeNW.normal`); in the application rule the result type is the normal form of `B[a]` (for a
normalizing specification, the hereditary substitution of the argument into the codomain); and,
unlike `HasTypeNR`, arguments are *not* restricted to base-erased ones, so constructors of
arrow kind may be passed.  `HasTypeNW.toHasTypeR` is soundness and `HasTypeNR.toHasTypeNW` embeds
the λP judgement.  Structural lemmas: `valid`, `rename`, `weaken_under`, `lookup`,
`product_domain`, `lam_inv`.  `HasTypeNW.app_type_exists`: in every corner of the cube, the
normal type demanded by the application rule exists (strong normalization of the cube).

Hereditary substitution (steps 2 and 3) and `lambdaPOmegaBar_productNormalizationR` are not
proved here.
-/

import Start.PTSExpansionLambdaPOmegaBarSkel
import Start.CoCSN

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

universe u

/-- Canonical λPω̲ typing: the rules of `HasTypeR` without the reduction rule, with the type
of an application normalized and a normal subject; arguments are unrestricted. -/
inductive HasTypeNW {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Prop
  | ax {s t} : P.axioms s t → HasTypeNW P ([]) (.sort s) (.sort t)
  | var {Γ A s} : HasTypeNW P Γ A (.sort s) →
      HasTypeNW P (A :: Γ) (.var 0) (A.rename Nat.succ)
  | weaken {Γ M B A s} : HasTypeNW P Γ M B → HasTypeNW P Γ A (.sort s) →
      HasTypeNW P (A :: Γ) (M.rename Nat.succ) (B.rename Nat.succ)
  | product {Γ A B s₁ s₂ s₃} : HasTypeNW P Γ A (.sort s₁) →
      HasTypeNW P (A :: Γ) B (.sort s₂) → P.rule s₁ s₂ s₃ →
      HasTypeNW P Γ (.pi A B) (.sort s₃)
  | abstraction {Γ A b B s} : HasTypeNW P (A :: Γ) b B →
      HasTypeNW P Γ (.pi A B) (.sort s) →
      HasTypeNW P Γ (.lam A b) (.pi A B)
  | application {Γ F a A B B'} : HasTypeNW P Γ F (.pi A B) → HasTypeNW P Γ a A →
      Reduces (B.instantiate a) B' → Normal B' → Normal (.app F a) →
      HasTypeNW P Γ (.app F a) B'

/-- Contexts whose declarations are canonically typed by sorts. -/
inductive ValidContextNW {S : Type u} (P : Specification S) : List (Expr S) → Prop
  | nil : ValidContextNW P ([])
  | cons {Γ A s} : ValidContextNW P Γ → HasTypeNW P Γ A (.sort s) →
      ValidContextNW P (A :: Γ)

namespace HasTypeNW

variable {S : Type u} {P : Specification S}

/-- Soundness of the canonical judgement. -/
theorem toHasTypeR {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNW P Γ M T) :
    HasTypeR P Γ M T := by
  induction h with
  | ax h => exact .ax h
  | var _ ih => exact .var ih
  | weaken _ _ ihM ihA => exact .weaken ihM ihA
  | product _ _ hr ihA ihB => exact .product ihA ihB hr
  | abstraction _ _ ihb ihP => exact .abstraction ihb ihP
  | application _ _ hr _ _ ihF iha => exact (HasTypeR.application ihF iha).reduces hr

theorem toHasType {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNW P Γ M T) :
    HasType P Γ M T := h.toHasTypeR.toHasType

theorem valid {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNW P Γ M T) :
    ValidContextNW P Γ := by
  induction h with
  | ax _ => exact .nil
  | var h ih => exact .cons ih h
  | weaken _ h _ ih => exact .cons ih h
  | product _ _ _ ih _ => exact ih
  | abstraction _ _ _ ih => exact ih
  | application _ _ _ _ _ ih _ => exact ih

/-- Subjects, types and contexts of canonical judgements are normal. -/
theorem normal {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNW P Γ M T) :
    Normal M ∧ Normal T ∧ ∀ X ∈ Γ, Normal X := by
  induction h with
  | ax _ => exact ⟨Normal.sort _, Normal.sort _, by simp⟩
  | var _ ih =>
      refine ⟨Normal.var 0, ih.1.rename _, ?_⟩
      intro X hX
      rcases List.mem_cons.1 hX with rfl | hX
      · exact ih.1
      · exact ih.2.2 X hX
  | weaken _ _ ihM ihA =>
      refine ⟨ihM.1.rename _, ihM.2.1.rename _, ?_⟩
      intro X hX
      rcases List.mem_cons.1 hX with rfl | hX
      · exact ihA.1
      · exact ihA.2.2 X hX
  | product _ _ _ ihA ihB => exact ⟨ihA.1.pi ihB.1, Normal.sort _, ihA.2.2⟩
  | abstraction _ _ ihb ihP =>
      exact ⟨ihP.1.pi_domain.lam ihb.1, ihP.1, ihP.2.2⟩
  | application _ _ _ hB' happ ihF _ => exact ⟨happ, hB', ihF.2.2⟩

theorem product_domain {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNW P Γ M T) :
    ∀ A B, M = .pi A B → ∃ s, HasTypeNW P Γ A (.sort s) := by
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
  | application => intro A B heq; cases heq

theorem sort_of_valid {Γ : List (Expr S)} (hΓ : ValidContextNW P Γ)
    {s t : S} (hst : P.axioms s t) : HasTypeNW P Γ (.sort s) (.sort t) := by
  induction hΓ with
  | nil => exact .ax hst
  | cons _ hA ih => exact .weaken ih hA

theorem lookup {Γ : List (Expr S)} (hΓ : ValidContextNW P Γ)
    {n : Nat} {A : Expr S} (hn : Lookup Γ n A) : HasTypeNW P Γ (.var n) A := by
  induction hΓ generalizing n A with
  | nil => cases hn
  | cons hΓ hB ih =>
      cases hn with
      | zero => exact .var hB
      | succ _ hn => exact .weaken (ih hn) hB

/-- Renaming along a declaration renaming. -/
theorem rename {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNW P Γ M T)
    {Δ : List (Expr S)} (hΔ : ValidContextNW P Δ) (ρ : Nat → Nat)
    (hρ : TypingTree.DeclRenaming Γ Δ ρ) : HasTypeNW P Δ (M.rename ρ) (T.rename ρ) := by
  induction h generalizing Δ ρ with
  | ax h => exact sort_of_valid hΔ h
  | @var Γ A s hA ih => exact lookup hΔ (hρ _ _ (.zero _ _))
  | @weaken Γ M B A s hM hA ihM ihA =>
      have hρ' : TypingTree.DeclRenaming Γ Δ (ρ ∘ Nat.succ) := by
        intro n C hn
        have := hρ _ _ (.succ A hn)
        rw [Expr.rename_comp] at this
        exact this
      simpa only [Expr.rename_comp] using ihM hΔ (ρ ∘ Nat.succ) hρ'
  | product hA hB hr ihA ihB =>
      have hA' := ihA hΔ ρ hρ
      exact .product hA' (ihB (.cons hΔ hA') _ (hρ.lift _)) hr
  | @abstraction Γ A b B s hb hP ihb ihP =>
      have hP' := ihP hΔ ρ hρ
      obtain ⟨t, hA'⟩ := hP'.product_domain _ _ rfl
      exact .abstraction (ihb (.cons hΔ hA') _ (hρ.lift _)) hP'
  | @application Γ F a A B B' hF ha hr hB' happ ihF iha =>
      refine .application (ihF hΔ ρ hρ) (iha hΔ ρ hρ) ?_ (hB'.rename ρ) (happ.rename ρ)
      simpa only [Expr.instantiate_rename] using hr.rename ρ

theorem weaken_under {Γ : List (Expr S)} {A D b B : Expr S} {s t : S}
    (hb : HasTypeNW P (A :: Γ) b B) (hA : HasTypeNW P Γ A (.sort s))
    (hD : HasTypeNW P Γ D (.sort t)) :
    HasTypeNW P (A.rename Nat.succ :: D :: Γ)
      (b.rename (Expr.liftRen Nat.succ)) (B.rename (Expr.liftRen Nat.succ)) := by
  have hA' : HasTypeNW P (D :: Γ) (A.rename Nat.succ) (.sort s) := .weaken hA hD
  exact hb.rename (.cons (.cons hD.valid hD) hA') _ ((TypingTree.DeclRenaming.weaken D).lift A)

/-- Inversion for abstractions. -/
theorem lam_inv {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNW P Γ M T) :
    ∀ A b, M = .lam A b → ∃ B s, T = .pi A B ∧ HasTypeNW P (A :: Γ) b B ∧
      HasTypeNW P Γ (.pi A B) (.sort s) := by
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
          obtain ⟨B, t, rfl, hc, hPi⟩ := ihM D c rfl
          obtain ⟨r, hD⟩ := hPi.product_domain _ _ rfl
          exact ⟨_, t, rfl, hc.weaken_under hD hC, .weaken hPi hC⟩
  | product => intro A b heq; cases heq
  | abstraction hb hT ihb ihT =>
      intro A b heq
      cases heq
      exact ⟨_, _, rfl, hb, hT⟩
  | application => intro A b heq; cases heq

end HasTypeNW

/-- The λP canonical judgement is an instance of the λPω̲ one. -/
theorem HasTypeNR.toHasTypeNW {S : Type u} {P : Specification S} {Γ : List (Expr S)}
    {M T : Expr S} (h : HasTypeNR P Γ M T) : HasTypeNW P Γ M T := by
  induction h with
  | ax h => exact .ax h
  | var _ ih => exact .var ih
  | weaken _ _ ihM ihA => exact .weaken ihM ihA
  | product _ _ hr ihA ihB => exact .product ihA ihB hr
  | abstraction _ _ ihb ihP => exact .abstraction ihb ihP
  | application _ _ hr hB happ _ ihF iha => exact .application ihF iha hr hB happ

open LambdaPi (Srt)

/-- In every corner of the cube, the normal type demanded by the application rule exists. -/
theorem HasTypeNW.app_type_exists (f : CubeFeatures) {Γ : List (Expr Srt)} {F a A B : Expr Srt}
    (hF : HasTypeNW (cubeSpec f) Γ F (.pi A B)) (ha : HasTypeNW (cubeSpec f) Γ a A) :
    ∃ B', Reduces (B.instantiate a) B' ∧ Normal B' := by
  have hT : HasType (cubeSpec f) Γ (.app F a) (B.instantiate a) :=
    .application hF.toHasType ha.toHasType
  exact weaklyNormalizing_of_stronglyNormalizing
    (cube_stronglyNormalizing f Γ hT.valid _ ⟨_, .inr hT⟩)

end PureTypeSystem
