/-
**Expansion postponement for λP, by canonical forms and hereditary substitution (M29-EP-CUBE).**

* `STy`, `Expr.erase`: the erasure of a term to a simple type (Harper–Honsell–Plotkin);
  `Expr.ErGood M`: every application argument inside `M` erases to `STy.base`.  Erasure is
  invariant under substitution of base-erased terms and under reduction of `ErGood` terms.
* `HasTypeNR P Γ M T`: a canonical typing judgement.  It has the rules of `HasTypeR` without the
  reduction rule; in the application rule the type `B[a]` is normalized and the subject is
  required to be normal (and the argument to erase to `base`).  All subjects, types and contexts
  are normal (`HasTypeNR.normal`); `HasTypeNR.toHasTypeR` is soundness.
* `HasTypeNR.hsubst`: hereditary substitution, by induction on the erasure of the type of the
  substituted variable and then on the derivation.
* `HasTypeR.normalizeNR` (λP): every `HasTypeR` derivation normalizes to a canonical one.
* `HasTypeR.ctx_expand`: context expansion for `HasTypeR`.
* `lambdaP_productNormalizationR` and **`lambdaP_expansionPostponement`**:
  `ExpansionPostponement (cubeSpec lambdaP)`.
-/

import Start.PTSExpansionCube

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

universe u

/-! ### Erasure to simple types -/

/-- Simple types. -/
inductive STy
  | base
  | arr (σ τ : STy)
  deriving DecidableEq

namespace STy

/-- Size of a simple type. -/
def size : STy → Nat
  | base => 1
  | arr σ τ => size σ + size τ + 1

/-- `ArrSuffix τ υ`: `τ` is obtained from `υ` by repeatedly taking codomains. -/
inductive ArrSuffix : STy → STy → Prop
  | refl (τ : STy) : ArrSuffix τ τ
  | cod {σ τ υ : STy} : ArrSuffix (arr σ τ) υ → ArrSuffix τ υ

theorem ArrSuffix.size_le {τ υ : STy} (h : ArrSuffix τ υ) : size τ ≤ size υ := by
  induction h with
  | refl => exact le_rfl
  | cod _ ih => simp only [size] at ih; omega

theorem ArrSuffix.dom_lt {σ τ υ : STy} (h : ArrSuffix (arr σ τ) υ) : size σ < size υ := by
  have := h.size_le
  simp only [size] at this
  omega

end STy

namespace Expr

variable {S : Type u}

/-- Erasure to simple types: products become arrows, abstractions and applications keep the
erasure of their body and head; everything else erases to `base`. -/
def erase : Expr S → STy
  | pi A B => .arr (erase A) (erase B)
  | lam _ F => erase F
  | app F _ => erase F
  | _ => .base

/-- Every application argument erases to `base`. -/
def ErGood : Expr S → Prop
  | var _ => True
  | sort _ => True
  | app F a => ErGood F ∧ ErGood a ∧ erase a = .base
  | lam A b => ErGood A ∧ ErGood b
  | pi A B => ErGood A ∧ ErGood B

theorem erase_rename (M : Expr S) (ρ : Nat → Nat) : (M.rename ρ).erase = M.erase := by
  induction M generalizing ρ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf _ => simp only [rename, erase, ihf]
  | lam A b _ ihb => simp only [rename, erase, ihb]
  | pi A B ihA ihB => simp only [rename, erase, ihA, ihB]

theorem erGood_rename {M : Expr S} (h : M.ErGood) (ρ : Nat → Nat) : (M.rename ρ).ErGood := by
  induction M generalizing ρ with
  | var n => trivial
  | sort s => trivial
  | app f a ihf iha =>
      exact ⟨ihf h.1 ρ, iha h.2.1 ρ, by rw [erase_rename]; exact h.2.2⟩
  | lam A b ihA ihb => exact ⟨ihA h.1 ρ, ihb h.2 _⟩
  | pi A B ihA ihB => exact ⟨ihA h.1 ρ, ihB h.2 _⟩

/-- Substitutions whose values are `ErGood` and erase to `base`. -/
def BaseSubst (σ : Nat → Expr S) : Prop := ∀ n, (σ n).erase = .base ∧ (σ n).ErGood

theorem BaseSubst.lift {σ : Nat → Expr S} (h : BaseSubst σ) : BaseSubst (liftSub σ) := by
  intro n
  cases n with
  | zero => exact ⟨rfl, trivial⟩
  | succ n => exact ⟨by rw [liftSub_succ, erase_rename]; exact (h n).1,
      erGood_rename (h n).2 _⟩

theorem BaseSubst.single {a : Expr S} (ha : a.erase = .base) (hg : a.ErGood) :
    BaseSubst (Expr.single a) := by
  intro n
  cases n with
  | zero => exact ⟨ha, hg⟩
  | succ n => exact ⟨rfl, trivial⟩

theorem erase_subst (M : Expr S) {σ : Nat → Expr S} (hσ : BaseSubst σ) :
    (M.subst σ).erase = M.erase := by
  induction M generalizing σ with
  | var n => exact (hσ n).1
  | sort s => rfl
  | app f a ihf _ => simp only [subst, erase, ihf hσ]
  | lam A b _ ihb => simp only [subst, erase, ihb hσ.lift]
  | pi A B ihA ihB => simp only [subst, erase, ihA hσ, ihB hσ.lift]

theorem erGood_subst {M : Expr S} (h : M.ErGood) {σ : Nat → Expr S} (hσ : BaseSubst σ) :
    (M.subst σ).ErGood := by
  induction M generalizing σ with
  | var n => exact (hσ n).2
  | sort s => trivial
  | app f a ihf iha =>
      exact ⟨ihf h.1 hσ, iha h.2.1 hσ, by rw [erase_subst a hσ]; exact h.2.2⟩
  | lam A b ihA ihb => exact ⟨ihA h.1 hσ, ihb h.2 hσ.lift⟩
  | pi A B ihA ihB => exact ⟨ihA h.1 hσ, ihB h.2 hσ.lift⟩

end Expr

namespace Beta

variable {S : Type u}

theorem erGood_erase {M N : Expr S} (h : Beta M N) (hg : M.ErGood) :
    N.ErGood ∧ N.erase = M.erase := by
  induction h with
  | head A b a =>
      obtain ⟨⟨_, hb⟩, ha, hab⟩ := hg
      have hσ := Expr.BaseSubst.single hab ha
      exact ⟨Expr.erGood_subst hb hσ, Expr.erase_subst b hσ⟩
  | app_left _ ih =>
      obtain ⟨h1, h2⟩ := ih hg.1
      exact ⟨⟨h1, hg.2.1, hg.2.2⟩, by simp only [Expr.erase, h2]⟩
  | app_right _ ih =>
      obtain ⟨h1, h2⟩ := ih hg.2.1
      exact ⟨⟨hg.1, h1, by rw [h2]; exact hg.2.2⟩, rfl⟩
  | lam_domain _ ih => exact ⟨⟨(ih hg.1).1, hg.2⟩, rfl⟩
  | lam_body _ ih =>
      obtain ⟨h1, h2⟩ := ih hg.2
      exact ⟨⟨hg.1, h1⟩, by simp only [Expr.erase, h2]⟩
  | pi_domain _ ih =>
      obtain ⟨h1, h2⟩ := ih hg.1
      exact ⟨⟨h1, hg.2⟩, by simp only [Expr.erase, h2]⟩
  | pi_body _ ih =>
      obtain ⟨h1, h2⟩ := ih hg.2
      exact ⟨⟨hg.1, h1⟩, by simp only [Expr.erase, h2]⟩

end Beta

namespace Reduces

variable {S : Type u}

theorem erGood_erase {M N : Expr S} (h : Reduces M N) (hg : M.ErGood) :
    N.ErGood ∧ N.erase = M.erase := by
  induction h with
  | refl => exact ⟨hg, rfl⟩
  | tail _ hs ih =>
      obtain ⟨h1, h2⟩ := ih
      obtain ⟨h3, h4⟩ := hs.erGood_erase h1
      exact ⟨h3, h4.trans h2⟩

theorem instantiate {b b' a a' : Expr S} (hb : Reduces b b') (ha : Reduces a a') :
    Reduces (b.instantiate a) (b'.instantiate a') := by
  refine (hb.subst _).trans ?_
  induction ha with
  | refl => exact .refl
  | tail _ hs ih =>
      exact ih.trans (Parallel.reduces (Parallel.instantiate (Parallel.refl b')
        (Parallel.of_beta hs)))

/-- Two normal reducts of one term are equal. -/
theorem normal_unique {M N₁ N₂ : Expr S} (h₁ : Reduces M N₁) (h₂ : Reduces M N₂)
    (hn₁ : Normal N₁) (hn₂ : Normal N₂) : N₁ = N₂ := by
  obtain ⟨K, hK₁, hK₂⟩ := Reduces.confluent h₁ h₂
  rw [hn₁.reduces_eq hK₁, hn₂.reduces_eq hK₂]

/-- If `M ↠ N₁` and `M ↠ N₂` with `N₂` normal, then `N₁ ↠ N₂`. -/
theorem to_normal {M N₁ N₂ : Expr S} (h₁ : Reduces M N₁) (h₂ : Reduces M N₂)
    (hn₂ : Normal N₂) : Reduces N₁ N₂ := by
  obtain ⟨K, hK₁, hK₂⟩ := Reduces.confluent h₁ h₂
  rw [hn₂.reduces_eq hK₂]
  exact hK₁

theorem sort_eq {s : S} {T : Expr S} (h : Reduces (.sort s) T) : T = .sort s :=
  ((Normal.sort s).reduces_eq h).symm

end Reduces

/-! ### The canonical judgement -/

/-- Canonical (normal) typing: the rules of `HasTypeR` without the reduction rule, with the type
of an application normalized, a normal subject, and a base-erased argument. -/
inductive HasTypeNR {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Prop
  | ax {s t} : P.axioms s t → HasTypeNR P ([]) (.sort s) (.sort t)
  | var {Γ A s} : HasTypeNR P Γ A (.sort s) →
      HasTypeNR P (A :: Γ) (.var 0) (A.rename Nat.succ)
  | weaken {Γ M B A s} : HasTypeNR P Γ M B → HasTypeNR P Γ A (.sort s) →
      HasTypeNR P (A :: Γ) (M.rename Nat.succ) (B.rename Nat.succ)
  | product {Γ A B s₁ s₂ s₃} : HasTypeNR P Γ A (.sort s₁) →
      HasTypeNR P (A :: Γ) B (.sort s₂) → P.rule s₁ s₂ s₃ →
      HasTypeNR P Γ (.pi A B) (.sort s₃)
  | abstraction {Γ A b B s} : HasTypeNR P (A :: Γ) b B →
      HasTypeNR P Γ (.pi A B) (.sort s) →
      HasTypeNR P Γ (.lam A b) (.pi A B)
  | application {Γ F a A B B'} : HasTypeNR P Γ F (.pi A B) → HasTypeNR P Γ a A →
      Reduces (B.instantiate a) B' → Normal B' → Normal (.app F a) → a.erase = .base →
      HasTypeNR P Γ (.app F a) B'

/-- Contexts whose declarations are canonically typed by sorts. -/
inductive ValidContextNR {S : Type u} (P : Specification S) : List (Expr S) → Prop
  | nil : ValidContextNR P ([])
  | cons {Γ A s} : ValidContextNR P Γ → HasTypeNR P Γ A (.sort s) →
      ValidContextNR P (A :: Γ)

namespace HasTypeNR

variable {S : Type u} {P : Specification S}

/-- Soundness of the canonical judgement. -/
theorem toHasTypeR {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNR P Γ M T) :
    HasTypeR P Γ M T := by
  induction h with
  | ax h => exact .ax h
  | var _ ih => exact .var ih
  | weaken _ _ ihM ihA => exact .weaken ihM ihA
  | product _ _ hr ihA ihB => exact .product ihA ihB hr
  | abstraction _ _ ihb ihP => exact .abstraction ihb ihP
  | application _ _ hr _ _ _ ihF iha => exact (HasTypeR.application ihF iha).reduces hr

theorem toHasType {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNR P Γ M T) :
    HasType P Γ M T := h.toHasTypeR.toHasType

theorem valid {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNR P Γ M T) :
    ValidContextNR P Γ := by
  induction h with
  | ax _ => exact .nil
  | var h ih => exact .cons ih h
  | weaken _ h _ ih => exact .cons ih h
  | product _ _ _ ih _ => exact ih
  | abstraction _ _ _ ih => exact ih
  | application _ _ _ _ _ _ ih _ => exact ih

/-- Subjects, types and contexts of canonical judgements are normal. -/
theorem normal {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNR P Γ M T) :
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
  | application _ _ _ hB' happ _ ihF _ => exact ⟨happ, hB', ihF.2.2⟩

theorem erGood {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNR P Γ M T) :
    M.ErGood ∧ T.ErGood := by
  induction h with
  | ax _ => exact ⟨trivial, trivial⟩
  | var _ ih => exact ⟨trivial, Expr.erGood_rename ih.1 _⟩
  | weaken _ _ ihM _ => exact ⟨Expr.erGood_rename ihM.1 _, Expr.erGood_rename ihM.2 _⟩
  | product _ _ _ ihA ihB => exact ⟨⟨ihA.1, ihB.1⟩, trivial⟩
  | abstraction _ _ ihb ihP => exact ⟨⟨ihP.1.1, ihb.1⟩, ihP.1⟩
  | application _ _ hr _ _ hbase ihF iha =>
      refine ⟨⟨ihF.1, iha.1, hbase⟩, ?_⟩
      exact (hr.erGood_erase (Expr.erGood_subst ihF.2.2
        (Expr.BaseSubst.single hbase iha.1))).1

theorem product_domain {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNR P Γ M T) :
    ∀ A B, M = .pi A B → ∃ s, HasTypeNR P Γ A (.sort s) := by
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

theorem sort_of_valid {Γ : List (Expr S)} (hΓ : ValidContextNR P Γ)
    {s t : S} (hst : P.axioms s t) : HasTypeNR P Γ (.sort s) (.sort t) := by
  induction hΓ with
  | nil => exact .ax hst
  | cons _ hA ih => exact .weaken ih hA

theorem lookup {Γ : List (Expr S)} (hΓ : ValidContextNR P Γ)
    {n : Nat} {A : Expr S} (hn : Lookup Γ n A) : HasTypeNR P Γ (.var n) A := by
  induction hΓ generalizing n A with
  | nil => cases hn
  | cons hΓ hB ih =>
      cases hn with
      | zero => exact .var hB
      | succ _ hn => exact .weaken (ih hn) hB

/-- Renaming along a declaration renaming. -/
theorem rename {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNR P Γ M T)
    {Δ : List (Expr S)} (hΔ : ValidContextNR P Δ) (ρ : Nat → Nat)
    (hρ : TypingTree.DeclRenaming Γ Δ ρ) : HasTypeNR P Δ (M.rename ρ) (T.rename ρ) := by
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
  | @application Γ F a A B B' hF ha hr hB' happ hbase ihF iha =>
      refine .application (ihF hΔ ρ hρ) (iha hΔ ρ hρ) ?_ (hB'.rename ρ) (happ.rename ρ)
        (by rw [Expr.erase_rename]; exact hbase)
      simpa only [Expr.instantiate_rename] using hr.rename ρ

theorem weaken_under {Γ : List (Expr S)} {A D b B : Expr S} {s t : S}
    (hb : HasTypeNR P (A :: Γ) b B) (hA : HasTypeNR P Γ A (.sort s))
    (hD : HasTypeNR P Γ D (.sort t)) :
    HasTypeNR P (A.rename Nat.succ :: D :: Γ)
      (b.rename (Expr.liftRen Nat.succ)) (B.rename (Expr.liftRen Nat.succ)) := by
  have hA' : HasTypeNR P (D :: Γ) (A.rename Nat.succ) (.sort s) := .weaken hA hD
  exact hb.rename (.cons (.cons hD.valid hD) hA') _ ((TypingTree.DeclRenaming.weaken D).lift A)

/-- Inversion for abstractions. -/
theorem lam_inv {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNR P Γ M T) :
    ∀ A b, M = .lam A b → ∃ B s, T = .pi A B ∧ HasTypeNR P (A :: Γ) b B ∧
      HasTypeNR P Γ (.pi A B) (.sort s) := by
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

end HasTypeNR

/-! ### Hereditary substitution -/

namespace Expr

variable {S : Type u}

/-- Head variable of an application spine. -/
def headVar : Expr S → Option Nat
  | var n => some n
  | app F _ => headVar F
  | _ => none

theorem headVar_rename (M : Expr S) (ρ : Nat → Nat) :
    (M.rename ρ).headVar = M.headVar.map ρ := by
  induction M with
  | var n => rfl
  | sort s => rfl
  | app f a ihf _ => simp only [rename, headVar, ihf]
  | lam A b _ _ => rfl
  | pi A B _ _ => rfl

/-- Substitution of `N` for the variable `k`, under `k` binders. -/
def substAt (N : Expr S) (k : Nat) : Nat → Expr S := liftSub^[k] (single N)

@[simp] theorem substAt_zero (N : Expr S) : substAt N 0 = single N := rfl

theorem substAt_succ (N : Expr S) (k : Nat) : substAt N (k + 1) = liftSub (substAt N k) :=
  Function.iterate_succ_apply' _ _ _

theorem substAt_base {N : Expr S} (hb : N.erase = .base) (hg : N.ErGood) (k : Nat) :
    BaseSubst (substAt N k) := by
  induction k with
  | zero => exact BaseSubst.single hb hg
  | succ k ih => rw [substAt_succ]; exact ih.lift

theorem substAt_ne (N : Expr S) : ∀ (k n : Nat), n ≠ k → ∃ m, substAt N k n = var m
  | 0, 0, h => absurd rfl h
  | 0, n + 1, _ => ⟨n, rfl⟩
  | k + 1, 0, _ => ⟨0, by rw [substAt_succ]; rfl⟩
  | k + 1, n + 1, h => by
      obtain ⟨m, hm⟩ := substAt_ne N k n (by omega)
      exact ⟨m + 1, by rw [substAt_succ, liftSub_succ, hm]; rfl⟩

theorem rename_succ_subst_lift (M : Expr S) (σ : Nat → Expr S) :
    (M.rename Nat.succ).subst (liftSub σ) = (M.subst σ).rename Nat.succ := by
  rw [subst_rename, rename_subst]
  rfl

end Expr

namespace Normal

variable {S : Type u}

theorem app_of {F a : Expr S} (hF : Normal F) (ha : Normal a)
    (hl : ∀ C b, F ≠ .lam C b) : Normal (.app F a) := by
  intro N h
  cases h with
  | head C b a => exact hl C b rfl
  | app_left h => exact hF _ h
  | app_right h => exact ha _ h

theorem app_not_lam {F a : Expr S} (h : Normal (.app F a)) : ∀ C b, F ≠ .lam C b := by
  rintro C b rfl
  exact h _ (Beta.head C b a)

end Normal

namespace Reduces

variable {S : Type u}

theorem app_inv_of_noLam {X b Z : Expr S} (hX : ∀ Y, Reduces X Y → ∀ C e, Y ≠ .lam C e)
    (h : Reduces (.app X b) Z) : ∃ X' b', Z = .app X' b' ∧ Reduces X X' := by
  induction h with
  | refl => exact ⟨X, b, rfl, .refl⟩
  | tail _ hs ih =>
      obtain ⟨X', b', rfl, hXX'⟩ := ih
      cases hs with
      | head C e a => exact absurd rfl (hX _ hXX' C e)
      | app_left h => exact ⟨_, b', rfl, hXX'.tail h⟩
      | app_right h => exact ⟨X', _, rfl, hXX'⟩

end Reduces

/-- After substituting for `k`, a normal non-abstraction whose head is not `k` never reduces to
an abstraction. -/
theorem subst_noLam {S : Type u} (N : Expr S) (k : Nat) :
    ∀ F : Expr S, Normal F → (∀ C b, F ≠ .lam C b) → F.headVar ≠ some k →
      ∀ Y, Reduces (F.subst (Expr.substAt N k)) Y → ∀ C b, Y ≠ .lam C b := by
  intro F
  induction F with
  | var n =>
      intro _ _ hk Y hY C b
      obtain ⟨m, hm⟩ := Expr.substAt_ne N k n (fun h => hk (by rw [h]; rfl))
      have hY' : Reduces (Expr.var m) Y := by simpa only [Expr.subst, hm] using hY
      rw [← (Normal.var m).reduces_eq hY']
      intro h; cases h
  | sort s =>
      intro _ _ _ Y hY C b
      rw [Reduces.sort_eq hY]
      intro h; cases h
  | pi A B _ _ =>
      intro _ _ _ Y hY C b
      obtain ⟨A', B', rfl, _, _⟩ := Reduces.pi_inv hY
      intro h; cases h
  | lam A b _ _ => intro _ hl; exact absurd rfl (hl A b)
  | app f a ihf _ =>
      intro hn _ hk Y hY C b
      have hf := ihf hn.app_left (hn.app_not_lam) hk
      obtain ⟨X', b', rfl, _⟩ := Reduces.app_inv_of_noLam hf hY
      intro h; cases h

theorem lookup_append_erase {S : Type u} :
    ∀ (Δ : List (Expr S)) {A : Expr S} {Γ : List (Expr S)} {U : Expr S},
      Lookup (Δ ++ A :: Γ) Δ.length U → U.erase = A.erase
  | [], A, Γ, U, h => by
      cases h
      exact Expr.erase_rename _ _
  | D :: Δ, A, Γ, U, h => by
      simp only [List.cons_append, List.length_cons] at h
      cases h with
      | succ _ h => rw [Expr.erase_rename]; exact lookup_append_erase Δ h

/-- Pointwise reduction of a context after substituting `N` for the variable below it. -/
inductive CtxSubstRed {S : Type u} (N : Expr S) : List (Expr S) → List (Expr S) → Prop
  | nil : CtxSubstRed N ([]) ([])
  | cons {Δ Δ' D D'} : CtxSubstRed N Δ Δ' →
      Reduces (D.subst (Expr.substAt N Δ.length)) D' → CtxSubstRed N (D :: Δ) (D' :: Δ')

theorem CtxSubstRed.unique {S : Type u} {N : Expr S} {Δ Δ₁ Δ₂ : List (Expr S)}
    (h₁ : CtxSubstRed N Δ Δ₁) (h₂ : CtxSubstRed N Δ Δ₂)
    (hn₁ : ∀ X ∈ Δ₁, Normal X) (hn₂ : ∀ X ∈ Δ₂, Normal X) : Δ₁ = Δ₂ := by
  induction h₁ generalizing Δ₂ with
  | nil => cases h₂; rfl
  | cons h hr ih =>
      cases h₂ with
      | cons h' hr' =>
          rw [Reduces.normal_unique hr hr' (hn₁ _ (List.mem_cons_self ..))
            (hn₂ _ (List.mem_cons_self ..)),
            ih h' (fun X hX => hn₁ X (List.mem_cons_of_mem _ hX))
              (fun X hX => hn₂ X (List.mem_cons_of_mem _ hX))]

namespace HasTypeNR

variable {S : Type u} {P : Specification S}

/-- The type of a variable-headed spine is a codomain of the type of its head. -/
theorem head_lookup {Θ : List (Expr S)} {F T : Expr S} (h : HasTypeNR P Θ F T) :
    ∀ x, F.headVar = some x → ∃ U, Lookup Θ x U ∧ STy.ArrSuffix T.erase U.erase := by
  induction h with
  | ax _ => intro x hx; cases hx
  | var _ _ =>
      intro x hx
      cases hx
      exact ⟨_, .zero _ _, .refl _⟩
  | @weaken Γ M B A s hM hA ihM _ =>
      intro x hx
      rw [Expr.headVar_rename] at hx
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
      obtain ⟨U, hU, hs⟩ := ihM y hy
      exact ⟨_, .succ A hU, by rw [Expr.erase_rename, Expr.erase_rename]; exact hs⟩
  | product => intro x hx; cases hx
  | abstraction => intro x hx; cases hx
  | @application Γ F a C D B' hF ha hr _ _ hbase ihF _ =>
      intro x hx
      obtain ⟨U, hU, hs⟩ := ihF x hx
      have hσ := Expr.BaseSubst.single hbase ha.erGood.1
      have he : B'.erase = D.erase :=
        (hr.erGood_erase (Expr.erGood_subst hF.erGood.2.2 hσ)).2.trans (Expr.erase_subst D hσ)
      exact ⟨U, hU, by rw [he]; exact .cod hs⟩

/-- **Hereditary substitution.**  Substituting a canonical `N : A` (erasing to `base`) into a
canonical derivation yields, after normalization, a canonical derivation.  Induction on the
erasure of `A`, then on the derivation. -/
theorem hsubst_aux (hw : SystemWeaklyNormalizing P) (n : Nat) :
    ∀ (A : Expr S), A.erase.size = n → ∀ (Γ : List (Expr S)) (N : Expr S),
      HasTypeNR P Γ N A → N.erase = .base →
      ∀ Θ M B, HasTypeNR P Θ M B → ∀ Δ, Θ = Δ ++ A :: Γ →
        ∃ Δ' M' B', CtxSubstRed N Δ Δ' ∧ Reduces (M.subst (Expr.substAt N Δ.length)) M' ∧
          Reduces (B.subst (Expr.substAt N Δ.length)) B' ∧ HasTypeNR P (Δ' ++ Γ) M' B' := by
  induction n using Nat.strong_induction_on with
  | _ n IHn =>
  intro A hAn Γ N hN hNb Θ M B h
  have hσ : ∀ k, Expr.BaseSubst (Expr.substAt N k) :=
    Expr.substAt_base hNb hN.erGood.1
  have ctxn : ∀ {Δ' : List (Expr S)} {M' B' : Expr S}, HasTypeNR P (Δ' ++ Γ) M' B' →
      ∀ X ∈ Δ', Normal X := fun h X hX => h.normal.2.2 X (List.mem_append_left _ hX)
  induction h with
  | ax _ => intro Δ heq; cases Δ <;> simp at heq
  | @var Θ₀ A₀ s hA₀ ih =>
      intro Δ heq
      cases Δ with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          refine ⟨[], N, A₀, .nil, ?_, ?_, hN⟩
          · exact .refl
          · simp only [List.length_nil, Expr.substAt_zero, Expr.subst_lift_single]
            exact .refl
      | cons D Δ₀ =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          obtain ⟨Δ', D', T', hc, hD, hT, hD'⟩ := ih Δ₀ rfl
          simp only [Expr.subst] at hT
          rw [Reduces.sort_eq hT] at hD'
          refine ⟨D' :: Δ', .var 0, D'.rename Nat.succ, .cons hc hD, ?_, ?_, .var hD'⟩
          · simp only [List.length_cons, Expr.substAt_succ]
            exact .refl
          · simp only [List.length_cons, Expr.substAt_succ, Expr.rename_succ_subst_lift]
            exact hD.rename _
  | @weaken Θ₀ M₀ B₀ A₀ s hM hA ihM ihA =>
      intro Δ heq
      cases Δ with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          refine ⟨[], M₀, B₀, .nil, ?_, ?_, hM⟩ <;>
            simp only [List.length_nil, Expr.substAt_zero, Expr.subst_lift_single] <;> exact .refl
      | cons D Δ₀ =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          obtain ⟨Δ₁, M', B', hc₁, hMr, hBr, hM'⟩ := ihM Δ₀ rfl
          obtain ⟨Δ₂, D', T', hc₂, hD, hT, hD'⟩ := ihA Δ₀ rfl
          simp only [Expr.subst] at hT
          rw [Reduces.sort_eq hT] at hD'
          obtain rfl := hc₁.unique hc₂ (ctxn hM') (ctxn hD')
          refine ⟨D' :: Δ₁, M'.rename Nat.succ, B'.rename Nat.succ, .cons hc₁ hD, ?_, ?_,
            .weaken hM' hD'⟩ <;>
            simp only [List.length_cons, Expr.substAt_succ, Expr.rename_succ_subst_lift]
          · exact hMr.rename _
          · exact hBr.rename _
  | @product Θ C E s₁ s₂ s₃ hC hE hr ihC ihE =>
      intro Δ heq
      obtain ⟨Δ₁, C', T₁, hc₁, hCr, hT₁, hC'⟩ := ihC Δ heq
      obtain ⟨Δ₂, E', T₂, hc₂, hEr, hT₂, hE'⟩ := ihE (C :: Δ) (by rw [heq]; rfl)
      simp only [Expr.subst] at hT₁
      rw [Reduces.sort_eq hT₁] at hC'
      simp only [Expr.subst] at hT₂
      rw [Reduces.sort_eq hT₂] at hE'
      cases hc₂ with
      | @cons _ Δ₂' _ C'' hc₂ hC'' =>
          have hn := hE'.normal.2.2
          obtain rfl : C'' = C' := Reduces.normal_unique hC'' hCr
            (hn _ (List.mem_cons_self ..)) hC'.normal.1
          obtain rfl := hc₂.unique hc₁ (fun X hX => hn X (by simp [hX])) (ctxn hC')
          refine ⟨Δ₂', .pi C'' E', .sort s₃, hc₁, ?_, .refl, .product hC' hE' hr⟩
          simp only [Expr.subst, ← Expr.substAt_succ]
          exact Reduces.pi hCr hEr
  | @abstraction Θ C b E s hb hP ihb ihP =>
      intro Δ heq
      obtain ⟨Δ₂, b', E', hc₂, hbr, hEr, hb'⟩ := ihb (C :: Δ) (by rw [heq]; rfl)
      obtain ⟨Δ₁, X, T₁, hc₁, hXr, hT₁, hX⟩ := ihP Δ heq
      simp only [Expr.subst] at hT₁
      rw [Reduces.sort_eq hT₁] at hX
      simp only [Expr.subst] at hXr
      obtain ⟨C₁, E₁, rfl, hC₁, hE₁⟩ := Reduces.pi_inv hXr
      cases hc₂ with
      | @cons _ Δ₂' _ C'' hc₂ hC'' =>
          have hn := hb'.normal
          have hXn := hX.normal.1
          obtain rfl : C'' = C₁ := Reduces.normal_unique hC'' hC₁
            (hn.2.2 _ (List.mem_cons_self ..)) hXn.pi_domain
          rw [← Expr.substAt_succ] at hE₁
          obtain rfl : E' = E₁ := Reduces.normal_unique hEr hE₁ hn.2.1 hXn.pi_body
          obtain rfl := hc₂.unique hc₁ (fun X hX => hn.2.2 X (by simp [hX])) (ctxn hX)
          refine ⟨Δ₂', .lam C'' b', .pi C'' E', hc₁, ?_, ?_, .abstraction hb' hX⟩
          · simp only [Expr.subst, ← Expr.substAt_succ]
            exact Reduces.lam hC'' hbr
          · simp only [Expr.subst, ← Expr.substAt_succ]
            exact Reduces.pi hC'' hE₁
  | @application Θ F a C D B₀ hF ha hr hB₀ happ hbase ihF iha =>
      intro Δ heq
      obtain ⟨Δ₁, F', T', hc₁, hFr, hTr, hF'⟩ := ihF Δ heq
      simp only [Expr.subst] at hTr
      obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Reduces.pi_inv hTr
      obtain ⟨Δ₂, a', C', hc₂, har, hCr, ha'⟩ := iha Δ heq
      obtain rfl : C' = A₁ := Reduces.normal_unique hCr hA₁ ha'.normal.2.1
        hF'.normal.2.1.pi_domain
      obtain rfl := hc₂.unique hc₁ (ctxn ha') (ctxn hF')
      set σ := Expr.substAt N Δ.length with hσdef
      have ha'b : a'.erase = .base := by
        rw [(har.erGood_erase (Expr.erGood_subst ha.erGood.1 (hσ _))).2,
          Expr.erase_subst a (hσ _)]
        exact hbase
      have hTy : Reduces ((D.instantiate a).subst σ) (B₁.instantiate a') := by
        rw [← Expr.instantiate_subst]
        exact Reduces.instantiate hB₁ har
      have hB₀σ : Reduces ((D.instantiate a).subst σ) (B₀.subst σ) := hr.subst σ
      by_cases hlam : ∃ C₀ e, F' = .lam C₀ e
      · obtain ⟨C₀, e, rfl⟩ := hlam
        obtain ⟨E₀, s, heqT, he, _⟩ := hF'.lam_inv _ _ rfl
        obtain ⟨rfl, rfl⟩ := Expr.pi.inj heqT
        have hhead : F.headVar = some Δ.length := by
          by_contra hne
          exact subst_noLam N Δ.length F happ.app_left happ.app_not_lam hne _ hFr C' e rfl
        obtain ⟨U, hU, hs⟩ := hF.head_lookup _ hhead
        rw [heq] at hU
        have hUA := lookup_append_erase Δ hU
        have hCg : C.ErGood := hF.erGood.2.1
        have hCe : C'.erase = C.erase :=
          (hA₁.erGood_erase (Expr.erGood_subst hCg (hσ _))).2.trans (Expr.erase_subst C (hσ _))
        have hlt : C'.erase.size < n := by
          rw [hCe, ← hAn, ← hUA]
          exact hs.dom_lt
        obtain ⟨Δ', e', E', hc', her, hEr, he'⟩ :=
          IHn _ hlt C' rfl (Δ₂ ++ Γ) a' ha' ha'b _ e B₁ he ([]) rfl
        cases hc'
        simp only [List.length_nil, Expr.substAt_zero, List.nil_append] at her hEr he'
        refine ⟨Δ₂, e', E', hc₁, ?_, ?_, he'⟩
        · simp only [Expr.subst]
          exact ((Reduces.app hFr har).tail (Beta.head C' e a')).trans her
        · exact Reduces.to_normal hB₀σ (hTy.trans hEr) he'.normal.2.1
      · simp only [not_exists] at hlam
        have happ' : Normal (.app F' a') :=
          Normal.app_of hF'.normal.1 ha'.normal.1 hlam
        have hT : HasType P (Δ₂ ++ Γ) (.app F' a') (B₁.instantiate a') :=
          .application hF'.toHasType ha'.toHasType
        obtain ⟨B'', hred, hnorm⟩ := hw _ hT.valid _ ⟨_, .inr hT⟩
        refine ⟨Δ₂, .app F' a', B'', hc₁, ?_, ?_, .application hF' ha' hred hnorm happ' ha'b⟩
        · simp only [Expr.subst]
          exact Reduces.app hFr har
        · exact Reduces.to_normal hB₀σ (hTy.trans hred) hnorm

/-- Hereditary substitution at the head of the context. -/
theorem hsubst (hw : SystemWeaklyNormalizing P) {Γ : List (Expr S)} {N A M B : Expr S}
    (hN : HasTypeNR P Γ N A) (hNb : N.erase = .base) (hM : HasTypeNR P (A :: Γ) M B) :
    ∃ M' B', Reduces (M.instantiate N) M' ∧ Reduces (B.instantiate N) B' ∧
      HasTypeNR P Γ M' B' := by
  obtain ⟨Δ', M', B', hc, hM', hB', h⟩ :=
    hsubst_aux hw _ A rfl Γ N hN hNb _ M B hM ([]) rfl
  cases hc
  exact ⟨M', B', hM', hB', h⟩

end HasTypeNR

/-! ### Kinds and base-erased arguments -/

namespace Expr

variable {S : Type u}

/-- Syntactic kinds: `Π x₁:A₁. … Π xₙ:Aₙ. s`. -/
def IsKind : Expr S → Prop
  | sort _ => True
  | pi _ B => IsKind B
  | _ => False

/-- Sorts and products. -/
def IsPS : Expr S → Prop
  | sort _ => True
  | pi _ _ => True
  | _ => False

/-- Applications. -/
def IsApp : Expr S → Prop
  | app _ _ => True
  | _ => False

theorem isKind_rename (M : Expr S) (ρ : Nat → Nat) : (M.rename ρ).IsKind ↔ M.IsKind := by
  induction M generalizing ρ with
  | var n => exact Iff.rfl
  | sort s => exact Iff.rfl
  | app f a _ _ => exact Iff.rfl
  | lam A b _ _ => exact Iff.rfl
  | pi A B _ ihB => exact ihB _

theorem isPS_rename (M : Expr S) (ρ : Nat → Nat) : (M.rename ρ).IsPS ↔ M.IsPS := by
  cases M <;> exact Iff.rfl

theorem isApp_rename (M : Expr S) (ρ : Nat → Nat) : (M.rename ρ).IsApp ↔ M.IsApp := by
  cases M <;> exact Iff.rfl

end Expr

namespace HasTypeNR

variable {S : Type u} {P : Specification S}

/-- A canonical term whose type is not a kind erases to `base`. -/
theorem erase_base {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNR P Γ M T) :
    (M.IsPS → ∃ s, T = .sort s) ∧ (M.IsApp → M.erase = .base) ∧
      (¬ T.IsKind → M.erase = .base) := by
  induction h with
  | ax _ => exact ⟨fun _ => ⟨_, rfl⟩, fun h => h.elim, fun h => absurd trivial h⟩
  | var _ _ => exact ⟨fun h => h.elim, fun h => h.elim, fun _ => rfl⟩
  | @weaken Γ M B A s _ _ ihM _ =>
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · obtain ⟨t, rfl⟩ := ihM.1 ((Expr.isPS_rename M _).1 h)
        exact ⟨t, rfl⟩
      · rw [Expr.erase_rename]; exact ihM.2.1 ((Expr.isApp_rename M _).1 h)
      · rw [Expr.erase_rename]; exact ihM.2.2 (fun h' => h ((Expr.isKind_rename B _).2 h'))
  | product => exact ⟨fun _ => ⟨_, rfl⟩, fun h => h.elim, fun h => absurd trivial h⟩
  | abstraction _ _ ihb _ => exact ⟨fun h => h.elim, fun h => h.elim, fun h => ihb.2.2 h⟩
  | @application Γ F a C D B' _ _ _ _ happ _ ihF _ =>
      have hb : (Expr.app F a).erase = .base := by
        cases F with
        | var n => rfl
        | app f c => exact ihF.2.1 trivial
        | lam X e => exact absurd rfl (happ.app_not_lam X e)
        | sort t => obtain ⟨_, h⟩ := ihF.1 trivial; cases h
        | pi X Y => obtain ⟨_, h⟩ := ihF.1 trivial; cases h
      exact ⟨fun h => h.elim, fun _ => hb, fun _ => hb⟩

end HasTypeNR

open LambdaPi (Srt)

/-- In λP no kind has type `∗`. -/
theorem lambdaP_kind_not_star : ∀ (X : Expr Srt) (Γ : List (Expr Srt)), X.IsKind →
    ¬ HasType (cubeSpec lambdaP) Γ X (.sort .star)
  | .sort s, Γ, _, h => by
      obtain ⟨t, ⟨_, rfl⟩, hc⟩ := h.generation
      exact absurd (Converts.sort_inj hc) (by decide)
  | .pi Y K, Γ, hK, h => by
      obtain ⟨s₁, s₂, s₃, _, hK', ⟨rfl, _⟩, hc⟩ := h.generation_pi
      obtain rfl := Converts.sort_inj hc
      exact lambdaP_kind_not_star K (Y :: Γ) hK hK'
  | .var _, _, hK, _ => hK.elim
  | .app _ _, _, hK, _ => hK.elim
  | .lam _ _, _, hK, _ => hK.elim

/-- In λP the domain of the type of a function has type `∗`. -/
theorem lambdaP_domain_star {Γ : List (Expr Srt)} {f A B : Expr Srt}
    (h : HasType (cubeSpec lambdaP) Γ f (.pi A B)) :
    HasType (cubeSpec lambdaP) Γ A (.sort .star) := by
  obtain ⟨s, hP⟩ := h.product_type_sorted
  obtain ⟨s₁, s₂, s₃, hA, _, ⟨_, hal⟩, _⟩ := hP.generation_pi
  cases s₁ with
  | star => exact hA
  | box => cases s₂ <;> simp [lambdaP, CubeFeatures.allows] at hal

theorem lambdaP_weaklyNormalizing : SystemWeaklyNormalizing (cubeSpec lambdaP) :=
  fun Γ hΓ M hM => weaklyNormalizing_of_stronglyNormalizing (cube_lambdaP_sn Γ hΓ M hM)

/-! ### Normalization of reduction-only derivations (λP) -/

theorem forall₂_reduces_unique {S : Type u} {Γ Γ₁ Γ₂ : List (Expr S)}
    (h₁ : List.Forall₂ Reduces Γ Γ₁) (h₂ : List.Forall₂ Reduces Γ Γ₂)
    (hn₁ : ∀ X ∈ Γ₁, Normal X) (hn₂ : ∀ X ∈ Γ₂, Normal X) : Γ₁ = Γ₂ := by
  induction h₁ generalizing Γ₂ with
  | nil => cases h₂; rfl
  | cons hr _ ih =>
      cases h₂ with
      | cons hr' h' =>
          rw [Reduces.normal_unique hr hr' (hn₁ _ (List.mem_cons_self ..))
            (hn₂ _ (List.mem_cons_self ..)),
            ih h' (fun X hX => hn₁ X (List.mem_cons_of_mem _ hX))
              (fun X hX => hn₂ X (List.mem_cons_of_mem _ hX))]

/-- **Normalization of derivations.**  Every reduction-only λP derivation reduces, context,
subject and type together, to a canonical derivation. -/
theorem HasTypeR.normalizeNR {Γ : List (Expr Srt)} {M T : Expr Srt}
    (h : HasTypeR (cubeSpec lambdaP) Γ M T) :
    ∃ Γ' M' T', List.Forall₂ Reduces Γ Γ' ∧ Reduces M M' ∧ Reduces T T' ∧
      HasTypeNR (cubeSpec lambdaP) Γ' M' T' := by
  have hw := lambdaP_weaklyNormalizing
  induction h with
  | ax h => exact ⟨[], _, _, .nil, .refl, .refl, .ax h⟩
  | var _ ih =>
      obtain ⟨Γ', A', T', hc, hAr, hT, hA'⟩ := ih
      rw [Reduces.sort_eq hT] at hA'
      exact ⟨_, _, _, .cons hAr hc, .refl, hAr.rename _, .var hA'⟩
  | weaken _ _ ihM ihA =>
      obtain ⟨Γ₁, M', B', hc₁, hMr, hBr, hM'⟩ := ihM
      obtain ⟨Γ₂, A', T', hc₂, hAr, hT, hA'⟩ := ihA
      rw [Reduces.sort_eq hT] at hA'
      obtain rfl := forall₂_reduces_unique hc₁ hc₂ hM'.normal.2.2 hA'.normal.2.2
      exact ⟨_, _, _, .cons hAr hc₁, hMr.rename _, hBr.rename _, .weaken hM' hA'⟩
  | product _ _ hr ihA ihB =>
      obtain ⟨Γ₁, A', T₁, hc₁, hAr, hT₁, hA'⟩ := ihA
      obtain ⟨Γ₂, B', T₂, hc₂, hBr, hT₂, hB'⟩ := ihB
      rw [Reduces.sort_eq hT₁] at hA'
      rw [Reduces.sort_eq hT₂] at hB'
      cases hc₂ with
      | cons hA'' hc₂ =>
          have hn := hB'.normal.2.2
          obtain rfl := Reduces.normal_unique hA'' hAr (hn _ (List.mem_cons_self ..))
            hA'.normal.1
          obtain rfl := forall₂_reduces_unique hc₂ hc₁
            (fun X hX => hn X (List.mem_cons_of_mem _ hX)) hA'.normal.2.2
          exact ⟨_, _, _, hc₁, Reduces.pi hA'' hBr, .refl, .product hA' hB' hr⟩
  | abstraction _ _ ihb ihP =>
      obtain ⟨Γ₂, b', B', hc₂, hbr, hBr, hb'⟩ := ihb
      obtain ⟨Γ₁, X, T₁, hc₁, hXr, hT₁, hX⟩ := ihP
      rw [Reduces.sort_eq hT₁] at hX
      obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Reduces.pi_inv hXr
      cases hc₂ with
      | cons hA'' hc₂ =>
          have hn := hb'.normal
          have hXn := hX.normal.1
          obtain rfl := Reduces.normal_unique hA'' hA₁ (hn.2.2 _ (List.mem_cons_self ..))
            hXn.pi_domain
          obtain rfl := Reduces.normal_unique hBr hB₁ hn.2.1 hXn.pi_body
          obtain rfl := forall₂_reduces_unique hc₂ hc₁
            (fun X hX => hn.2.2 X (List.mem_cons_of_mem _ hX)) hX.normal.2.2
          exact ⟨_, _, _, hc₁, Reduces.lam hA'' hbr, Reduces.pi hA'' hBr,
            .abstraction hb' hX⟩
  | @application Γ f a A B hf _ ihf iha =>
      obtain ⟨Γ₁, f', T', hc₁, hfr, hTr, hf'⟩ := ihf
      obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Reduces.pi_inv hTr
      obtain ⟨Γ₂, a', A₂, hc₂, har, hAr, ha'⟩ := iha
      obtain rfl := Reduces.normal_unique hAr hA₁ ha'.normal.2.1 hf'.normal.2.1.pi_domain
      obtain rfl := forall₂_reduces_unique hc₂ hc₁ ha'.normal.2.2 hf'.normal.2.2
      have hab : a'.erase = .base :=
        ha'.erase_base.2.2 (fun hk => lambdaP_kind_not_star _ _ hk
          ((lambdaP_domain_star hf.toHasType).subject_reduces hAr))
      have hTy : Reduces (B.instantiate a) (B₁.instantiate a') := Reduces.instantiate hB₁ har
      by_cases hlam : ∃ C e, f' = .lam C e
      · obtain ⟨C, e, rfl⟩ := hlam
        obtain ⟨E, s, heqT, he, _⟩ := hf'.lam_inv _ _ rfl
        obtain ⟨rfl, rfl⟩ := Expr.pi.inj heqT
        obtain ⟨e', E', her, hEr, he'⟩ := HasTypeNR.hsubst hw ha' hab he
        exact ⟨_, e', E', hc₂,
          ((Reduces.app hfr har).tail (Beta.head _ e a')).trans her, hTy.trans hEr, he'⟩
      · simp only [not_exists] at hlam
        have happ' : Normal (.app f' a') := Normal.app_of hf'.normal.1 ha'.normal.1 hlam
        have hT : HasType (cubeSpec lambdaP) Γ₂ (.app f' a') (B₁.instantiate a') :=
          .application hf'.toHasType ha'.toHasType
        obtain ⟨B'', hred, hnorm⟩ := hw _ hT.valid _ ⟨_, .inr hT⟩
        exact ⟨_, _, B'', hc₂, Reduces.app hfr har, hTy.trans hred,
          .application hf' ha' hred hnorm happ' hab⟩
  | reduction _ hAB ih =>
      obtain ⟨Γ', M', A', hc, hMr, hAr, hM'⟩ := ih
      exact ⟨Γ', M', A', hc, hMr,
        Reduces.to_normal (Relation.ReflTransGen.single hAB) hAr hM'.normal.2.1, hM'⟩

/-! ### Context expansion -/

/-- Context expansion for the reduction-only system: a derivation in a reduct of a valid
context is a derivation in the context itself. -/
theorem HasTypeR.ctx_expand {S : Type u} {P : Specification S} {Γ' : List (Expr S)}
    {M T : Expr S} (h : HasTypeR P Γ' M T) :
    ∀ Γ, ValidContextR P Γ → List.Forall₂ Reduces Γ Γ' → HasTypeR P Γ M T := by
  induction h with
  | ax h => intro Γ _ hc; cases hc; exact .ax h
  | var _ _ =>
      intro Γ hΓ hc
      cases hc with
      | cons hAA _ =>
          cases hΓ with
          | cons _ hA => exact (HasTypeR.var hA).reduces (hAA.rename _)
  | weaken _ _ ihM _ =>
      intro Γ hΓ hc
      cases hc with
      | cons _ hc₀ =>
          cases hΓ with
          | cons hΓ₁ hA => exact .weaken (ihM _ hΓ₁ hc₀) hA
  | product _ _ hr ihA ihB =>
      intro Γ hΓ hc
      have hA := ihA Γ hΓ hc
      exact .product hA (ihB _ (.cons hΓ hA) (.cons .refl hc)) hr
  | abstraction _ _ ihb ihP =>
      intro Γ hΓ hc
      have hP := ihP Γ hΓ hc
      obtain ⟨t, hA⟩ := hP.product_domain _ _ rfl
      exact .abstraction (ihb _ (.cons hΓ hA) (.cons .refl hc)) hP
  | application _ _ ihf iha =>
      intro Γ hΓ hc
      exact .application (ihf Γ hΓ hc) (iha Γ hΓ hc)
  | reduction _ hAB ih =>
      intro Γ hΓ hc
      exact .reduction (ih Γ hΓ hc) hAB

/-! ### Expansion postponement for λP -/

/-- Product normalization for λP. -/
theorem lambdaP_productNormalizationR : ProductNormalizationR (cubeSpec lambdaP) := by
  intro Γ A B B' s hP hBB' hB'n
  obtain ⟨s₁, s₂, s₃, hA, hB, hr, hs⟩ := hP.generation_pi A B rfl
  obtain ⟨Γ', M', T', hc, hM, hT, hNR⟩ := hB.normalizeNR
  rw [Reduces.sort_eq hT] at hNR
  obtain rfl := Reduces.normal_unique hM hBB' hNR.normal.1 hB'n
  have hB' := hNR.toHasTypeR.ctx_expand (A :: Γ) hB.valid hc
  cases hs
  exact .product hA hB' hr

/-- **Expansion postponement for λP** (TLCA open problem 23, the λP corner of the cube). -/
theorem lambdaP_expansionPostponement : ExpansionPostponement (cubeSpec lambdaP) :=
  cube_expansionPostponement_of_productNormalizationR lambdaP lambdaP_productNormalizationR

end PureTypeSystem
