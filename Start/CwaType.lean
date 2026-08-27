/-
The standard (set-theoretic) model of dependent type theory: the category with attributes of
**families of types**, whose contexts are types, whose types in a context `Γ` are families
`Γ → Type u`, whose context extension is the sigma type and whose dependent product is the
dependent function type.

* `CwaType.families` — the category with attributes on `Type u`;
* `CwaType.secEquiv` — its terms are exactly the dependent functions `∀ x, A x`, the display map
  being the first projection out of the sigma type;
* `CwaType.piStruct` — the Π-structure, with `Pi A B x = (a : A x) → B ⟨x, a⟩`; the
  Beck–Chevalley condition (stability of Π under substitution) holds *definitionally* here;
* `CwaType.piStruct_lam`, `CwaType.piStruct_app` — the abstract `lam`/`app` of the model are
  ordinary abstraction and application of dependent functions.

`Start/LcccType.lean` identifies this Π with the categorical dependent product (the pushforward
right adjoint to pullback) of the locally cartesian closed structure of `Type u`.
-/

import Start.Cwa
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace CwaType

/-- Context extension in the standard model: the total space of a family. -/
abbrev Total {Γ : Type u} (A : Γ → Type u) : Type u := Σ x : Γ, A x

theorem sigma_mk_eq {Γ : Type u} {A : Γ → Type u} (p : Total A) (x₀ : Γ) (h : p.1 = x₀) :
    (⟨x₀, h ▸ p.2⟩ : Total A) = p := by
  obtain ⟨x, a⟩ := p
  cases h
  rfl

/-- The category with attributes of families of types: contexts are types, a type in context `Γ`
is a family `Γ → Type u`, and context extension is the sigma type. -/
@[reducible] def families : Cwa.{u + 1, u, u + 1} (Type u) where
  Ty Γ := Γ → Type u
  tySub σ A := fun d => A (σ d)
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  ext _ A := Total A
  disp _ := ↾Sigma.fst
  extend σ A := ↾fun p => ⟨σ p.1, p.2⟩
  isPullback := by
    intro Γ Δ σ A
    rw [Types.isPullback_iff]
    refine ⟨rfl, ?_, ?_⟩
    · rintro ⟨d₁, a₁⟩ ⟨d₂, a₂⟩ ⟨h₁, h₂⟩
      cases h₂
      simpa using h₁
    · rintro ⟨x, a⟩ d hx
      cases hx
      exact ⟨⟨d, a⟩, rfl, rfl⟩

@[simp] theorem families_Ty (Γ : Type u) : families.Ty Γ = (Γ → Type u) := rfl

@[simp] theorem families_ext {Γ : Type u} (A : Γ → Type u) :
    families.ext Γ A = Total A := rfl

@[simp] theorem families_tySub {Γ Δ : Type u} (σ : Δ ⟶ Γ) (A : Γ → Type u) :
    families.tySub σ A = fun d => A (σ d) := rfl

/-- A term of the standard model is a section of the first projection; the condition says
precisely that the section does not move the base point. -/
theorem tm_base {Γ : Type u} {A : Γ → Type u} (a : families.Tm Γ A) (x : Γ) :
    (a.1 x).1 = x := by
  simpa using ConcreteCategory.congr_hom a.2 x

/-- **Terms of the standard model are dependent functions.** -/
def secEquiv {Γ : Type u} (A : Γ → Type u) : families.Tm Γ A ≃ ∀ x, A x where
  toFun a := fun x => (tm_base a x) ▸ (a.1 x).2
  invFun f := ⟨↾fun x => ⟨x, f x⟩, rfl⟩
  left_inv a := by
    refine Subtype.ext (ConcreteCategory.hom_ext _ _ fun x => ?_)
    exact sigma_mk_eq (a.1 x) x (tm_base a x)
  right_inv f := by funext x; rfl

/-- Currying for dependent functions out of a sigma type. -/
def piEquiv {Γ : Type u} (A : Γ → Type u) (B : Total A → Type u) :
    (∀ p : Total A, B p) ≃ ∀ x, (a : A x) → B ⟨x, a⟩ where
  toFun f := fun x a => f ⟨x, a⟩
  invFun g := fun p => g p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The Π-structure of the standard model: the dependent function type. -/
def piStruct : Cwa.PiStruct families where
  Pi A B := fun x => (a : A x) → B ⟨x, a⟩
  Pi_sub _ _ _ := rfl
  lam {_ A B} b := (secEquiv _).symm (piEquiv A B (secEquiv B b))
  app {_ A B} f := (secEquiv B).symm ((piEquiv A B).symm (secEquiv _ f))
  app_lam b := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  lam_app f := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- The Σ-structure of the standard model: the dependent sum type.  Its Beck–Chevalley condition
holds definitionally, and the pairing isomorphism is the associativity of sigma types. -/
def sigmaStruct : Cwa.SigmaStruct families.{u} where
  Sig {_Γ} A B := fun x => ((Σ a : A x, B ⟨x, a⟩ : Type u))
  Sig_sub _ _ _ := rfl
  pair {Γ} A B := Equiv.toIso (Equiv.sigmaAssoc (fun (x : Γ) (a : A x) => B ⟨x, a⟩))
  pair_disp _ _ := rfl

@[simp] theorem sigmaStruct_Sig {Γ : Type u} (A : Γ → Type u) (B : Total A → Type u) :
    sigmaStruct.Sig A B = fun x => ((Σ a : A x, B ⟨x, a⟩ : Type u)) := rfl

@[simp] theorem piStruct_Pi {Γ : Type u} (A : Γ → Type u) (B : Total A → Type u) :
    piStruct.Pi A B = fun x => (a : A x) → B ⟨x, a⟩ := rfl

/-- The abstraction of the model is ordinary abstraction of dependent functions. -/
theorem piStruct_lam {Γ : Type u} {A : Γ → Type u} {B : Total A → Type u}
    (b : families.Tm (Total A) B) :
    secEquiv _ (piStruct.lam b) = fun x a => secEquiv B b ⟨x, a⟩ := by
  simp only [piStruct, piEquiv]
  exact Equiv.apply_symm_apply _ _

/-- The application of the model is ordinary application of dependent functions. -/
theorem piStruct_app {Γ : Type u} {A : Γ → Type u} {B : Total A → Type u}
    (f : families.Tm Γ (piStruct.Pi A B)) :
    secEquiv _ (piStruct.app f) = fun p : Total A => secEquiv _ f p.1 p.2 := by
  simp only [piStruct, piEquiv, Equiv.apply_symm_apply]
  rfl

end CwaType
