/-
Intersection type assignment for the untyped lambda calculus, in strict (normalised) form.

This module introduces the type assignment system `λ∩` of Coppo, Dezani-Ciancaglini and
Venneri (the system `DΩ` of Krivine's book), presented in the *strict* normal form of van
Bakel: a type is either an atom or an arrow `a → σ` whose source `a` is a **finite
intersection** of strict types and whose target `σ` is again strict.  The empty intersection
is the universal type `ω`.

Strict types are exactly the tokens `GraphModel.Tok` of Scott's graph model, and this is not a
coincidence: `Start/FilterModel.lean` proves that the set of types assignable to a term *is*
its denotation in the graph model.  Consequently the graph model is the filter model of this
type system, and "syntactically typable" and "semantically different from `⊥`" become literally
the same statement.

Contents:

* `Inter.Sty`, `Inter.Ty`, `Inter.Basis` — strict types, intersections, bases;
* `Inter.Deriv` — the type assignment relation `Γ ⊢ M : σ`, with the intersection-elimination
  built into the variable rule and intersection-introduction built into the application rule;
* `Inter.DerivI` — the derived judgement `Γ ⊢ M : a` for a general (intersection) type, so that
  `Γ ⊢ M : ω` holds vacuously for every `M`;
* generation (inversion) lemmas for the three syntactic shapes;
* `Inter.Deriv.weaken` — weakening in the basis;
* `Inter.Typable` — being typable at all.

`Start/FilterModel.lean` contains the semantic results (subject reduction and expansion, and
the characterisation of typability by head normalisation).
-/

import Start.GraphModelSemantics

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Inter

open GraphModel

/-- A **strict** intersection type: an atom, or an arrow whose source is a finite intersection.
These are precisely the tokens of Scott's graph model. -/
abbrev Sty : Type := GraphModel.Tok

/-- A general intersection type is a finite list of strict types, read as their intersection.
The empty list is the universal type `ω`. -/
abbrev Ty : Type := List Sty

/-- The universal type `ω`: the empty intersection. -/
def omegaTy : Ty := []

/-- A basis assigns an intersection type to every de Bruijn index. -/
abbrev Basis : Type := ℕ → Ty

/-- Extend a basis with a type for the index `0`. -/
def push (a : Ty) (Γ : Basis) : Basis := fun i =>
  match i with
  | 0 => a
  | (j + 1) => Γ j

@[simp] theorem push_zero (a : Ty) (Γ : Basis) : push a Γ 0 = a := rfl
@[simp] theorem push_succ (a : Ty) (Γ : Basis) (j : ℕ) : push a Γ (j + 1) = Γ j := rfl

/-- **Type assignment** `Γ ⊢ M : σ` for strict types.

* `var`: any component of the intersection assigned to a variable may be selected — this is
  intersection elimination;
* `app`: the argument must carry *every* component of the source of the arrow — this is
  intersection introduction (and, when the source is `ω`, no requirement at all);
* `lam`: abstraction. -/
inductive Deriv : Basis → Lambda → Sty → Prop
  | var {Γ : Basis} {i : ℕ} {σ : Sty} : σ ∈ Γ i → Deriv Γ (Lambda.var i) σ
  | app {Γ : Basis} {M N : Lambda} {a : Ty} {σ : Sty} :
      Deriv Γ M (Tok.arrow a σ) → (∀ τ ∈ a, Deriv Γ N τ) → Deriv Γ (Lambda.app M N) σ
  | lam {Γ : Basis} {M : Lambda} {a : Ty} {σ : Sty} :
      Deriv (push a Γ) M σ → Deriv Γ (Lambda.lam M) (Tok.arrow a σ)

/-- Type assignment for a general intersection type: every component must be derivable.
For the empty intersection `ω` this is vacuously true, which is the `ω` rule. -/
def DerivI (Γ : Basis) (M : Lambda) (a : Ty) : Prop := ∀ σ ∈ a, Deriv Γ M σ

theorem derivI_omega (Γ : Basis) (M : Lambda) : DerivI Γ M omegaTy := by
  intro σ hσ
  exact absurd hσ (by simp [omegaTy])

theorem derivI_append {Γ : Basis} {M : Lambda} {a b : Ty}
    (ha : DerivI Γ M a) (hb : DerivI Γ M b) : DerivI Γ M (a ++ b) := by
  intro σ hσ
  rcases List.mem_append.1 hσ with h | h
  · exact ha σ h
  · exact hb σ h

theorem derivI_of_subset {Γ : Basis} {M : Lambda} {a b : Ty}
    (h : ∀ σ ∈ b, σ ∈ a) (ha : DerivI Γ M a) : DerivI Γ M b :=
  fun σ hσ => ha σ (h σ hσ)

/-! ### Generation lemmas -/

theorem deriv_var_iff {Γ : Basis} {i : ℕ} {σ : Sty} :
    Deriv Γ (Lambda.var i) σ ↔ σ ∈ Γ i := by
  constructor
  · intro h; cases h with | var h => exact h
  · exact Deriv.var

theorem deriv_app_iff {Γ : Basis} {M N : Lambda} {σ : Sty} :
    Deriv Γ (Lambda.app M N) σ ↔ ∃ a : Ty, Deriv Γ M (Tok.arrow a σ) ∧ DerivI Γ N a := by
  constructor
  · intro h
    cases h with | app hM hN => exact ⟨_, hM, hN⟩
  · rintro ⟨a, hM, hN⟩
    exact Deriv.app hM hN

theorem deriv_lam_iff {Γ : Basis} {M : Lambda} {σ : Sty} :
    Deriv Γ (Lambda.lam M) σ ↔ ∃ a : Ty, ∃ τ : Sty, σ = Tok.arrow a τ ∧ Deriv (push a Γ) M τ := by
  constructor
  · intro h
    cases h with | lam h => exact ⟨_, _, rfl, h⟩
  · rintro ⟨a, τ, rfl, h⟩
    exact Deriv.lam h

/-- No atom can be assigned to an abstraction. -/
theorem not_deriv_lam_atom {Γ : Basis} {M : Lambda} {n : ℕ} :
    ¬ Deriv Γ (Lambda.lam M) (Tok.atom n) := by
  intro h
  obtain ⟨a, τ, hσ, -⟩ := deriv_lam_iff.1 h
  exact Tok.noConfusion hσ

/-! ### Weakening -/

/-- Enlarging every entry of the basis preserves derivability. -/
theorem Deriv.weaken {Γ : Basis} {M : Lambda} {σ : Sty} (h : Deriv Γ M σ)
    {Γ' : Basis} (hΓ : ∀ i, ∀ τ ∈ Γ i, τ ∈ Γ' i) : Deriv Γ' M σ := by
  induction h generalizing Γ' with
  | var hi => exact Deriv.var (hΓ _ _ hi)
  | app _ _ ihM ihN =>
      refine Deriv.app (ihM hΓ) ?_
      intro τ hτ
      exact ihN τ hτ hΓ
  | @lam Γ₀ M₀ a σ₀ _ ih =>
      refine Deriv.lam (ih ?_)
      intro i τ hτ
      cases i with
      | zero => exact hτ
      | succ j => exact hΓ j τ hτ

/-- A term is *typable* when some basis assigns it some strict type. -/
def Typable (M : Lambda) : Prop := ∃ Γ : Basis, ∃ σ : Sty, Deriv Γ M σ

theorem typable_var (i : ℕ) : Typable (Lambda.var i) :=
  ⟨fun _ => [Tok.atom 0], Tok.atom 0, Deriv.var (by simp)⟩

end Inter
