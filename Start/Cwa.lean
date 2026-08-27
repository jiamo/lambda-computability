/-
Categories with attributes: the categorical structure that interprets a *dependent* type theory.

`Start/StlcCcc.lean` matched the simply typed lambda calculus with cartesian closed categories.
Once types may depend on terms, a plain category of types is no longer enough: a type lives *in a
context*, and substitution must act on types.  The standard structure that records this is a
**category with attributes** (Cartmell; equivalently, a split comprehension category, or the
"types + context extension" half of a category with families).

* `Cwa C` — a category with attributes over a category `C` of contexts: a strict presheaf of
  types `Ty`, context extension `ext Γ A` with its display map `disp A : ext Γ A ⟶ Γ`, and the
  requirement that the extension squares are pullbacks (`Cwa.isPullback`), which is exactly the
  statement that substitution into an extended context is "a substitution plus a term";
* `Cwa.Tm Γ A` — terms of `A` in context `Γ`, defined as *sections* of the display map, and
  `Cwa.tmSub` — their substitution, built from the pullback property;
* `Cwa.PiStruct` — a Π-type structure: a type former `Pi A B` stable under substitution
  (`Pi_sub`, the Beck–Chevalley condition) together with a bijection `lam`/`app` between terms of
  `B` in the extended context and terms of `Pi A B`;
* `Cwa.NaturalPiStruct` — a Π-structure whose abstraction is also stable under substitution,
  which is the law a model needs in order to interpret a calculus with substitution.

Two models of this interface are built in the project: the standard set-theoretic one in
`Start/CwaType.lean` (where the categorical Π is the dependent product, and is identified with
the pushforward of the locally cartesian closed structure of `Type` in `Start/LcccType.lean`),
and the syntactic one in `Start/LambdaPiCwa.lean`, built from the contexts and substitutions of
the dependently typed calculus `λΠ`.
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

/-- A **category with attributes** over the category `C` of contexts: a strictly functorial
assignment of types to contexts, together with context extension whose squares are pullbacks. -/
structure Cwa (C : Type u) [Category.{v} C] where
  /-- The types in a context. -/
  Ty : C → Type w
  /-- Substitution acting on types. -/
  tySub : {Γ Δ : C} → (Δ ⟶ Γ) → Ty Γ → Ty Δ
  /-- Substituting the identity does nothing. -/
  tySub_id : ∀ {Γ : C} (A : Ty Γ), tySub (𝟙 Γ) A = A
  /-- Substitution is strictly functorial. -/
  tySub_comp : ∀ {Γ Δ Θ : C} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (A : Ty Γ),
      tySub (τ ≫ σ) A = tySub τ (tySub σ A)
  /-- Context extension. -/
  ext : (Γ : C) → Ty Γ → C
  /-- The display map (weakening) out of an extended context. -/
  disp : {Γ : C} → (A : Ty Γ) → ext Γ A ⟶ Γ
  /-- The action of a substitution on extended contexts. -/
  extend : {Γ Δ : C} → (σ : Δ ⟶ Γ) → (A : Ty Γ) → ext Δ (tySub σ A) ⟶ ext Γ A
  /-- Context extension squares are pullbacks: this is the universal property that says a
  substitution into `ext Γ A` is a substitution into `Γ` together with a term of `A`. -/
  isPullback : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (A : Ty Γ),
      IsPullback (extend σ A) (disp (tySub σ A)) (disp A) σ

namespace Cwa

variable {C : Type u} [Category.{v} C] (T : Cwa.{u, v, w} C)

/-- A term of type `A` in context `Γ` is a section of the display map of `A`. -/
def Tm (Γ : C) (A : T.Ty Γ) : Type v := {s : Γ ⟶ T.ext Γ A // s ≫ T.disp A = 𝟙 Γ}

variable {T}

@[ext] theorem Tm.ext' {Γ : C} {A : T.Ty Γ} {a b : T.Tm Γ A} (h : a.1 = b.1) : a = b :=
  Subtype.ext h

/-- Transport a term along an equality of types. -/
def tmCast {Γ : C} {A A' : T.Ty Γ} (h : A = A') (a : T.Tm Γ A) : T.Tm Γ A' := h ▸ a

@[simp] theorem tmCast_rfl {Γ : C} {A : T.Ty Γ} (a : T.Tm Γ A) : tmCast rfl a = a := rfl

/-- Substitution of terms, obtained from the universal property of context extension. -/
noncomputable def tmSub {Γ Δ : C} (σ : Δ ⟶ Γ) {A : T.Ty Γ} (a : T.Tm Γ A) :
    T.Tm Δ (T.tySub σ A) := by
  refine ⟨(T.isPullback σ A).lift (σ ≫ a.1) (𝟙 Δ) ?_, ?_⟩
  · rw [Category.assoc, a.2, Category.comp_id, Category.id_comp]
  · exact (T.isPullback σ A).lift_snd _ _ _

/-- The generic term of `A` in the extended context `ext Γ A`, i.e. the de Bruijn variable `0`. -/
noncomputable def var {Γ : C} (A : T.Ty Γ) : T.Tm (T.ext Γ A) (T.tySub (T.disp A) A) := by
  refine ⟨(T.isPullback (T.disp A) A).lift (𝟙 _) (𝟙 _) ?_, ?_⟩
  · simp
  · exact (T.isPullback (T.disp A) A).lift_snd _ _ _

/-- A **weak Π-type structure** on a category with attributes: a dependent product former which
is stable under substitution, with abstraction and application satisfying the β-law only.  This
is what a type theory with β-reduction but no η-rule (such as the calculus `λΠ` of
`Start/LambdaPi.lean`) provides. -/
structure WeakPiStruct (T : Cwa.{u, v, w} C) where
  /-- The dependent product of a family `B` over `A`. -/
  Pi : {Γ : C} → (A : T.Ty Γ) → T.Ty (T.ext Γ A) → T.Ty Γ
  /-- Beck–Chevalley: the dependent product is stable under substitution. -/
  Pi_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (A : T.Ty Γ) (B : T.Ty (T.ext Γ A)),
      T.tySub σ (Pi A B) = Pi (T.tySub σ A) (T.tySub (T.extend σ A) B)
  /-- Abstraction. -/
  lam : {Γ : C} → {A : T.Ty Γ} → {B : T.Ty (T.ext Γ A)} →
      T.Tm (T.ext Γ A) B → T.Tm Γ (Pi A B)
  /-- Application, in the "generic argument" form. -/
  app : {Γ : C} → {A : T.Ty Γ} → {B : T.Ty (T.ext Γ A)} →
      T.Tm Γ (Pi A B) → T.Tm (T.ext Γ A) B
  /-- β: applying an abstraction gives the body back. -/
  app_lam : ∀ {Γ : C} {A : T.Ty Γ} {B : T.Ty (T.ext Γ A)} (b : T.Tm (T.ext Γ A) B),
      app (lam b) = b

/-- A **Π-type structure** on a category with attributes: a weak Π-structure whose abstraction
and application are mutually inverse, i.e. which also satisfies the η-law.  This is the form the
categorical dependent product (the right adjoint to substitution) takes. -/
structure PiStruct (T : Cwa.{u, v, w} C) extends WeakPiStruct T where
  /-- η: abstracting an application gives the function back. -/
  lam_app : ∀ {Γ : C} {A : T.Ty Γ} {B : T.Ty (T.ext Γ A)} (f : T.Tm Γ (toWeakPiStruct.Pi A B)),
      toWeakPiStruct.lam (toWeakPiStruct.app f) = f

/-- A **natural Π-type structure**: a Π-structure whose abstraction is also stable under
substitution, `(λ b)[σ] = λ (b[σ⁺])`.  The bare `PiStruct` interface constrains the type former
only; this is the extra law a model needs in order to interpret a calculus with substitution. -/
structure NaturalPiStruct (T : Cwa.{u, v, w} C) extends PiStruct T where
  /-- Abstraction commutes with substitution. -/
  lam_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) {A : T.Ty Γ} {B : T.Ty (T.ext Γ A)}
      (b : T.Tm (T.ext Γ A) B),
      tmCast (toPiStruct.Pi_sub σ A B) (T.tmSub σ (toPiStruct.lam b)) =
        toPiStruct.lam (T.tmSub (T.extend σ A) b)

/-- A **Σ-type structure** on a category with attributes: a dependent sum former, stable under
substitution, whose context extension is the two-step extension.  The isomorphism `pair` is the
pairing/projection bijection: to give a term of `Sig A B` is to give a term `a` of `A` together
with a term of `B` over it. -/
structure SigmaStruct (T : Cwa.{u, v, w} C) where
  /-- The dependent sum of a family `B` over `A`. -/
  Sig : {Γ : C} → (A : T.Ty Γ) → T.Ty (T.ext Γ A) → T.Ty Γ
  /-- Beck–Chevalley: the dependent sum is stable under substitution. -/
  Sig_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (A : T.Ty Γ) (B : T.Ty (T.ext Γ A)),
      T.tySub σ (Sig A B) = Sig (T.tySub σ A) (T.tySub (T.extend σ A) B)
  /-- Pairing: extending by `A` and then by `B` is the same as extending by `Sig A B`. -/
  pair : {Γ : C} → (A : T.Ty Γ) → (B : T.Ty (T.ext Γ A)) →
      T.ext (T.ext Γ A) B ≅ T.ext Γ (Sig A B)
  /-- The pairing isomorphism lives over the base context. -/
  pair_disp : ∀ {Γ : C} (A : T.Ty Γ) (B : T.Ty (T.ext Γ A)),
      (pair A B).hom ≫ T.disp (Sig A B) = T.disp B ≫ T.disp A

namespace PiStruct

variable (P : PiStruct T)

/-- The bijection between terms of the body and terms of the dependent product. -/
def equiv {Γ : C} (A : T.Ty Γ) (B : T.Ty (T.ext Γ A)) :
    T.Tm (T.ext Γ A) B ≃ T.Tm Γ (P.Pi A B) where
  toFun := P.lam
  invFun := P.app
  left_inv := P.app_lam
  right_inv := P.lam_app

end PiStruct

end Cwa
