/-
A **universe of small types** in a category with attributes, and dependent products over it.

`Start/Cwa.lean` gives the interface of a category with attributes and `Start/CwaPi.lean` a
dependent product on it, where the product may be formed over *any* type.  The calculus `λΠ` of
`Start/LambdaPi.lean` is not of that shape: its types are stratified, a product may only be formed
over a term of the sort `∗`, and the types of the calculus *are* the terms of `∗`.  A model of
`λΠ` therefore needs one more piece of structure — a type `U` of the model whose terms name types
of the model, closed under dependent products.  That is what is defined here.

* `Cwa.Universe T` — a universe à la Tarski in a category with attributes: a type `U Γ` in every
  context, strictly stable under substitution, together with a decoding `El` of its terms as types,
  again strictly stable under substitution;
* `Cwa.Universe.sub` — substitution acting on the codes, i.e. on the terms of `U`;
* `Cwa.Universe.extHom`, `Cwa.Universe.isPullback_extHom` — the context-extension square for a
  decoded type, whose top-left corner is written with the *substituted code* rather than with the
  substituted type;
* `Cwa.Universe.SmallPi` — a dependent product over the small types: a product `Pi a B` of a family
  `B` over the decoding of a code `a`, stable under substitution, with abstraction, application and
  the β-law;
* `Cwa.Universe.PiClosed` — the universe is **closed** under those products: a code `code a b` for
  the product of two small types, with `El (code a b) = Pi a (El b)`;
* `Cwa.Universe.smallPiOfWeakPi` — a model whose products are defined over *all* types has, in
  particular, products over the small ones.

`Start/LambdaPiUniv.lean` builds the syntactic instance: the contexts of `λΠ` with *all* of its
types (not only the small ones) form a category with attributes, `∗` is a universe in it, and the
product rules `(∗,∗)` and `(∗,□)` give exactly a `SmallPi` structure.
-/

import Start.Cwa

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] {T : Cwa.{u, v, w} C}

/-! ### Terms and substitution -/

/-- A term substitution is determined by its composite with the action on extended contexts:
`tmSub σ a` is the *only* section of the substituted display map whose composite with
`extend σ A` is `σ ≫ a`. -/
theorem tmSub_eq_of {Γ Δ : C} (σ : Δ ⟶ Γ) {A : T.Ty Γ} (a : T.Tm Γ A)
    (s : T.Tm Δ (T.tySub σ A)) (h : s.1 ≫ T.extend σ A = σ ≫ a.1) :
    s = T.tmSub σ a := by
  refine Tm.ext' ((T.isPullback σ A).hom_ext ?_ ?_)
  · rw [h]
    exact ((T.isPullback σ A).lift_fst (σ ≫ a.1) (𝟙 Δ) (by simp [a.2])).symm
  · rw [s.2]
    exact ((T.isPullback σ A).lift_snd (σ ≫ a.1) (𝟙 Δ) (by simp [a.2])).symm

/-- The defining property of the substitution of a term. -/
theorem tmSub_extend {Γ Δ : C} (σ : Δ ⟶ Γ) {A : T.Ty Γ} (a : T.Tm Γ A) :
    (T.tmSub σ a).1 ≫ T.extend σ A = σ ≫ a.1 :=
  (T.isPullback σ A).lift_fst _ _ (by simp [a.2])

/-- The context-extension square, written with a type that is *equal* to the substituted one. -/
theorem isPullback_extend_of_eq {Γ Δ : C} (σ : Δ ⟶ Γ) (A : T.Ty Γ) {A' : T.Ty Δ}
    (h : T.tySub σ A = A') :
    IsPullback (eqToHom (congrArg (T.ext Δ) h).symm ≫ T.extend σ A) (T.disp A') (T.disp A) σ := by
  cases h
  simpa using T.isPullback σ A

/-! ### Universes -/

/-- A **universe of small types** in a category with attributes: a type `U Γ` in every context,
stable under substitution on the nose, whose terms are *codes* for types, decoded by `El`, again
stably under substitution.  This is a universe à la Tarski: the codes are terms of a type of the
model, and decoding is an operation of the model, not an inclusion. -/
structure Universe (T : Cwa.{u, v, w} C) where
  /-- The type of codes for small types. -/
  U : (Γ : C) → T.Ty Γ
  /-- The universe is stable under substitution. -/
  U_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ), T.tySub σ (U Γ) = U Δ
  /-- Decoding: a code names a type. -/
  El : {Γ : C} → T.Tm Γ (U Γ) → T.Ty Γ
  /-- Decoding is stable under substitution. -/
  El_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (a : T.Tm Γ (U Γ)),
      T.tySub σ (El a) = El (tmCast (U_sub σ) (T.tmSub σ a))

namespace Universe

variable (Un : Universe T)

/-- Substitution acting on codes. -/
noncomputable def sub {Γ Δ : C} (σ : Δ ⟶ Γ) (a : T.Tm Γ (Un.U Γ)) : T.Tm Δ (Un.U Δ) :=
  tmCast (Un.U_sub σ) (T.tmSub σ a)

theorem El_sub' {Γ Δ : C} (σ : Δ ⟶ Γ) (a : T.Tm Γ (Un.U Γ)) :
    T.tySub σ (Un.El a) = Un.El (Un.sub σ a) := Un.El_sub σ a

/-- Extending by the decoding of a substituted code is extending by the substituted decoding. -/
theorem ext_El_sub {Γ Δ : C} (σ : Δ ⟶ Γ) (a : T.Tm Γ (Un.U Γ)) :
    T.ext Δ (T.tySub σ (Un.El a)) = T.ext Δ (Un.El (Un.sub σ a)) :=
  congrArg (T.ext Δ) (Un.El_sub' σ a)

/-- The action of a substitution on a context extended by a decoded type. -/
noncomputable def extHom {Γ Δ : C} (σ : Δ ⟶ Γ) (a : T.Tm Γ (Un.U Γ)) :
    T.ext Δ (Un.El (Un.sub σ a)) ⟶ T.ext Γ (Un.El a) :=
  eqToHom (Un.ext_El_sub σ a).symm ≫ T.extend σ (Un.El a)

/-- The extension square of a decoded type is a pullback. -/
theorem isPullback_extHom {Γ Δ : C} (σ : Δ ⟶ Γ) (a : T.Tm Γ (Un.U Γ)) :
    IsPullback (Un.extHom σ a) (T.disp (Un.El (Un.sub σ a))) (T.disp (Un.El a)) σ :=
  isPullback_extend_of_eq σ (Un.El a) (Un.El_sub' σ a)

/-- A **dependent product over the small types**: a product may be formed over the decoding of a
code, its body being an arbitrary type of the model; the product is stable under substitution and
has abstraction, application and the β-law.  The last two fields say that the universe is *closed*
under these products: the product of two small types is again small, `El (code a b) = Pi a (El b)`.

This is exactly the shape of the product rules of `λΠ`: `(∗,∗)` forms a product of two small types,
`(∗,□)` a product whose body is a kind; in both cases the domain is small. -/
structure SmallPi (Un : Universe T) where
  /-- The dependent product of `B` over the type named by `a`. -/
  Pi : {Γ : C} → (a : T.Tm Γ (Un.U Γ)) → T.Ty (T.ext Γ (Un.El a)) → T.Ty Γ
  /-- Beck–Chevalley: the product is stable under substitution. -/
  Pi_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (a : T.Tm Γ (Un.U Γ)) (B : T.Ty (T.ext Γ (Un.El a))),
      T.tySub σ (Pi a B) = Pi (Un.sub σ a) (T.tySub (Un.extHom σ a) B)
  /-- Abstraction. -/
  lam : {Γ : C} → {a : T.Tm Γ (Un.U Γ)} → {B : T.Ty (T.ext Γ (Un.El a))} →
      T.Tm (T.ext Γ (Un.El a)) B → T.Tm Γ (Pi a B)
  /-- Application, in the "generic argument" form. -/
  app : {Γ : C} → {a : T.Tm Γ (Un.U Γ)} → {B : T.Ty (T.ext Γ (Un.El a))} →
      T.Tm Γ (Pi a B) → T.Tm (T.ext Γ (Un.El a)) B
  /-- β: applying an abstraction gives the body back. -/
  app_lam : ∀ {Γ : C} {a : T.Tm Γ (Un.U Γ)} {B : T.Ty (T.ext Γ (Un.El a))}
      (b : T.Tm (T.ext Γ (Un.El a)) B), app (lam b) = b

/-- **The universe is closed under dependent products**: the product of two small types is again
small, and its code decodes to the product.  This is the piece of structure that the type former
of a category with attributes does not provide: it makes the *type* `Pi a (El b)` the decoding of
a *term* of the universe. -/
structure PiClosed (Un : Universe T) (P : SmallPi Un) where
  /-- A code for the product of two small types. -/
  code : {Γ : C} → (a : T.Tm Γ (Un.U Γ)) → T.Tm (T.ext Γ (Un.El a)) (Un.U (T.ext Γ (Un.El a))) →
      T.Tm Γ (Un.U Γ)
  /-- The code of a product decodes to the product of the decodings. -/
  El_code : ∀ {Γ : C} (a : T.Tm Γ (Un.U Γ)) (b : T.Tm (T.ext Γ (Un.El a)) (Un.U _)),
      Un.El (code a b) = P.Pi a (Un.El b)

namespace SmallPi

variable {Un}

/-- Abstraction is injective, being a section of application. -/
theorem lam_injective (P : SmallPi Un) {Γ : C} {a : T.Tm Γ (Un.U Γ)}
    {B : T.Ty (T.ext Γ (Un.El a))} : Function.Injective (P.lam (a := a) (B := B)) := by
  intro b b' h
  rw [← P.app_lam b, ← P.app_lam b', h]

end SmallPi

/-- The dependent product does not change when the domain type is replaced by an equal one, the
body being transported along the induced equality of extended contexts. -/
theorem _root_.Cwa.WeakPiStruct.Pi_congr (P : Cwa.WeakPiStruct T) {Γ : C} {A A' : T.Ty Γ}
    (h : A = A') (B : T.Ty (T.ext Γ A)) :
    P.Pi A' (T.tySub (eqToHom (congrArg (T.ext Γ) h).symm) B) = P.Pi A B := by
  cases h
  simp only [congrArg, eqToHom_refl, T.tySub_id]

/-- **A model whose dependent product is defined over all types has products over the small ones.**
The universe contributes nothing here beyond naming the domain; what it does *not* give for free is
closure (`PiClosed`), which asks the product of two small types to be small again. -/
noncomputable def smallPiOfWeakPi (Un : Universe T) (P : Cwa.WeakPiStruct T) : SmallPi Un where
  Pi a B := P.Pi (Un.El a) B
  Pi_sub σ a B := by
    rw [P.Pi_sub σ (Un.El a) B, Universe.extHom, T.tySub_comp]
    exact (P.Pi_congr (Un.El_sub' σ a) _).symm
  lam := P.lam
  app := P.app
  app_lam := P.app_lam

end Universe

end Cwa
