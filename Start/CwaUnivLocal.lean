/-
**A universe object gives a universe of small types in the strictified model.**

`Start/CwaUniverse.lean` axiomatises what a model of `λΠ` needs beyond a category with attributes:
a type `U` whose terms name types.  `Start/LambdaPiUniv.lean` shows the syntax has one.  This file
gives the semantic counterpart, in the strictified model `Cwa.ofPullbacks C` of
`Start/CwaLocalUniverse.lean`, where a type is presented by a morphism of `C` together with a
classifying map.

The construction is the expected one: a **universe object** is just a morphism `p : E ⟶ 𝒰` of `C`,
the generic family of small types.  A code in context `Γ` is a map `Γ ⟶ 𝒰`, and it decodes to the
type presented by `p` with that classifying map.  Because substitution in the strictified model
acts on the classifying map alone, decoding is stable under substitution *on the nose* — the
coherence problem does not reappear.

* `CwaUniv.uTy` — the type of codes: the local universe `p₀ : 𝒰 ⟶ ⊤` with the unique classifying
  map, so that its terms are exactly the maps `Γ ⟶ 𝒰` (`CwaUniv.codeOf`);
* `CwaUniv.universeOfHom` — **every morphism of a category with pullbacks and a terminal object is
  a universe** in the strictified model;
* `CwaUniv.smallPiOfLccc` — in a locally cartesian closed category that universe carries a
  dependent product over the small types, obtained from the product of `Start/CwaPi.lean`;
* `CwaUniv.typeUniverse` — the motivating instance: `Σ A : Type u, A ⟶ Type u`, the generic family
  of small types, is a universe in the strictified model of `Type (u+1)`.

What is *not* provided here is `Cwa.Universe.PiClosed`: for the pushforward of `Start/CwaPi.lean` to
be literally the decoding of a code, the generic product data would have to be the universe object
itself, which is an extra requirement on `p` and not a consequence of local cartesian closure.
-/

import Start.CwaUniverse
import Start.CwaPi

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

open CategoryTheory Limits

namespace CwaUniv

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- The code of a term of a type of the strictified model: a term is a section of the display map,
and composing it with the generic element gives a map into the total space of the presentation. -/
noncomputable def codeOf {Γ : C} {A : LuTy Γ} (a : Cwa.Tm (Cwa.ofPullbacks C) Γ A) :
    Γ ⟶ A.total := a.1 ≫ LuTy.gen A

/-- The code of a substituted term is the substituted code. -/
theorem codeOf_tmSub {Γ Δ : C} (σ : Δ ⟶ Γ) {A : LuTy Γ} (a : Cwa.Tm (Cwa.ofPullbacks C) Γ A) :
    codeOf (Cwa.tmSub (T := Cwa.ofPullbacks C) σ a) = σ ≫ codeOf a := by
  have hgen : LuTy.extend σ A ≫ LuTy.gen A = LuTy.gen (LuTy.sub σ A) := LuTy.extend_gen σ A
  have hlift : (Cwa.tmSub (T := Cwa.ofPullbacks C) σ a).1 ≫ LuTy.extend σ A = σ ≫ a.1 :=
    Cwa.tmSub_extend (T := Cwa.ofPullbacks C) σ a
  change (Cwa.tmSub (T := Cwa.ofPullbacks C) σ a).1 ≫ LuTy.gen (LuTy.sub σ A) = σ ≫ codeOf a
  rw [← hgen, ← Category.assoc, hlift, codeOf, Category.assoc]

/-- Transporting a term along an equality of types transports its code. -/
theorem codeOf_tmCast {Γ : C} {A A' : LuTy Γ} (h : A = A')
    (a : Cwa.Tm (Cwa.ofPullbacks C) Γ A) :
    codeOf (Cwa.tmCast h a) = codeOf a ≫ eqToHom (congrArg LuTy.total h) := by
  cases h
  simp [codeOf]

variable [HasTerminal C]

/-- The type of codes for small types: the universe object seen over the terminal object, so that
its classifying map carries no information and a term of it is a map into the universe. -/
noncomputable def uTy (U : C) (Γ : C) : LuTy Γ :=
  ⟨⊤_ C, U, terminal.from U, terminal.from Γ⟩

omit [HasPullbacks C] in
/-- The universe is stable under substitution, the classifying map being the unique one. -/
theorem uTy_sub (U : C) {Γ Δ : C} (σ : Δ ⟶ Γ) : LuTy.sub σ (uTy U Γ) = uTy U Δ := by
  simp [uTy, LuTy.sub]

/-- Decoding a code: the type presented by the universe object with that classifying map. -/
noncomputable def elTy {E U : C} (p : E ⟶ U) {Γ : C}
    (a : Cwa.Tm (Cwa.ofPullbacks C) Γ (uTy U Γ)) : LuTy Γ :=
  ⟨U, E, p, codeOf a⟩

/-- Decoding is stable under substitution: both the classifying map and the substitution act by
composition. -/
theorem elTy_sub {E U : C} (p : E ⟶ U) {Γ Δ : C} (σ : Δ ⟶ Γ)
    (a : Cwa.Tm (Cwa.ofPullbacks C) Γ (uTy U Γ)) :
    LuTy.sub σ (elTy p a)
      = elTy p (Cwa.tmCast (uTy_sub U σ) (Cwa.tmSub (T := Cwa.ofPullbacks C) σ a)) := by
  have h : codeOf (Cwa.tmCast (uTy_sub U σ) (Cwa.tmSub (T := Cwa.ofPullbacks C) σ a))
      = σ ≫ codeOf a := by
    rw [codeOf_tmCast, codeOf_tmSub]
    exact Category.comp_id _
  simp only [elTy, LuTy.sub, h]
  rfl

/-- **Every morphism of `C` is a universe of small types in the strictified model.**  A code in
context `Γ` is a map `Γ ⟶ 𝒰`, and it decodes to the family it classifies; substitution acts by
composition on both, so decoding is strictly stable under substitution. -/
noncomputable def universeOfHom {E U : C} (p : E ⟶ U) :
    Cwa.Universe (Cwa.ofPullbacks C) where
  U := uTy U
  U_sub := fun σ => uTy_sub U σ
  El := fun {_} a => elTy p a
  El_sub := fun σ a => elTy_sub p σ a

@[simp] theorem universeOfHom_El {E U : C} (p : E ⟶ U) {Γ : C}
    (a : Cwa.Tm (Cwa.ofPullbacks C) Γ (uTy U Γ)) : (universeOfHom p).El a = elTy p a := rfl

/-- **In a locally cartesian closed category the universe carries a dependent product over the
small types**: the product of `Start/CwaPi.lean` restricted to a small domain. -/
noncomputable def smallPiOfLccc [HasBinaryProducts C] [LcccPullbacks C] {E U : C} (p : E ⟶ U) :
    Cwa.Universe.SmallPi (universeOfHom p) :=
  Cwa.Universe.smallPiOfWeakPi _ (Cwa.piStructOfLccc C).toWeakPiStruct

/-! ### The motivating instance -/

/-- The generic family of small types: the first projection out of the total space of `Type u`. -/
def genFam : (Σ A : Type u, A) → Type u := Sigma.fst

/-- **The universe of small types is a universe in the strictified model of `Type (u+1)`.** -/
noncomputable def typeUniverse : Cwa.Universe (Cwa.ofPullbacks (Type (u + 1))) :=
  universeOfHom (↾genFam)

end CwaUniv
