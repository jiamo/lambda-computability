/-
**Dependent sums of codes.**

`Start/CwaCodePi.lean` isolates the dependent *product* a universe needs in order to interpret
`λΠ` on its small fragment.  This module does the same for the dependent *sum*:

* `Cwa.Universe.CodeSigma` — a code for the sum of two small types, stable under substitution,
  whose extended context is the twice-extended context of the two codes;
* `Cwa.Universe.smallSigmaOfCodeSigma` — such data gives the small fragment a `Cwa.SigmaStruct`.

As for the product, the point of stating the closure of a universe under sums this way is that it
mentions only codes, so it can be verified in a model presented by a universe object; the
set-theoretic instance is `Start/CwaTypeModelSigma.lean`.
-/

import Start.CwaCodePi

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory

namespace Cwa

namespace Universe

variable {C : Type u} [Category.{v} C] {T : Cwa.{u, v, w} C}

/-- **A dependent sum of codes**: for a code `a` and a code `b` in the context extended by its
decoding, a code `code a b` for the sum, stable under substitution, whose extended context is the
context extended first by `a` and then by `b`. -/
structure CodeSigma (Un : Universe T) where
  /-- The code of the sum of two small types. -/
  code : {Γ : C} → (a : T.Tm Γ (Un.U Γ)) →
      T.Tm (T.ext Γ (Un.El a)) (Un.U (T.ext Γ (Un.El a))) → T.Tm Γ (Un.U Γ)
  /-- Beck–Chevalley: the code of a sum is stable under substitution. -/
  code_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (a : T.Tm Γ (Un.U Γ))
      (b : T.Tm (T.ext Γ (Un.El a)) (Un.U (T.ext Γ (Un.El a)))),
      Un.sub σ (code a b) = code (Un.sub σ a) (Un.sub (Un.extHom σ a) b)
  /-- Pairing: extending by `a` and then by `b` is extending by the code of the sum. -/
  pair : {Γ : C} → (a : T.Tm Γ (Un.U Γ)) →
      (b : T.Tm (T.ext Γ (Un.El a)) (Un.U (T.ext Γ (Un.El a)))) →
      T.ext (T.ext Γ (Un.El a)) (Un.El b) ≅ T.ext Γ (Un.El (code a b))
  /-- The pairing isomorphism lives over the base context. -/
  pair_disp : ∀ {Γ : C} (a : T.Tm Γ (Un.U Γ))
      (b : T.Tm (T.ext Γ (Un.El a)) (Un.U (T.ext Γ (Un.El a)))),
      (pair a b).hom ≫ T.disp (Un.El (code a b)) = T.disp (Un.El b) ≫ T.disp (Un.El a)

/-- **A sum of codes makes the small fragment a model with dependent sums.** -/
noncomputable def smallSigmaOfCodeSigma (co : ExtCoherent T) (Un : Universe T) (Q : CodeSigma Un) :
    SigmaStruct (smallCwa co Un) where
  Sig a b := Q.code a b
  Sig_sub σ a b := Q.code_sub σ a b
  pair a b := Q.pair a b
  pair_disp a b := Q.pair_disp a b

@[simp] theorem smallSigmaOfCodeSigma_Sig (co : ExtCoherent T) (Un : Universe T) (Q : CodeSigma Un)
    {Γ : C} (a : (smallCwa co Un).Ty Γ) (b : (smallCwa co Un).Ty ((smallCwa co Un).ext Γ a)) :
    (smallSigmaOfCodeSigma co Un Q).Sig a b = Q.code a b := rfl

end Universe

end Cwa
