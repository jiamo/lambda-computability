/-
**Dependent products of codes, and what they give: a model of `λΠ`.**

`Start/CwaUniverse.lean` asks a model of `λΠ` for a dependent product `Cwa.Universe.SmallPi`
formed over a *small* domain but with an *arbitrary* body, and then for the closure of the universe
under those products (`Cwa.Universe.PiClosed`, `Cwa.Universe.NaturalPiClosed`).  The small fragment
`Cwa.Universe.smallCwa` — the model whose types are the codes — only ever uses the products of two
*small* types, and this module isolates exactly that much structure:

* `Cwa.Universe.CodePi` — a **product of codes**: a code `code a b` for the product of two small
  types, stable under substitution, whose terms are the terms of the body in the extended context
  (abstraction, application and the β-law);
* `Cwa.Universe.smallWeakPiOfCodePi` — such data makes the small fragment a model of `λΠ`: the
  dependent product of the model whose types are the codes;
* `Cwa.Universe.CodePiEta`, `Cwa.Universe.smallPiOfCodePiEta` — with the η-law as well, the small
  fragment carries a full `Cwa.PiStruct`;
* `Cwa.Universe.CodePiNatural`, `Cwa.Universe.smallNaturalPiOfCodePiNatural` — with the naturality
  of abstraction, a `Cwa.NaturalPiStruct`.  `Cwa.Universe.smallCwa_tmSub` computes substitution of
  terms in the small fragment, which is what that law speaks about;
* `Cwa.Universe.codePiOfNaturalPiClosed` — the previous interface is stronger: a `SmallPi` closed
  naturally under products gives a `CodePi`, with the same associated product on the small
  fragment (`Cwa.Universe.smallWeakPi_eq_ofCodePi`).

The point of the weaker interface is that it can be *verified* semantically.  A universe object of
a category with pullbacks presents its types by classifying maps, and a product of two codes is
again a classifying map; whereas the product of a code with an arbitrary type of the ambient
strictified model is presented by a different local universe and is therefore not the decoding of
a code on the nose.  `Start/CwaTypeModel.lean` uses this to build a set-theoretic model of `λΠ`.
-/

import Start.CwaSmall

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace Cwa

namespace Universe

variable {C : Type u} [Category.{v} C] {T : Cwa.{u, v, w} C}

/-- **A dependent product of codes**: for a code `a` and a code `b` in the context extended by
its decoding, a code `code a b` for the product, stable under substitution, together with the
bijection-up-to-β between the terms of `El b` in the extended context and the terms of
`El (code a b)`.

This is what the small fragment of a model needs, and no more: unlike `Cwa.Universe.SmallPi`
together with `Cwa.Universe.PiClosed`, it never mentions a product whose body is a type of the
ambient model rather than a code. -/
structure CodePi (Un : Universe T) where
  /-- The code of the product of two small types. -/
  code : {Γ : C} → (a : T.Tm Γ (Un.U Γ)) →
      T.Tm (T.ext Γ (Un.El a)) (Un.U (T.ext Γ (Un.El a))) → T.Tm Γ (Un.U Γ)
  /-- Beck–Chevalley: the code of a product is stable under substitution. -/
  code_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (a : T.Tm Γ (Un.U Γ))
      (b : T.Tm (T.ext Γ (Un.El a)) (Un.U (T.ext Γ (Un.El a)))),
      Un.sub σ (code a b) = code (Un.sub σ a) (Un.sub (Un.extHom σ a) b)
  /-- Abstraction. -/
  lam : {Γ : C} → {a : T.Tm Γ (Un.U Γ)} →
      {b : T.Tm (T.ext Γ (Un.El a)) (Un.U (T.ext Γ (Un.El a)))} →
      T.Tm (T.ext Γ (Un.El a)) (Un.El b) → T.Tm Γ (Un.El (code a b))
  /-- Application, in the "generic argument" form. -/
  app : {Γ : C} → {a : T.Tm Γ (Un.U Γ)} →
      {b : T.Tm (T.ext Γ (Un.El a)) (Un.U (T.ext Γ (Un.El a)))} →
      T.Tm Γ (Un.El (code a b)) → T.Tm (T.ext Γ (Un.El a)) (Un.El b)
  /-- β: applying an abstraction gives the body back. -/
  app_lam : ∀ {Γ : C} {a : T.Tm Γ (Un.U Γ)}
      {b : T.Tm (T.ext Γ (Un.El a)) (Un.U (T.ext Γ (Un.El a)))}
      (x : T.Tm (T.ext Γ (Un.El a)) (Un.El b)), app (lam x) = x

/-- **A product of codes makes the small fragment a model of `λΠ`**: the dependent product of two
codes is their code, its Beck–Chevalley condition is the stability of the code under substitution,
and abstraction and application are those of the data. -/
noncomputable def smallWeakPiOfCodePi (co : ExtCoherent T) (Un : Universe T) (Q : CodePi Un) :
    WeakPiStruct (smallCwa co Un) where
  Pi a b := Q.code a b
  Pi_sub σ a b := Q.code_sub σ a b
  lam x := Q.lam x
  app f := Q.app f
  app_lam x := Q.app_lam x

@[simp] theorem smallWeakPiOfCodePi_Pi (co : ExtCoherent T) (Un : Universe T) (Q : CodePi Un)
    {Γ : C} (a : (smallCwa co Un).Ty Γ) (b : (smallCwa co Un).Ty ((smallCwa co Un).ext Γ a)) :
    (smallWeakPiOfCodePi co Un Q).Pi a b = Q.code a b := rfl

/-! ### Substitution of terms in the small fragment -/

/-- The inclusion of the small fragment into the model is the identity on terms. -/
theorem smallMor_tmMap (co : ExtCoherent T) (Un : Universe T) {Γ : C} {a : T.Tm Γ (Un.U Γ)}
    (x : (smallCwa co Un).Tm Γ a) : (smallMor co Un).tmMap x = x := by
  refine Cwa.Tm.ext' ?_
  rw [Mor.tmMap_val]
  exact Category.comp_id _

/-- **Substitution of terms in the small fragment is substitution in the ambient model**, read
through the decoding of the substituted code. -/
theorem smallCwa_tmSub (co : ExtCoherent T) (Un : Universe T) {Γ Δ : C} (σ : Δ ⟶ Γ)
    {a : T.Tm Γ (Un.U Γ)} (x : (smallCwa co Un).Tm Γ a) :
    (smallCwa co Un).tmSub σ x = tmCast (T := T) (Un.El_sub' σ a) (T.tmSub σ x) := by
  have h := Mor.tmMap_tmSub (smallMor co Un) σ x
  rw [smallMor_tmMap, smallMor_tmMap] at h
  refine Eq.symm (Eq.trans (congrArg (tmCast (T := T) (Un.El_sub' σ a)) h.symm) ?_)
  exact tmCast_trans (T := T) (Un.El_sub' σ a).symm (Un.El_sub' σ a) _

/-- **A product of codes with the η-law**: abstraction and application are mutually inverse, so
the terms of the code of a product are *exactly* the terms of the body in the extended context. -/
structure CodePiEta (Un : Universe T) extends CodePi Un where
  /-- η: abstracting an application gives the function back. -/
  lam_app : ∀ {Γ : C} {a : T.Tm Γ (Un.U Γ)}
      {b : T.Tm (T.ext Γ (Un.El a)) (Un.U (T.ext Γ (Un.El a)))}
      (f : T.Tm Γ (Un.El (toCodePi.code a b))), toCodePi.lam (toCodePi.app f) = f

/-- **A product of codes with η makes the small fragment a model of `λΠ` with η**: the small
fragment carries a full `Cwa.PiStruct`, not merely a weak one. -/
noncomputable def smallPiOfCodePiEta (co : ExtCoherent T) (Un : Universe T) (Q : CodePiEta Un) :
    PiStruct (smallCwa co Un) where
  toWeakPiStruct := smallWeakPiOfCodePi co Un Q.toCodePi
  lam_app f := Q.lam_app f

@[simp] theorem smallPiOfCodePiEta_Pi (co : ExtCoherent T) (Un : Universe T) (Q : CodePiEta Un)
    {Γ : C} (a : (smallCwa co Un).Ty Γ) (b : (smallCwa co Un).Ty ((smallCwa co Un).ext Γ a)) :
    (smallPiOfCodePiEta co Un Q).Pi a b = Q.code a b := rfl

/-- **A product of codes that is natural in the context**: abstraction commutes with
substitution.  This is the last law a model needs in order to interpret a calculus with an
explicit substitution calculus, and it upgrades the small fragment to a
`Cwa.NaturalPiStruct`. -/
structure CodePiNatural (co : ExtCoherent T) (Un : Universe T) extends CodePiEta Un where
  /-- Abstraction commutes with substitution. -/
  lam_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (a : T.Tm Γ (Un.U Γ))
      (b : T.Tm (T.ext Γ (Un.El a)) (Un.U (T.ext Γ (Un.El a))))
      (x : T.Tm (T.ext Γ (Un.El a)) (Un.El b)),
      tmCast (T := smallCwa co Un) (toCodePi.code_sub σ a b)
          ((smallCwa co Un).tmSub σ (toCodePi.lam x))
        = toCodePi.lam ((smallCwa co Un).tmSub (Un.extHom σ a) x)

/-- **A natural product of codes makes the small fragment a model of `λΠ` with substitution**:
the small fragment carries a `Cwa.NaturalPiStruct`. -/
noncomputable def smallNaturalPiOfCodePiNatural (co : ExtCoherent T) (Un : Universe T)
    (Q : CodePiNatural co Un) : NaturalPiStruct (smallCwa co Un) where
  toPiStruct := smallPiOfCodePiEta co Un Q.toCodePiEta
  lam_sub {_Γ _Δ} σ {a b} x := Q.lam_sub σ a b x

/-- **The previous interface is stronger**: a dependent product over the small types whose
universe is naturally closed under it gives a product of codes.  Abstraction and application are
transported along `El_code`. -/
noncomputable def codePiOfNaturalPiClosed (Un : Universe T) (P : SmallPi Un)
    (Pc : NaturalPiClosed Un P) : CodePi Un where
  code a b := Pc.code a b
  code_sub σ a b := Pc.code_sub σ a b
  lam x := tmCast (T := T) (Pc.El_code _ _).symm (P.lam x)
  app f := P.app (tmCast (T := T) (Pc.El_code _ _) f)
  app_lam {_Γ a b} x := by
    have h : tmCast (T := T) (Pc.El_code a b)
        (tmCast (T := T) (Pc.El_code a b).symm (P.lam x)) = P.lam x := by
      rw [tmCast_trans]
      rfl
    change P.app (tmCast (T := T) (Pc.El_code a b)
      (tmCast (T := T) (Pc.El_code a b).symm (P.lam x))) = x
    rw [h]
    exact P.app_lam x

/-- The product of the small fragment does not depend on which of the two interfaces it is read
off: `Cwa.Universe.smallWeakPi` is the product associated with the induced `CodePi`. -/
theorem smallWeakPi_eq_ofCodePi (co : ExtCoherent T) (Un : Universe T) (P : SmallPi Un)
    (Pc : NaturalPiClosed Un P) :
    smallWeakPi co Un P Pc = smallWeakPiOfCodePi co Un (codePiOfNaturalPiClosed Un P Pc) := rfl

end Universe

end Cwa
