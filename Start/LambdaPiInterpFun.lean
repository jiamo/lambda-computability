/-
**Functionality of the interpretation of `λΠ`**: when does a raw expression denote at most one
type, and at most one term of it?

`Start/LambdaPiInterp.lean` defines the interpretation as a *relation*, because a raw expression
need not denote anything.  For it to be an interpretation it must be single-valued, and that is
what is studied here.

* `LambdaPi.Interp.Functional M` — the property that the interpretation into `M` is single-valued;
* `LambdaPi.Model.PiInj` — the dependent product of the model determines its domain and its body;
* `LambdaPi.functional_of_piInj` — **a model whose product former is injective interprets
  functionally**.  The reason a hypothesis is needed at all is the application rule: the raw term
  `f g` does not record the domain of the type of `f`, so two derivations may name the *same*
  semantic product type by different codes; a model in which the product determines its domain
  cannot do this.  A calculus with type-annotated applications would not need the hypothesis.

The one place where two different rules apply to the same raw expression is a product of two small
types, which denotes a type both directly (`TyI.pi`) and through its code (`TyI.el` of `TmI.pi`);
they agree precisely because the universe of a model is closed under products, `El_code`.
-/

import Start.LambdaPiInterp

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory

namespace LambdaPi

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

/-- The pair of a code and a type over its decoding: the data a dependent product is formed from. -/
abbrev PiVal (M : Model.{u, v, w} C) (Γ : C) : Type max v w :=
  (a : Cwa.Tm M.T Γ (M.Un.U Γ)) × M.T.Ty (M.T.ext Γ (M.Un.El a))

/-- The **interpretation into `M` is functional**: every raw expression denotes at most one type,
and at most one term of it. -/
structure Interp.Functional (M : Model.{u, v, w} C) : Prop where
  /-- An expression denotes at most one type. -/
  ty : ∀ {Γ : C} {s : SemCtx M Γ} {t : Tm} {A A' : M.T.Ty Γ}, TyI s t A → TyI s t A' → A = A'
  /-- An expression denotes at most one term. -/
  tm : ∀ {Γ : C} {s : SemCtx M Γ} {t : Tm} {A A' : M.T.Ty Γ} {x : Cwa.Tm M.T Γ A}
      {x' : Cwa.Tm M.T Γ A'}, TmI s t A x → TmI s t A' x' → (⟨A, x⟩ : TmVal M Γ) = ⟨A', x'⟩

/-- **The product former of the model is injective**: a dependent product determines the code of
its domain and its body.  The syntax has this property, by injectivity of the product former of
`λΠ` (`LambdaPi.pi_inj_left`, `LambdaPi.pi_inj_right`). -/
def Model.PiInj (M : Model.{u, v, w} C) : Prop :=
  ∀ {Γ : C} {a a' : Cwa.Tm M.T Γ (M.Un.U Γ)} {B : M.T.Ty (M.T.ext Γ (M.Un.El a))}
    {B' : M.T.Ty (M.T.ext Γ (M.Un.El a'))},
    M.SP.Pi a B = M.SP.Pi a' B' → (⟨a, B⟩ : PiVal M Γ) = ⟨a', B'⟩

mutual

/-- An expression denotes at most one type, in a model with injective products. -/
theorem TyI.unique_of_piInj (hinj : M.PiInj) {Γ : C} {s : SemCtx M Γ} {t : Tm} {A A' : M.T.Ty Γ}
    (h : TyI s t A) (h' : TyI s t A') : A = A' := by
  cases h with
  | star s =>
      cases h' with
      | star => rfl
      | el hc => exact absurd hc (by rintro ⟨⟩)
  | @el Γ s t c hc =>
      cases h' with
      | star => exact absurd hc (by rintro ⟨⟩)
      | el hc' =>
          have hval := TmI.unique_of_piInj hinj hc hc'
          rcases Sigma.mk.inj_iff.mp hval with ⟨_, h2⟩
          exact congrArg M.Un.El (eq_of_heq h2)
      | pi ha hB => exact TyI.el_pi_aux hinj hc ha hB
  | @pi Γ s A B a B' ha hB =>
      cases h' with
      | el hc => exact (TyI.el_pi_aux hinj hc ha hB).symm
      | @pi _ _ _ _ a₂ B₂ ha₂ hB₂ =>
          have hval := TmI.unique_of_piInj hinj ha ha₂
          rcases Sigma.mk.inj_iff.mp hval with ⟨_, h2⟩
          have haa : a = a₂ := eq_of_heq h2
          subst haa
          exact congrArg _ (TyI.unique_of_piInj hinj hB hB₂)

/-- Auxiliary: a product of two small types denotes the same type through its code as directly. -/
theorem TyI.el_pi_aux (hinj : M.PiInj) {Γ : C} {s : SemCtx M Γ} {A B : Tm}
    {c a : Cwa.Tm M.T Γ (M.Un.U Γ)} {B' : M.T.Ty (M.T.ext Γ (M.Un.El a))}
    (hc : TmI s (Tm.pi A B) (M.Un.U Γ) c) (ha : TmI s A (M.Un.U Γ) a)
    (hB : TyI (s.cons (M.Un.El a)) B B') :
    M.Un.El c = M.SP.Pi a B' := by
  cases hc with
  | @pi _ _ _ _ a₂ b₂ ha₂ hb₂ =>
      have hval := TmI.unique_of_piInj hinj ha ha₂
      rcases Sigma.mk.inj_iff.mp hval with ⟨_, h2⟩
      have haa : a = a₂ := eq_of_heq h2
      subst haa
      have hBB : B' = M.Un.El b₂ := TyI.unique_of_piInj hinj hB (TyI.el hb₂)
      subst hBB
      exact M.PC.El_code a b₂

/-- An expression denotes at most one term, in a model with injective products. -/
theorem TmI.unique_of_piInj (hinj : M.PiInj) {Γ : C} {s : SemCtx M Γ} {t : Tm} {A A' : M.T.Ty Γ}
    {x : Cwa.Tm M.T Γ A} {x' : Cwa.Tm M.T Γ A'}
    (h : TmI s t A x) (h' : TmI s t A' x') :
    (⟨A, x⟩ : TmVal M Γ) = ⟨A', x'⟩ := by
  cases h with
  | var hv =>
      cases h' with
      | var hv' => exact Option.some.inj (hv.symm.trans hv')
  | @pi Γ s A B a b ha hb =>
      cases h' with
      | @pi _ _ _ _ a₂ b₂ ha₂ hb₂ =>
          have hval := TmI.unique_of_piInj hinj ha ha₂
          rcases Sigma.mk.inj_iff.mp hval with ⟨_, h2⟩
          have haa : a = a₂ := eq_of_heq h2
          subst haa
          have hval2 := TmI.unique_of_piInj hinj hb hb₂
          rcases Sigma.mk.inj_iff.mp hval2 with ⟨_, h4⟩
          have : b = b₂ := eq_of_heq h4
          subst this
          rfl
  | @lam Γ s A b a B' x ha hb =>
      cases h' with
      | @lam _ _ _ _ a₂ B₂ x₂ ha₂ hb₂ =>
          have hval := TmI.unique_of_piInj hinj ha ha₂
          rcases Sigma.mk.inj_iff.mp hval with ⟨_, h2⟩
          have haa : a = a₂ := eq_of_heq h2
          subst haa
          have hval2 := TmI.unique_of_piInj hinj hb hb₂
          rcases Sigma.mk.inj_iff.mp hval2 with ⟨h3, h4⟩
          subst h3
          have : x = x₂ := eq_of_heq h4
          subst this
          rfl
  | @app Γ s f g a B' f' g' hf hg =>
      cases h' with
      | @app _ _ _ _ a₂ B₂ f₂ g₂ hf₂ hg₂ =>
          have hvalf := TmI.unique_of_piInj hinj hf hf₂
          rcases Sigma.mk.inj_iff.mp hvalf with ⟨hPi, h4⟩
          have hdata : (⟨a, B'⟩ : PiVal M Γ) = ⟨a₂, B₂⟩ := hinj hPi
          rcases Sigma.mk.inj_iff.mp hdata with ⟨haa, hBB⟩
          subst haa
          have : B' = B₂ := eq_of_heq hBB
          subst this
          have : f' = f₂ := eq_of_heq h4
          subst this
          have hvalg := TmI.unique_of_piInj hinj hg hg₂
          rcases Sigma.mk.inj_iff.mp hvalg with ⟨_, h6⟩
          have : g' = g₂ := eq_of_heq h6
          subst this
          rfl

end

/-- **A model whose product former is injective interprets functionally.** -/
theorem functional_of_piInj (hinj : M.PiInj) : Interp.Functional M where
  ty h h' := TyI.unique_of_piInj hinj h h'
  tm h h' := TmI.unique_of_piInj hinj h h'

/-- **The interpretation of a syntactic context is unique**, both as an object of the category and
as a semantic context, when the interpretation is functional. -/
theorem CtxI.unique (hf : Interp.Functional M) {Γ : Ctx} {Γ₁ Γ₂ : C} {s₁ : SemCtx M Γ₁}
    {s₂ : SemCtx M Γ₂} (h₁ : CtxI Γ s₁) (h₂ : CtxI Γ s₂) :
    (⟨Γ₁, s₁⟩ : (Γ' : C) × SemCtx M Γ') = ⟨Γ₂, s₂⟩ := by
  induction h₁ generalizing Γ₂ with
  | nil =>
      cases h₂ with
      | nil => rfl
  | @cons Γ Γ' s A A' _ hA ih =>
      cases h₂ with
      | @cons _ Γ₂' s₂' _ A₂ h₂' hA₂ =>
          have hval := ih h₂'
          rcases Sigma.mk.inj_iff.mp hval with ⟨h3, h4⟩
          subst h3
          have hss : s = s₂' := eq_of_heq h4
          subst hss
          have : A' = A₂ := hf.ty hA hA₂
          subst this
          rfl

end LambdaPi
