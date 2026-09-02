/-
**`λΠ` is a functional pure type system: types are unique up to conversion.**

`Start/LambdaPiTyping.lean` gives the typing judgement of `λΠ` and its five inversion lemmas, each
in the form "the term has its canonical type, *convertible* to the type it was given".  This module
draws the standard consequence: two types of the same term are convertible, so a term determines
its type up to conversion, and in particular a *sort* is determined outright.

The proof is a structural induction on the raw term.  Each case applies the inversion lemma for
that construct to both derivations and compares the two canonical types: variables use the
determinism of context lookup, products and abstractions use the induction hypothesis for the body,
and applications use the injectivity of the product former
(`LambdaPi.pi_inj_left`, `LambdaPi.pi_inj_right`), itself a consequence of the Church–Rosser
theorem.

Main results:

* `LambdaPi.Lookup.det` — context lookup is deterministic;
* `LambdaPi.Typing.conv_type` — **two types of the same term are convertible**;
* `LambdaPi.Typing.srt_unique` — hence a term is typed by at most one sort;
* `LambdaPi.Typing.not_star_box` — no term is both a type and a kind.

The last one is what `Start/LambdaPiFull.lean` had to work around: there a type of the syntactic
model is a raw term *together with* the sort typing it, because uniqueness of sorts was not
available.  It says the extra datum is in fact determined, and
`LambdaPiFull.tyMk_eq_of_conv` records the consequence — convertible types of the syntactic model
are equal.
-/

import Start.LambdaPiFull

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

/-! ### Context lookup is deterministic -/

/-- **A de Bruijn index has at most one type in a context.** -/
theorem Lookup.det {Γ : Ctx} {n : ℕ} {A B : Tm} (hA : Lookup Γ n A) (hB : Lookup Γ n B) :
    A = B := by
  induction hA generalizing B with
  | zero Γ A => cases hB with | zero => rfl
  | succ C hA ih => cases hB with | succ _ hB => exact congrArg shift (ih hB)

/-! ### Uniqueness of types -/

/-- **Two types of the same term are convertible.**  `λΠ` is a functional pure type system: the
type of a term is determined up to conversion. -/
theorem Typing.conv_type {t : Tm} : ∀ {Γ : Ctx} {A B : Tm},
    Typing Γ t A → Typing Γ t B → Conv A B := by
  induction t with
  | sort s =>
      intro Γ A B hA hB
      exact (hA.sort_inv.2).symm.trans hB.sort_inv.2
  | var n =>
      intro Γ A B hA hB
      obtain ⟨A₀, hlA, hcA⟩ := hA.var_inv
      obtain ⟨B₀, hlB, hcB⟩ := hB.var_inv
      cases hlA.det hlB
      exact hcA.symm.trans hcB
  | app f a ihf _ =>
      intro Γ A B hA hB
      obtain ⟨A₁, B₁, hf₁, _, hc₁⟩ := hA.app_inv
      obtain ⟨A₂, B₂, hf₂, _, hc₂⟩ := hB.app_inv
      have hpi : Conv (Tm.pi A₁ B₁) (Tm.pi A₂ B₂) := ihf hf₁ hf₂
      have hbody : Conv (B₁[a]) (B₂[a]) := (pi_inj_right hpi).subst _
      exact hc₁.symm.trans (hbody.trans hc₂)
  | lam A₀ b _ ihb =>
      intro Γ A B hA hB
      obtain ⟨B₁, _, _, hb₁, hc₁⟩ := hA.lam_inv
      obtain ⟨B₂, _, _, hb₂, hc₂⟩ := hB.lam_inv
      exact hc₁.symm.trans ((Conv.piR A₀ (ihb hb₁ hb₂)).trans hc₂)
  | pi A₀ B₀ _ ihB =>
      intro Γ A B hA hB
      obtain ⟨_, t₁, _, _, hB₁, hc₁⟩ := hA.pi_inv
      obtain ⟨_, t₂, _, _, hB₂, hc₂⟩ := hB.pi_inv
      have : t₁ = t₂ := sort_conv_inj (ihB hB₁ hB₂)
      subst this
      exact hc₁.symm.trans hc₂

/-- **A term is typed by at most one sort.** -/
theorem Typing.srt_unique {Γ : Ctx} {t : Tm} {s s' : Srt} (h : Typing Γ t (Tm.sort s))
    (h' : Typing Γ t (Tm.sort s')) : s = s' :=
  sort_conv_inj (h.conv_type h')

/-- **No term is both a type and a kind.** -/
theorem Typing.not_star_box {Γ : Ctx} {t : Tm} (h : Typing Γ t (Tm.sort Srt.star)) :
    ¬ Typing Γ t (Tm.sort Srt.box) := fun h' => by
  cases h.srt_unique h'

end LambdaPi

namespace LambdaPiFull

open LambdaPi LambdaPiCat

/-- **Convertible types of the syntactic model carry the same sort.**  Both reduce to a common
term, which subject reduction types by each of the two sorts. -/
theorem srt_eq_of_conv {Γ : Ob} {A B : TyOf Γ} (h : Conv A.ty B.ty) : A.srt = B.srt := by
  obtain ⟨v, hv₁, hv₂⟩ := h.church_rosser
  exact (A.ok.red Γ.wf hv₁).srt_unique (B.ok.red Γ.wf hv₂)

/-- **Convertible types of the syntactic model are equal.**  The sort recorded by `TyOf` is
determined by the underlying term, so conversion alone identifies two types. -/
theorem tyMk_eq_of_conv {Γ : Ob} {A B : TyOf Γ} (h : Conv A.ty B.ty) : tyMk A = tyMk B :=
  tyMk_eq (srt_eq_of_conv h) h

end LambdaPiFull
