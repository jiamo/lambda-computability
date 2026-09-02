/-
**Convertible contexts are isomorphic objects of the syntactic category of `λΠ`.**

`Start/LambdaPiTyping.lean` defines `LambdaPi.CtxConvOk Γ Δ`: the entries of `Δ` are convertible
to those of `Γ`, and the entries of `Γ` are still typable over `Δ`.  Typing is stable under such a
conversion (`LambdaPi.Typing.ctxConv`).  This module records the categorical content: a conversion
of contexts is a morphism of the syntactic category carried by the *identity* substitution, and a
conversion in both directions is an isomorphism.

* `LambdaPi.CtxConvOk.trans` — conversions of contexts compose;
* `LambdaPiCat.ctxConvHom` — **the morphism induced by a conversion of contexts**, and
  `LambdaPiCat.ctxConvHom_out_conv`, which says it is carried by the identity substitution;
* `LambdaPiCat.ctxConvIso` — **a conversion in both directions is an isomorphism of contexts**.

This generalises `LambdaPiFull.convIso`, which converts only the last entry of a context.
-/

import Start.LambdaPiFull

set_option relaxedAutoImplicit false
set_option autoImplicit false

open CategoryTheory

namespace LambdaPi

/-- **Conversions of contexts compose.** -/
theorem CtxConvOk.trans {Γ Δ Θ : Ctx} (h : CtxConvOk Γ Δ) (h' : CtxConvOk Δ Θ) :
    CtxConvOk Γ Θ := by
  intro n A hA
  obtain ⟨A', s, hA', hconv, hty⟩ := h n A hA
  obtain ⟨A'', _, hA'', hconv', _⟩ := h' n A' hA'
  exact ⟨A'', s, hA'', hconv.trans hconv', hty.ctxConv h'⟩

end LambdaPi

namespace LambdaPiCat

open LambdaPi

/-- The identity substitution, seen as a raw morphism between convertible contexts. -/
def ctxConvHomRaw {Γ Δ : Ob} (h : CtxConvOk Γ.ctx Δ.ctx) : RawHom Δ Γ where
  sub := ids
  ok := by
    intro n A hA
    obtain ⟨A', s, hA', hconv, hty⟩ := h n A hA
    rw [subst_ids, ids_apply]
    exact (Typing.var hA').conv hty hconv.symm

/-- **The morphism of the syntactic category induced by a conversion of contexts.** -/
def ctxConvHom {Γ Δ : Ob} (h : CtxConvOk Γ.ctx Δ.ctx) : Δ ⟶ Γ := mk (ctxConvHomRaw h)

/-- The induced morphism is carried by the identity substitution. -/
theorem ctxConvHom_sub {Γ Δ : Ob} (h : CtxConvOk Γ.ctx Δ.ctx) (n : ℕ) :
    (ctxConvHomRaw h).sub n = Tm.var n := ids_apply n

/-- **Contexts convertible in both directions are isomorphic**, via the identity substitution. -/
def ctxConvIso {Γ Δ : Ob} (h : CtxConvOk Γ.ctx Δ.ctx) (h' : CtxConvOk Δ.ctx Γ.ctx) : Δ ≅ Γ where
  hom := ctxConvHom h
  inv := ctxConvHom h'
  hom_inv_id := by
    refine mk_eq ?_
    intro n _
    simp only [RawHom.comp, ctxConvHomRaw, RawHom.id, ids_apply, subst_var]
    exact Conv.refl _
  inv_hom_id := by
    refine mk_eq ?_
    intro n _
    simp only [RawHom.comp, ctxConvHomRaw, RawHom.id, ids_apply, subst_var]
    exact Conv.refl _

end LambdaPiCat
