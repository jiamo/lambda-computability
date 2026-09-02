/-
**The interpretation of the syntax of `λΠ` in itself is the identity.**

`Start/LambdaPiSelfInterp.lean` proves the *uniqueness* half of self-interpretation: a raw
expression denotes, in the syntactic model, an object convertible to itself.  This module turns
that into a statement about the comparison morphism of `Start/LambdaPiInitial.lean`.

* `LambdaPiSelf.ctxI_ctxConv` — a semantic context of the syntactic model interpreting a
  well-formed context lives over a **conversion** of that context;
* `LambdaPiSelf.objIso` — hence the object interpreting a context is isomorphic to it, by the
  identity substitution.
-/

import Start.LambdaPiCtxConv
import Start.LambdaPiSelfInterp

set_option relaxedAutoImplicit false
set_option autoImplicit false

open CategoryTheory

namespace LambdaPiSelf

open LambdaPi LambdaPiCat LambdaPiFull LambdaPiUniv LambdaPiInitial

/-- **A semantic context of the syntactic model interpreting a well-formed context lives over a
conversion of that context.** -/
theorem ctxI_ctxConv {l : Ctx} {Γ' : Ob} {sc : SemCtx syntacticModel Γ'} (h : CtxI l sc) :
    Wf l → CtxConvOk l Γ'.ctx ∧ CtxConvOk Γ'.ctx l := by
  induction h with
  | nil =>
      intro _
      refine ⟨?_, ?_⟩ <;> (intro n A hA; cases hA)
  | @cons l Γ' sc A A' hc hA ih =>
      intro hl
      cases hl with
      | @cons _ _ s hlt hAty =>
          obtain ⟨ih₁, ih₂⟩ := ih hlt
          have hAty' : Typing Γ'.ctx A (Tm.sort s) := hAty.ctxConv ih₁
          have hconv : Conv A'.rep.ty A := tyI_rep_conv hA
          exact ⟨(ih₁.cons hAty').trans (CtxConvOk.consConv Γ'.wf hAty' hconv.symm),
            (CtxConvOk.consConv Γ'.wf A'.rep.ok hconv).trans (ih₂.cons hAty)⟩

/-- The context interpreting `Γ` in the syntactic model is a conversion of `Γ`. -/
theorem objCtxConv (Γ : Ob) :
    CtxConvOk Γ.ctx (obj syntacticModel_piInj Γ).ctx
      ∧ CtxConvOk (obj syntacticModel_piInj Γ).ctx Γ.ctx :=
  ctxI_ctxConv (sem_spec syntacticModel_piInj Γ) Γ.wf

/-- **The object interpreting a context in the syntactic model is isomorphic to that context**,
by the identity substitution. -/
noncomputable def objIso (Γ : Ob) : obj syntacticModel_piInj Γ ≅ Γ :=
  ctxConvIso (objCtxConv Γ).1 (objCtxConv Γ).2

end LambdaPiSelf
