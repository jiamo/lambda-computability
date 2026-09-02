/-
**Morphisms of models of `λΠ`, and the transport of the interpretation along one.**

`Start/LambdaPiInterp.lean` interprets the raw syntax of `λΠ` in a model, and
`Start/LambdaPiInitial.lean` packages the interpretation as a morphism of categories with
attributes out of the syntactic model.  What is missing for the 2-categorical statements of
`Start/CwaBiInitial.lean` is *naturality*: a structure-preserving morphism between two models
should carry the interpretation in the source to the interpretation in the target.

This module supplies the definitions that make that statement expressible.

* `LambdaPi.ModelHom M N` — a **morphism of models of `λΠ`**: a morphism of the underlying
  categories with attributes which preserves the universe, the products over the small types and
  their codes, abstraction and application, and which sends the interpretation of the empty
  context to a terminal object;
* `Cwa.extendIso` — extending a context along an isomorphism is an isomorphism;
* `LambdaPi.ModelHom.semCtx` — the **image of a semantic context**: a morphism of models carries
  the list of types out of which an object was built to such a list in the target, and
  `LambdaPi.ModelHom.semIso` compares the image of the object with the object so built.
-/

import Start.CwaTwoCell
import Start.CwaMorUniv
import Start.LambdaPiInterp

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w'

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] {T : Cwa.{u, v, w} C}

/-- **Extending a context along an isomorphism is an isomorphism.**  The inverse is the canonical
map of the inverse substitution. -/
noncomputable def extendIso (co : ExtCoherent T) {X Y : C} (e : X ≅ Y) (A : T.Ty Y) :
    T.ext X (T.tySub e.hom A) ≅ T.ext Y A where
  hom := T.extend e.hom A
  inv := T.substCompare e.inv (by rw [← T.tySub_comp, e.inv_hom_id, T.tySub_id])
  hom_inv_id := by
    rw [← substCompare_rfl (S := T) e.hom A, substCompare_comp co]
    rw [substCompare_congr (S := T) e.hom_inv_id _ (by rw [T.tySub_id]), substCompare_id co]
    simp
  inv_hom_id := by
    rw [← substCompare_rfl (S := T) e.hom A, substCompare_comp co]
    rw [substCompare_congr (S := T) e.inv_hom_id _ (by rw [T.tySub_id]), substCompare_id co]
    simp

@[simp] theorem extendIso_hom (co : ExtCoherent T) {X Y : C} (e : X ≅ Y) (A : T.Ty Y) :
    (extendIso co e A).hom = T.extend e.hom A := rfl

end Cwa

namespace LambdaPi

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- **A morphism of models of `λΠ`**: a morphism of the underlying categories with attributes
preserving all the structure the calculus uses — the universe and its decoding, the products over
the small types, the codes for them, abstraction and application — and sending the object
interpreting the empty context to a terminal object. -/
structure ModelHom (M : Model.{u, v, w} C) (N : Model.{u', v', w'} D) where
  /-- The underlying morphism of categories with attributes. -/
  mor : Cwa.Mor M.T N.T
  /-- The universe and its decoding are preserved. -/
  pu : mor.PreservesUniverse M.Un N.Un
  /-- The products over the small types are preserved. -/
  psp : mor.PreservesSmallPi pu M.SP N.SP
  /-- The codes for the products are preserved. -/
  ppc : mor.PreservesPiClosed pu M.PC.toPiClosed N.PC.toPiClosed
  /-- Abstraction is preserved. -/
  lam_map : ∀ {Γ : C} {a : M.T.Tm Γ (M.Un.U Γ)} {B : M.T.Ty (M.T.ext Γ (M.Un.El a))}
      (b : M.T.Tm (M.T.ext Γ (M.Un.El a)) B),
      Cwa.tmCast (psp.Pi_map a B) (mor.tmMap (M.SP.lam b))
        = N.SP.lam (N.T.tmSub (pu.extElIso a).inv (mor.tmMap b))
  /-- Application is preserved. -/
  app_map : ∀ {Γ : C} {a : M.T.Tm Γ (M.Un.U Γ)} {B : M.T.Ty (M.T.ext Γ (M.Un.El a))}
      (f : M.T.Tm Γ (M.SP.Pi a B)),
      N.T.tmSub (pu.extElIso a).inv (mor.tmMap (M.SP.app f))
        = N.SP.app (Cwa.tmCast (psp.Pi_map a B) (mor.tmMap f))
  /-- The interpretation of the empty context is carried to a terminal object. -/
  empTerminal : IsTerminal (mor.fnc.obj M.emp)

namespace ModelHom

variable {M : Model.{u, v, w} C} {N : Model.{u', v', w'} D}

/-- The comparison of the image of the empty context with the empty context of the target. -/
noncomputable def empIso (H : ModelHom M N) : H.mor.fnc.obj M.emp ≅ N.emp :=
  H.empTerminal.uniqueUpToIso N.empIsTerminal

/-- The image of a semantic context: an object of the target built by iterated extension, the
semantic context over it, and the comparison with the image of the object. -/
noncomputable def semTrans (H : ModelHom M N) : {Γ : C} → SemCtx M Γ →
    Σ X : D, SemCtx N X × (H.mor.fnc.obj Γ ≅ X)
  | _, SemCtx.nil => ⟨N.emp, SemCtx.nil, H.empIso⟩
  | _, SemCtx.cons s A =>
      let r := H.semTrans s
      ⟨N.T.ext r.1 (N.T.tySub r.2.2.inv (H.mor.tyMap A)),
        (r.2.1).cons (N.T.tySub r.2.2.inv (H.mor.tyMap A)),
        H.mor.extIso A ≪≫ (Cwa.extendIso N.co r.2.2.symm (H.mor.tyMap A)).symm⟩

/-- The object of the target over which the image of a semantic context lives. -/
noncomputable def semObj (H : ModelHom M N) {Γ : C} (s : SemCtx M Γ) : D := (H.semTrans s).1

/-- The image of a semantic context. -/
noncomputable def semCtx (H : ModelHom M N) {Γ : C} (s : SemCtx M Γ) : SemCtx N (H.semObj s) :=
  (H.semTrans s).2.1

/-- The comparison of the image of the object with the object built by iterated extension. -/
noncomputable def semIso (H : ModelHom M N) {Γ : C} (s : SemCtx M Γ) :
    H.mor.fnc.obj Γ ≅ H.semObj s := (H.semTrans s).2.2

@[simp] theorem semObj_nil (H : ModelHom M N) : H.semObj SemCtx.nil = N.emp := rfl

@[simp] theorem semCtx_nil (H : ModelHom M N) : H.semCtx SemCtx.nil = SemCtx.nil := rfl

@[simp] theorem semIso_nil (H : ModelHom M N) : H.semIso SemCtx.nil = H.empIso := rfl

/-- The type of the target by which the image of an extended semantic context is extended. -/
noncomputable def semTy (H : ModelHom M N) {Γ : C} (s : SemCtx M Γ) (A : M.T.Ty Γ) :
    N.T.Ty (H.semObj s) := N.T.tySub (H.semIso s).inv (H.mor.tyMap A)

@[simp] theorem semObj_cons (H : ModelHom M N) {Γ : C} (s : SemCtx M Γ) (A : M.T.Ty Γ) :
    H.semObj (s.cons A) = N.T.ext (H.semObj s) (H.semTy s A) := rfl

@[simp] theorem semCtx_cons (H : ModelHom M N) {Γ : C} (s : SemCtx M Γ) (A : M.T.Ty Γ) :
    H.semCtx (s.cons A) = (H.semCtx s).cons (H.semTy s A) := rfl

@[simp] theorem semIso_cons (H : ModelHom M N) {Γ : C} (s : SemCtx M Γ) (A : M.T.Ty Γ) :
    H.semIso (s.cons A)
      = H.mor.extIso A ≪≫ (Cwa.extendIso N.co (H.semIso s).symm (H.mor.tyMap A)).symm := rfl

end ModelHom

end LambdaPi
