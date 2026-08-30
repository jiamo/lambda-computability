/-
**The comparison morphism of `λΠ` preserves the universe, the small products and their codes.**

`Start/LambdaPiInitial.lean` builds, out of the interpretation of `λΠ` in a model `M` with
injective products, a morphism of categories with attributes `LambdaPiInitial.mor` from the
syntactic model to `M`.  A morphism of categories with attributes compares the *types* of the two
models; but the types of `λΠ` are the **terms of the sort `∗`**, so a comparison deserves to be
called an interpretation of the calculus only if it also respects the universe.  This module
proves that it does.

* `LambdaPi.SubI.secTy` — the section defined by an interpreted term carries the substitution
  instantiating the last variable of the context by it, for an arbitrary type of the model (the
  form of `LambdaPi.SubI.sec` that a general type, not only a decoded code, requires);
* `LambdaPiInitial.sec_out_conv` — a term of the syntactic model, read as a substitution out of
  the extended context, is the substitution `scons` of its representative;
* `LambdaPiInitial.tmMap_spec` — **the action of the comparison on terms is the interpretation**:
  the term `mor.tmMap x` of the model is what the representative of `x` denotes.  This is the
  missing half of `LambdaPiInitial.tyMap_spec`, and it is proved from the uniqueness of the
  interpretation of a substitution: a term is a section, and the two candidate sections carry the
  same raw substitution;
* `LambdaPiInitial.tyMap_uQ`, `LambdaPiInitial.tyMap_elQ` — the sort `∗` is interpreted by the
  universe of the model, and a decoded code by the decoding of its image;
* `LambdaPiInitial.mor_preservesUniverse` — **the comparison morphism preserves the universe**
  (`Cwa.Mor.PreservesUniverse`), so it compares the two models as models of `λΠ` and not merely as
  categories with attributes;
* `LambdaPiInitial.tyMap_piQ` — the product of the syntax is interpreted by the dependent product
  of the model, over the image of the domain code and of the body read in the compared extended
  context;
* `LambdaPiInitial.mor_preservesSmallPi` — **the comparison morphism preserves the dependent
  products over the small types** (`Cwa.Mor.PreservesSmallPi`);
* `LambdaPiInitial.tmMap_lamQ` — **abstraction is preserved**: the image of an abstraction of the
  syntax is the abstraction of the model, applied to the image of the body read in the compared
  extended context;
* `LambdaPiInitial.codeMap_codeQ` — the code of a product of two small types is interpreted by the
  code of the dependent product of the model;
* `LambdaPiInitial.mor_preservesPiClosed` — **the comparison morphism preserves the codes for the
  products** (`Cwa.Mor.PreservesPiClosed`).

Together the last three say that the comparison morphism respects *all* of the structure that
makes a category with attributes a model of `λΠ`: the universe, the products over it and the
closure of the universe under those products.
-/

import Start.LambdaPiInitial
import Start.LambdaPiSyntacticModel
import Start.CwaMorUniv

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory

namespace LambdaPi

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

/-- **The section defined by an interpreted term carries the substitution that instantiates the
last variable of the context by it**, for an arbitrary type of the model.  This is
`LambdaPi.SubI.sec` with the decoded code replaced by a general type. -/
theorem SubI.secTy {Γ : C} {s : SemCtx M Γ} {g : Tm} {A' : M.T.Ty Γ} {g' : Cwa.Tm M.T Γ A'}
    (hg : TmI s g A' g') : SubI (s.cons A') s g'.1 (scons g ids) := by
  intro n p hp
  cases n with
  | zero =>
      simp only [SemCtx.varVal, Option.some.injEq] at hp
      subst hp
      exact TmI.cast_val hg (M.co.val_sub_sec_var g').symm
  | succ m =>
      simp only [SemCtx.varVal, Option.map_eq_some_iff] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      refine TmI.cast_val (TmI.var hq) ?_
      change q = Cwa.Val.sub g'.1 (Cwa.Val.sub (M.T.disp A') q)
      rw [M.co.val_sub_comp, g'.2, M.co.val_sub_id]

/-- **Transport of the interpretation of a type along conversion**, when the other expression is
known to denote something: reduction preserves the interpretation only in one direction, but
uniqueness turns that into invariance. -/
theorem TyI.of_conv (hinj : M.PiInj) {Γ : C} {s : SemCtx M Γ} {t u : Tm} {A : M.T.Ty Γ}
    (hc : Conv t u) (h : TyI s t A) (hu : ∃ A' : M.T.Ty Γ, TyI s u A') : TyI s u A := by
  obtain ⟨A', hA'⟩ := hu
  rwa [TyI.conv_eq hinj hc h hA']

/-- **Transport of the interpretation of a term along conversion.** -/
theorem TmI.of_conv (hinj : M.PiInj) {Γ : C} {s : SemCtx M Γ} {t u : Tm} {A : M.T.Ty Γ}
    {x : Cwa.Tm M.T Γ A} (hc : Conv t u) (h : TmI s t A x)
    (hu : ∃ (A' : M.T.Ty Γ) (x' : Cwa.Tm M.T Γ A'), TmI s u A' x') : TmI s u A x := by
  obtain ⟨A', x', h'⟩ := hu
  exact TmI.cast_val h' (TmI.conv_eq hinj hc h h').symm

/-- **Transport of the interpretation of a type along an identification of semantic contexts.** -/
theorem TyI.congr_ctx {Γ₁ Γ₂ : C} {s₁ : SemCtx M Γ₁} {s₂ : SemCtx M Γ₂}
    (h : (⟨Γ₁, s₁⟩ : (X : C) × SemCtx M X) = ⟨Γ₂, s₂⟩) {t : Tm} {A : M.T.Ty Γ₁}
    (hA : TyI s₁ t A) : TyI s₂ t (M.T.tySub (eqToHom (congrArg Sigma.fst h).symm) A) := by
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
  subst h1
  cases eq_of_heq h2
  simpa only [eqToHom_refl, M.T.tySub_id] using hA

/-- **Transport of the interpretation of a term along an identification of semantic contexts.** -/
theorem TmI.congr_ctx {Γ₁ Γ₂ : C} {s₁ : SemCtx M Γ₁} {s₂ : SemCtx M Γ₂}
    (h : (⟨Γ₁, s₁⟩ : (X : C) × SemCtx M X) = ⟨Γ₂, s₂⟩) {t : Tm} {A : M.T.Ty Γ₁}
    {x : Cwa.Tm M.T Γ₁ A} (hx : TmI s₁ t A x) :
    TmI s₂ t (M.T.tySub (eqToHom (congrArg Sigma.fst h).symm) A)
      (M.T.tmSub (eqToHom (congrArg Sigma.fst h).symm) x) := by
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
  subst h1
  cases eq_of_heq h2
  simp only [eqToHom_refl]
  rw [(Cwa.tmCast_eq_iff (M.T.tySub_id A) (M.T.tmSub (𝟙 Γ₁) x) x).mp (M.co.tmSub_id x)]
  exact hx.cast (M.T.tySub_id A).symm

end LambdaPi

namespace LambdaPiInitial

open LambdaPi LambdaPiCat LambdaPiFull LambdaPiUniv

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

/-! ### A term of the syntactic model, read as a substitution -/

/-- A type of the syntactic model is not the top sort, so its terms have an interpretation. -/
theorem rep_ty_ne_box {Γ : Ob} (A : TyQ Γ) : A.rep.ty ≠ Tm.sort Srt.box := by
  intro h
  exact not_typing_box (h ▸ A.rep.ok)

/-- **A term of the syntactic model, read as a substitution out of the extended context, is the
substitution instantiating the last variable by its representative.** -/
theorem sec_out_conv {Γ : Ob} {A : TyQ Γ} (x : Cwa.Tm syntactic Γ A) (n : ℕ)
    (hn : n < (extOb Γ A).ctx.length) : Conv (x.1.out.sub n) (scons (rep x) ids n) := by
  cases n with
  | zero => exact (rep_conv_of_eq (x := x) rfl).symm
  | succ m =>
      have hm : m < Γ.ctx.length := by
        simpa [extOb, LambdaPiCat.cons] using Nat.lt_of_succ_lt_succ hn
      have h := sec_isSecRaw A.rep.ok x m hm
      simp only [scons_succ, ids_apply]
      exact h

variable (hinj : M.PiInj)

/-! ### The action of the comparison on terms is the interpretation -/

/-- **The term of the model interpreting a term of the syntactic model is its image under the
comparison morphism.** -/
theorem tmMap_spec {Γ : Ob} (A : TyQ Γ) (x : Cwa.Tm syntactic Γ A) :
    TmI (sem hinj Γ) (rep x) (tyMap hinj A) ((mor hinj).tmMap x) := by
  obtain ⟨A', y, hA', hy⟩ :=
    TmI.total hinj (rep_ok x) (rep_ty_ne_box A) (sem_spec hinj Γ)
  have hAA : tyMap hinj A = A' :=
    TyI.conv_eq hinj (Conv.refl _) (tyMap_spec hinj A) hA'
  subst hAA
  have hsec : SubI (sem hinj (extOb Γ A)) (sem hinj Γ)
      (y.1 ≫ eqToHom (objExt hinj A).symm) (scons (rep x) ids) := by
    have h := SubI.congr_tgt (ctxI_ext hinj A).symm (SubI.secTy hy)
    simpa using h
  have hhom : homMap hinj x.1 = y.1 ≫ eqToHom (objExt hinj A).symm :=
    homMap_eq hinj x.1 (sec_out_conv x) hsec
  have hval : ((mor hinj).tmMap x).1 = y.1 := by
    rw [Cwa.Mor.tmMap_val]
    change homMap hinj x.1 ≫ (eqToIso (objExt hinj A)).hom = y.1
    rw [hhom, eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  have : (mor hinj).tmMap x = y := Cwa.Tm.ext' hval
  rw [this]
  exact hy

/-! ### The universe is preserved -/

/-- The inverse of a composite of two transports between objects is the transport along the
composite identification: all the transports between two given objects agree. -/
theorem eqToIso_trans_inv {X Y Z : C} (h₁ : X = Y) (h₂ : Y = Z) (h₃ : Z = X) :
    (eqToIso h₁ ≪≫ eqToIso h₂).inv = eqToHom h₃ := by
  cases h₁
  cases h₂
  simp

/-- The comparison of the extended contexts under the comparison morphism is the transport along
the identification `objExt` of the underlying objects. -/
theorem mor_extIso {Γ : Ob} (A : TyQ Γ) :
    (mor hinj).extIso A = eqToIso (objExt hinj A) := rfl

/-- **The sort `∗` is interpreted by the universe of the model.** -/
theorem tyMap_uQ (Γ : Ob) : tyMap hinj (uQ Γ) = M.Un.U (obj hinj Γ) :=
  tyMap_eq hinj (uQ Γ) (uQ_rep_conv Γ) (TyI.star _)

/-- **A decoded code is interpreted by the decoding of its image.** -/
theorem tyMap_elQ {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) :
    tyMap hinj (elQ a)
      = M.Un.El (Cwa.tmCast (tyMap_uQ hinj Γ) ((mor hinj).tmMap a)) :=
  tyMap_eq hinj (elQ a) (elQ_rep_conv a)
    (TyI.el ((tmMap_spec hinj (uQ Γ) a).cast (tyMap_uQ hinj Γ)))

/-- The representative of a decoded code denotes the image of that code. -/
theorem tmI_elQ_rep {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) :
    TmI (sem hinj Γ) (elQ a).rep.ty (M.Un.U (obj hinj Γ))
      (Cwa.tmCast (tyMap_uQ hinj Γ) ((mor hinj).tmMap a)) :=
  TmI.of_conv hinj (elQ_rep_conv a).symm
    ((tmMap_spec hinj (uQ Γ) a).cast (tyMap_uQ hinj Γ))
    (by
      obtain ⟨A', x, _, hx⟩ :=
        TmI.total hinj (elQ_rep_ok a) (by simp) (sem_spec hinj Γ)
      exact ⟨A', x, hx⟩)

/-- **The comparison morphism preserves the universe**: it carries the sort `∗` of the syntax to
the universe of the model and commutes with decoding, so it compares the two *models of `λΠ`*. -/
theorem mor_preservesUniverse : (mor hinj).PreservesUniverse univ M.Un where
  U_map Γ := tyMap_uQ hinj Γ
  El_map a := tyMap_elQ hinj a

/-! ### The products over the small types are preserved -/

/-- **The interpretation of a context extended by a decoded code** is the context of the model
extended by the decoding of the image of that code. -/
theorem ctxI_ext_elQ {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) :
    (⟨obj hinj (extOb Γ (elQ a)), sem hinj (extOb Γ (elQ a))⟩ : (X : C) × SemCtx M X)
      = ⟨M.T.ext (obj hinj Γ) (M.Un.El ((mor_preservesUniverse hinj).codeMap a)),
          (sem hinj Γ).cons (M.Un.El ((mor_preservesUniverse hinj).codeMap a))⟩ := by
  rw [ctxI_ext hinj (elQ a), tyMap_elQ hinj a]
  rfl

/-- The comparison of the extended contexts is the transport along `ctxI_ext_elQ`. -/
theorem extElIso_inv_eq {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) :
    ((mor_preservesUniverse hinj).extElIso a).inv
      = eqToHom (congrArg Sigma.fst (ctxI_ext_elQ hinj a)).symm :=
  eqToIso_trans_inv _ _ _

/-- **The product rule of `λΠ` is interpreted by the dependent product of the model.** -/
theorem tyMap_piQ {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) (B : TyQ (extOb Γ (elQ a))) :
    tyMap hinj (piQ a B)
      = M.SP.Pi ((mor_preservesUniverse hinj).codeMap a)
          (M.T.tySub ((mor_preservesUniverse hinj).extElIso a).inv (tyMap hinj B)) := by
  have hbody := TyI.congr_ctx (ctxI_ext_elQ hinj a) (tyMap_spec hinj B)
  rw [extElIso_inv_eq hinj a]
  exact tyMap_eq hinj (piQ a B) (piQ_rep_conv a B) (TyI.pi (tmI_elQ_rep hinj a) hbody)

/-- **The comparison morphism preserves the dependent products over the small types.** -/
theorem mor_preservesSmallPi :
    (mor hinj).PreservesSmallPi (mor_preservesUniverse hinj) smallPi M.SP where
  Pi_map a B := tyMap_piQ hinj a B

/-! ### Abstraction is preserved -/

/-- **Any interpretation of the representative of a term of the syntactic model is the value of
that term** under the comparison morphism, as a pair of a type and a term. -/
theorem tmMap_val_eq {Γ : Ob} {A : TyQ Γ} (x : Cwa.Tm syntactic Γ A) {t : Tm}
    {A' : M.T.Ty (obj hinj Γ)} {y : Cwa.Tm M.T (obj hinj Γ) A'} (hc : Conv (rep x) t)
    (h : TmI (sem hinj Γ) t A' y) :
    (⟨tyMap hinj A, (mor hinj).tmMap x⟩ : TmVal M (obj hinj Γ)) = ⟨A', y⟩ :=
  TmI.conv_eq hinj hc (tmMap_spec hinj A x) h

/-- **The abstraction of `λΠ` is interpreted by the abstraction of the model**: the value of the
image of `lam b` is the abstraction of the image of `b`, read in the compared extended context. -/
theorem tmMap_lamQ {Γ : Ob} {a : Cwa.Tm syntactic Γ (uQ Γ)} {B : TyQ (extOb Γ (elQ a))}
    (b : Cwa.Tm syntactic (extOb Γ (elQ a)) B) :
    (⟨tyMap hinj (piQ a B), (mor hinj).tmMap (smallPi.lam b)⟩ : TmVal M (obj hinj Γ))
      = ⟨M.SP.Pi ((mor_preservesUniverse hinj).codeMap a)
            (M.T.tySub ((mor_preservesUniverse hinj).extElIso a).inv (tyMap hinj B)),
          M.SP.lam (M.T.tmSub ((mor_preservesUniverse hinj).extElIso a).inv
            ((mor hinj).tmMap b))⟩ := by
  have hbody := TmI.congr_ctx (ctxI_ext_elQ hinj a) (tmMap_spec hinj B b)
  rw [extElIso_inv_eq hinj a]
  exact tmMap_val_eq hinj (smallPi.lam b) (rep_lamQ b) (TmI.lam (tmI_elQ_rep hinj a) hbody)

/-! ### The codes for the products are preserved -/

/-- The representative of the code of a product is the product of the representatives. -/
theorem rep_codeQ_conv {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ))
    (b : Cwa.Tm syntactic (extOb Γ (elQ a)) (uQ (extOb Γ (elQ a)))) :
    Conv (rep (codeQ a b)) (Tm.pi (elQ a).rep.ty (rep b)) :=
  codeTm_symm _

/-- **Any interpretation of the representative of a code is the image of that code** under the
comparison morphism. -/
theorem codeMap_eq {Γ : Ob} (x : Cwa.Tm syntactic Γ (uQ Γ)) {t : Tm}
    {y : Cwa.Tm M.T (obj hinj Γ) (M.Un.U (obj hinj Γ))} (hc : Conv (rep x) t)
    (h : TmI (sem hinj Γ) t (M.Un.U (obj hinj Γ)) y) :
    (mor_preservesUniverse hinj).codeMap x = y := by
  have h0 : TmI (sem hinj Γ) (rep x) (M.Un.U (obj hinj Γ))
      ((mor_preservesUniverse hinj).codeMap x) :=
    (tmMap_spec hinj (uQ Γ) x).cast (tyMap_uQ hinj Γ)
  exact eq_of_heq (Sigma.mk.inj_iff.mp (TmI.conv_eq hinj hc h0 h)).2

/-- **The code of a product of `λΠ` is interpreted by the code of the dependent product of the
model.** -/
theorem codeMap_codeQ {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ))
    (b : Cwa.Tm syntactic (extOb Γ (elQ a)) (uQ (extOb Γ (elQ a)))) :
    (mor_preservesUniverse hinj).codeMap (codeQ a b)
      = M.PC.code ((mor_preservesUniverse hinj).codeMap a)
          (M.Un.sub ((mor_preservesUniverse hinj).extElIso a).inv
            ((mor_preservesUniverse hinj).codeMap b)) := by
  have hb0 : TmI (sem hinj (extOb Γ (elQ a))) (rep b)
      (M.Un.U (obj hinj (extOb Γ (elQ a)))) ((mor_preservesUniverse hinj).codeMap b) :=
    (tmMap_spec hinj (uQ (extOb Γ (elQ a))) b).cast (tyMap_uQ hinj _)
  have hb1 := (TmI.congr_ctx (ctxI_ext_elQ hinj a) hb0).cast
    (M.Un.U_sub (eqToHom (congrArg Sigma.fst (ctxI_ext_elQ hinj a)).symm))
  rw [extElIso_inv_eq hinj a]
  exact codeMap_eq hinj (codeQ a b) (rep_codeQ_conv a b) (TmI.pi (tmI_elQ_rep hinj a) hb1)

/-- **The comparison morphism preserves the codes for the products**: the universe of the syntax
is closed under products, and the comparison respects that closure. -/
theorem mor_preservesPiClosed :
    (mor hinj).PreservesPiClosed (mor_preservesUniverse hinj) piClosed M.PC.toPiClosed where
  code_map a b := codeMap_codeQ hinj a b

end LambdaPiInitial
