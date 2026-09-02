/-
**The self-interpretation of `λΠ` is the identity, and every morphism of models out of the
syntax is the canonical interpretation.**

`Start/LambdaPiSelfInterp.lean` proves that the interpretation of a raw expression in the
syntactic model is that expression, and `Start/LambdaPiSelfIso.lean` turns this into an
isomorphism `LambdaPiSelf.objIso Γ : obj Γ ≅ Γ` between the object interpreting a context and the
context itself.  This module upgrades that family of isomorphisms to a **2-cell of categories with
attributes** from the self-interpretation to the identity, and draws the consequence the
bi-initiality programme of `Start/CwaBiInitial.lean` was missing.

* `LambdaPiSelf.hom_eq_of_out_conv` — a morphism of the syntactic category is determined by its
  representative;
* `LambdaPiSelf.subI_out_conv` — **a morphism of the syntactic model carrying a substitution is
  that substitution**, up to conversion; hence
* `LambdaPiSelf.objIso_naturality` — the comparison `objIso` is natural, and
  `LambdaPiSelf.selfTwoCell : Cwa.TwoCell (LambdaPiInitial.mor syntacticModel_piInj)
  (Cwa.Mor.id syntactic)` — **the syntax interprets itself by the identity**, invertibly
  (`LambdaPiSelf.selfIso`);
* `LambdaPiSelf.twoCell_of_modelHom` — **the existence half of bi-initiality**: every morphism of
  models of `λΠ` out of the syntactic model receives a 2-cell from the canonical interpretation,
  and `LambdaPiSelf.iso_mor_modelHom` — that 2-cell is invertible, so the two 1-cells are
  isomorphic; by the rigidity of `Start/CwaBiInitial.lean` the isomorphism is unique.
-/

import Start.LambdaPiSelfIso
import Start.LambdaPiInitialNatural
import Start.LambdaPiTypeUnique
import Start.CwaBiInitial

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory

namespace LambdaPiSelf

open LambdaPi LambdaPiCat LambdaPiFull LambdaPiUniv LambdaPiInitial

/-! ### Morphisms of the syntactic category are determined by their representatives -/

/-- **A morphism of the syntactic category is determined by its representative.** -/
theorem hom_eq_of_out_conv {Δ Γ : Ob} {f g : Δ ⟶ Γ}
    (h : ∀ n, n < Γ.ctx.length → Conv (f.out.sub n) (g.out.sub n)) : f = g := by
  conv_lhs => rw [← Quotient.out_eq f]
  conv_rhs => rw [← Quotient.out_eq g]
  exact mk_eq h

/-! ### The interpretation of a substitution in the syntactic model is that substitution -/

/-- **A morphism of the syntactic model carrying a substitution is that substitution**, up to
conversion: this is `LambdaPiSelf.tmI_rep_conv` read at the variables of the source context. -/
theorem subI_out_conv {l : Ctx} {Γ Δ : Ob} {sc : SemCtx syntacticModel Γ}
    {sd : SemCtx syntacticModel Δ} (hsc : CtxI l sc) {u : Δ ⟶ Γ} {f : ℕ → Tm}
    (h : SubI sc sd u f) {n : ℕ} (hn : n < l.length) : Conv (u.out.sub n) (f n) := by
  obtain ⟨A, hA⟩ := exists_lookup hn
  obtain ⟨A', x, _, hv⟩ := CtxI.lookup hA hsc
  have hrep : Conv (rep x) (Tm.var n) := varVal_rep_conv sc n ⟨A', x⟩ hv
  have hval := tmI_rep_conv (h n ⟨A', x⟩ hv)
  have hsub : Conv (rep (Cwa.tmSub (T := syntactic) u x)) (subst u.out.sub (rep x)) :=
    rep_tmSub u x
  have hvar : Conv (subst u.out.sub (rep x)) (u.out.sub n) := by
    have := hrep.subst u.out.sub
    simpa using this
  exact hvar.symm.trans (hsub.symm.trans hval)

/-! ### The comparison with the identity is natural -/

/-- The comparison `objIso` is carried by the identity substitution. -/
theorem objIso_hom_out_conv (Γ : Ob) {n : ℕ} (hn : n < Γ.ctx.length) :
    Conv ((objIso Γ).hom.out.sub n) (Tm.var n) := by
  have h := hom_out_conv (f := (objIso Γ).hom) (g := ctxConvHomRaw (objCtxConv Γ).1) rfl hn
  simpa [ctxConvHomRaw] using h

/-- **The comparison of the self-interpretation with the identity is natural.** -/
theorem objIso_naturality {Δ Γ : Ob} (σ : Δ ⟶ Γ) :
    homMap syntacticModel_piInj σ ≫ (objIso Γ).hom = (objIso Δ).hom ≫ σ := by
  refine hom_eq_of_out_conv (fun n hn => ?_)
  have hL : Conv ((homMap syntacticModel_piInj σ ≫ (objIso Γ).hom).out.sub n) (σ.out.sub n) := by
    refine (comp_out_conv (homMap syntacticModel_piInj σ) (objIso Γ).hom hn).trans ?_
    have h1 : Conv (subst (homMap syntacticModel_piInj σ).out.sub ((objIso Γ).hom.out.sub n))
        (subst (homMap syntacticModel_piInj σ).out.sub (Tm.var n)) :=
      (objIso_hom_out_conv Γ hn).subst _
    refine h1.trans ?_
    simpa using
      subI_out_conv (sem_spec syntacticModel_piInj Γ) (homMap_spec syntacticModel_piInj σ) hn
  have hR : Conv (((objIso Δ).hom ≫ σ).out.sub n) (σ.out.sub n) := by
    refine (comp_out_conv (objIso Δ).hom σ hn).trans ?_
    have hb : Bnd Δ.ctx.length (σ.out.sub n) := σ.out.bnd hn
    have := conv_subst_congr (σ := (objIso Δ).hom.out.sub) (τ := ids) hb
      (fun m hm => objIso_hom_out_conv Δ hm)
    simpa using this
  exact hL.trans hR.symm

/-- The comparison of the self-interpretation with the identity, as a natural transformation. -/
noncomputable def selfNatTrans :
    (functor syntacticModel_piInj) ⟶ (Cwa.Mor.id syntactic).fnc where
  app Γ := (objIso Γ).hom
  naturality _ _ σ := by
    simpa using objIso_naturality σ

/-- **The self-interpretation of a type is that type.** -/
theorem tySubQ_objIso (Γ : Ob) (A : TyQ Γ) :
    tySubQ (objIso Γ).hom A = tyMap syntacticModel_piInj A := by
  have hb : Bnd Γ.ctx.length A.rep.ty := (A.rep.ok.bnd_of_wf Γ.wf).1
  have h1 : Conv (tySubQ (objIso Γ).hom A).rep.ty A.rep.ty := by
    refine (tySubQ_rep_conv (objIso Γ).hom A).trans ?_
    have := conv_subst_congr (σ := (objIso Γ).hom.out.sub) (τ := ids) hb
      (fun m hm => objIso_hom_out_conv Γ hm)
    simpa [tySubRaw] using this
  have h2 : Conv (tyMap syntacticModel_piInj A).rep.ty A.rep.ty :=
    tyI_rep_conv (tyMap_spec syntacticModel_piInj A)
  conv_lhs => rw [← TyQ.tyMk_rep (tySubQ (objIso Γ).hom A)]
  conv_rhs => rw [← TyQ.tyMk_rep (tyMap syntacticModel_piInj A)]
  exact tyMk_eq_of_conv (h1.trans h2.symm)

/-! ### Contexts convertible in both directions have the same length -/

/-- A conversion of contexts does not shrink the context. -/
theorem ctxConvOk_length_le {Γ Δ : Ctx} (h : CtxConvOk Γ Δ) : Γ.length ≤ Δ.length := by
  by_contra hlt
  obtain ⟨A, hA⟩ := exists_lookup (Nat.lt_of_not_le hlt)
  obtain ⟨A', _, hA', _, _⟩ := h _ A hA
  exact absurd hA'.lt (by omega)

/-- **The object interpreting a context has a context of the same length.** -/
theorem objCtx_length (Γ : Ob) :
    (obj syntacticModel_piInj Γ).ctx.length = Γ.ctx.length :=
  le_antisymm (ctxConvOk_length_le (objCtxConv Γ).2) (ctxConvOk_length_le (objCtxConv Γ).1)

/-! ### Composites of morphisms carried by the identity substitution -/

/-- A composite of two morphisms carried by the identity substitution is carried by it. -/
theorem comp_ids_out_conv {X Y Z : Ob} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hlen : Z.ctx.length ≤ Y.ctx.length)
    (hf : ∀ n, n < Y.ctx.length → Conv (f.out.sub n) (Tm.var n))
    (hg : ∀ n, n < Z.ctx.length → Conv (g.out.sub n) (Tm.var n))
    {n : ℕ} (hn : n < Z.ctx.length) : Conv ((f ≫ g).out.sub n) (Tm.var n) := by
  refine (comp_out_conv f g hn).trans ?_
  refine ((hg n hn).subst f.out.sub).trans ?_
  simpa using hf n (lt_of_lt_of_le hn hlen)

/-- The action of the comparison on an extended context is carried by the identity
substitution. -/
theorem extendQ_objIso_out_conv (Γ : Ob) (A : TyQ Γ) {n : ℕ}
    (hn : n < (extOb Γ A).ctx.length) :
    Conv ((extendQ (objIso Γ).hom A).out.sub n) (Tm.var n) := by
  refine (extendQ_out_conv (objIso Γ).hom A hn).trans ?_
  have hlen : (extOb Γ A).ctx.length = Γ.ctx.length + 1 := rfl
  rw [hlen] at hn
  cases n with
  | zero => exact Conv.refl _
  | succ m =>
      have hm : m < Γ.ctx.length := Nat.lt_of_succ_lt_succ hn
      have := (objIso_hom_out_conv Γ hm).rename Nat.succ
      simpa using this

/-- The comparison is compatible with the comparisons of extended contexts. -/
theorem extend_objIso (Γ : Ob) (A : TyQ Γ) :
    ((mor syntacticModel_piInj).extIso A).hom
        ≫ syntactic.substCompare (objIso Γ).hom (tySubQ_objIso Γ A)
      = (objIso (extOb Γ A)).hom ≫ ((Cwa.Mor.id syntactic).extIso A).hom := by
  have hobj : (obj syntacticModel_piInj Γ).ctx.length = Γ.ctx.length := objCtx_length Γ
  refine hom_eq_of_out_conv (fun n hn => ?_)
  have hL : Conv ((((mor syntacticModel_piInj).extIso A).hom
      ≫ syntactic.substCompare (objIso Γ).hom (tySubQ_objIso Γ A)).out.sub n) (Tm.var n) := by
    have h1 : ∀ m, m < (extOb (obj syntacticModel_piInj Γ)
        (tyMap syntacticModel_piInj A)).ctx.length →
        Conv (((mor syntacticModel_piInj).extIso A).hom.out.sub m) (Tm.var m) := fun m hm =>
      eqToHom_out_conv (objExt syntacticModel_piInj A) hm
    have h2 : ∀ m, m < (extOb Γ A).ctx.length →
        Conv ((syntactic.substCompare (objIso Γ).hom (tySubQ_objIso Γ A)).out.sub m)
          (Tm.var m) := by
      intro m hm
      refine comp_ids_out_conv (Y := extOb (obj syntacticModel_piInj Γ)
        (tySubQ (objIso Γ).hom A)) ?_ (fun k hk => eqToHom_out_conv _ hk)
        (fun k hk => extendQ_objIso_out_conv Γ A hk) hm
      show (extOb Γ A).ctx.length ≤ (extOb (obj syntacticModel_piInj Γ)
        (tySubQ (objIso Γ).hom A)).ctx.length
      exact Nat.succ_le_succ (le_of_eq hobj.symm)
    refine comp_ids_out_conv ?_ h1 h2 hn
    show (extOb Γ A).ctx.length ≤ (extOb (obj syntacticModel_piInj Γ)
      (tyMap syntacticModel_piInj A)).ctx.length
    exact Nat.succ_le_succ (le_of_eq hobj.symm)
  have hR : Conv (((objIso (extOb Γ A)).hom
      ≫ ((Cwa.Mor.id syntactic).extIso A).hom).out.sub n) (Tm.var n) := by
    have : ((Cwa.Mor.id syntactic).extIso A).hom = 𝟙 (extOb Γ A) := rfl
    rw [this, Category.comp_id]
    exact objIso_hom_out_conv (extOb Γ A) hn
  exact hL.trans hR.symm

/-- **The syntax of `λΠ` interprets itself by the identity**: the canonical interpretation of the
syntactic model in itself is connected to the identity morphism by a 2-cell. -/
noncomputable def selfTwoCell :
    Cwa.TwoCell (mor syntacticModel_piInj) (Cwa.Mor.id syntactic) where
  nat := selfNatTrans
  tySub_app A := tySubQ_objIso _ A
  extend_app A := extend_objIso _ A

/-- The 2-cell is invertible, its natural transformation being an isomorphism. -/
theorem isIso_selfTwoCell :
    @IsIso _ (Cwa.morCategory (T := syntactic) extCoherent_syntactic) _ _ selfTwoCell := by
  have hnat : IsIso selfTwoCell.nat := by
    have : ∀ Γ, IsIso (selfTwoCell.nat.app Γ) := fun Γ =>
      inferInstanceAs (IsIso (objIso Γ).hom)
    exact NatIso.isIso_of_isIso_app _
  exact Cwa.TwoCell.isIso_of_isIso_nat extCoherent_syntactic _

/-- **The self-interpretation is isomorphic to the identity morphism.** -/
noncomputable def selfIso :
    @Iso _ (Cwa.morCategory (T := syntactic) extCoherent_syntactic)
      (mor syntacticModel_piInj) (Cwa.Mor.id syntactic) :=
  @asIso _ (Cwa.morCategory (T := syntactic) extCoherent_syntactic) _ _ selfTwoCell
    isIso_selfTwoCell

/-! ### Every morphism of models out of the syntax is the canonical interpretation -/

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

/-- The self-interpretation whiskered by a morphism of models is invertible. -/
theorem isIso_whiskerRight_selfTwoCell (H : ModelHom syntacticModel M) :
    @IsIso _ (Cwa.morCategory (T := syntactic) M.co) _ _
      (selfTwoCell.whiskerRight H.mor) := by
  have hnat : IsIso (selfTwoCell.whiskerRight H.mor).nat := by
    have happ : ∀ Γ, IsIso ((selfTwoCell.whiskerRight H.mor).nat.app Γ) := fun Γ =>
      inferInstanceAs (IsIso (H.mor.fnc.map (objIso Γ).hom))
    exact NatIso.isIso_of_isIso_app _
  exact Cwa.TwoCell.isIso_of_isIso_nat M.co _

/-- **Every morphism of models of `λΠ` out of the syntactic model is isomorphic to the canonical
interpretation.**  This is the existence half of bi-initiality: interpreting the syntax in itself
and then applying the morphism is the morphism, and it is isomorphic to interpreting directly. -/
noncomputable def isoModelHom (hinj : M.PiInj) (H : ModelHom syntacticModel M) :
    @Iso _ (Cwa.morCategory (T := syntactic) M.co) (mor hinj) H.mor := by
  letI := Cwa.morCategory (T := syntactic) M.co
  exact transportIso syntacticModel_piInj hinj H ≪≫
    (@asIso _ _ _ _ (selfTwoCell.whiskerRight H.mor) (isIso_whiskerRight_selfTwoCell H)) ≪≫
      eqToIso (Cwa.Mor.id_comp H.mor)

/-- **The existence half of bi-initiality**: a morphism of models of `λΠ` out of the syntactic
model receives a 2-cell from the canonical interpretation. -/
noncomputable def twoCell_of_modelHom (hinj : M.PiInj) (H : ModelHom syntacticModel M) :
    Cwa.TwoCell (mor hinj) H.mor := by
  letI := Cwa.morCategory (T := syntactic) M.co
  exact (isoModelHom hinj H).hom

/-- **Any two morphisms of models of `λΠ` out of the syntactic model are isomorphic** as 1-cells
of categories with attributes. -/
noncomputable def isoModelHom_modelHom (hinj : M.PiInj) (H K : ModelHom syntacticModel M) :
    @Iso _ (Cwa.morCategory (T := syntactic) M.co) H.mor K.mor := by
  letI := Cwa.morCategory (T := syntactic) M.co
  exact (isoModelHom hinj H).symm ≪≫ isoModelHom hinj K

/-- **The hom-category from the syntax of `λΠ` to a model of `λΠ` is contractible on the
morphisms of models**: between the 1-cells underlying two morphisms of models out of the syntax
there is exactly one 2-cell.  Existence is the isomorphism above; uniqueness is the rigidity of
`Start/CwaBiInitial.lean`, the empty context being sent to a terminal object. -/
theorem nonempty_unique_twoCell_modelHom (hinj : M.PiInj) (H K : ModelHom syntacticModel M) :
    Nonempty (Cwa.TwoCell H.mor K.mor) ∧ Subsingleton (Cwa.TwoCell H.mor K.mor) := by
  let _ := Cwa.morCategory (T := syntactic) M.co
  exact ⟨⟨(isoModelHom_modelHom hinj H K).hom⟩,
    LambdaPiBiInitial.subsingleton_twoCell K.empTerminal⟩

end LambdaPiSelf
