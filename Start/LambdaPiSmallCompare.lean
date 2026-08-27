/-
**The two syntactic models of `λΠ` are compared.**

`Start/LambdaPiCwa.lean` makes the contexts of `λΠ` into a category with attributes whose types are
the *small* types — the terms of `∗` — while `Start/LambdaPiFull.lean` does the same with *all* the
types of the calculus, and `Start/LambdaPiUniv.lean` exhibits `∗` as a universe inside the latter.
`Start/CwaSmall.lean` extracts from a model with a universe its small fragment, and applied to that
universe it gives a third model, `LambdaPiUniv.smallSyntactic`, whose types in a context are the
terms of `∗`.

This module compares the third with the first, and finds them the same:

* `LambdaPiUniv.smallToCwa` is a morphism of categories with attributes from the small fragment of
  the model with all types to the model of small types.  It is the identity on contexts, its action
  on types is the bijection `LambdaPiUniv.smallTyEquiv` between the terms of `∗` and the small types
  (`LambdaPiUniv.smallToCwa_tyMap_bijective`), and its comparison of extended contexts is the
  identity substitution, read as an isomorphism between extensions by convertible types;
* `LambdaPiUniv.cwaToSmall` is the morphism in the other direction, coding a small type;
* `LambdaPiUniv.smallModelIso` — the two are mutually inverse
  (`LambdaPiUniv.smallToCwa_comp_cwaToSmall`, `LambdaPiUniv.cwaToSmall_comp_smallToCwa`), so the
  two syntactic models are **isomorphic** in the category of models of `Start/CwaCat.lean`.

The work is in the last axiom of a morphism, the compatibility with the action of a substitution on
extended contexts: both sides are substitutions up to conversion, and both are shown to act as the
lifting `up` of the calculus.
-/

import Start.CwaCat
import Start.CwaSmall

set_option relaxedAutoImplicit false
set_option autoImplicit false

open CategoryTheory Limits

namespace LambdaPiUniv

open LambdaPi LambdaPiCat LambdaPiFull

/-! ### Morphisms acting as the identity substitution -/

/-- Substituting along a morphism that acts as the identity substitution does nothing. -/
theorem subst_out_ids_conv {X Y : Ob} {f : X ⟶ Y}
    (hf : ∀ n, n < Y.ctx.length → Conv (f.out.sub n) (Tm.var n)) {t : Tm}
    (ht : Bnd Y.ctx.length t) : Conv (subst f.out.sub t) t := by
  have h := conv_subst_congr (σ := f.out.sub) (τ := ids) ht (fun n hn => hf n hn)
  rwa [subst_ids] at h

/-- The isomorphism between extensions by convertible types acts as the identity
substitution. -/
theorem convIso_out_conv {Γ : Ob} {C D : TyOf Γ} (h : Conv C.ty D.ty) {n : ℕ}
    (hn : n < (cons Γ D.ok).ctx.length) :
    Conv ((convIso h).hom.out.sub n) (Tm.var n) := by
  have hdef : (convIso h).hom = mk (convHomRaw h) := rfl
  simpa [convHomRaw] using hom_out_conv hdef hn

/-- Two morphisms of the syntactic category are equal when their representatives are convertible
at every variable of the target context. -/
theorem hom_ext_out {X Y : Ob} {f g : X ⟶ Y}
    (h : ∀ n, n < Y.ctx.length → Conv (f.out.sub n) (g.out.sub n)) : f = g := by
  conv_lhs => rw [← Quotient.out_eq f]
  conv_rhs => rw [← Quotient.out_eq g]
  exact mk_eq h

/-- The action of a substitution on extended contexts, in the model of small types, acts as
`up`. -/
theorem cwaExtendQ_out_conv {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : LambdaPiCwa.TyQ Γ) {n : ℕ}
    (hn : n < (LambdaPiCwa.extOb Γ A).ctx.length) :
    Conv ((LambdaPiCwa.extendQ σ A).out.sub n) (up σ.out.sub n) := by
  have hdef : LambdaPiCwa.extendQ σ A
      = mk (RawHom.comp (LambdaPiCwa.convHomRaw (LambdaPiCwa.tySubQ_rep_conv σ A))
          (extendRaw σ.out A.rep.ok)) := rfl
  have h := hom_out_conv hdef hn
  simpa only [RawHom.comp, LambdaPiCwa.convHomRaw, extendRaw, subst_ids] using h

/-! ### The comparison of the two syntactic models -/

/-- A code, read as a small type of `Start/LambdaPiCwa.lean`, with its typing derivation. -/
noncomputable def smallTyOf (Γ : Ob) (a : Cwa.Tm syntactic Γ (uQ Γ)) : TyOf Γ :=
  ⟨(smallTyEquiv Γ a).rep.ty, Srt.star, (smallTyEquiv Γ a).rep.ok⟩

/-- The decoding of a code is convertible to the small type it names. -/
theorem elQ_conv_smallTyOf {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) :
    Conv (elQ a).rep.ty (smallTyOf Γ a).ty :=
  (elQ_rep_conv a).trans
    (LambdaPiCwa.TyQ.rep_conv (A := (⟨codeTm a, codeTm_ok a⟩ : LambdaPiCwa.TyOf Γ))).symm

/-- The action on types is compatible with substitution. -/
theorem smallTyEquiv_sub {Γ Δ : Ob} (σ : Δ ⟶ Γ) (a : Cwa.Tm syntactic Γ (uQ Γ)) :
    smallTyEquiv Δ (univ.sub σ a) = LambdaPiCwa.tySubQ σ (smallTyEquiv Γ a) := by
  rw [show smallTyEquiv Γ a = LambdaPiCwa.tyMk ⟨codeTm a, codeTm_ok a⟩ from rfl,
    LambdaPiCwa.tySubQ_tyMk]
  exact LambdaPiCwa.tyMk_eq (codeTm_sub σ a)

/-- **The comparison of the two syntactic models of `λΠ`**: the small fragment of the model with
all types maps to the model of small types, by the identity on contexts and by the identification
of the terms of `∗` with the small types. -/
noncomputable def smallToCwa : Cwa.Mor smallSyntactic LambdaPiCwa.syntactic where
  fnc := 𝟭 Ob
  tyMap {Γ} a := smallTyEquiv Γ a
  tyMap_sub σ a := smallTyEquiv_sub σ a
  extIso {Γ} a := convIso (C := (elQ a).rep) (D := smallTyOf Γ a) (elQ_conv_smallTyOf a)
  extIso_disp a := convIso_hom_disp _
  extIso_extend {Γ Δ} σ a := by
    refine hom_ext_out ?_
    intro n hn
    have hleft : Conv ((((𝟭 Ob).map (smallSyntactic.extend σ a)
        ≫ (convIso (elQ_conv_smallTyOf a)).hom)).out.sub n) (up σ.out.sub n) := by
      refine (comp_out_conv _ _ hn).trans ?_
      refine Conv.trans ((convIso_out_conv (elQ_conv_smallTyOf a) hn).subst _) ?_
      rw [subst_var]
      exact extHom_out_conv σ a hn
    refine hleft.trans (Conv.symm ?_)
    refine (comp_out_conv _ _ hn).trans ?_
    refine Conv.trans (subst_out_ids_conv
      (fun m hm => convIso_out_conv (elQ_conv_smallTyOf (univ.sub σ a)) hm)
      (RawHom.bnd _ hn)) ?_
    refine (comp_out_conv _ _ hn).trans ?_
    refine Conv.trans (subst_out_ids_conv (fun m hm => eqToHom_out_conv _ hm)
      (RawHom.bnd _ hn)) ?_
    exact cwaExtendQ_out_conv σ (smallTyEquiv Γ a) hn

/-- The action of the comparison on types is a bijection: the terms of `∗` are exactly the small
types. -/
theorem smallToCwa_tyMap_bijective (Γ : Ob) :
    Function.Bijective (smallToCwa.tyMap (Γ := Γ)) := (smallTyEquiv Γ).bijective

/-! ### The comparison in the other direction -/

/-- A small type of `Start/LambdaPiCwa.lean`, read as a type of the model with all types. -/
noncomputable def fullTyOf (Γ : Ob) (A : LambdaPiCwa.TyQ Γ) : TyOf Γ :=
  ⟨A.rep.ty, Srt.star, A.rep.ok⟩

/-- Coding a small type and decoding it again gives back a convertible type. -/
theorem fullTyOf_conv_elQ {Γ : Ob} (A : LambdaPiCwa.TyQ Γ) :
    Conv (fullTyOf Γ A).ty (elQ (ofSmall A)).rep.ty :=
  ((elQ_rep_conv (ofSmall A)).trans (codeTm_ofSmall A)).symm

/-- The code of a small type, read back, is the small type. -/
theorem smallTyEquiv_ofSmall {Γ : Ob} (A : LambdaPiCwa.TyQ Γ) :
    smallTyEquiv Γ (ofSmall A) = A := (smallTyEquiv Γ).apply_symm_apply A

/-- The small type named by a code, coded again, is the code. -/
theorem ofSmall_smallTyEquiv {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) :
    ofSmall (smallTyEquiv Γ a) = a := (smallTyEquiv Γ).symm_apply_apply a

/-- Coding a small type is compatible with substitution. -/
theorem ofSmall_sub {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : LambdaPiCwa.TyQ Γ) :
    ofSmall (LambdaPiCwa.tySubQ σ A) = univ.sub σ (ofSmall A) := by
  refine (smallTyEquiv Δ).injective ?_
  rw [smallTyEquiv_ofSmall, smallTyEquiv_sub σ (ofSmall A), smallTyEquiv_ofSmall]

/-- **The inverse comparison**: the model of small types maps back to the small fragment of the
model with all types, by the identity on contexts and by coding a small type. -/
noncomputable def cwaToSmall : Cwa.Mor LambdaPiCwa.syntactic smallSyntactic where
  fnc := 𝟭 Ob
  tyMap {_} A := ofSmall A
  tyMap_sub σ A := ofSmall_sub σ A
  extIso {Γ} A := convIso (C := fullTyOf Γ A) (D := (elQ (ofSmall A)).rep) (fullTyOf_conv_elQ A)
  extIso_disp _ := convIso_hom_disp _
  extIso_extend {Γ Δ} σ A := by
    refine hom_ext_out ?_
    intro n hn
    have hleft : Conv ((((𝟭 Ob).map (LambdaPiCwa.syntactic.extend σ A)
        ≫ (convIso (fullTyOf_conv_elQ A)).hom)).out.sub n) (up σ.out.sub n) := by
      refine (comp_out_conv _ _ hn).trans ?_
      refine Conv.trans ((convIso_out_conv (fullTyOf_conv_elQ A) hn).subst _) ?_
      rw [subst_var]
      exact cwaExtendQ_out_conv σ A hn
    refine hleft.trans (Conv.symm ?_)
    refine (comp_out_conv _ _ hn).trans ?_
    refine Conv.trans (subst_out_ids_conv
      (fun m hm => convIso_out_conv (fullTyOf_conv_elQ (LambdaPiCwa.tySubQ σ A)) hm)
      (RawHom.bnd _ hn)) ?_
    refine (comp_out_conv _ _ hn).trans ?_
    refine Conv.trans (subst_out_ids_conv (fun m hm => eqToHom_out_conv _ hm)
      (RawHom.bnd _ hn)) ?_
    exact extHom_out_conv σ (ofSmall A) hn

/-! ### The two comparisons are mutually inverse -/

/-- A composite of two morphisms acting as the identity substitution acts as the identity
substitution. -/
theorem comp_out_ids_conv {X Y Z : Ob} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : ∀ n, n < Y.ctx.length → Conv (f.out.sub n) (Tm.var n))
    (hg : ∀ n, n < Z.ctx.length → Conv (g.out.sub n) (Tm.var n))
    {n : ℕ} (hn : n < Z.ctx.length) (hn' : n < Y.ctx.length) :
    Conv ((f ≫ g).out.sub n) (Tm.var n) := by
  refine (comp_out_conv f g hn).trans ?_
  refine Conv.trans ((hg n hn).subst _) ?_
  rw [subst_var]
  exact hf n hn'

/-- **Coding and then decoding is the identity**: the comparison followed by its inverse is the
identity morphism of the small fragment. -/
theorem smallToCwa_comp_cwaToSmall : smallToCwa.comp cwaToSmall = Cwa.Mor.id smallSyntactic := by
  refine Cwa.Mor.ext rfl (fun a => heq_of_eq (ofSmall_smallTyEquiv a)) (fun a => ?_)
  refine Cwa.heq_iso_ext (ofSmall_smallTyEquiv a) ?_
  refine hom_ext_out (fun n hn => ?_)
  refine Conv.trans ?_ (id_out_conv _ rfl hn).symm
  refine comp_out_ids_conv (fun m hm => ?_) (fun m hm => eqToHom_out_conv _ hm) hn hn
  exact comp_out_ids_conv (fun k hk => convIso_out_conv _ hk)
    (fun k hk => convIso_out_conv _ hk) hm hm

/-- **Decoding and then coding is the identity**: the inverse comparison followed by the
comparison is the identity morphism of the model of small types. -/
theorem cwaToSmall_comp_smallToCwa :
    cwaToSmall.comp smallToCwa = Cwa.Mor.id LambdaPiCwa.syntactic := by
  refine Cwa.Mor.ext rfl (fun A => heq_of_eq (smallTyEquiv_ofSmall A)) (fun A => ?_)
  refine Cwa.heq_iso_ext (smallTyEquiv_ofSmall A) ?_
  refine hom_ext_out (fun n hn => ?_)
  refine Conv.trans ?_ (id_out_conv _ rfl hn).symm
  refine comp_out_ids_conv (fun m hm => ?_) (fun m hm => eqToHom_out_conv _ hm) hn hn
  exact comp_out_ids_conv (fun k hk => convIso_out_conv _ hk)
    (fun k hk => convIso_out_conv _ hk) hm hm

/-- **The two syntactic models of `λΠ` are isomorphic**, in the category of models of
`Start/CwaCat.lean`: the small fragment of the model with all types and the model whose types are
the small types are the same model. -/
noncomputable def smallModelIso :
    (⟨Ob, smallSyntactic⟩ : Cwa.Model.{0, 0, 0}) ≅ ⟨Ob, LambdaPiCwa.syntactic⟩ where
  hom := smallToCwa
  inv := cwaToSmall
  hom_inv_id := smallToCwa_comp_cwaToSmall
  inv_hom_id := cwaToSmall_comp_smallToCwa

end LambdaPiUniv
