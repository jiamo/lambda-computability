/-
**The sort `∗` is a universe of small types in the syntactic model of `λΠ`, closed under the
dependent product.**

`Start/LambdaPiFull.lean` makes the contexts of `λΠ` with *all* of its types into a category with
attributes.  This file exhibits the extra structure that the interpretation of `λΠ` needs and that
`Start/CwaUniverse.lean` axiomatises:

* `LambdaPiUniv.tmSub_tmEquiv_symm` — the categorical substitution of terms (the lift given by the
  universal property of context extension) is the substitution of the calculus;
* `LambdaPiUniv.uQ` — the type `∗` of a context, and `LambdaPiUniv.elQ` the decoding of its terms:
  a term of `∗` *is* a small type;
* `LambdaPiUniv.univ : Cwa.Universe LambdaPiFull.syntactic` — **`∗` is a universe à la Tarski in
  the syntactic category with attributes**: it is stable under substitution on the nose, and so is
  the decoding;
* `LambdaPiUniv.smallPi : Cwa.Universe.SmallPi univ` — **the product rules `(∗,∗)` and `(∗,□)` of
  `λΠ` are exactly a dependent product over that universe**, with the Beck–Chevalley condition, the
  β-law, and a code for the product of two small types (`LambdaPiUniv.codeQ`), witnessing that the
  universe is closed under products.
-/

import Start.LambdaPiFull

set_option relaxedAutoImplicit false
set_option autoImplicit false

open CategoryTheory Limits

namespace LambdaPiUniv

open LambdaPi LambdaPiCat LambdaPiFull

/-! ### Reading a morphism off a representative -/

/-- A composite acts, at every variable of its target, as the composite of representatives. -/
theorem comp_out_conv {X Y Z : Ob} (f : X ⟶ Y) (g : Y ⟶ Z) {n : ℕ} (hn : n < Z.ctx.length) :
    Conv ((f ≫ g).out.sub n) (subst f.out.sub (g.out.sub n)) := by
  refine hom_out_conv (g := RawHom.comp f.out g.out) ?_ hn
  conv_lhs => rw [← Quotient.out_eq f, ← Quotient.out_eq g]
  rfl

/-- The identity acts as the identity substitution. -/
theorem id_out_conv {X : Ob} (f : X ⟶ X) (hf : f = 𝟙 X) {n : ℕ} (hn : n < X.ctx.length) :
    Conv (f.out.sub n) (Tm.var n) :=
  hom_out_conv (g := RawHom.id X) (by rw [hf]; rfl) hn

/-- The canonical morphism between equal contexts acts as the identity substitution. -/
theorem eqToHom_out_conv {X Y : Ob} (h : X = Y) {n : ℕ} (hn : n < Y.ctx.length) :
    Conv ((eqToHom h).out.sub n) (Tm.var n) := by
  cases h
  exact id_out_conv _ (by simp) hn

/-- Substituting along a morphism between equal contexts does nothing. -/
theorem subst_eqToHom_conv {X Y : Ob} (h : X = Y) {t : Tm} (ht : Bnd Y.ctx.length t) :
    Conv (subst (eqToHom h).out.sub t) t := by
  have := conv_subst_congr (σ := (eqToHom h).out.sub) (τ := ids) ht
    (fun n hn => eqToHom_out_conv h hn)
  rwa [subst_ids] at this

/-- The action of a substitution on an extended context acts as `up`. -/
theorem extendQ_out_conv {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) {n : ℕ}
    (hn : n < (extOb Γ A).ctx.length) :
    Conv ((extendQ σ A).out.sub n) (up σ.out.sub n) := by
  have h : extendQ σ A
      = mk (RawHom.comp (convHomRaw (tySubQ_rep_conv σ A)) (extendRaw σ.out A.rep.ok)) := rfl
  have := hom_out_conv (f := extendQ σ A) h (n := n) hn
  simpa only [RawHom.comp, convHomRaw, extendRaw, subst_ids] using this

/-! ### The categorical substitution of terms is the substitution of the calculus -/

/-- The substitution of a term, on a representative. -/
noncomputable def tmSubOf {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) (t : TmOf Γ A.rep.ty) :
    TmOf Δ (tySubQ σ A).rep.ty :=
  ⟨subst σ.out.sub t.tm,
    (t.ok.substs σ.out.ok).conv (tySubQ σ A).rep.ok (tySubQ_rep_conv σ A).symm⟩

/-- **The categorical substitution of terms is the substitution of the calculus.**  The term
substitution of a category with attributes is defined by the universal property of context
extension; on the syntactic model it is computed by substituting in a representative. -/
theorem tmSub_tmEquiv_symm {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) (t : TmOf Γ A.rep.ty) :
    Cwa.tmSub (T := syntactic) σ ((tmEquiv A).symm (tmMk t))
      = (tmEquiv (tySubQ σ A)).symm (tmMk (tmSubOf σ A t)) := by
  refine (Cwa.tmSub_eq_of σ _ _ ?_).symm
  have hl : (((tmEquiv (tySubQ σ A)).symm (tmMk (tmSubOf σ A t))) :
        Cwa.Tm syntactic Δ (tySubQ σ A)).1
      = mk (tmRaw (tySubQ σ A).rep.ok (tmSubOf σ A t)) := rfl
  have hr : (((tmEquiv A).symm (tmMk t)) : Cwa.Tm syntactic Γ A).1 = mk (tmRaw A.rep.ok t) := rfl
  have hext : (syntactic.extend σ A)
      = mk (RawHom.comp (convHomRaw (tySubQ_rep_conv σ A)) (extendRaw σ.out A.rep.ok)) := rfl
  rw [hl, hr, hext]
  conv_rhs => rw [← Quotient.out_eq σ]
  refine mk_eq ?_
  intro n _
  cases n with
  | zero =>
      change Conv (subst (scons (subst σ.out.sub t.tm) ids) (subst ids (up σ.out.sub 0)))
        (subst σ.out.sub (scons t.tm ids 0))
      simp only [up_zero, subst_ids]
      exact Conv.refl _
  | succ n =>
      change Conv (subst (scons (subst σ.out.sub t.tm) ids) (subst ids (up σ.out.sub (n + 1))))
        (subst σ.out.sub (scons t.tm ids (n + 1)))
      simp only [up_succ, subst_ids, scons_succ, ids_apply, subst_var]
      rw [← shift, subst_shift']
      simp only [scons_succ, subst_ids]
      exact Conv.refl _

/-- The representative of a substituted term is the substituted representative. -/
theorem tmEquiv_tmSub_conv {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) (a : Cwa.Tm syntactic Γ A) :
    Conv ((tmEquiv (tySubQ σ A) (Cwa.tmSub (T := syntactic) σ a)).out.tm)
      (subst σ.out.sub ((tmEquiv A a).out.tm)) := by
  have h2 : tmMk (tmEquiv A a).out = tmEquiv A a := Quotient.out_eq _
  have ha0 : a = (tmEquiv A).symm (tmMk (tmEquiv A a).out) := by
    rw [h2, Equiv.symm_apply_apply]
  have ha : Cwa.tmSub (T := syntactic) σ a
      = (tmEquiv (tySubQ σ A)).symm (tmMk (tmSubOf σ A (tmEquiv A a).out)) := by
    conv_lhs => rw [ha0]
    exact tmSub_tmEquiv_symm σ A _
  rw [ha, Equiv.apply_symm_apply]
  exact Quotient.exact (Quotient.out_eq (tmMk (tmSubOf σ A (tmEquiv A a).out)))

/-! ### The universe -/

/-- The sort `∗`, as a type of a context: it is typed by `□`. -/
def uOf (Γ : Ob) : TyOf Γ := ⟨Tm.sort Srt.star, Srt.box, Typing.ax Γ.ctx⟩

/-- The universe of small types: the type `∗` of a context. -/
def uQ (Γ : Ob) : TyQ Γ := tyMk (uOf Γ)

theorem uQ_rep_conv (Γ : Ob) : Conv (uQ Γ).rep.ty (Tm.sort Srt.star) := TyQ.rep_conv

/-- The universe is stable under substitution: `∗` is a closed term. -/
theorem uQ_sub {Γ Δ : Ob} (σ : Δ ⟶ Γ) : tySubQ σ (uQ Γ) = uQ Δ := by
  rw [uQ, tySubQ_tyMk]
  exact tyMk_eq rfl (Conv.refl _)

/-- The raw term underlying a code, i.e. a term of `∗`. -/
noncomputable def codeTm {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) : Tm :=
  (tmEquiv (uQ Γ) a).out.tm

theorem codeTm_ok {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) :
    Typing Γ.ctx (codeTm a) (Tm.sort Srt.star) :=
  ((tmEquiv (uQ Γ) a).out.ok).conv (Typing.ax Γ.ctx) (uQ_rep_conv Γ)

/-- The code of a term built from a representative is that representative. -/
theorem codeTm_symm {Γ : Ob} (t : TmOf Γ (uQ Γ).rep.ty) :
    Conv (codeTm ((tmEquiv (uQ Γ)).symm (tmMk t))) t.tm := by
  change Conv ((tmEquiv (uQ Γ) ((tmEquiv (uQ Γ)).symm (tmMk t))).out.tm) t.tm
  rw [Equiv.apply_symm_apply]
  exact Quotient.exact (Quotient.out_eq (tmMk t))

/-- **Decoding**: a term of `∗` is a small type. -/
noncomputable def elQ {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) : TyQ Γ :=
  tyMk ⟨codeTm a, Srt.star, codeTm_ok a⟩

theorem elQ_rep_conv {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) :
    Conv (elQ a).rep.ty (codeTm a) := TyQ.rep_conv

theorem elQ_rep_srt {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) :
    (elQ a).rep.srt = Srt.star := TyQ.rep_srt

/-- A decoded type is typed by `∗`; this is what makes it a legal domain of a product. -/
theorem elQ_rep_ok {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) :
    Typing Γ.ctx (elQ a).rep.ty (Tm.sort Srt.star) := by
  have h := (elQ a).rep.ok
  rwa [elQ_rep_srt a] at h

/-- Casting a term along an equality with the universe does not change its representative. -/
theorem codeTm_cast {Γ : Ob} {A : TyQ Γ} (h : A = uQ Γ) (a : Cwa.Tm syntactic Γ A) :
    codeTm (Cwa.tmCast h a) = (tmEquiv A a).out.tm := by
  cases h
  rfl

/-- **Decoding is stable under substitution.** -/
theorem elQ_sub {Γ Δ : Ob} (σ : Δ ⟶ Γ) (a : Cwa.Tm syntactic Γ (uQ Γ)) :
    tySubQ σ (elQ a) = elQ (Cwa.tmCast (uQ_sub σ) (Cwa.tmSub (T := syntactic) σ a)) := by
  have h1 : tySubQ σ (elQ a) = tyMk (tySubRaw σ.out ⟨codeTm a, Srt.star, codeTm_ok a⟩) :=
    tySubQ_tyMk σ _
  rw [h1]
  refine tyMk_eq rfl ?_
  change Conv (subst σ.out.sub (codeTm a)) (codeTm (Cwa.tmCast (uQ_sub σ) _))
  rw [codeTm_cast]
  exact (tmEquiv_tmSub_conv σ (uQ Γ) a).symm

/-- **`∗` is a universe of small types in the syntactic category with attributes of `λΠ`.** -/
noncomputable def univ : Cwa.Universe syntactic where
  U := uQ
  U_sub := uQ_sub
  El := elQ
  El_sub := elQ_sub

@[simp] theorem univ_U (Γ : Ob) : univ.U Γ = uQ Γ := rfl

@[simp] theorem univ_El {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) : univ.El a = elQ a := rfl

/-! ### The terms of the universe are exactly the small types -/

/-- A small type, read as a term of the universe. -/
noncomputable def ofSmall {Γ : Ob} (A : LambdaPiCwa.TyQ Γ) : Cwa.Tm syntactic Γ (uQ Γ) :=
  (tmEquiv (uQ Γ)).symm
    (tmMk ⟨A.rep.ty, A.rep.ok.conv (uQ Γ).rep.ok (uQ_rep_conv Γ).symm⟩)

theorem codeTm_ofSmall {Γ : Ob} (A : LambdaPiCwa.TyQ Γ) :
    Conv (codeTm (ofSmall A)) A.rep.ty := codeTm_symm _

/-- A term of the universe is determined by its code. -/
theorem eq_of_codeTm_conv {Γ : Ob} {a b : Cwa.Tm syntactic Γ (uQ Γ)}
    (h : Conv (codeTm a) (codeTm b)) : a = b := by
  have ha : tmMk (tmEquiv (uQ Γ) a).out = tmEquiv (uQ Γ) a := Quotient.out_eq _
  have hb : tmMk (tmEquiv (uQ Γ) b).out = tmEquiv (uQ Γ) b := Quotient.out_eq _
  have : tmEquiv (uQ Γ) a = tmEquiv (uQ Γ) b := by
    rw [← ha, ← hb]
    exact Quotient.sound h
  exact (tmEquiv (uQ Γ)).injective this

/-- **The terms of the universe `∗` are exactly the small types of the context.**  This is the
precise sense in which `∗` is the universe of the types of `λΠ`: its terms are the objects that
`Start/LambdaPiCwa.lean` takes as the types of its (small) syntactic model. -/
noncomputable def smallTyEquiv (Γ : Ob) :
    Cwa.Tm syntactic Γ (uQ Γ) ≃ LambdaPiCwa.TyQ Γ where
  toFun a := LambdaPiCwa.tyMk ⟨codeTm a, codeTm_ok a⟩
  invFun := ofSmall
  left_inv a := by
    refine eq_of_codeTm_conv ?_
    exact (codeTm_ofSmall _).trans LambdaPiCwa.TyQ.rep_conv
  right_inv A := by
    refine (LambdaPiCwa.tyMk_eq (B := A.rep) (codeTm_ofSmall A)).trans ?_
    exact LambdaPiCwa.TyQ.tyMk_rep A

/-- Decoding is injective: a small type has exactly one code. -/
theorem elQ_injective {Γ : Ob} : Function.Injective (elQ (Γ := Γ)) := by
  intro a b h
  refine eq_of_codeTm_conv ?_
  have h1 : Conv (codeTm a) (elQ a).rep.ty := (elQ_rep_conv a).symm
  rw [h] at h1
  exact h1.trans (elQ_rep_conv b)

/-! ### The dependent product over the universe -/

/-- The dependent product of `λΠ`, formed over a small type. -/
noncomputable def piQ {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) (B : TyQ (extOb Γ (elQ a))) :
    TyQ Γ :=
  tyMk ⟨Tm.pi (elQ a).rep.ty B.rep.ty, B.rep.srt, Typing.pi rfl (elQ_rep_ok a) B.rep.ok⟩

theorem piQ_rep_conv {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) (B : TyQ (extOb Γ (elQ a))) :
    Conv (piQ a B).rep.ty (Tm.pi (elQ a).rep.ty B.rep.ty) := TyQ.rep_conv

theorem piQ_rep_srt {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ)) (B : TyQ (extOb Γ (elQ a))) :
    (piQ a B).rep.srt = B.rep.srt := TyQ.rep_srt

/-- The action of a substitution on a context extended by a decoded type acts as `up`. -/
theorem extHom_out_conv {Γ Δ : Ob} (σ : Δ ⟶ Γ) (a : Cwa.Tm syntactic Γ (uQ Γ)) {n : ℕ}
    (hn : n < (extOb Γ (elQ a)).ctx.length) :
    Conv ((univ.extHom σ a).out.sub n) (up σ.out.sub n) := by
  have hdef : univ.extHom σ a
      = eqToHom (univ.ext_El_sub σ a).symm ≫ extendQ σ (elQ a) := rfl
  rw [hdef]
  refine (comp_out_conv _ _ hn).trans ?_
  refine Conv.trans (subst_eqToHom_conv _ ?_) (extendQ_out_conv σ (elQ a) hn)
  exact RawHom.bnd (extendQ σ (elQ a)).out hn

/-- **Beck–Chevalley**: the dependent product is stable under substitution. -/
theorem piQ_sub {Γ Δ : Ob} (σ : Δ ⟶ Γ) (a : Cwa.Tm syntactic Γ (uQ Γ))
    (B : TyQ (extOb Γ (elQ a))) :
    tySubQ σ (piQ a B) = piQ (univ.sub σ a) (tySubQ (univ.extHom σ a) B) := by
  have h1 : tySubQ σ (piQ a B)
      = tyMk (tySubRaw σ.out
          ⟨Tm.pi (elQ a).rep.ty B.rep.ty, B.rep.srt, Typing.pi rfl (elQ_rep_ok a) B.rep.ok⟩) :=
    tySubQ_tyMk σ _
  rw [h1]
  refine tyMk_eq (tySubQ_rep_srt (univ.extHom σ a) B).symm ?_
  refine Conv.pi ?_ ?_
  · have h3 := tySubQ_rep_conv σ (elQ a)
    rw [elQ_sub σ a] at h3
    exact h3.symm
  · refine Conv.trans ?_ (tySubQ_rep_conv (univ.extHom σ a) B).symm
    refine conv_subst_congr (B.rep.ok.bnd_of_wf (extOb Γ (elQ a)).wf).1 ?_
    intro n hn
    exact (extHom_out_conv σ a hn).symm

/-- Abstraction. -/
noncomputable def lamQ {Γ : Ob} {a : Cwa.Tm syntactic Γ (uQ Γ)} {B : TyQ (extOb Γ (elQ a))}
    (b : Cwa.Tm syntactic (extOb Γ (elQ a)) B) : Cwa.Tm syntactic Γ (piQ a B) :=
  (tmEquiv (piQ a B)).symm
    (tmConvEquiv (Typing.pi rfl (elQ_rep_ok a) B.rep.ok) (piQ a B).rep.ok (piQ_rep_conv a B).symm
      (lamTm (elQ a).rep.ok (Typing.pi rfl (elQ_rep_ok a) B.rep.ok) (tmEquiv B b)))

/-- Application, in generic-argument form. -/
noncomputable def appQ {Γ : Ob} {a : Cwa.Tm syntactic Γ (uQ Γ)} {B : TyQ (extOb Γ (elQ a))}
    (f : Cwa.Tm syntactic Γ (piQ a B)) : Cwa.Tm syntactic (extOb Γ (elQ a)) B :=
  (tmEquiv B).symm
    (appTm (elQ a).rep.ok
      ((tmConvEquiv (Typing.pi rfl (elQ_rep_ok a) B.rep.ok) (piQ a B).rep.ok
          (piQ_rep_conv a B).symm).symm (tmEquiv (piQ a B) f)))

/-- **β**: applying an abstraction to the generic argument gives the body back. -/
theorem appQ_lamQ {Γ : Ob} {a : Cwa.Tm syntactic Γ (uQ Γ)} {B : TyQ (extOb Γ (elQ a))}
    (b : Cwa.Tm syntactic (extOb Γ (elQ a)) B) : appQ (lamQ b) = b := by
  have h := appTm_lamTm (elQ a).rep.ok (Typing.pi rfl (elQ_rep_ok a) B.rep.ok) (tmEquiv B b)
  simp only [appQ, lamQ, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  exact (congrArg (tmEquiv B).symm h).trans ((tmEquiv B).symm_apply_apply b)

/-- **The universe is closed under products**: the code of the product of two small types. -/
noncomputable def codeQ {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ))
    (b : Cwa.Tm syntactic (extOb Γ (elQ a)) (uQ (extOb Γ (elQ a)))) :
    Cwa.Tm syntactic Γ (uQ Γ) :=
  (tmEquiv (uQ Γ)).symm
    (tmMk ⟨Tm.pi (elQ a).rep.ty (codeTm b),
      (Typing.pi rfl (elQ_rep_ok a) (codeTm_ok b)).conv (uQ Γ).rep.ok (uQ_rep_conv Γ).symm⟩)

/-- The code of a product decodes to the product of the decodings. -/
theorem elQ_codeQ {Γ : Ob} (a : Cwa.Tm syntactic Γ (uQ Γ))
    (b : Cwa.Tm syntactic (extOb Γ (elQ a)) (uQ (extOb Γ (elQ a)))) :
    elQ (codeQ a b) = piQ a (elQ b) := by
  refine tyMk_eq (elQ_rep_srt b).symm ?_
  refine (codeTm_symm _).trans ?_
  exact Conv.pi (Conv.refl _) (elQ_rep_conv b).symm

/-- **The product rules of `λΠ` are a dependent product over the universe `∗`.** -/
noncomputable def smallPi : Cwa.Universe.SmallPi univ where
  Pi := piQ
  Pi_sub := piQ_sub
  lam := lamQ
  app := appQ
  app_lam := appQ_lamQ

/-- **The universe `∗` is closed under the dependent product**: the product of two small types is
again a small type, by the rule `(∗,∗)`. -/
noncomputable def piClosed : Cwa.Universe.PiClosed univ smallPi where
  code := codeQ
  El_code := elQ_codeQ

end LambdaPiUniv
