/-
The syntactic category with attributes of `λΠ` with **all** of its types.

`Start/LambdaPiCwa.lean` builds a category with attributes on the syntactic category whose types
in a context are the *small* types, i.e. the terms of the sort `∗`.  That is the fragment on which
the dependent product of `λΠ` is defined, but it is too small to see the stratification of the
calculus: the sort `∗` itself is a type of the calculus (it is typed by `□`), and it is the type
whose terms are precisely the small types.  Interpreting `λΠ` therefore requires a category with
attributes whose types are *all* the types of the calculus, together with a universe inside it.

This file builds the first half of that: the category with attributes.

* `LambdaPiFull.TyOf Γ` — a type in a context: a term typable by *some* sort;
* `LambdaPiFull.TyQ Γ` — those types, up to conversion; `LambdaPiFull.tySubQ` is substitution;
* `LambdaPiFull.syntactic : Cwa LambdaPiCat.Ob` — **the contexts of `λΠ` with all its types form a
  category with attributes.**

The construction is the one of `Start/LambdaPiCwa.lean`, with the restriction to the sort `∗`
dropped; everything it uses from `Start/LambdaPiCat.lean` (context extension `cons`, the display
map, and the pullback property `isPullback_extend`) is already stated for an arbitrary sort.

`Start/LambdaPiUniv.lean` adds the universe: `∗` is a type of this model whose terms are the small
types, and the product rules of `λΠ` make it a `Cwa.Universe.SmallPi`.
-/

import Start.LambdaPiCwa
import Start.CwaUniverse

set_option relaxedAutoImplicit false
set_option autoImplicit false

open CategoryTheory Limits

namespace LambdaPiFull

open LambdaPi LambdaPiCat

/-! ### Types in a context -/

/-- A **type** in a context: a term typable by a sort.  Unlike `LambdaPiCwa.TyOf`, the sort is not
required to be `∗`, so the kinds of the calculus — `∗` itself, and the products landing in it —
are types here as well. -/
structure TyOf (Γ : Ob) where
  /-- The underlying term. -/
  ty : Tm
  /-- The sort it is typed by. -/
  srt : Srt
  /-- Its typing derivation. -/
  ok : Typing Γ.ctx ty (Tm.sort srt)

/-- Two types are identified when they are convertible *and* are typed by the same sort.  The
sort is recorded because the domain of a product of `λΠ` must be typed by `∗` specifically, and
uniqueness of sorts is not part of the metatheory developed in the project; nothing is lost, since
a type of the model is then a conversion class together with the sort it lives at. -/
instance tySetoid (Γ : Ob) : Setoid (TyOf Γ) where
  r A B := A.srt = B.srt ∧ Conv A.ty B.ty
  iseqv :=
    ⟨fun _ => ⟨rfl, Conv.refl _⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
      fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩

/-- Types in a context, up to conversion. -/
def TyQ (Γ : Ob) : Type := Quotient (tySetoid Γ)

/-- The conversion class of a type. -/
def tyMk {Γ : Ob} (A : TyOf Γ) : TyQ Γ := Quotient.mk _ A

theorem tyMk_eq {Γ : Ob} {A B : TyOf Γ} (hs : A.srt = B.srt) (h : Conv A.ty B.ty) :
    tyMk A = tyMk B :=
  Quotient.sound ⟨hs, h⟩

@[elab_as_elim] theorem TyQ.ind {Γ : Ob} {motive : TyQ Γ → Prop}
    (h : ∀ A : TyOf Γ, motive (tyMk A)) (x : TyQ Γ) : motive x := Quotient.ind h x

/-- A chosen representative of a conversion class of types. -/
noncomputable def TyQ.rep {Γ : Ob} (A : TyQ Γ) : TyOf Γ := Quotient.out A

@[simp] theorem TyQ.tyMk_rep {Γ : Ob} (A : TyQ Γ) : tyMk A.rep = A := Quotient.out_eq A

theorem TyQ.rep_conv {Γ : Ob} {A : TyOf Γ} : Conv (tyMk A).rep.ty A.ty :=
  (Quotient.exact (TyQ.tyMk_rep (tyMk A))).2

theorem TyQ.rep_srt {Γ : Ob} {A : TyOf Γ} : (tyMk A).rep.srt = A.srt :=
  (Quotient.exact (TyQ.tyMk_rep (tyMk A))).1

/-! ### Substitution on types -/

/-- Substitution acting on a representative. -/
def tySubRaw {Γ Δ : Ob} (f : RawHom Δ Γ) (A : TyOf Γ) : TyOf Δ :=
  ⟨subst f.sub A.ty, A.srt, A.ok.substs f.ok⟩

theorem tySubRaw_congr {Γ Δ : Ob} {f g : RawHom Δ Γ} {A B : TyOf Γ}
    (hf : RawHom.Rel f g) (hA : A.srt = B.srt ∧ Conv A.ty B.ty) :
    (tySubRaw f A).srt = (tySubRaw g B).srt ∧ Conv (tySubRaw f A).ty (tySubRaw g B).ty := by
  refine ⟨hA.1, ?_⟩
  refine (hA.2.subst f.sub).trans ?_
  exact conv_subst_congr (B.ok.bnd_of_wf Γ.wf).1 (fun n hn => hf n hn)

/-- Substitution acting on types. -/
def tySubQ {Γ Δ : Ob} (f : Δ ⟶ Γ) (A : TyQ Γ) : TyQ Δ :=
  Quotient.map₂ tySubRaw (fun _ _ hf _ _ hA => tySubRaw_congr hf hA) f A

@[simp] theorem tySubQ_mk {Γ Δ : Ob} (f : RawHom Δ Γ) (A : TyOf Γ) :
    tySubQ (mk f) (tyMk A) = tyMk (tySubRaw f A) := rfl

theorem tySubQ_id {Γ : Ob} (A : TyQ Γ) : tySubQ (𝟙 Γ) A = A := by
  refine TyQ.ind (fun A => ?_) A
  refine tyMk_eq rfl ?_
  simp only [tySubRaw, RawHom.id, subst_ids]
  exact Conv.refl _

theorem tySubQ_comp {Γ Δ Θ : Ob} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (A : TyQ Γ) :
    tySubQ (τ ≫ σ) A = tySubQ τ (tySubQ σ A) := by
  refine Hom.ind (motive := fun σ => tySubQ (τ ≫ σ) A = tySubQ τ (tySubQ σ A)) ?_ σ
  intro σ
  refine Hom.ind (motive := fun τ => tySubQ (τ ≫ mk σ) A = tySubQ τ (tySubQ (mk σ) A)) ?_ τ
  intro τ
  refine TyQ.ind (fun A => ?_) A
  refine tyMk_eq rfl ?_
  simp only [tySubRaw, RawHom.comp, subst_subst]
  exact Conv.refl _

/-! ### Context extension -/

/-- Context extension: the chosen representative of `A` is put in front of `Γ`. -/
noncomputable def extOb (Γ : Ob) (A : TyQ Γ) : Ob := cons Γ A.rep.ok

/-- The display map out of an extended context. -/
noncomputable def dispQ {Γ : Ob} (A : TyQ Γ) : extOb Γ A ⟶ Γ := disp Γ A.rep.ok

/-- Weakening a well-typed term of a sort past a variable. -/
theorem typing_shift_sort {Γ : Ob} (C : Tm) {D : Tm} {s : Srt}
    (hD : Typing Γ.ctx D (Tm.sort s)) :
    Typing (C :: Γ.ctx) (shift D) (Tm.sort s) := by
  have := hD.weaken C
  simpa [shift, rename] using this

/-- The identity substitution, seen as a morphism between two extensions by convertible types. -/
def convHomRaw {Γ : Ob} {C D : TyOf Γ} (h : Conv C.ty D.ty) :
    RawHom (cons Γ C.ok) (cons Γ D.ok) where
  sub := ids
  ok := by
    intro n B hB
    cases hB with
    | zero _ _ =>
        rw [subst_ids]
        have h0 : Typing (C.ty :: Γ.ctx) (Tm.var 0) (shift C.ty) := Typing.var (Lookup.zero _ _)
        refine h0.conv (typing_shift_sort C.ty D.ok) ?_
        exact h.rename Nat.succ
    | succ _ hB' =>
        rw [subst_ids]
        exact Typing.var (Lookup.succ _ hB')

/-- Extensions by convertible types are isomorphic, via the identity substitution. -/
def convIso {Γ : Ob} {C D : TyOf Γ} (h : Conv C.ty D.ty) : cons Γ C.ok ≅ cons Γ D.ok where
  hom := mk (convHomRaw h)
  inv := mk (convHomRaw h.symm)
  hom_inv_id := by
    refine mk_eq ?_
    intro n _
    simp only [RawHom.comp, convHomRaw, RawHom.id, ids_apply, subst_var]
    exact Conv.refl _
  inv_hom_id := by
    refine mk_eq ?_
    intro n _
    simp only [RawHom.comp, convHomRaw, RawHom.id, ids_apply, subst_var]
    exact Conv.refl _

theorem convIso_hom_disp {Γ : Ob} {C D : TyOf Γ} (h : Conv C.ty D.ty) :
    (convIso h).hom ≫ disp Γ D.ok = disp Γ C.ok := by
  refine mk_eq ?_
  intro n _
  simp only [RawHom.comp, convHomRaw, dispRaw, subst_ids]
  exact Conv.refl _

/-- The chosen representative of a substituted type, on representatives. -/
theorem tySubQ_out {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) :
    tySubQ σ A = tyMk (tySubRaw σ.out A.rep) := by
  conv_lhs => rw [← Quotient.out_eq σ, ← TyQ.tyMk_rep A]
  rfl

theorem tySubQ_rep_conv {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) :
    Conv (tySubQ σ A).rep.ty (tySubRaw σ.out A.rep).ty := by
  rw [tySubQ_out σ A]
  exact TyQ.rep_conv

/-- Substitution does not change the sort of a type. -/
theorem tySubQ_rep_srt {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) :
    (tySubQ σ A).rep.srt = A.rep.srt := by
  rw [tySubQ_out σ A]
  exact TyQ.rep_srt

/-- The action of a substitution on extended contexts. -/
noncomputable def extendQ {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) :
    extOb Δ (tySubQ σ A) ⟶ extOb Γ A :=
  (convIso (C := (tySubQ σ A).rep) (D := tySubRaw σ.out A.rep) (tySubQ_rep_conv σ A)).hom ≫
    LambdaPiCat.extend σ.out A.rep.ok

theorem isPullback_extendQ {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) :
    IsPullback (extendQ σ A) (dispQ (tySubQ σ A)) (dispQ A) σ := by
  have h' := LambdaPiCwa.isPullback_of_iso (LambdaPiCat.isPullback_extend σ.out A.rep.ok)
    (convIso (tySubQ_rep_conv σ A))
  have hσ : mk σ.out = σ := Quotient.out_eq σ
  rw [hσ] at h'
  have hdisp : dispQ (tySubQ σ A)
      = (convIso (tySubQ_rep_conv σ A)).hom ≫ disp Δ (tySubRaw σ.out A.rep).ok :=
    (convIso_hom_disp _).symm
  rw [hdisp]
  exact h'

/-- **The contexts of `λΠ`, with all of its types, form a category with attributes.** -/
@[reducible] noncomputable def syntactic : Cwa Ob where
  Ty := TyQ
  tySub := tySubQ
  tySub_id := tySubQ_id
  tySub_comp := tySubQ_comp
  ext := extOb
  disp := dispQ
  extend := extendQ
  isPullback := isPullback_extendQ

/-! ### Terms -/

/-- Substitution of a type, computed on a chosen representative of the substitution. -/
theorem tySubQ_tyMk {Γ Δ : Ob} (σ : Δ ⟶ Γ) (X : TyOf Γ) :
    tySubQ σ (tyMk X) = tyMk (tySubRaw σ.out X) := by
  conv_lhs => rw [← Quotient.out_eq σ]
  rfl

/-- A morphism is convertible, at the variables of its source, to any representative of it. -/
theorem hom_out_conv {Γ Δ : Ob} {f : Δ ⟶ Γ} {g : RawHom Δ Γ} (h : f = mk g) {n : ℕ}
    (hn : n < Γ.ctx.length) : Conv (f.out.sub n) (g.sub n) :=
  Quotient.exact ((Quotient.out_eq f).trans h) n hn

/-- Transporting terms along a conversion of their type. -/
def tmConvMap {Γ : Ob} {X Y : Tm} {s : Srt} (hY : Typing Γ.ctx Y (Tm.sort s)) (h : Conv X Y) :
    TmQuot Γ X → TmQuot Γ Y :=
  Quotient.map (fun t => ⟨t.tm, t.ok.conv hY h⟩) (fun _ _ hc => hc)

/-- Convertible types have the same terms. -/
def tmConvEquiv {Γ : Ob} {X Y : Tm} {s t : Srt} (hX : Typing Γ.ctx X (Tm.sort s))
    (hY : Typing Γ.ctx Y (Tm.sort t)) (h : Conv X Y) : TmQuot Γ X ≃ TmQuot Γ Y where
  toFun := tmConvMap hY h
  invFun := tmConvMap hX h.symm
  left_inv q := by
    induction q using Quotient.ind with
    | _ t => rfl
  right_inv q := by
    induction q using Quotient.ind with
    | _ t => rfl

/-- Terms of the syntactic category with attributes are the well-typed terms of the calculus,
modulo conversion. -/
noncomputable def tmEquiv {Γ : Ob} (A : TyQ Γ) : Cwa.Tm syntactic Γ A ≃ TmQuot Γ A.rep.ty :=
  secEquiv Γ A.rep.ok

end LambdaPiFull
