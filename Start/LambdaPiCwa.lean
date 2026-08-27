/-
The **syntactic category with attributes** of the dependently typed calculus `λΠ`.

`Start/LambdaPiCat.lean` built the syntactic category: objects are well-formed contexts and
morphisms are substitutions up to conversion, the empty context is terminal and the
context-extension squares are pullbacks.  This file assembles those pieces into an instance of the
interface of `Start/Cwa.lean`:

* `LambdaPiCwa.TyQ Γ` — the *small types* in a context, i.e. terms of sort `∗`, taken up to
  conversion; substitution acts on them (`LambdaPiCwa.tySubQ`);
* `LambdaPiCwa.syntactic : Cwa LambdaPiCat.Ob` — **the syntactic category of `λΠ` is a category
  with attributes**: context extension is `A :: Γ` for a chosen representative of the conversion
  class of `A`, the display map is weakening, and the extension squares are pullbacks;
* `LambdaPiCwa.weakPi : Cwa.WeakPiStruct syntactic` — **the dependent product of `λΠ` is a weak
  Π-structure** on it: the type former is stable under substitution (Beck–Chevalley) and the
  abstraction/application pair satisfies the β-law.

Two points deserve comment.

*Why small types.*  In `λΠ` a product may only be formed over a term of `∗` (the rules are
`(∗,∗)` and `(∗,□)`), so `Ty Γ` is taken to be the terms of sort `∗`; this is closed under
substitution and under context extension, and it is exactly the fragment on which the dependent
product is defined.

*Why only a weak Π-structure.*  `Cwa.PiStruct` demands that abstraction and application be
mutually inverse, i.e. the η-law, which the β-only calculus of `Start/LambdaPi.lean` does not
provide; `Cwa.WeakPiStruct` is the β-only interface, and that is what the syntax satisfies.
-/

import Start.LambdaPiCat
import Start.Cwa

set_option relaxedAutoImplicit false
set_option autoImplicit false

open CategoryTheory Limits

namespace LambdaPiCwa

open LambdaPi LambdaPiCat

/-! ### Small types in a context -/

/-- A **small type** in a context: a term of sort `∗`. -/
structure TyOf (Γ : Ob) where
  /-- The underlying term. -/
  ty : Tm
  /-- Its typing derivation. -/
  ok : Typing Γ.ctx ty (Tm.sort Srt.star)

instance tySetoid (Γ : Ob) : Setoid (TyOf Γ) where
  r A B := Conv A.ty B.ty
  iseqv := ⟨fun _ => Conv.refl _, Conv.symm, Conv.trans⟩

/-- Small types in a context, up to conversion. -/
def TyQ (Γ : Ob) : Type := Quotient (tySetoid Γ)

/-- The conversion class of a small type. -/
def tyMk {Γ : Ob} (A : TyOf Γ) : TyQ Γ := Quotient.mk _ A

theorem tyMk_eq {Γ : Ob} {A B : TyOf Γ} (h : Conv A.ty B.ty) : tyMk A = tyMk B :=
  Quotient.sound h

@[elab_as_elim] theorem TyQ.ind {Γ : Ob} {motive : TyQ Γ → Prop}
    (h : ∀ A : TyOf Γ, motive (tyMk A)) (x : TyQ Γ) : motive x := Quotient.ind h x

/-- A chosen representative of a conversion class of types. -/
noncomputable def TyQ.rep {Γ : Ob} (A : TyQ Γ) : TyOf Γ := Quotient.out A

@[simp] theorem TyQ.tyMk_rep {Γ : Ob} (A : TyQ Γ) : tyMk A.rep = A := Quotient.out_eq A

theorem TyQ.rep_conv {Γ : Ob} {A : TyOf Γ} : Conv (tyMk A).rep.ty A.ty :=
  Quotient.exact (TyQ.tyMk_rep (tyMk A))

/-! ### Substitution on types -/

/-- Substitution acting on a representative. -/
def tySubRaw {Γ Δ : Ob} (f : RawHom Δ Γ) (A : TyOf Γ) : TyOf Δ :=
  ⟨subst f.sub A.ty, A.ok.substs f.ok⟩

theorem tySubRaw_congr {Γ Δ : Ob} {f g : RawHom Δ Γ} {A B : TyOf Γ}
    (hf : RawHom.Rel f g) (hA : Conv A.ty B.ty) :
    Conv (tySubRaw f A).ty (tySubRaw g B).ty := by
  refine (hA.subst f.sub).trans ?_
  exact conv_subst_congr (B.ok.bnd_of_wf Γ.wf).1 (fun n hn => hf n hn)

/-- Substitution acting on types. -/
def tySubQ {Γ Δ : Ob} (f : Δ ⟶ Γ) (A : TyQ Γ) : TyQ Δ :=
  Quotient.map₂ tySubRaw (fun _ _ hf _ _ hA => tySubRaw_congr hf hA) f A

@[simp] theorem tySubQ_mk {Γ Δ : Ob} (f : RawHom Δ Γ) (A : TyOf Γ) :
    tySubQ (mk f) (tyMk A) = tyMk (tySubRaw f A) := rfl

theorem tySubQ_id {Γ : Ob} (A : TyQ Γ) : tySubQ (𝟙 Γ) A = A := by
  refine TyQ.ind (fun A => ?_) A
  refine tyMk_eq ?_
  simp only [tySubRaw, RawHom.id, subst_ids]
  exact Conv.refl _

theorem tySubQ_comp {Γ Δ Θ : Ob} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (A : TyQ Γ) :
    tySubQ (τ ≫ σ) A = tySubQ τ (tySubQ σ A) := by
  refine Hom.ind (motive := fun σ => tySubQ (τ ≫ σ) A = tySubQ τ (tySubQ σ A)) ?_ σ
  intro σ
  refine Hom.ind (motive := fun τ => tySubQ (τ ≫ mk σ) A = tySubQ τ (tySubQ (mk σ) A)) ?_ τ
  intro τ
  refine TyQ.ind (fun A => ?_) A
  refine tyMk_eq ?_
  simp only [tySubRaw, RawHom.comp, subst_subst]
  exact Conv.refl _

/-! ### Context extension -/

/-- Context extension: the chosen representative of `A` is put in front of `Γ`. -/
noncomputable def extOb (Γ : Ob) (A : TyQ Γ) : Ob := cons Γ A.rep.ok

/-- The display map out of an extended context. -/
noncomputable def dispQ {Γ : Ob} (A : TyQ Γ) : extOb Γ A ⟶ Γ := disp Γ A.rep.ok

/-- Weakening a well-typed term of a sort past a variable. -/
theorem typing_shift_sort {Γ : Ob} (C : Tm) {D : Tm}
    (hD : Typing Γ.ctx D (Tm.sort Srt.star)) :
    Typing (C :: Γ.ctx) (shift D) (Tm.sort Srt.star) := by
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

/-- Transporting a pullback square along an isomorphism of its top-left corner. -/
theorem isPullback_of_iso {C : Type} [Category C] {P P' X Y Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    (e : P' ≅ P) : IsPullback (e.hom ≫ fst) (e.hom ≫ snd) f g := by
  have hiso : IsPullback e.hom (e.hom ≫ snd) snd (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := hiso.paste_horiz h
  simpa using this

/-- The chosen representative of a substituted type, on representatives. -/
theorem tySubQ_out {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) :
    tySubQ σ A = tyMk (tySubRaw σ.out A.rep) := by
  conv_lhs => rw [← Quotient.out_eq σ, ← TyQ.tyMk_rep A]
  rfl

theorem tySubQ_rep_conv {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) :
    Conv (tySubQ σ A).rep.ty (tySubRaw σ.out A.rep).ty := by
  rw [tySubQ_out σ A]
  exact TyQ.rep_conv

/-- The action of a substitution on extended contexts. -/
noncomputable def extendQ {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) :
    extOb Δ (tySubQ σ A) ⟶ extOb Γ A :=
  (convIso (C := (tySubQ σ A).rep) (D := tySubRaw σ.out A.rep) (tySubQ_rep_conv σ A)).hom ≫
    LambdaPiCat.extend σ.out A.rep.ok

theorem isPullback_extendQ {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) :
    IsPullback (extendQ σ A) (dispQ (tySubQ σ A)) (dispQ A) σ := by
  have h' := isPullback_of_iso (LambdaPiCat.isPullback_extend σ.out A.rep.ok)
    (convIso (tySubQ_rep_conv σ A))
  have hσ : mk σ.out = σ := Quotient.out_eq σ
  rw [hσ] at h'
  have hdisp : dispQ (tySubQ σ A)
      = (convIso (tySubQ_rep_conv σ A)).hom ≫ disp Δ (tySubRaw σ.out A.rep).ok :=
    (convIso_hom_disp _).symm
  rw [hdisp]
  exact h'

/-- **The syntactic category of `λΠ` is a category with attributes.** -/
@[reducible] noncomputable def syntactic : Cwa Ob where
  Ty := TyQ
  tySub := tySubQ
  tySub_id := tySubQ_id
  tySub_comp := tySubQ_comp
  ext := extOb
  disp := dispQ
  extend := extendQ
  isPullback := isPullback_extendQ

/-! ### The dependent product -/

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

/-- The dependent product of the syntactic category with attributes. -/
noncomputable def PiQ {Γ : Ob} (A : TyQ Γ) (B : TyQ (extOb Γ A)) : TyQ Γ :=
  tyMk ⟨Tm.pi A.rep.ty B.rep.ty, Typing.pi rfl A.rep.ok B.rep.ok⟩

theorem piQ_rep_conv {Γ : Ob} (A : TyQ Γ) (B : TyQ (extOb Γ A)) :
    Conv (PiQ A B).rep.ty (Tm.pi A.rep.ty B.rep.ty) := TyQ.rep_conv

/-- **Beck–Chevalley**: the dependent product is stable under substitution. -/
theorem piQ_sub {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) (B : TyQ (extOb Γ A)) :
    tySubQ σ (PiQ A B) = PiQ (tySubQ σ A) (tySubQ (extendQ σ A) B) := by
  rw [PiQ, tySubQ_tyMk]
  refine tyMk_eq ?_
  refine Conv.pi ?_ ?_
  · exact (tySubQ_rep_conv σ A).symm
  · -- the codomain: substituting along `extendQ σ A` is substituting along `up σ`
    have hrel : Conv (subst (up σ.out.sub) B.rep.ty)
        (subst (extendQ σ A).out.sub B.rep.ty) := by
      refine conv_subst_congr (B.rep.ok.bnd_of_wf (extOb Γ A).wf).1 ?_
      intro n hn
      refine Conv.symm ?_
      have h : extendQ σ A
          = mk (RawHom.comp (convHomRaw (tySubQ_rep_conv σ A)) (extendRaw σ.out A.rep.ok)) := rfl
      have := hom_out_conv (f := extendQ σ A) h (n := n) hn
      simpa only [RawHom.comp, convHomRaw, extendRaw, subst_ids] using this
    exact hrel.trans (tySubQ_rep_conv (extendQ σ A) B).symm

/-- Abstraction. -/
noncomputable def lamQ {Γ : Ob} {A : TyQ Γ} {B : TyQ (extOb Γ A)}
    (b : Cwa.Tm syntactic (extOb Γ A) B) : Cwa.Tm syntactic Γ (PiQ A B) :=
  (tmEquiv (PiQ A B)).symm
    (tmConvEquiv (Typing.pi rfl A.rep.ok B.rep.ok) (PiQ A B).rep.ok (piQ_rep_conv A B).symm
      (lamTm A.rep.ok (Typing.pi rfl A.rep.ok B.rep.ok) (tmEquiv B b)))

/-- Application, in generic-argument form. -/
noncomputable def appQ {Γ : Ob} {A : TyQ Γ} {B : TyQ (extOb Γ A)}
    (f : Cwa.Tm syntactic Γ (PiQ A B)) : Cwa.Tm syntactic (extOb Γ A) B :=
  (tmEquiv B).symm
    (appTm A.rep.ok
      ((tmConvEquiv (Typing.pi rfl A.rep.ok B.rep.ok) (PiQ A B).rep.ok
          (piQ_rep_conv A B).symm).symm (tmEquiv (PiQ A B) f)))

/-- **β**: applying an abstraction to the generic argument gives the body back. -/
theorem appQ_lamQ {Γ : Ob} {A : TyQ Γ} {B : TyQ (extOb Γ A)}
    (b : Cwa.Tm syntactic (extOb Γ A) B) : appQ (lamQ b) = b := by
  have h := appTm_lamTm A.rep.ok (Typing.pi rfl A.rep.ok B.rep.ok) (tmEquiv B b)
  simp only [appQ, lamQ, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  exact (congrArg (tmEquiv B).symm h).trans ((tmEquiv B).symm_apply_apply b)

/-- **The dependent product of `λΠ` is a weak Π-structure on the syntactic category with
attributes.**  Only the β-law is available: the calculus has no η-rule, so abstraction and
application are not mutually inverse. -/
noncomputable def weakPi : Cwa.WeakPiStruct syntactic where
  Pi := PiQ
  Pi_sub := piQ_sub
  lam := lamQ
  app := appQ
  app_lam := appQ_lamQ

/-! ### The η-law really fails

The weak Π-structure above cannot be improved to a `Cwa.PiStruct`: abstraction and application are
not mutually inverse, because `λΠ` as formalized has β-reduction only.  The witness is the usual
one: in a context holding a variable `f` of a product type, `λ x. f x` is not β-convertible to
`f`. -/

/-- Nothing reduces out of a variable. -/
theorem red_var_inv {n : ℕ} {t : Tm} (h : Red (Tm.var n) t) : t = Tm.var n := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [ih] at hs; cases hs

/-- A reduct of an abstraction is an abstraction. -/
theorem red_lam_inv {A b t : Tm} (h : Red (Tm.lam A b) t) : ∃ A' b', t = Tm.lam A' b' := by
  induction h with
  | refl => exact ⟨A, b, rfl⟩
  | tail _ hs ih =>
      obtain ⟨A', b', rfl⟩ := ih
      cases hs with
      | lamL _ _ => exact ⟨_, _, rfl⟩
      | lamR _ _ => exact ⟨_, _, rfl⟩

/-- An abstraction is never convertible to a variable. -/
theorem not_conv_lam_var {A b : Tm} {n : ℕ} : ¬ Conv (Tm.lam A b) (Tm.var n) := by
  intro h
  obtain ⟨v, hv₁, hv₂⟩ := h.church_rosser
  obtain ⟨A', b', rfl⟩ := red_lam_inv hv₁
  exact absurd (red_var_inv hv₂) (by simp)

/-- The context `∗, f : Π x : α. α` used as the witness that η fails. -/
def etaCtx : Ctx := [Tm.pi (Tm.var 0) (Tm.var 1), Tm.sort Srt.star]

theorem lookup_star_zero : Lookup [Tm.sort Srt.star] 0 (Tm.sort Srt.star) := Lookup.zero _ _

theorem etaCtx_wf : Wf etaCtx :=
  Wf.cons (s := Srt.star) (Wf.cons Wf.nil (Typing.ax _))
    (Typing.pi rfl (Typing.var lookup_star_zero) (Typing.var (Lookup.succ _ lookup_star_zero)))

/-- The object of the syntactic category used as the witness that η fails. -/
def etaOb : Ob := ⟨etaCtx, etaCtx_wf⟩

theorem etaOb_var_one : Typing etaOb.ctx (Tm.var 1) (Tm.sort Srt.star) := by
  change Typing etaCtx (Tm.var 1) (Tm.sort Srt.star)
  exact Typing.var (Lookup.succ _ lookup_star_zero)

/-- The domain type of the witness: the variable `α` of the context. -/
def etaA : TyQ etaOb := tyMk ⟨Tm.var 1, etaOb_var_one⟩

theorem etaA_rep_conv : Conv etaA.rep.ty (Tm.var 1) := TyQ.rep_conv

theorem etaOb_var_two : Typing (extOb etaOb etaA).ctx (Tm.var 2) (Tm.sort Srt.star) := by
  change Typing (etaA.rep.ty :: etaCtx) (Tm.var 2) (Tm.sort Srt.star)
  exact Typing.var (Lookup.succ _ (Lookup.succ _ lookup_star_zero))

/-- The codomain type of the witness: the same variable, weakened. -/
noncomputable def etaB : TyQ (extOb etaOb etaA) := tyMk ⟨Tm.var 2, etaOb_var_two⟩

theorem etaB_rep_conv : Conv etaB.rep.ty (Tm.var 2) := TyQ.rep_conv

theorem conv_piQ_etaA_etaB : Conv (Tm.pi (Tm.var 1) (Tm.var 2)) (PiQ etaA etaB).rep.ty :=
  ((piQ_rep_conv etaA etaB).trans (Conv.pi etaA_rep_conv etaB_rep_conv)).symm

theorem typing_etaF : Typing etaOb.ctx (Tm.var 0) (PiQ etaA etaB).rep.ty := by
  have h0 : Typing etaOb.ctx (Tm.var 0) (Tm.pi (Tm.var 1) (Tm.var 2)) := by
    change Typing etaCtx (Tm.var 0) (Tm.pi (Tm.var 1) (Tm.var 2))
    exact Typing.var (Lookup.zero _ _)
  exact h0.conv (PiQ etaA etaB).rep.ok conv_piQ_etaA_etaB

/-- The witness: a variable of product type in the syntactic category with attributes. -/
noncomputable def etaF : Cwa.Tm syntactic etaOb (PiQ etaA etaB) :=
  (tmEquiv (PiQ etaA etaB)).symm (tmMk ⟨Tm.var 0, typing_etaF⟩)

/-- **η fails**: abstracting an application does not give the function back. -/
theorem lamQ_appQ_ne : lamQ (appQ etaF) ≠ etaF := by
  intro hEq
  have h := congrArg (tmEquiv (PiQ etaA etaB)) hEq
  rw [lamQ, appQ, etaF] at h
  simp only [Equiv.apply_symm_apply] at h
  exact not_conv_lam_var (Quotient.exact h)

/-- **The weak Π-structure of `λΠ` does not extend to a `Cwa.PiStruct`**: no Π-structure on the
syntactic category with attributes has the abstraction and application of the calculus, since
those do not satisfy η. -/
theorem not_piStruct_weakPi (P : Cwa.PiStruct syntactic) : P.toWeakPiStruct ≠ weakPi := by
  intro h
  obtain ⟨W, hEta⟩ := P
  cases h
  exact lamQ_appQ_ne (hEta etaF)

end LambdaPiCwa
