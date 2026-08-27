/-
The **syntactic category** of the dependently typed calculus `λΠ`: contexts and substitutions.

This is the object-language half of the correspondence "dependent type theory ⟺ locally cartesian
closed category".  Its objects are the well-formed contexts of `Start/LambdaPiTyping.lean`, and a
morphism `Δ ⟶ Γ` is a well-typed substitution sending the variables of `Γ` to terms over `Δ`,
identified when they are convertible on the variables that actually occur in `Γ`.  Composition is
substitution, and the category laws hold on the nose thanks to the substitution calculus of
`Start/LambdaPi.lean`.

* `LambdaPiCat.Ob` — well-formed contexts;
* `LambdaPiCat.Hom` — substitutions up to conversion, and the `Category` instance;
* `LambdaPiCat.emptyIsTerminal` — the empty context is a terminal object;
* `LambdaPiCat.disp` — the display map (weakening) out of an extended context;
* `LambdaPiCat.extend` — the action of a substitution on an extended context;
* `LambdaPiCat.isPullback_extend` — **the context-extension square is a pullback**.  This is the
  universal property that a category with attributes (`Start/Cwa.lean`) demands, and it is the
  precise sense in which "a substitution into an extended context is a substitution plus a term".

Note that the well-definedness of composition is exactly where the bound-variable analysis of
`Start/LambdaPiBound.lean` is needed: conversion of substitutions is only required at the
variables `< Γ.length`, so one must know that a term typed in `Δ` mentions no variable beyond
`Δ.length`.
-/

import Start.LambdaPiBound
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

open CategoryTheory Limits

namespace LambdaPiCat

open LambdaPi

/-! ### Objects and morphisms -/

/-- An object of the syntactic category: a well-formed context. -/
structure Ob where
  /-- The underlying context. -/
  ctx : Ctx
  /-- Its well-formedness. -/
  wf : Wf ctx

/-- A raw morphism `Δ ⟶ Γ`: a substitution taking the variables of `Γ` to terms over `Δ`. -/
structure RawHom (Δ Γ : Ob) where
  /-- The underlying substitution. -/
  sub : ℕ → Tm
  /-- It is well typed. -/
  ok : SubOk sub Γ.ctx Δ.ctx

/-- Two raw morphisms are identified when they are convertible at every variable of the source
context.  (Their values beyond `Γ.length` are irrelevant.) -/
def RawHom.Rel {Δ Γ : Ob} (f g : RawHom Δ Γ) : Prop :=
  ∀ n, n < Γ.ctx.length → Conv (f.sub n) (g.sub n)

instance rawSetoid (Δ Γ : Ob) : Setoid (RawHom Δ Γ) where
  r := RawHom.Rel
  iseqv :=
    { refl := fun _ _ _ => Conv.refl _
      symm := fun h n hn => (h n hn).symm
      trans := fun h₁ h₂ n hn => (h₁ n hn).trans (h₂ n hn) }

/-- Morphisms of the syntactic category: substitutions up to conversion. -/
def Hom (Δ Γ : Ob) : Type := Quotient (rawSetoid Δ Γ)

/-- The class of a raw substitution. -/
def mk {Δ Γ : Ob} (f : RawHom Δ Γ) : Hom Δ Γ := Quotient.mk _ f

theorem mk_eq {Δ Γ : Ob} {f g : RawHom Δ Γ} (h : RawHom.Rel f g) : mk f = mk g :=
  Quotient.sound h

@[elab_as_elim] theorem Hom.ind {Δ Γ : Ob} {motive : Hom Δ Γ → Prop}
    (h : ∀ f : RawHom Δ Γ, motive (mk f)) (x : Hom Δ Γ) : motive x :=
  Quotient.ind h x

/-! ### Identity and composition -/

/-- Every variable of a context has a type. -/
theorem exists_lookup {Γ : Ctx} {n : ℕ} (hn : n < Γ.length) : ∃ A, Lookup Γ n A := by
  induction Γ generalizing n with
  | nil => simp at hn
  | cons B Γ ih =>
      cases n with
      | zero => exact ⟨shift B, Lookup.zero _ _⟩
      | succ n =>
          obtain ⟨A, hA⟩ := ih (by simpa using Nat.lt_of_succ_lt_succ hn)
          exact ⟨shift A, Lookup.succ _ hA⟩

/-- A well-typed substitution takes the variables of its source to terms with no variable beyond
the target context. -/
theorem RawHom.bnd {Δ Γ : Ob} (f : RawHom Δ Γ) {n : ℕ} (hn : n < Γ.ctx.length) :
    Bnd Δ.ctx.length (f.sub n) := by
  obtain ⟨A, hA⟩ := exists_lookup hn
  exact ((f.ok n A hA).bnd_of_wf Δ.wf).1

/-- The identity substitution. -/
def RawHom.id (Γ : Ob) : RawHom Γ Γ where
  sub := ids
  ok := by
    intro n A hA
    simpa using Typing.var hA

/-- Composition of raw substitutions. -/
def RawHom.comp {Θ Δ Γ : Ob} (g : RawHom Θ Δ) (f : RawHom Δ Γ) : RawHom Θ Γ where
  sub n := subst g.sub (f.sub n)
  ok := by
    intro n A hA
    have h := (f.ok n A hA).substs g.ok
    rwa [subst_subst] at h

theorem RawHom.comp_congr {Θ Δ Γ : Ob} {g g' : RawHom Θ Δ} {f f' : RawHom Δ Γ}
    (hg : RawHom.Rel g g') (hf : RawHom.Rel f f') :
    RawHom.Rel (RawHom.comp g f) (RawHom.comp g' f') := by
  intro n hn
  refine ((hf n hn).subst g.sub).trans ?_
  exact conv_subst_congr (f'.bnd hn) (fun m hm => hg m hm)

instance : Category Ob where
  Hom := Hom
  id Γ := mk (RawHom.id Γ)
  comp {_ _ _} g f := Quotient.map₂ (fun g' f' => RawHom.comp g' f')
    (fun _ _ hg _ _ hf => RawHom.comp_congr hg hf) g f
  id_comp {_ Γ} f := by
    refine Hom.ind (fun f => ?_) f
    exact mk_eq (fun n _ => by simp only [RawHom.comp, RawHom.id, subst_ids]; exact Conv.refl _)
  comp_id {_ _} f := by
    refine Hom.ind (fun f => ?_) f
    refine mk_eq (fun n _ => ?_)
    simp only [RawHom.comp, RawHom.id, ids_apply, subst_var]
    exact Conv.refl _
  assoc {_ _ _ _} f g h := by
    refine Hom.ind (fun f => ?_) f
    refine Hom.ind (fun g => ?_) g
    refine Hom.ind (fun h => ?_) h
    exact mk_eq (fun n _ => by simp only [RawHom.comp, subst_subst]; exact Conv.refl _)

@[simp] theorem comp_mk {Θ Δ Γ : Ob} (g : RawHom Θ Δ) (f : RawHom Δ Γ) :
    (mk g ≫ mk f : Θ ⟶ Γ) = mk (RawHom.comp g f) := rfl

@[simp] theorem id_mk (Γ : Ob) : (𝟙 Γ : Γ ⟶ Γ) = mk (RawHom.id Γ) := rfl

/-! ### The empty context is terminal -/

/-- The empty context. -/
def empty : Ob := ⟨[], Wf.nil⟩

/-- **The empty context is a terminal object**: there is exactly one substitution into it, since
it has no variables. -/
def emptyIsTerminal : IsTerminal empty :=
  IsTerminal.ofUniqueHom (fun _ => mk ⟨ids, by
      intro n A hA
      have h := hA.lt
      simp [empty] at h⟩)
    (fun _ f => by
      refine Hom.ind (fun f => ?_) f
      exact (mk_eq (fun n hn => by simp [empty] at hn)).symm)

/-! ### Context extension -/

/-- Extending an object by a type. -/
def cons (Γ : Ob) {A : Tm} {s : Srt} (hA : Typing Γ.ctx A (Tm.sort s)) : Ob :=
  ⟨A :: Γ.ctx, Wf.cons Γ.wf hA⟩

/-! ### Substitution lemmas for weakening -/

/-- Substituting into a shifted term ignores the value of the substitution at `0`. -/
theorem subst_shift' (σ : ℕ → Tm) (t : Tm) :
    subst σ (shift t) = subst (fun n => σ (n + 1)) t := by
  rw [shift, subst_rename]

/-- The substitution `fun n => var (n+1)` is weakening. -/
theorem subst_succ_var (t : Tm) : subst (fun n => Tm.var (n + 1)) t = shift t := by
  rw [shift, rename_eq_subst]

/-- The raw display map out of an extended context: weakening. -/
def dispRaw (Γ : Ob) {A : Tm} {s : Srt} (hA : Typing Γ.ctx A (Tm.sort s)) :
    RawHom (cons Γ hA) Γ where
  sub := fun n => Tm.var (n + 1)
  ok := by
    intro n B hB
    rw [subst_succ_var]
    exact Typing.var (Lookup.succ _ hB)

/-- The display map out of an extended context: weakening. -/
def disp (Γ : Ob) {A : Tm} {s : Srt} (hA : Typing Γ.ctx A (Tm.sort s)) :
    (cons Γ hA) ⟶ Γ := mk (dispRaw Γ hA)

/-- Substituting a type along a substitution gives a type. -/
theorem tySub_typing {Γ Δ : Ob} (f : RawHom Δ Γ) {A : Tm} {s : Srt}
    (hA : Typing Γ.ctx A (Tm.sort s)) : Typing Δ.ctx (subst f.sub A) (Tm.sort s) :=
  hA.substs f.ok

/-- The raw action of a substitution on an extended context. -/
def extendRaw {Γ Δ : Ob} (f : RawHom Δ Γ) {A : Tm} {s : Srt}
    (hA : Typing Γ.ctx A (Tm.sort s)) : RawHom (cons Δ (tySub_typing f hA)) (cons Γ hA) where
  sub := up f.sub
  ok := SubOk.up f.ok A

/-- The action of a substitution on an extended context. -/
def extend {Γ Δ : Ob} (f : RawHom Δ Γ) {A : Tm} {s : Srt}
    (hA : Typing Γ.ctx A (Tm.sort s)) : cons Δ (tySub_typing f hA) ⟶ cons Γ hA :=
  mk (extendRaw f hA)

/-! ### The context extension square is a pullback -/

/-- The lift produced by the universal property, on representatives: a substitution into an
extended context is a substitution together with a term. -/
def liftRaw {Γ Δ T : Ob} (f : RawHom Δ Γ) {A : Tm} {s : Srt}
    (hA : Typing Γ.ctx A (Tm.sort s)) (θ : RawHom T (cons Γ hA)) (υ : RawHom T Δ)
    (hc : ∀ n, n < Γ.ctx.length → Conv (θ.sub (n + 1)) (subst υ.sub (f.sub n))) :
    RawHom T (cons Δ (tySub_typing f hA)) where
  sub := scons (θ.sub 0) υ.sub
  ok := by
    intro n B hB
    cases hB with
    | zero _ _ =>
        have hsub : subst (scons (θ.sub 0) υ.sub) (shift (subst f.sub A))
            = subst (fun m => subst υ.sub (f.sub m)) A := by
          rw [subst_shift', subst_subst]
          exact subst_congr (fun _ => rfl) A
        rw [hsub]
        have h0 := θ.ok 0 (shift A) (Lookup.zero _ _)
        rw [subst_shift'] at h0
        refine h0.conv (hA.substs (RawHom.comp υ f).ok) ?_
        exact conv_subst_congr (hA.bnd_of_wf Γ.wf).1 hc
    | succ _ hB' =>
        rw [subst_shift']
        have := υ.ok _ _ hB'
        rwa [subst_congr (fun _ => rfl)]

/-- **The context-extension square is a pullback.**  This is the universal property required of a
category with attributes: to give a substitution into `A :: Γ` is to give a substitution into `Γ`
together with a term of the substituted `A`. -/
theorem isPullback_extend {Γ Δ : Ob} (f : RawHom Δ Γ) {A : Tm} {s : Srt}
    (hA : Typing Γ.ctx A (Tm.sort s)) :
    IsPullback (extend f hA) (disp Δ (tySub_typing f hA)) (disp Γ hA) (mk f) := by
  have eq : extend f hA ≫ disp Γ hA = disp Δ (tySub_typing f hA) ≫ mk f := by
    refine mk_eq ?_
    intro n _
    change Conv (subst (up f.sub) (Tm.var (n + 1))) (subst (fun m => Tm.var (m + 1)) (f.sub n))
    rw [subst_succ_var]
    exact Conv.refl _
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk eq ?_ ?_ ?_ ?_)
  · -- the lift
    intro c
    refine mk (liftRaw f hA c.fst.out c.snd.out ?_)
    intro n hn
    have hcond := c.condition
    rw [← Quotient.out_eq c.fst, ← Quotient.out_eq c.snd] at hcond
    have := Quotient.exact hcond n (by simpa using Nat.succ_lt_succ hn)
    change Conv (c.fst.out.sub (n + 1)) (subst c.snd.out.sub (f.sub n))
    have h1 : (RawHom.comp c.fst.out (dispRaw Γ hA)).sub n = c.fst.out.sub (n + 1) := rfl
    have h2 : (RawHom.comp c.snd.out f).sub n = subst c.snd.out.sub (f.sub n) := rfl
    rwa [h1, h2] at this
  · -- lift ≫ extend = c.fst
    intro c
    conv_rhs => rw [← Quotient.out_eq c.fst]
    refine mk_eq ?_
    intro n hn
    cases n with
    | zero => exact Conv.refl _
    | succ n =>
        have hn' : n < Γ.ctx.length := by simpa using Nat.lt_of_succ_lt_succ hn
        have hcond := c.condition
        rw [← Quotient.out_eq c.fst, ← Quotient.out_eq c.snd] at hcond
        have hrel := Quotient.exact hcond n hn'
        change Conv (subst (scons (c.fst.out.sub 0) c.snd.out.sub) (up f.sub (n + 1)))
          (c.fst.out.sub (n + 1))
        rw [up_succ, ← shift, subst_shift']
        refine Conv.symm ?_
        have h1 : (RawHom.comp c.fst.out (dispRaw Γ hA)).sub n = c.fst.out.sub (n + 1) := rfl
        have h2 : (RawHom.comp c.snd.out f).sub n = subst c.snd.out.sub (f.sub n) := rfl
        rw [h1, h2] at hrel
        rw [subst_congr (fun m => scons_succ (c.fst.out.sub 0) c.snd.out.sub m)]
        exact hrel
  · -- lift ≫ disp = c.snd
    intro c
    conv_rhs => rw [← Quotient.out_eq c.snd]
    exact mk_eq (fun _ _ => Conv.refl _)
  · -- uniqueness
    intro c m h₁ h₂
    refine Hom.ind (motive := fun m => m ≫ extend f hA = c.fst →
      m ≫ disp Δ (tySub_typing f hA) = c.snd → m = _) ?_ m h₁ h₂
    intro μ hμ₁ hμ₂
    refine mk_eq ?_
    intro n hn
    cases n with
    | zero =>
        rw [← Quotient.out_eq c.fst] at hμ₁
        exact Quotient.exact hμ₁ 0 (Nat.succ_pos _)
    | succ n =>
        have hn' : n < Δ.ctx.length := by simpa using Nat.lt_of_succ_lt_succ hn
        rw [← Quotient.out_eq c.snd] at hμ₂
        exact Quotient.exact hμ₂ n hn'

/-! ### Terms are sections of display maps

The categorical notion of a *term* of `A` in context `Γ` is a section of the display map of `A`.
We check that this reproduces the syntactic notion: sections correspond exactly to well-typed
`λΠ` terms of type `A`, taken up to conversion. -/

/-- A **term** of `A` in `Γ` in the categorical sense: a section of the display map. -/
def Sec (Γ : Ob) {A : Tm} {srt : Srt} (hA : Typing Γ.ctx A (Tm.sort srt)) : Type :=
  {u : Γ ⟶ cons Γ hA // u ≫ disp Γ hA = 𝟙 Γ}

/-- A well-typed term of `A` in `Γ`, in the syntactic sense. -/
structure TmOf (Γ : Ob) (A : Tm) where
  /-- The underlying raw term. -/
  tm : Tm
  /-- Its typing derivation. -/
  ok : Typing Γ.ctx tm A

instance tmSetoid (Γ : Ob) (A : Tm) : Setoid (TmOf Γ A) where
  r t u := Conv t.tm u.tm
  iseqv := ⟨fun _ => Conv.refl _, Conv.symm, Conv.trans⟩

/-- Well-typed terms of `A` in `Γ`, up to conversion. -/
abbrev TmQuot (Γ : Ob) (A : Tm) : Type := Quotient (tmSetoid Γ A)

/-- The class of a well-typed term. -/
def tmMk {Γ : Ob} {A : Tm} (t : TmOf Γ A) : TmQuot Γ A := Quotient.mk _ t

/-- The condition, on a representative, that a substitution out of an extended context is a
section of the display map. -/
def IsSecRaw {Γ : Ob} {A : Tm} {srt : Srt} (hA : Typing Γ.ctx A (Tm.sort srt))
    (ρ : RawHom Γ (cons Γ hA)) : Prop :=
  ∀ n, n < Γ.ctx.length → Conv (ρ.sub (n + 1)) (Tm.var n)

/-- The value at `0` of a section is a term of the displayed type. -/
theorem secRaw_typing {Γ : Ob} {A : Tm} {srt : Srt} (hA : Typing Γ.ctx A (Tm.sort srt))
    {ρ : RawHom Γ (cons Γ hA)} (h : IsSecRaw hA ρ) : Typing Γ.ctx (ρ.sub 0) A := by
  have h0 := ρ.ok 0 (shift A) (Lookup.zero _ _)
  rw [subst_shift'] at h0
  refine h0.conv hA ?_
  have hc : Conv (subst (fun n => ρ.sub (n + 1)) A) (subst ids A) :=
    conv_subst_congr (hA.bnd_of_wf Γ.wf).1 h
  rwa [subst_ids] at hc

/-- Reading off the representative of a section. -/
theorem sec_isSecRaw {Γ : Ob} {A : Tm} {srt : Srt} (hA : Typing Γ.ctx A (Tm.sort srt))
    (u : Sec Γ hA) : IsSecRaw hA u.1.out := by
  intro n hn
  have hcond := u.2
  rw [← Quotient.out_eq u.1] at hcond
  exact Quotient.exact hcond n hn

/-- A well-typed term, read as a substitution out of an extended context. -/
def tmRaw {Γ : Ob} {A : Tm} {srt : Srt} (hA : Typing Γ.ctx A (Tm.sort srt)) (t : TmOf Γ A) :
    RawHom Γ (cons Γ hA) where
  sub := scons t.tm ids
  ok := by
    intro n B hB
    cases hB with
    | zero _ _ =>
        rw [subst_shift', subst_congr (fun m => scons_succ t.tm ids m), subst_ids]
        exact t.ok
    | succ _ hB' =>
        rw [subst_shift', subst_congr (fun m => scons_succ t.tm ids m), subst_ids]
        exact Typing.var hB'

/-- A well-typed term, read as a section of the display map. -/
def tmSec {Γ : Ob} {A : Tm} {srt : Srt} (hA : Typing Γ.ctx A (Tm.sort srt)) (t : TmOf Γ A) :
    Sec Γ hA :=
  ⟨mk (tmRaw hA t), mk_eq (fun _ _ => Conv.refl _)⟩

/-- **Sections of a display map are exactly the well-typed terms of the displayed type, taken up
to conversion.**  This is the syntactic counterpart of `Cwa.Tm`. -/
noncomputable def secEquiv (Γ : Ob) {A : Tm} {srt : Srt} (hA : Typing Γ.ctx A (Tm.sort srt)) :
    Sec Γ hA ≃ TmQuot Γ A where
  toFun u := tmMk ⟨u.1.out.sub 0, secRaw_typing hA (sec_isSecRaw hA u)⟩
  invFun := Quotient.lift (fun t => tmSec hA t)
    (by
      intro t t' h
      refine Subtype.ext (mk_eq ?_)
      intro n _
      cases n with
      | zero => exact h
      | succ n => exact Conv.refl _)
  left_inv u := by
    refine Subtype.ext ?_
    conv_rhs => rw [← Quotient.out_eq u.1]
    refine mk_eq ?_
    intro n hn
    cases n with
    | zero => exact Conv.refl _
    | succ n =>
        have hn' : n < Γ.ctx.length := by simpa using Nat.lt_of_succ_lt_succ hn
        exact (sec_isSecRaw hA u n hn').symm
  right_inv q := by
    induction q using Quotient.ind with
    | _ t =>
      refine Quotient.sound ?_
      exact Quotient.exact (Quotient.out_eq (mk (tmRaw hA t))) 0 (Nat.succ_pos _)

/-! ### The dependent product on the syntactic side

The Π-type former of `λΠ` induces, on terms modulo conversion, an abstraction map from the
extended context to the base context and an application map back, satisfying the β-law.  (The
η-law fails: `λΠ` as formalized here has β-reduction only, which is why the syntactic side gives
a *weak* Π-structure rather than the bijection demanded by `Cwa.PiStruct`.) -/

/-- Weakening a type past one variable and then instantiating that variable with `0` is the
identity. -/
theorem inst_upr_shift (B : Tm) : (rename (upr Nat.succ) B)[Tm.var 0] = B := by
  rw [inst, subst_rename]
  have h : ∀ n, scons (Tm.var 0) ids (upr Nat.succ n) = ids n := by
    intro n; cases n <;> rfl
  rw [subst_congr h, subst_ids]

/-- **Abstraction** on terms modulo conversion. -/
def lamTm {Γ : Ob} {A B : Tm} {srt srt' : Srt} (hA : Typing Γ.ctx A (Tm.sort srt))
    (hpi : Typing Γ.ctx (Tm.pi A B) (Tm.sort srt')) :
    TmQuot (cons Γ hA) B → TmQuot Γ (Tm.pi A B) :=
  Quotient.map (fun b => ⟨Tm.lam A b.tm, Typing.lam hpi b.ok⟩)
    (fun _ _ h => Conv.lamR A h)

/-- **Application** on terms modulo conversion, in the generic-argument form: a term of
`Π A. B` over `Γ` is applied to the variable `0` over `A :: Γ`. -/
def appTm {Γ : Ob} {A B : Tm} {srt : Srt} (hA : Typing Γ.ctx A (Tm.sort srt)) :
    TmQuot Γ (Tm.pi A B) → TmQuot (cons Γ hA) B :=
  Quotient.map
    (fun f => ⟨Tm.app (shift f.tm) (Tm.var 0), by
      have hf : Typing (A :: Γ.ctx) (shift f.tm) (Tm.pi (shift A) (rename (upr Nat.succ) B)) :=
        f.ok.weaken A
      have h0 : Typing (A :: Γ.ctx) (Tm.var 0) (shift A) := Typing.var (Lookup.zero _ _)
      have := Typing.app hf h0
      rwa [inst_upr_shift] at this⟩)
    (fun _ _ h => Conv.appL _ (h.rename Nat.succ))

/-- **β**: applying an abstraction to the generic argument gives the body back. -/
theorem appTm_lamTm {Γ : Ob} {A B : Tm} {srt srt' : Srt} (hA : Typing Γ.ctx A (Tm.sort srt))
    (hpi : Typing Γ.ctx (Tm.pi A B) (Tm.sort srt')) (b : TmQuot (cons Γ hA) B) :
    appTm hA (lamTm hA hpi b) = b := by
  induction b using Quotient.ind with
  | _ b =>
    refine Quotient.sound ?_
    have hstep : Step (Tm.app (Tm.lam (shift A) (rename (upr Nat.succ) b.tm)) (Tm.var 0))
        ((rename (upr Nat.succ) b.tm)[Tm.var 0]) := Step.beta _ _ _
    rw [inst_upr_shift] at hstep
    exact Conv.single hstep

end LambdaPiCat
