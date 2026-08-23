/-
The simply typed lambda calculus with unit and product types, intrinsically typed, together with
its βη-conversion.

This is the syntactic half of the Curry–Howard–**Lambek** correspondence, carried out in
`Start/StlcCcc.lean`: types are the objects of a cartesian closed category, terms are its
morphisms.  For that construction the calculus must have the type formers that the categorical
structure needs — a unit type (terminal object), products, and function types (exponentials) —
so this file introduces a self-contained typed syntax rather than reusing the Curry-style
untyped syntax of `Start/Syntax.lean`.

* `Stlc.Ty`, `Stlc.Var`, `Stlc.Tm` — types, de Bruijn variables and intrinsically typed terms:
  `Tm Γ A` is the type of *well-typed* terms, so no separate typing judgement is needed;
* `Stlc.Ren`, `Stlc.Sub`, `Stlc.ren`, `Stlc.sub` — renamings and simultaneous substitutions with
  the four composition laws (`Stlc.ren_ren`, `Stlc.sub_ren`, `Stlc.ren_sub`, `Stlc.sub_sub`) and
  the identity laws;
* `Stlc.Conv` — βη-conversion: the least congruence containing β and η for functions, the two
  projection rules and the surjective-pairing rule for products, and the terminality rule for the
  unit type;
* `Stlc.Conv.sub`, `Stlc.Conv.subCongr` — conversion is compatible with substitution in the term
  and in the substitution, which is what makes the quotient by conversion a category.
-/

import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Stlc

------------------------------------------------------------------------
-- Syntax
------------------------------------------------------------------------

/-- Simple types with a unit type, binary products and function types. -/
inductive Ty where
  | base : Ty
  | unit : Ty
  | prod : Ty → Ty → Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq

/-- Contexts are lists of types, the type of the variable `0` first. -/
abbrev Ctx := List Ty

/-- De Bruijn variables, intrinsically typed. -/
inductive Var : Ctx → Ty → Type
  | zero {Γ : Ctx} {A : Ty} : Var (A :: Γ) A
  | succ {Γ : Ctx} {A B : Ty} : Var Γ A → Var (B :: Γ) A

/-- Intrinsically typed terms. -/
inductive Tm : Ctx → Ty → Type
  | var {Γ : Ctx} {A : Ty} : Var Γ A → Tm Γ A
  | app {Γ : Ctx} {A B : Ty} : Tm Γ (Ty.arrow A B) → Tm Γ A → Tm Γ B
  | lam {Γ : Ctx} {A B : Ty} : Tm (A :: Γ) B → Tm Γ (Ty.arrow A B)
  | star {Γ : Ctx} : Tm Γ Ty.unit
  | pair {Γ : Ctx} {A B : Ty} : Tm Γ A → Tm Γ B → Tm Γ (Ty.prod A B)
  | fst {Γ : Ctx} {A B : Ty} : Tm Γ (Ty.prod A B) → Tm Γ A
  | snd {Γ : Ctx} {A B : Ty} : Tm Γ (Ty.prod A B) → Tm Γ B

------------------------------------------------------------------------
-- Renamings
------------------------------------------------------------------------

/-- A renaming maps the variables of one context to variables of another. -/
def Ren (Γ Δ : Ctx) : Type := ∀ A : Ty, Var Γ A → Var Δ A

/-- The identity renaming. -/
def Ren.id (Γ : Ctx) : Ren Γ Γ := fun _ v => v

/-- Composition of renamings. -/
def Ren.comp {Γ Δ Θ : Ctx} (r' : Ren Δ Θ) (r : Ren Γ Δ) : Ren Γ Θ := fun A v => r' A (r A v)

/-- Weakening by one variable. -/
def Ren.wk {Γ : Ctx} (B : Ty) : Ren Γ (B :: Γ) := fun _ v => v.succ

/-- A renaming pushed under a binder. -/
def Ren.lift {Γ Δ : Ctx} (r : Ren Γ Δ) (B : Ty) : Ren (B :: Γ) (B :: Δ) := fun _ v =>
  match v with
  | Var.zero => Var.zero
  | Var.succ v => (r _ v).succ

/-- Renaming of terms. -/
def ren : ∀ {Γ Δ : Ctx}, Ren Γ Δ → ∀ {A : Ty}, Tm Γ A → Tm Δ A
  | _, _, r, _, Tm.var v => Tm.var (r _ v)
  | _, _, r, _, Tm.app f a => Tm.app (ren r f) (ren r a)
  | _, _, r, _, Tm.lam t => Tm.lam (ren (r.lift _) t)
  | _, _, _, _, Tm.star => Tm.star
  | _, _, r, _, Tm.pair a b => Tm.pair (ren r a) (ren r b)
  | _, _, r, _, Tm.fst t => Tm.fst (ren r t)
  | _, _, r, _, Tm.snd t => Tm.snd (ren r t)

theorem Ren.lift_id (Γ : Ctx) (B : Ty) : (Ren.id Γ).lift B = Ren.id (B :: Γ) := by
  funext A v
  cases v with
  | zero => rfl
  | succ v => rfl

theorem Ren.lift_comp {Γ Δ Θ : Ctx} (r' : Ren Δ Θ) (r : Ren Γ Δ) (B : Ty) :
    (r'.comp r).lift B = (r'.lift B).comp (r.lift B) := by
  funext A v
  cases v with
  | zero => rfl
  | succ v => rfl

@[simp] theorem ren_id : ∀ {Γ : Ctx} {A : Ty} (t : Tm Γ A), ren (Ren.id Γ) t = t
  | _, _, Tm.var v => rfl
  | _, _, Tm.app f a => by simp only [ren, ren_id]
  | _, _, Tm.lam t => by simp only [ren, Ren.lift_id, ren_id]
  | _, _, Tm.star => rfl
  | _, _, Tm.pair a b => by simp only [ren, ren_id]
  | _, _, Tm.fst t => by simp only [ren, ren_id]
  | _, _, Tm.snd t => by simp only [ren, ren_id]

theorem ren_ren : ∀ {Γ Δ Θ : Ctx} (r' : Ren Δ Θ) (r : Ren Γ Δ) {A : Ty} (t : Tm Γ A),
    ren r' (ren r t) = ren (r'.comp r) t
  | _, _, _, _, _, _, Tm.var v => rfl
  | _, _, _, r', r, _, Tm.app f a => by simp only [ren, ren_ren]
  | _, _, _, r', r, _, Tm.lam t => by simp only [ren, ren_ren, Ren.lift_comp]
  | _, _, _, _, _, _, Tm.star => rfl
  | _, _, _, r', r, _, Tm.pair a b => by simp only [ren, ren_ren]
  | _, _, _, r', r, _, Tm.fst t => by simp only [ren, ren_ren]
  | _, _, _, r', r, _, Tm.snd t => by simp only [ren, ren_ren]

------------------------------------------------------------------------
-- Substitutions
------------------------------------------------------------------------

/-- A substitution maps the variables of one context to terms over another. -/
def Sub (Γ Δ : Ctx) : Type := ∀ A : Ty, Var Γ A → Tm Δ A

/-- The identity substitution. -/
def Sub.id (Γ : Ctx) : Sub Γ Γ := fun _ v => Tm.var v

/-- A substitution pushed under a binder. -/
def Sub.lift {Γ Δ : Ctx} (σ : Sub Γ Δ) (B : Ty) : Sub (B :: Γ) (B :: Δ) := fun _ v =>
  match v with
  | Var.zero => Tm.var Var.zero
  | Var.succ v => ren (Ren.wk B) (σ _ v)

/-- Substitution in terms. -/
def sub : ∀ {Γ Δ : Ctx}, Sub Γ Δ → ∀ {A : Ty}, Tm Γ A → Tm Δ A
  | _, _, σ, _, Tm.var v => σ _ v
  | _, _, σ, _, Tm.app f a => Tm.app (sub σ f) (sub σ a)
  | _, _, σ, _, Tm.lam t => Tm.lam (sub (σ.lift _) t)
  | _, _, _, _, Tm.star => Tm.star
  | _, _, σ, _, Tm.pair a b => Tm.pair (sub σ a) (sub σ b)
  | _, _, σ, _, Tm.fst t => Tm.fst (sub σ t)
  | _, _, σ, _, Tm.snd t => Tm.snd (sub σ t)

/-- The substitution induced by a renaming. -/
def Ren.toSub {Γ Δ : Ctx} (r : Ren Γ Δ) : Sub Γ Δ := fun A v => Tm.var (r A v)

theorem Ren.lift_toSub {Γ Δ : Ctx} (r : Ren Γ Δ) (B : Ty) :
    (r.lift B).toSub = r.toSub.lift B := by
  funext A v
  cases v with
  | zero => rfl
  | succ v => rfl

theorem ren_eq_sub : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {A : Ty} (t : Tm Γ A),
    ren r t = sub r.toSub t
  | _, _, _, _, Tm.var v => rfl
  | _, _, r, _, Tm.app f a => by simp only [ren, sub, ren_eq_sub]
  | _, _, r, _, Tm.lam t => by simp only [ren, sub, ren_eq_sub, Ren.lift_toSub]
  | _, _, _, _, Tm.star => rfl
  | _, _, r, _, Tm.pair a b => by simp only [ren, sub, ren_eq_sub]
  | _, _, r, _, Tm.fst t => by simp only [ren, sub, ren_eq_sub]
  | _, _, r, _, Tm.snd t => by simp only [ren, sub, ren_eq_sub]

/-- Composition of a substitution with a renaming, on the right. -/
def Sub.compRen {Γ Δ Θ : Ctx} (σ : Sub Δ Θ) (r : Ren Γ Δ) : Sub Γ Θ := fun A v => σ A (r A v)

/-- Composition of a renaming with a substitution, on the left. -/
def Sub.renComp {Γ Δ Θ : Ctx} (r : Ren Δ Θ) (σ : Sub Γ Δ) : Sub Γ Θ := fun A v => ren r (σ A v)

theorem Sub.lift_compRen {Γ Δ Θ : Ctx} (σ : Sub Δ Θ) (r : Ren Γ Δ) (B : Ty) :
    (σ.compRen r).lift B = (σ.lift B).compRen (r.lift B) := by
  funext A v
  cases v with
  | zero => rfl
  | succ v => rfl

theorem Sub.lift_renComp {Γ Δ Θ : Ctx} (r : Ren Δ Θ) (σ : Sub Γ Δ) (B : Ty) :
    (Sub.renComp r σ).lift B = Sub.renComp (r.lift B) (σ.lift B) := by
  funext A v
  cases v with
  | zero => rfl
  | succ v =>
      change ren (Ren.wk B) (ren r (σ A v)) = ren (Ren.lift r B) (ren (Ren.wk B) (σ A v))
      rw [ren_ren, ren_ren]
      rfl

theorem sub_ren : ∀ {Γ Δ Θ : Ctx} (σ : Sub Δ Θ) (r : Ren Γ Δ) {A : Ty} (t : Tm Γ A),
    sub σ (ren r t) = sub (σ.compRen r) t
  | _, _, _, _, _, _, Tm.var v => rfl
  | _, _, _, σ, r, _, Tm.app f a => by simp only [ren, sub, sub_ren]
  | _, _, _, σ, r, _, Tm.lam t => by simp only [ren, sub, sub_ren, Sub.lift_compRen]
  | _, _, _, _, _, _, Tm.star => rfl
  | _, _, _, σ, r, _, Tm.pair a b => by simp only [ren, sub, sub_ren]
  | _, _, _, σ, r, _, Tm.fst t => by simp only [ren, sub, sub_ren]
  | _, _, _, σ, r, _, Tm.snd t => by simp only [ren, sub, sub_ren]

theorem ren_sub : ∀ {Γ Δ Θ : Ctx} (r : Ren Δ Θ) (σ : Sub Γ Δ) {A : Ty} (t : Tm Γ A),
    ren r (sub σ t) = sub (Sub.renComp r σ) t
  | _, _, _, _, _, _, Tm.var v => rfl
  | _, _, _, r, σ, _, Tm.app f a => by simp only [ren, sub, ren_sub]
  | _, _, _, r, σ, _, Tm.lam t => by simp only [ren, sub, ren_sub, Sub.lift_renComp]
  | _, _, _, _, _, _, Tm.star => rfl
  | _, _, _, r, σ, _, Tm.pair a b => by simp only [ren, sub, ren_sub]
  | _, _, _, r, σ, _, Tm.fst t => by simp only [ren, sub, ren_sub]
  | _, _, _, r, σ, _, Tm.snd t => by simp only [ren, sub, ren_sub]

/-- Composition of substitutions. -/
def Sub.comp {Γ Δ Θ : Ctx} (σ' : Sub Δ Θ) (σ : Sub Γ Δ) : Sub Γ Θ := fun A v => sub σ' (σ A v)

theorem Sub.lift_id (Γ : Ctx) (B : Ty) : (Sub.id Γ).lift B = Sub.id (B :: Γ) := by
  funext A v
  cases v with
  | zero => rfl
  | succ v => rfl

@[simp] theorem sub_id : ∀ {Γ : Ctx} {A : Ty} (t : Tm Γ A), sub (Sub.id Γ) t = t
  | _, _, Tm.var v => rfl
  | _, _, Tm.app f a => by simp only [sub, sub_id]
  | _, _, Tm.lam t => by simp only [sub, Sub.lift_id, sub_id]
  | _, _, Tm.star => rfl
  | _, _, Tm.pair a b => by simp only [sub, sub_id]
  | _, _, Tm.fst t => by simp only [sub, sub_id]
  | _, _, Tm.snd t => by simp only [sub, sub_id]

theorem Sub.lift_comp {Γ Δ Θ : Ctx} (σ' : Sub Δ Θ) (σ : Sub Γ Δ) (B : Ty) :
    (σ'.comp σ).lift B = (σ'.lift B).comp (σ.lift B) := by
  funext A v
  cases v with
  | zero => rfl
  | succ v =>
      change ren (Ren.wk B) (sub σ' (σ A v)) = sub ((σ'.lift B)) (ren (Ren.wk B) (σ A v))
      rw [ren_sub, sub_ren]
      rfl

theorem sub_sub : ∀ {Γ Δ Θ : Ctx} (σ' : Sub Δ Θ) (σ : Sub Γ Δ) {A : Ty} (t : Tm Γ A),
    sub σ' (sub σ t) = sub (σ'.comp σ) t
  | _, _, _, _, _, _, Tm.var v => rfl
  | _, _, _, σ', σ, _, Tm.app f a => by simp only [sub, sub_sub]
  | _, _, _, σ', σ, _, Tm.lam t => by simp only [sub, sub_sub, Sub.lift_comp]
  | _, _, _, _, _, _, Tm.star => rfl
  | _, _, _, σ', σ, _, Tm.pair a b => by simp only [sub, sub_sub]
  | _, _, _, σ', σ, _, Tm.fst t => by simp only [sub, sub_sub]
  | _, _, _, σ', σ, _, Tm.snd t => by simp only [sub, sub_sub]

/-- Extending a substitution with a term for the variable `0`. -/
def Sub.cons {Γ Δ : Ctx} {A : Ty} (t : Tm Δ A) (σ : Sub Γ Δ) : Sub (A :: Γ) Δ := fun _ v =>
  match v with
  | Var.zero => t
  | Var.succ v => σ _ v

/-- The substitution replacing the variable `0` by a term. -/
def Sub.single {Γ : Ctx} {A : Ty} (t : Tm Γ A) : Sub (A :: Γ) Γ := Sub.cons t (Sub.id Γ)

/-- Instantiating the variable `0`. -/
def inst {Γ : Ctx} {A B : Ty} (t : Tm (A :: Γ) B) (s : Tm Γ A) : Tm Γ B := sub (Sub.single s) t

/-- Weakening a term by one variable. -/
def wk {Γ : Ctx} {A : Ty} (B : Ty) (t : Tm Γ A) : Tm (B :: Γ) A := ren (Ren.wk B) t

theorem inst_wk {Γ : Ctx} {A B : Ty} (t : Tm Γ A) (s : Tm Γ B) : inst (wk B t) s = t := by
  change sub (Sub.single s) (ren (Ren.wk B) t) = t
  rw [sub_ren]
  have : (Sub.single s).compRen (Ren.wk B) = Sub.id Γ := by
    funext A v
    rfl
  rw [this, sub_id]

theorem sub_single {Γ Δ : Ctx} {A B : Ty} (σ : Sub Γ Δ) (t : Tm (A :: Γ) B) (s : Tm Γ A) :
    sub σ (inst t s) = inst (sub (σ.lift A) t) (sub σ s) := by
  change sub σ (sub (Sub.single s) t) = sub (Sub.single (sub σ s)) (sub (σ.lift A) t)
  rw [sub_sub, sub_sub]
  congr 1
  funext C v
  cases v with
  | zero => rfl
  | succ v =>
      change sub σ (Sub.id Γ C v) = sub (Sub.single (sub σ s)) (ren (Ren.wk A) (σ C v))
      rw [sub_ren]
      have : (Sub.single (sub σ s)).compRen (Ren.wk A) = Sub.id Δ := by
        funext D w
        rfl
      rw [this, sub_id]
      rfl

theorem wk_sub {Γ Δ : Ctx} {A B : Ty} (σ : Sub Γ Δ) (t : Tm Γ A) :
    wk B (sub σ t) = sub (σ.lift B) (wk B t) := by
  change ren (Ren.wk B) (sub σ t) = sub (σ.lift B) (ren (Ren.wk B) t)
  rw [ren_sub, sub_ren]
  rfl

------------------------------------------------------------------------
-- βη-conversion
------------------------------------------------------------------------

/-- βη-conversion: the least congruence containing β and η for functions, the projection and
surjective-pairing rules for products, and the terminality rule for the unit type. -/
inductive Conv : ∀ {Γ : Ctx} {A : Ty}, Tm Γ A → Tm Γ A → Prop
  | refl {Γ : Ctx} {A : Ty} (t : Tm Γ A) : Conv t t
  | symm {Γ : Ctx} {A : Ty} {t u : Tm Γ A} : Conv t u → Conv u t
  | trans {Γ : Ctx} {A : Ty} {t u v : Tm Γ A} : Conv t u → Conv u v → Conv t v
  | app {Γ : Ctx} {A B : Ty} {f f' : Tm Γ (Ty.arrow A B)} {a a' : Tm Γ A} :
      Conv f f' → Conv a a' → Conv (Tm.app f a) (Tm.app f' a')
  | lam {Γ : Ctx} {A B : Ty} {t t' : Tm (A :: Γ) B} : Conv t t' → Conv (Tm.lam t) (Tm.lam t')
  | pair {Γ : Ctx} {A B : Ty} {a a' : Tm Γ A} {b b' : Tm Γ B} :
      Conv a a' → Conv b b' → Conv (Tm.pair a b) (Tm.pair a' b')
  | fst {Γ : Ctx} {A B : Ty} {t t' : Tm Γ (Ty.prod A B)} : Conv t t' → Conv (Tm.fst t) (Tm.fst t')
  | snd {Γ : Ctx} {A B : Ty} {t t' : Tm Γ (Ty.prod A B)} : Conv t t' → Conv (Tm.snd t) (Tm.snd t')
  | beta {Γ : Ctx} {A B : Ty} (t : Tm (A :: Γ) B) (s : Tm Γ A) :
      Conv (Tm.app (Tm.lam t) s) (inst t s)
  | eta {Γ : Ctx} {A B : Ty} (t : Tm Γ (Ty.arrow A B)) :
      Conv t (Tm.lam (Tm.app (wk A t) (Tm.var Var.zero)))
  | fst_pair {Γ : Ctx} {A B : Ty} (a : Tm Γ A) (b : Tm Γ B) : Conv (Tm.fst (Tm.pair a b)) a
  | snd_pair {Γ : Ctx} {A B : Ty} (a : Tm Γ A) (b : Tm Γ B) : Conv (Tm.snd (Tm.pair a b)) b
  | pair_eta {Γ : Ctx} {A B : Ty} (t : Tm Γ (Ty.prod A B)) :
      Conv (Tm.pair (Tm.fst t) (Tm.snd t)) t
  | unit_eta {Γ : Ctx} (t : Tm Γ Ty.unit) : Conv t Tm.star

attribute [refl] Conv.refl

/-- Conversion is an equivalence relation. -/
theorem Conv.equivalence (Γ : Ctx) (A : Ty) : Equivalence (@Conv Γ A) :=
  ⟨Conv.refl, Conv.symm, Conv.trans⟩

/-- The setoid of terms modulo conversion. -/
def convSetoid (Γ : Ctx) (A : Ty) : Setoid (Tm Γ A) where
  r := Conv
  iseqv := Conv.equivalence Γ A

/-- Conversion is preserved by substitution. -/
theorem Conv.sub : ∀ {Γ : Ctx} {A : Ty} {t u : Tm Γ A}, Conv t u →
    ∀ {Δ : Ctx} (σ : Sub Γ Δ), Conv (Stlc.sub σ t) (Stlc.sub σ u) := by
  intro Γ A t u h
  induction h with
  | refl t => intro Δ σ; exact Conv.refl _
  | symm _ ih => intro Δ σ; exact (ih σ).symm
  | trans _ _ ih1 ih2 => intro Δ σ; exact (ih1 σ).trans (ih2 σ)
  | app _ _ ihf iha => intro Δ σ; exact Conv.app (ihf σ) (iha σ)
  | lam _ ih => intro Δ σ; exact Conv.lam (ih _)
  | pair _ _ iha ihb => intro Δ σ; exact Conv.pair (iha σ) (ihb σ)
  | fst _ ih => intro Δ σ; exact Conv.fst (ih σ)
  | snd _ ih => intro Δ σ; exact Conv.snd (ih σ)
  | beta t s =>
      intro Δ σ
      rw [sub_single]
      exact Conv.beta _ _
  | eta t =>
      intro Δ σ
      have := Conv.eta (Stlc.sub σ t)
      rwa [wk_sub σ t] at this
  | fst_pair a b => intro Δ σ; exact Conv.fst_pair _ _
  | snd_pair a b => intro Δ σ; exact Conv.snd_pair _ _
  | pair_eta t => intro Δ σ; exact Conv.pair_eta _
  | unit_eta t => intro Δ σ; exact Conv.unit_eta _

/-- Conversion is preserved by renaming. -/
theorem Conv.ren {Γ Δ : Ctx} {A : Ty} {t u : Tm Γ A} (h : Conv t u) (r : Ren Γ Δ) :
    Conv (Stlc.ren r t) (Stlc.ren r u) := by
  rw [ren_eq_sub, ren_eq_sub]
  exact h.sub _

/-- Substituting pointwise convertible substitutions gives convertible results. -/
theorem Conv.subCongr : ∀ {Γ Δ : Ctx} {A : Ty} (t : Tm Γ A) {σ τ : Sub Γ Δ},
    (∀ (B : Ty) (v : Var Γ B), Conv (σ B v) (τ B v)) → Conv (Stlc.sub σ t) (Stlc.sub τ t)
  | _, _, _, Tm.var v, _, _, h => h _ v
  | _, _, _, Tm.app f a, _, _, h => Conv.app (Conv.subCongr f h) (Conv.subCongr a h)
  | _, _, _, Tm.lam t, σ, τ, h => by
      refine Conv.lam (Conv.subCongr t ?_)
      intro B v
      cases v with
      | zero => exact Conv.refl _
      | succ v => exact (h _ v).ren _
  | _, _, _, Tm.star, _, _, _ => Conv.refl _
  | _, _, _, Tm.pair a b, _, _, h => Conv.pair (Conv.subCongr a h) (Conv.subCongr b h)
  | _, _, _, Tm.fst t, _, _, h => Conv.fst (Conv.subCongr t h)
  | _, _, _, Tm.snd t, _, _, h => Conv.snd (Conv.subCongr t h)

end Stlc
