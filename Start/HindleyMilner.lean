/-
**The Hindley–Milner type system**: monotypes, type schemes, instantiation and let-generalization,
the typing judgement, and its metatheory (substitution of types, weakening, substitution of terms,
subject reduction).

The monotypes are `HM.Ty` of `Start/Unification.lean`.  A **type scheme** `HM.Sch` is a monotype
in which some variables are bound: `Sch.fv v` is a free type variable and `Sch.bv k` a bound one.
Bound variables are indexed by name, so the scheme `∀ᾱ. τ` is `τ` with the variables `ᾱ` written
as `bv`; a substitution acts on the free variables only, which makes capture impossible by
construction.

* `HM.Sch.inst ts σ` — the instance of `σ` that replaces the bound variable `k` by `ts k`;
* `HM.gen Γ τ` — the generalization of `τ` relative to the context `Γ`: every variable of `τ`
  that is not free in `Γ` becomes bound;
* `HM.Expr` — the terms of mini-ML: variables (de Bruijn indices), application, abstraction and
  `let`;
* `HM.Typing Γ e τ` — the four rules of Damas–Milner in syntax-directed form: the variable rule
  instantiates the scheme of the variable, and the `let` rule generalizes the type of the bound
  term;
* `HM.MoreGen σ' σ` — `σ'` is more general than `σ` (every instance of `σ` is one of `σ'`), and
  `HM.Typing.mono` — typing is preserved by making the context more general;
* `HM.Typing.subst` — **typing is stable under substitution of type variables**;
* `HM.Typing.rename`, `HM.Typing.weaken` — weakening (and renaming of term variables);
* `HM.Typing.substE` — **substitution of terms**: a variable of scheme `σ` may be replaced by a
  term having every instance of `σ`;
* `HM.Typing.preservation` — **subject reduction** for β-reduction and `let`-reduction.

The `let` cases of the substitution and weakening lemmas are where Hindley–Milner differs from
the simply typed calculus: the generalized variables of the bound term have to be renamed away
from the new context first (`HM.moreGen_gen_rename`).
-/

import Start.Unification

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace HM

open Ty

/-! ### Type schemes -/

/-- Type schemes: monotypes in which some variables (`bv`) are bound. -/
inductive Sch where
  /-- A free type variable. -/
  | fv : ℕ → Sch
  /-- A bound type variable. -/
  | bv : ℕ → Sch
  /-- A type constant. -/
  | con : ℕ → Sch
  /-- A function type. -/
  | arrow : Sch → Sch → Sch
  deriving DecidableEq, Repr

namespace Sch

/-- A monotype as a scheme with no bound variables. -/
def ofTy : Ty → Sch
  | Ty.var v => fv v
  | Ty.con c => con c
  | Ty.arrow a b => arrow (ofTy a) (ofTy b)

/-- The general instantiation: free variables by `f`, bound variables by `ts`. -/
def inst2 (f ts : ℕ → Ty) : Sch → Ty
  | fv v => f v
  | bv k => ts k
  | con c => Ty.con c
  | arrow a b => Ty.arrow (inst2 f ts a) (inst2 f ts b)

/-- The instance of a scheme replacing the bound variable `k` by `ts k`. -/
def inst (ts : ℕ → Ty) (σ : Sch) : Ty := inst2 Ty.var ts σ

/-- Substitution of the free variables of a scheme. -/
def subst (s : ℕ → Ty) : Sch → Sch
  | fv v => ofTy (s v)
  | bv k => bv k
  | con c => con c
  | arrow a b => arrow (subst s a) (subst s b)

/-- The free variables of a scheme. -/
def fvs : Sch → Finset ℕ
  | fv v => {v}
  | bv _ => ∅
  | con _ => ∅
  | arrow a b => fvs a ∪ fvs b

/-- A strict upper bound of the bound variables of a scheme. -/
def bnd : Sch → ℕ
  | fv _ => 0
  | bv k => k + 1
  | con _ => 0
  | arrow a b => max (bnd a) (bnd b)

@[simp] theorem inst2_ofTy (f ts : ℕ → Ty) (t : Ty) : (ofTy t).inst2 f ts = t.subst f := by
  induction t with
  | var v => rfl
  | con c => rfl
  | arrow a b iha ihb => simp [ofTy, inst2, iha, ihb]

@[simp] theorem inst_ofTy (ts : ℕ → Ty) (t : Ty) : (ofTy t).inst ts = t := by
  simp [inst]

@[simp] theorem fvs_ofTy (t : Ty) : (ofTy t).fvs = t.vars := by
  induction t with
  | var v => rfl
  | con c => rfl
  | arrow a b iha ihb => simp [ofTy, fvs, iha, ihb]

@[simp] theorem ofTy_subst (s : ℕ → Ty) (t : Ty) : (ofTy t).subst s = ofTy (t.subst s) := by
  induction t with
  | var v => rfl
  | con c => rfl
  | arrow a b iha ihb => simp [ofTy, subst, iha, ihb]

theorem inst2_subst (s f ts : ℕ → Ty) (σ : Sch) :
    (σ.subst s).inst2 f ts = σ.inst2 (fun v => (s v).subst f) ts := by
  induction σ with
  | fv v => simp [subst, inst2]
  | bv k => rfl
  | con c => rfl
  | arrow a b iha ihb => simp [subst, inst2, iha, ihb]

theorem subst_inst2 (r f ts : ℕ → Ty) (σ : Sch) :
    (σ.inst2 f ts).subst r = σ.inst2 (fun v => (f v).subst r) (fun k => (ts k).subst r) := by
  induction σ with
  | fv v => rfl
  | bv k => rfl
  | con c => rfl
  | arrow a b iha ihb => simp [inst2, iha, ihb]

theorem inst2_congr {f f' : ℕ → Ty} (ts : ℕ → Ty) {σ : Sch} (h : ∀ v ∈ σ.fvs, f v = f' v) :
    σ.inst2 f ts = σ.inst2 f' ts := by
  induction σ with
  | fv v => simpa [inst2, fvs] using h v (by simp [fvs])
  | bv k => rfl
  | con c => rfl
  | arrow a b iha ihb =>
    simp only [inst2, Ty.arrow.injEq]
    exact ⟨iha fun v hv => h v (by simp [fvs, hv]), ihb fun v hv => h v (by simp [fvs, hv])⟩

theorem subst_congr {s s' : ℕ → Ty} {σ : Sch} (h : ∀ v ∈ σ.fvs, s v = s' v) :
    σ.subst s = σ.subst s' := by
  induction σ with
  | fv v => simp only [subst]; rw [h v (by simp [fvs])]
  | bv k => rfl
  | con c => rfl
  | arrow a b iha ihb =>
    simp only [subst, arrow.injEq]
    exact ⟨iha fun v hv => h v (by simp [fvs, hv]), ihb fun v hv => h v (by simp [fvs, hv])⟩

@[simp] theorem subst_var (σ : Sch) : σ.subst Ty.var = σ := by
  induction σ with
  | fv v => rfl
  | bv k => rfl
  | con c => rfl
  | arrow a b iha ihb => simp [subst, iha, ihb]

theorem subst_subst (s s' : ℕ → Ty) (σ : Sch) :
    (σ.subst s).subst s' = σ.subst (fun v => (s v).subst s') := by
  induction σ with
  | fv v => simp [subst]
  | bv k => rfl
  | con c => rfl
  | arrow a b iha ihb => simp [subst, iha, ihb]

theorem mem_fvs_subst {s : ℕ → Ty} {σ : Sch} {w : ℕ} :
    w ∈ (σ.subst s).fvs ↔ ∃ v ∈ σ.fvs, w ∈ (s v).vars := by
  induction σ with
  | fv v => simp [subst, fvs]
  | bv k => simp [subst, fvs]
  | con c => simp [subst, fvs]
  | arrow a b iha ihb =>
    simp only [subst, fvs, Finset.mem_union, iha, ihb]
    constructor
    · rintro (⟨v, hv, h⟩ | ⟨v, hv, h⟩)
      · exact ⟨v, Or.inl hv, h⟩
      · exact ⟨v, Or.inr hv, h⟩
    · rintro ⟨v, hv | hv, h⟩
      · exact Or.inl ⟨v, hv, h⟩
      · exact Or.inr ⟨v, hv, h⟩

/-- Every free variable of a scheme occurs in each of its instances. -/
theorem fvs_subset_vars_inst (ts : ℕ → Ty) (σ : Sch) : σ.fvs ⊆ (σ.inst ts).vars := by
  induction σ with
  | fv v => simp [fvs, inst, inst2]
  | bv k => simp [fvs]
  | con c => simp [fvs]
  | arrow a b iha ihb =>
    simp only [fvs, inst, inst2, vars_arrow] at iha ihb ⊢
    exact Finset.union_subset_union iha ihb

/-- The instance by constants has no variables but the free ones. -/
theorem vars_inst_con_subset (σ : Sch) : (σ.inst fun _ => Ty.con 0).vars ⊆ σ.fvs := by
  induction σ with
  | fv v => simp [fvs, inst, inst2]
  | bv k => simp [inst, inst2]
  | con c => simp [inst, inst2]
  | arrow a b iha ihb =>
    simp only [fvs, inst, inst2, vars_arrow] at iha ihb ⊢
    exact Finset.union_subset_union iha ihb

end Sch

/-- Generalization over every variable outside the set `A`. -/
def gen' (A : Finset ℕ) : Ty → Sch
  | Ty.var v => if v ∈ A then Sch.fv v else Sch.bv v
  | Ty.con c => Sch.con c
  | Ty.arrow a b => Sch.arrow (gen' A a) (gen' A b)

theorem inst2_gen' (A : Finset ℕ) (f ts : ℕ → Ty) (t : Ty) :
    (gen' A t).inst2 f ts = t.subst fun v => if v ∈ A then f v else ts v := by
  induction t with
  | var v => by_cases h : v ∈ A <;> simp [gen', h, Sch.inst2]
  | con c => rfl
  | arrow a b iha ihb => simp [gen', Sch.inst2, iha, ihb]

theorem fvs_gen'_subset (A : Finset ℕ) (t : Ty) : (gen' A t).fvs ⊆ A := by
  induction t with
  | var v => by_cases h : v ∈ A <;> simp [gen', h, Sch.fvs]
  | con c => simp [gen', Sch.fvs]
  | arrow a b iha ihb => simp only [gen', Sch.fvs]; exact Finset.union_subset iha ihb

/-! ### Contexts -/

/-- The free type variables of a context. -/
def ctxFvs : List Sch → Finset ℕ
  | [] => ∅
  | σ :: Γ => σ.fvs ∪ ctxFvs Γ

/-- Generalization of a monotype relative to a context. -/
def gen (Γ : List Sch) (τ : Ty) : Sch := gen' (ctxFvs Γ) τ

/-- Substitution in every scheme of a context. -/
def ctxSubst (s : ℕ → Ty) (Γ : List Sch) : List Sch := Γ.map (Sch.subst s)

@[simp] theorem ctxFvs_nil : ctxFvs [] = ∅ := rfl
@[simp] theorem ctxFvs_cons (σ : Sch) (Γ : List Sch) : ctxFvs (σ :: Γ) = σ.fvs ∪ ctxFvs Γ := rfl
@[simp] theorem ctxSubst_nil (s : ℕ → Ty) : ctxSubst s [] = [] := rfl
@[simp] theorem ctxSubst_cons (s : ℕ → Ty) (σ : Sch) (Γ : List Sch) :
    ctxSubst s (σ :: Γ) = σ.subst s :: ctxSubst s Γ := rfl

theorem mem_ctxFvs {Γ : List Sch} {v : ℕ} : v ∈ ctxFvs Γ ↔ ∃ σ ∈ Γ, v ∈ σ.fvs := by
  induction Γ with
  | nil => simp
  | cons σ Γ ih => simp [ih]

theorem fvs_subset_ctxFvs {Γ : List Sch} {i : ℕ} {σ : Sch} (h : Γ[i]? = some σ) :
    σ.fvs ⊆ ctxFvs Γ := fun _ hv =>
  mem_ctxFvs.2 ⟨σ, List.mem_of_getElem? h, hv⟩

theorem ctxSubst_congr {s s' : ℕ → Ty} {Γ : List Sch} (h : ∀ v ∈ ctxFvs Γ, s v = s' v) :
    ctxSubst s Γ = ctxSubst s' Γ := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
    simp only [ctxSubst_cons, List.cons.injEq]
    exact ⟨Sch.subst_congr fun v hv => h v (by simp [hv]),
      ih fun v hv => h v (by simp [hv])⟩

@[simp] theorem ctxSubst_var (Γ : List Sch) : ctxSubst Ty.var Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih => simp [ih]

theorem ctxSubst_ctxSubst (s s' : ℕ → Ty) (Γ : List Sch) :
    ctxSubst s' (ctxSubst s Γ) = ctxSubst (fun v => (s v).subst s') Γ := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih => simp [ih, Sch.subst_subst]

theorem mem_ctxFvs_subst {s : ℕ → Ty} {Γ : List Sch} {w : ℕ} :
    w ∈ ctxFvs (ctxSubst s Γ) ↔ ∃ v ∈ ctxFvs Γ, w ∈ (s v).vars := by
  induction Γ with
  | nil => simp
  | cons σ Γ ih =>
    simp only [ctxSubst_cons, ctxFvs_cons, Finset.mem_union, ih, Sch.mem_fvs_subst]
    constructor
    · rintro (⟨v, hv, h⟩ | ⟨v, hv, h⟩)
      · exact ⟨v, Or.inl hv, h⟩
      · exact ⟨v, Or.inr hv, h⟩
    · rintro ⟨v, hv | hv, h⟩
      · exact Or.inl ⟨v, hv, h⟩
      · exact Or.inr ⟨v, hv, h⟩

theorem getElem?_ctxSubst {s : ℕ → Ty} {Γ : List Sch} {i : ℕ} {σ : Sch} (h : Γ[i]? = some σ) :
    (ctxSubst s Γ)[i]? = some (σ.subst s) := by
  simp [ctxSubst, h]

/-! ### Terms and typing -/

/-- The terms of mini-ML, with de Bruijn indices: `let_ a b` binds the variable `0` in `b`. -/
inductive Expr where
  /-- A variable. -/
  | var : ℕ → Expr
  /-- Application. -/
  | app : Expr → Expr → Expr
  /-- Abstraction. -/
  | lam : Expr → Expr
  /-- `let x = a in b`. -/
  | let_ : Expr → Expr → Expr
  deriving DecidableEq, Repr

/-- The **Hindley–Milner type system** (Damas–Milner, syntax-directed form). -/
inductive Typing : List Sch → Expr → Ty → Prop
  /-- A variable has every instance of its scheme. -/
  | var {Γ : List Sch} {i : ℕ} {σ : Sch} (ts : ℕ → Ty) :
      Γ[i]? = some σ → Typing Γ (Expr.var i) (σ.inst ts)
  /-- Application. -/
  | app {Γ : List Sch} {a b : Expr} {A B : Ty} :
      Typing Γ a (Ty.arrow A B) → Typing Γ b A → Typing Γ (Expr.app a b) B
  /-- Abstraction: the bound variable gets a monotype. -/
  | lam {Γ : List Sch} {t : Expr} {A B : Ty} :
      Typing (Sch.ofTy A :: Γ) t B → Typing Γ (Expr.lam t) (Ty.arrow A B)
  /-- `let`: the bound variable gets the generalization of the type of the bound term. -/
  | let_ {Γ : List Sch} {a b : Expr} {A B : Ty} :
      Typing Γ a A → Typing (gen Γ A :: Γ) b B → Typing Γ (Expr.let_ a b) B

/-! ### The instance order on schemes -/

/-- `σ'` is **more general** than `σ`: every instance of `σ` is an instance of `σ'`. -/
def MoreGen (σ' σ : Sch) : Prop := ∀ ts, ∃ ts', σ'.inst ts' = σ.inst ts

theorem MoreGen.refl (σ : Sch) : MoreGen σ σ := fun ts => ⟨ts, rfl⟩

theorem MoreGen.trans {σ₁ σ₂ σ₃ : Sch} (h₁ : MoreGen σ₁ σ₂) (h₂ : MoreGen σ₂ σ₃) :
    MoreGen σ₁ σ₃ := fun ts => by
  obtain ⟨ts₂, h⟩ := h₂ ts
  obtain ⟨ts₁, h'⟩ := h₁ ts₂
  exact ⟨ts₁, h'.trans h⟩

/-- A more general scheme has fewer free variables. -/
theorem MoreGen.fvs_subset {σ' σ : Sch} (h : MoreGen σ' σ) : σ'.fvs ⊆ σ.fvs := by
  obtain ⟨ts', h⟩ := h fun _ => Ty.con 0
  intro v hv
  have := Sch.fvs_subset_vars_inst ts' σ' hv
  rw [h] at this
  exact Sch.vars_inst_con_subset σ this

theorem moreGen_gen'_of_subset {A A' : Finset ℕ} (h : A' ⊆ A) (t : Ty) :
    MoreGen (gen' A' t) (gen' A t) := fun ts => by
  refine ⟨fun v => if v ∈ A then Ty.var v else ts v, ?_⟩
  simp only [Sch.inst, inst2_gen']
  apply Ty.subst_congr
  intro v _
  by_cases hA : v ∈ A
  · by_cases hA' : v ∈ A' <;> simp [hA, hA']
  · have : v ∉ A' := fun h' => hA (h h')
    simp [hA, this]

/-- **Renaming the generalized variables away.**  If a substitution `s` maps the variables of
`A` into the set `C`, then some `s'` agreeing with `s` on `A` makes the generalization over `C`
after substitution at least as general as the generalization over `A` before it. -/
theorem moreGen_gen_rename (A C : Finset ℕ) (s : ℕ → Ty) (t : Ty)
    (h : ∀ v ∈ A, (s v).vars ⊆ C) :
    ∃ s' : ℕ → Ty, (∀ v ∈ A, s' v = s v) ∧ MoreGen (gen' C (t.subst s')) ((gen' A t).subst s) := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ w ∈ C, w < N := ⟨C.sup id + 1, fun w hw =>
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hw)⟩
  refine ⟨fun v => if v ∈ A then s v else Ty.var (N + v), fun v hv => by simp [hv], ?_⟩
  intro ts
  refine ⟨fun k => ts (k - N), ?_⟩
  simp only [Sch.inst, inst2_gen', Sch.inst2_subst, Ty.subst_subst]
  apply Ty.subst_congr
  intro v _
  by_cases hA : v ∈ A
  · simp only [hA, if_true, Ty.subst_id]
    conv_rhs => rw [← Ty.subst_id (s v)]
    apply Ty.subst_congr
    intro w hw
    simp [h v hA hw]
  · have : N + v ∉ C := fun hc => by have := hN _ hc; omega
    simp [hA, this]

/-- Substituting after generalizing is at least as general as generalizing after substituting. -/
theorem moreGen_subst_gen (A C : Finset ℕ) (r : ℕ → Ty) (t : Ty)
    (h : ∀ v ∈ A, (r v).vars ⊆ C) :
    MoreGen ((gen' A t).subst r) (gen' C (t.subst r)) := fun ts => by
  refine ⟨fun v => (r v).subst fun w => if w ∈ C then Ty.var w else ts w, ?_⟩
  simp only [Sch.inst, inst2_gen', Sch.inst2_subst, Ty.subst_subst]
  apply Ty.subst_congr
  intro v _
  by_cases hA : v ∈ A
  · simp only [hA, if_true, Ty.subst_id]
    conv_lhs => rw [← Ty.subst_id (r v)]
    apply Ty.subst_congr
    intro w hw
    simp [h v hA hw]
  · simp [hA]

theorem forall₂_getElem? {R : Sch → Sch → Prop} {Γ' Γ : List Sch} (h : List.Forall₂ R Γ' Γ)
    {i : ℕ} {σ : Sch} (hi : Γ[i]? = some σ) : ∃ σ', Γ'[i]? = some σ' ∧ R σ' σ := by
  induction h generalizing i with
  | nil => simp at hi
  | cons hab _ ih =>
    cases i with
    | zero => obtain rfl := Option.some.inj hi; exact ⟨_, rfl, hab⟩
    | succ i => simpa using ih (by simpa using hi)

theorem ctxFvs_subset_of_forall₂ {Γ' Γ : List Sch} (h : List.Forall₂ MoreGen Γ' Γ) :
    ctxFvs Γ' ⊆ ctxFvs Γ := by
  induction h with
  | nil => exact le_rfl
  | cons hab _ ih => exact Finset.union_subset_union hab.fvs_subset ih

/-- **Typing is preserved by making the context more general.** -/
theorem Typing.mono {Γ : List Sch} {e : Expr} {τ : Ty} (h : Typing Γ e τ) :
    ∀ {Γ' : List Sch}, List.Forall₂ MoreGen Γ' Γ → Typing Γ' e τ := by
  induction h with
  | var ts hi =>
    intro Γ' hΓ
    obtain ⟨σ', hσ', hmg⟩ := forall₂_getElem? hΓ hi
    obtain ⟨ts', hts'⟩ := hmg ts
    rw [← hts']
    exact Typing.var ts' hσ'
  | app _ _ iha ihb => intro Γ' hΓ; exact Typing.app (iha hΓ) (ihb hΓ)
  | lam _ ih => intro Γ' hΓ; exact Typing.lam (ih (List.Forall₂.cons (MoreGen.refl _) hΓ))
  | let_ _ _ iha ihb =>
    intro Γ' hΓ
    exact Typing.let_ (iha hΓ) (ihb (List.Forall₂.cons
      (moreGen_gen'_of_subset (ctxFvs_subset_of_forall₂ hΓ) _) hΓ))

/-! ### Substitution of type variables -/

theorem Sch.subst_inst (s ts : ℕ → Ty) (σ : Sch) :
    (σ.inst ts).subst s = (σ.subst s).inst fun k => (ts k).subst s := by
  simp [Sch.inst, Sch.subst_inst2, Sch.inst2_subst]

/-- **Typing is stable under substitution**: `Γ ⊢ e : τ` implies `sΓ ⊢ e : sτ`. -/
theorem Typing.subst {Γ : List Sch} {e : Expr} {τ : Ty} (h : Typing Γ e τ) (s : ℕ → Ty) :
    Typing (ctxSubst s Γ) e (τ.subst s) := by
  induction h generalizing s with
  | var ts hi =>
    rw [Sch.subst_inst]
    exact Typing.var _ (getElem?_ctxSubst hi)
  | app _ _ iha ihb => exact Typing.app (iha s) (ihb s)
  | lam _ ih => exact Typing.lam (by simpa using ih s)
  | @let_ Γ a b A B _ _ iha ihb =>
    obtain ⟨s', hs', hmg⟩ := moreGen_gen_rename (ctxFvs Γ) (ctxFvs (ctxSubst s Γ)) s A
      (fun v hv w hw => mem_ctxFvs_subst.2 ⟨v, hv, hw⟩)
    have h1 := iha s'
    rw [ctxSubst_congr hs'] at h1
    refine Typing.let_ h1 ?_
    exact (ihb s).mono (List.Forall₂.cons hmg (List.forall₂_same.2 fun σ _ => MoreGen.refl σ))

/-! ### Renaming and weakening -/

/-- Lifting a renaming of term variables under a binder. -/
def liftR (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => r n + 1

/-- Renaming the term variables of a term. -/
def Expr.rename (r : ℕ → ℕ) : Expr → Expr
  | var i => var (r i)
  | app a b => app (rename r a) (rename r b)
  | lam t => lam (rename (liftR r) t)
  | let_ a b => let_ (rename r a) (rename (liftR r) b)

/-- **Renaming**: a term stays typable when its variables are renamed into a context that gives
each of them a scheme at least as general. -/
theorem Typing.rename {e : Expr} :
    ∀ {Γ : List Sch} {τ : Ty}, Typing Γ e τ → ∀ {Δ : List Sch} {r : ℕ → ℕ},
      (∀ i σ, Γ[i]? = some σ → ∃ σ', Δ[r i]? = some σ' ∧ MoreGen σ' σ) →
      Typing Δ (e.rename r) τ := by
  induction e with
  | var i =>
    intro Γ τ h Δ r hr
    cases h with
    | var ts hi =>
      obtain ⟨σ', hσ', hmg⟩ := hr _ _ hi
      obtain ⟨ts', hts'⟩ := hmg ts
      rw [Expr.rename, ← hts']
      exact Typing.var ts' hσ'
  | app a b iha ihb =>
    intro Γ τ h Δ r hr
    cases h with
    | app ha hb => exact Typing.app (iha ha hr) (ihb hb hr)
  | lam t ih =>
    intro Γ τ h Δ r hr
    cases h with
    | lam ht =>
      refine Typing.lam (ih ht fun i σ hi => ?_)
      cases i with
      | zero => obtain rfl := Option.some.inj hi; exact ⟨_, rfl, MoreGen.refl _⟩
      | succ i => simpa [liftR] using hr i σ (by simpa using hi)
  | let_ a b iha ihb =>
    intro Γ τ h Δ r hr
    cases h with
    | @let_ _ _ _ A B ha hb =>
      obtain ⟨s', hs', hmg⟩ := moreGen_gen_rename (ctxFvs Γ) (ctxFvs Γ ∪ ctxFvs Δ) Ty.var A
        (fun v hv => by simp [hv])
      have h1 := ha.subst s'
      rw [ctxSubst_congr hs', ctxSubst_var] at h1
      have hmg' : MoreGen (gen Δ (A.subst s')) (gen Γ A) := by
        have := (moreGen_gen'_of_subset (Finset.subset_union_right (s₁ := ctxFvs Γ))
          (A.subst s')).trans hmg
        simpa [gen] using this
      refine Typing.let_ (iha h1 hr) (ihb hb fun i σ hi => ?_)
      cases i with
      | zero => obtain rfl := Option.some.inj hi; exact ⟨_, rfl, hmg'⟩
      | succ i => simpa [liftR] using hr i σ (by simpa using hi)

/-- **Weakening**: a typable term stays typable in a context with one more variable. -/
theorem Typing.weaken {Γ : List Sch} {e : Expr} {τ : Ty} (h : Typing Γ e τ) (σ : Sch) :
    Typing (σ :: Γ) (e.rename Nat.succ) τ :=
  h.rename fun i σ' hi => ⟨σ', by simpa using hi, MoreGen.refl _⟩

/-! ### Substitution of terms -/

/-- Lifting a substitution of term variables under a binder. -/
def liftS (f : ℕ → Expr) : ℕ → Expr
  | 0 => Expr.var 0
  | n + 1 => (f n).rename Nat.succ

/-- Parallel substitution of the term variables of a term. -/
def Expr.substE (f : ℕ → Expr) : Expr → Expr
  | var i => f i
  | app a b => app (substE f a) (substE f b)
  | lam t => lam (substE (liftS f) t)
  | let_ a b => let_ (substE f a) (substE (liftS f) b)

/-- The substitution replacing the variable `0` by `a` and lowering the others. -/
def cons0 (a : Expr) : ℕ → Expr
  | 0 => a
  | n + 1 => Expr.var n

/-- **Substitution of terms**: if each variable of `Γ`, of scheme `σ`, is replaced by a term
having every instance of `σ` in `Δ`, typing is preserved. -/
theorem Typing.substE {e : Expr} :
    ∀ {Γ : List Sch} {τ : Ty}, Typing Γ e τ → ∀ {Δ : List Sch} {f : ℕ → Expr},
      (∀ i σ, Γ[i]? = some σ → ∀ ts, Typing Δ (f i) (σ.inst ts)) →
      Typing Δ (e.substE f) τ := by
  induction e with
  | var i =>
    intro Γ τ h Δ f hf
    cases h with
    | var ts hi => exact hf _ _ hi ts
  | app a b iha ihb =>
    intro Γ τ h Δ f hf
    cases h with
    | app ha hb => exact Typing.app (iha ha hf) (ihb hb hf)
  | lam t ih =>
    intro Γ τ h Δ f hf
    cases h with
    | @lam _ _ A _ ht =>
      refine Typing.lam (ih ht fun i σ hi ts => ?_)
      cases i with
      | zero => obtain rfl := Option.some.inj hi; exact Typing.var ts rfl
      | succ i => exact (hf i σ (by simpa using hi) ts).weaken _
  | let_ a b iha ihb =>
    intro Γ τ h Δ f hf
    cases h with
    | @let_ _ _ _ A B ha hb =>
      obtain ⟨s', hs', hmg⟩ := moreGen_gen_rename (ctxFvs Γ) (ctxFvs Γ ∪ ctxFvs Δ) Ty.var A
        (fun v hv => by simp [hv])
      have h1 := ha.subst s'
      rw [ctxSubst_congr hs', ctxSubst_var] at h1
      have hmg' : MoreGen (gen Δ (A.subst s')) (gen Γ A) := by
        have := (moreGen_gen'_of_subset (Finset.subset_union_right (s₁ := ctxFvs Γ))
          (A.subst s')).trans hmg
        simpa [gen] using this
      refine Typing.let_ (iha h1 hf) (ihb hb fun i σ hi ts => ?_)
      cases i with
      | zero =>
        obtain rfl := Option.some.inj hi
        obtain ⟨ts', hts'⟩ := hmg' ts
        rw [← hts']
        exact Typing.var ts' rfl
      | succ i => exact (hf i σ (by simpa using hi) ts).weaken _

/-- A term of type `τ` has every instance of the generalization of `τ`. -/
theorem Typing.inst_gen {Γ : List Sch} {e : Expr} {τ : Ty} (h : Typing Γ e τ) (ts : ℕ → Ty) :
    Typing Γ e ((gen Γ τ).inst ts) := by
  have := h.subst fun v => if v ∈ ctxFvs Γ then Ty.var v else ts v
  rw [ctxSubst_congr (s' := Ty.var) (fun v hv => by simp [hv]), ctxSubst_var] at this
  simpa [gen, Sch.inst, inst2_gen'] using this

/-! ### Subject reduction -/

/-- One step of reduction: β, `let`, and the congruences. -/
inductive Step : Expr → Expr → Prop
  /-- β-reduction. -/
  | beta (b a : Expr) : Step (Expr.app (Expr.lam b) a) (b.substE (cons0 a))
  /-- `let`-reduction. -/
  | letb (a b : Expr) : Step (Expr.let_ a b) (b.substE (cons0 a))
  /-- Reduction in the function position. -/
  | appL {a a' : Expr} (b : Expr) : Step a a' → Step (Expr.app a b) (Expr.app a' b)
  /-- Reduction in the argument position. -/
  | appR (a : Expr) {b b' : Expr} : Step b b' → Step (Expr.app a b) (Expr.app a b')
  /-- Reduction under an abstraction. -/
  | lam {t t' : Expr} : Step t t' → Step (Expr.lam t) (Expr.lam t')
  /-- Reduction in the bound term of a `let`. -/
  | letL {a a' : Expr} (b : Expr) : Step a a' → Step (Expr.let_ a b) (Expr.let_ a' b)
  /-- Reduction in the body of a `let`. -/
  | letR (a : Expr) {b b' : Expr} : Step b b' → Step (Expr.let_ a b) (Expr.let_ a b')

/-- **Subject reduction**: reduction preserves Hindley–Milner types. -/
theorem Typing.preservation {e e' : Expr} (hs : Step e e') :
    ∀ {Γ : List Sch} {τ : Ty}, Typing Γ e τ → Typing Γ e' τ := by
  induction hs with
  | beta b a =>
    intro Γ τ h
    cases h with
    | app hf ha =>
      cases hf with
      | lam hb =>
        refine hb.substE fun i σ hi ts => ?_
        cases i with
        | zero => obtain rfl := Option.some.inj hi; simpa [cons0] using ha
        | succ i => exact Typing.var ts (by simpa using hi)
  | letb a b =>
    intro Γ τ h
    cases h with
    | let_ ha hb =>
      refine hb.substE fun i σ hi ts => ?_
      cases i with
      | zero => obtain rfl := Option.some.inj hi; exact ha.inst_gen ts
      | succ i => exact Typing.var ts (by simpa using hi)
  | appL b _ ih =>
    intro Γ τ h
    cases h with
    | app ha hb => exact Typing.app (ih ha) hb
  | appR a _ ih =>
    intro Γ τ h
    cases h with
    | app ha hb => exact Typing.app ha (ih hb)
  | lam _ ih =>
    intro Γ τ h
    cases h with
    | lam ht => exact Typing.lam (ih ht)
  | letL b _ ih =>
    intro Γ τ h
    cases h with
    | let_ ha hb => exact Typing.let_ (ih ha) hb
  | letR a _ ih =>
    intro Γ τ h
    cases h with
    | let_ ha hb => exact Typing.let_ ha (ih hb)

/-! ### Sanity checks -/

/-- `let id = λx. x in id id` is typable: the `let`-bound identity is used at two different
types, which the simply typed calculus (and the `λ`-bound version) cannot do. -/
theorem typing_let_id_id :
    Typing [] (Expr.let_ (Expr.lam (Expr.var 0)) (Expr.app (Expr.var 0) (Expr.var 0)))
      (Ty.arrow (Ty.var 0) (Ty.var 0)) := by
  have hid : Typing [Sch.ofTy (Ty.var 0)] (Expr.var 0) (Ty.var 0) := by
    simpa using Typing.var (Γ := [Sch.ofTy (Ty.var 0)]) (i := 0) (fun _ => Ty.var 0) rfl
  refine Typing.let_ (A := Ty.arrow (Ty.var 0) (Ty.var 0)) (Typing.lam hid) ?_
  have hg : gen [] (Ty.arrow (Ty.var 0) (Ty.var 0)) = Sch.arrow (Sch.bv 0) (Sch.bv 0) := rfl
  rw [hg]
  refine Typing.app (A := Ty.arrow (Ty.var 0) (Ty.var 0))
    (Typing.var (σ := Sch.arrow (Sch.bv 0) (Sch.bv 0))
      (fun _ => Ty.arrow (Ty.var 0) (Ty.var 0)) rfl) ?_
  exact Typing.var (σ := Sch.arrow (Sch.bv 0) (Sch.bv 0)) (fun _ => Ty.var 0) rfl

end HM
