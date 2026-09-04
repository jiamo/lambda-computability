/-
The syntax of the dependently typed lambda calculus `λΠ` (the logical framework `LF`), in
de Bruijn form, with its substitution calculus and the Church–Rosser theorem for β-reduction.

This is the bottom layer of the dependent-type-theory tower: `Start/Stlc.lean` gives the simply
typed calculus (types cannot mention terms), while here a type may *depend on a term*, so types
and terms live in one grammar and are separated only by the typing judgement of
`Start/LambdaPiTyping.lean`.

* `LambdaPi.Tm` — raw terms: variables, the two sorts `∗` and `□`, application, typed
  abstraction `λ(x : A). b` and dependent products `Π(x : A). B`;
* `LambdaPi.rename`, `LambdaPi.subst` — renamings and *parallel* substitutions, with the four
  composition laws (`rename_rename`, `subst_rename`, `rename_subst`, `subst_subst`);
* `LambdaPi.Step`, `LambdaPi.Red`, `LambdaPi.Conv` — β-reduction, its reflexive–transitive
  closure and β-conversion;
* `LambdaPi.church_rosser` — confluence of β-reduction, proved by Takahashi's method of complete
  developments, and the consequences `LambdaPi.Conv.church_rosser`, `LambdaPi.pi_inj_left`,
  `LambdaPi.pi_inj_right`, `LambdaPi.sort_conv_inj`, `LambdaPi.not_conv_sort_pi`, which are what
  the typing metatheory needs.
-/

import Mathlib.Tactic
import Start.Rewriting

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

/-- The two sorts of `λΠ`: `∗` classifies types, `□` classifies kinds. -/
inductive Srt where
  | star : Srt
  | box : Srt
  deriving DecidableEq, Repr

/-- Raw terms of `λΠ`, with de Bruijn indices. -/
inductive Tm where
  | var : ℕ → Tm
  | sort : Srt → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm → Tm
  | pi : Tm → Tm → Tm
  deriving DecidableEq, Repr

open Tm

/-! ### Renamings -/

/-- Lift a renaming under a binder. -/
def upr (ρ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Apply a renaming to a term. -/
def rename (ρ : ℕ → ℕ) : Tm → Tm
  | var n => var (ρ n)
  | sort s => sort s
  | app f a => app (rename ρ f) (rename ρ a)
  | lam A b => lam (rename ρ A) (rename (upr ρ) b)
  | pi A B => pi (rename ρ A) (rename (upr ρ) B)

@[simp] theorem rename_var (ρ : ℕ → ℕ) (n : ℕ) : rename ρ (var n) = var (ρ n) := rfl
@[simp] theorem rename_sort (ρ : ℕ → ℕ) (s : Srt) : rename ρ (sort s) = sort s := rfl
@[simp] theorem rename_app (ρ : ℕ → ℕ) (f a : Tm) :
    rename ρ (app f a) = app (rename ρ f) (rename ρ a) := rfl
@[simp] theorem rename_lam (ρ : ℕ → ℕ) (A b : Tm) :
    rename ρ (lam A b) = lam (rename ρ A) (rename (upr ρ) b) := rfl
@[simp] theorem rename_pi (ρ : ℕ → ℕ) (A B : Tm) :
    rename ρ (pi A B) = pi (rename ρ A) (rename (upr ρ) B) := rfl

theorem rename_congr {ρ ρ' : ℕ → ℕ} (h : ∀ n, ρ n = ρ' n) (t : Tm) :
    rename ρ t = rename ρ' t := by
  induction t generalizing ρ ρ' with
  | var n => simp [h]
  | sort s => rfl
  | app f a ihf iha => simp [ihf h, iha h]
  | lam A b ihA ihb =>
      have h' : ∀ n, upr ρ n = upr ρ' n := by intro n; cases n <;> simp [upr, h]
      simp [ihA h, ihb h']
  | pi A B ihA ihB =>
      have h' : ∀ n, upr ρ n = upr ρ' n := by intro n; cases n <;> simp [upr, h]
      simp [ihA h, ihB h']

theorem upr_id (n : ℕ) : upr id n = id n := by cases n <;> rfl

@[simp] theorem rename_id (t : Tm) : rename id t = t := by
  induction t with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [ihf, iha]
  | lam A b ihA ihb => rw [rename_lam, ihA, rename_congr upr_id, ihb]
  | pi A B ihA ihB => rw [rename_pi, ihA, rename_congr upr_id, ihB]

theorem upr_comp (ρ ρ' : ℕ → ℕ) (n : ℕ) : upr ρ (upr ρ' n) = upr (fun k => ρ (ρ' k)) n := by
  cases n <;> rfl

theorem rename_rename (ρ ρ' : ℕ → ℕ) (t : Tm) :
    rename ρ (rename ρ' t) = rename (fun n => ρ (ρ' n)) t := by
  induction t generalizing ρ ρ' with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [ihf, iha]
  | lam A b ihA ihb =>
      simp only [rename_lam, ihA, ihb]
      exact congrArg₂ _ rfl (rename_congr (upr_comp ρ ρ') b)
  | pi A B ihA ihB =>
      simp only [rename_pi, ihA, ihB]
      exact congrArg₂ _ rfl (rename_congr (upr_comp ρ ρ') B)

/-! ### Parallel substitutions -/

/-- Lift a substitution under a binder. -/
def up (σ : ℕ → Tm) : ℕ → Tm
  | 0 => var 0
  | n + 1 => rename Nat.succ (σ n)

@[simp] theorem up_zero (σ : ℕ → Tm) : up σ 0 = var 0 := rfl
@[simp] theorem up_succ (σ : ℕ → Tm) (n : ℕ) : up σ (n + 1) = rename Nat.succ (σ n) := rfl

/-- Apply a parallel substitution to a term. -/
def subst (σ : ℕ → Tm) : Tm → Tm
  | var n => σ n
  | sort s => sort s
  | app f a => app (subst σ f) (subst σ a)
  | lam A b => lam (subst σ A) (subst (up σ) b)
  | pi A B => pi (subst σ A) (subst (up σ) B)

@[simp] theorem subst_var (σ : ℕ → Tm) (n : ℕ) : subst σ (var n) = σ n := rfl
@[simp] theorem subst_sort (σ : ℕ → Tm) (s : Srt) : subst σ (sort s) = sort s := rfl
@[simp] theorem subst_app (σ : ℕ → Tm) (f a : Tm) :
    subst σ (app f a) = app (subst σ f) (subst σ a) := rfl
@[simp] theorem subst_lam (σ : ℕ → Tm) (A b : Tm) :
    subst σ (lam A b) = lam (subst σ A) (subst (up σ) b) := rfl
@[simp] theorem subst_pi (σ : ℕ → Tm) (A B : Tm) :
    subst σ (pi A B) = pi (subst σ A) (subst (up σ) B) := rfl

theorem subst_congr {σ σ' : ℕ → Tm} (h : ∀ n, σ n = σ' n) (t : Tm) : subst σ t = subst σ' t := by
  induction t generalizing σ σ' with
  | var n => simp [h]
  | sort s => rfl
  | app f a ihf iha => simp [ihf h, iha h]
  | lam A b ihA ihb =>
      have h' : ∀ n, up σ n = up σ' n := by intro n; cases n <;> simp [h]
      simp [ihA h, ihb h']
  | pi A B ihA ihB =>
      have h' : ∀ n, up σ n = up σ' n := by intro n; cases n <;> simp [h]
      simp [ihA h, ihB h']

/-- The substitution that does nothing. -/
def ids : ℕ → Tm := fun n => var n

@[simp] theorem ids_apply (n : ℕ) : ids n = var n := rfl

theorem up_ids (n : ℕ) : up ids n = ids n := by cases n <;> rfl

@[simp] theorem subst_ids (t : Tm) : subst ids t = t := by
  induction t with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [ihf, iha]
  | lam A b ihA ihb => rw [subst_lam, ihA, subst_congr up_ids, ihb]
  | pi A B ihA ihB => rw [subst_pi, ihA, subst_congr up_ids, ihB]

@[simp] theorem subst_var_eta (t : Tm) : subst (fun n => var n) t = t := subst_ids t

/-- A renaming acts as the substitution by variables. -/
theorem rename_eq_subst (ρ : ℕ → ℕ) (t : Tm) : rename ρ t = subst (fun n => var (ρ n)) t := by
  induction t generalizing ρ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [ihf, iha]
  | lam A b ihA ihb =>
      have h : ∀ n, up (fun k => var (ρ k)) n = var (upr ρ n) := by
        intro n; cases n <;> rfl
      simp only [rename_lam, subst_lam, ihA, ihb, subst_congr h]
  | pi A B ihA ihB =>
      have h : ∀ n, up (fun k => var (ρ k)) n = var (upr ρ n) := by
        intro n; cases n <;> rfl
      simp only [rename_pi, subst_pi, ihA, ihB, subst_congr h]

theorem subst_rename (σ : ℕ → Tm) (ρ : ℕ → ℕ) (t : Tm) :
    subst σ (rename ρ t) = subst (fun n => σ (ρ n)) t := by
  induction t generalizing σ ρ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [ihf, iha]
  | lam A b ihA ihb =>
      have h : ∀ n, up σ (upr ρ n) = up (fun k => σ (ρ k)) n := by intro n; cases n <;> rfl
      simp only [rename_lam, subst_lam, ihA, ihb, subst_congr h]
  | pi A B ihA ihB =>
      have h : ∀ n, up σ (upr ρ n) = up (fun k => σ (ρ k)) n := by intro n; cases n <;> rfl
      simp only [rename_pi, subst_pi, ihA, ihB, subst_congr h]

theorem rename_up_subst (ρ : ℕ → ℕ) (σ : ℕ → Tm) (n : ℕ) :
    rename (upr ρ) (up σ n) = up (fun k => rename ρ (σ k)) n := by
  cases n with
  | zero => rfl
  | succ n =>
      simp only [up_succ, rename_rename]
      exact rename_congr (by intro k; rfl) (σ n)

theorem rename_subst (ρ : ℕ → ℕ) (σ : ℕ → Tm) (t : Tm) :
    rename ρ (subst σ t) = subst (fun n => rename ρ (σ n)) t := by
  induction t generalizing ρ σ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [ihf, iha]
  | lam A b ihA ihb =>
      simp only [rename_lam, subst_lam, ihA, ihb, subst_congr (rename_up_subst ρ σ)]
  | pi A B ihA ihB =>
      simp only [rename_pi, subst_pi, ihA, ihB, subst_congr (rename_up_subst ρ σ)]

theorem subst_up_subst (σ τ : ℕ → Tm) (n : ℕ) :
    subst (up σ) (up τ n) = up (fun k => subst σ (τ k)) n := by
  cases n with
  | zero => rfl
  | succ n => simp only [up_succ, subst_rename, rename_subst]

theorem subst_subst (σ τ : ℕ → Tm) (t : Tm) :
    subst σ (subst τ t) = subst (fun n => subst σ (τ n)) t := by
  induction t generalizing σ τ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [ihf, iha]
  | lam A b ihA ihb => simp only [subst_lam, ihA, ihb, subst_congr (subst_up_subst σ τ)]
  | pi A B ihA ihB => simp only [subst_pi, ihA, ihB, subst_congr (subst_up_subst σ τ)]

/-! ### Single substitution -/

/-- Extend a substitution by a term for the variable `0`. -/
def scons (a : Tm) (σ : ℕ → Tm) : ℕ → Tm
  | 0 => a
  | n + 1 => σ n

@[simp] theorem scons_zero (a : Tm) (σ : ℕ → Tm) : scons a σ 0 = a := rfl
@[simp] theorem scons_succ (a : Tm) (σ : ℕ → Tm) (n : ℕ) : scons a σ (n + 1) = σ n := rfl

/-- Substitution of the de Bruijn variable `0` by `a`, decrementing the other variables. -/
def inst (a : Tm) (t : Tm) : Tm := subst (scons a ids) t

@[inherit_doc] notation:max t "[" a "]" => inst a t

/-- Weakening: shift every variable up by one. -/
def shift (t : Tm) : Tm := rename Nat.succ t

@[simp] theorem inst_shift (a t : Tm) : (shift t)[a] = t := by
  simp only [shift, inst, subst_rename]
  exact subst_ids t

/-- The substitution lemma in the form the typing rules need. -/
theorem inst_subst (σ : ℕ → Tm) (a t : Tm) :
    subst σ (t[a]) = (subst (up σ) t)[subst σ a] := by
  simp only [inst, subst_subst]
  refine subst_congr ?_ t
  intro n
  cases n with
  | zero => rfl
  | succ n => simp [subst_rename]

theorem inst_rename (ρ : ℕ → ℕ) (a t : Tm) :
    rename ρ (t[a]) = (rename (upr ρ) t)[rename ρ a] := by
  simp only [inst, rename_subst, subst_rename]
  refine subst_congr ?_ t
  intro n
  cases n <;> rfl

/-! ### β-reduction -/

/-- One step of β-reduction. -/
inductive Step : Tm → Tm → Prop
  | beta (A b a : Tm) : Step (app (lam A b) a) (b[a])
  | appL {f f' : Tm} (a : Tm) : Step f f' → Step (app f a) (app f' a)
  | appR (f : Tm) {a a' : Tm} : Step a a' → Step (app f a) (app f a')
  | lamL {A A' : Tm} (b : Tm) : Step A A' → Step (lam A b) (lam A' b)
  | lamR (A : Tm) {b b' : Tm} : Step b b' → Step (lam A b) (lam A b')
  | piL {A A' : Tm} (B : Tm) : Step A A' → Step (pi A B) (pi A' B)
  | piR (A : Tm) {B B' : Tm} : Step B B' → Step (pi A B) (pi A B')

/-- Many-step β-reduction. -/
inductive Red : Tm → Tm → Prop
  | refl (t : Tm) : Red t t
  | tail {t u v : Tm} : Red t u → Step u v → Red t v

/-- β-conversion: the equivalence relation generated by β-reduction. -/
inductive Conv : Tm → Tm → Prop
  | refl (t : Tm) : Conv t t
  | step {t u v : Tm} : Conv t u → Step u v → Conv t v
  | stepInv {t u v : Tm} : Conv t u → Step v u → Conv t v

namespace Red

theorem single {t u : Tm} (h : Step t u) : Red t u := (Red.refl t).tail h

theorem trans {t u v : Tm} (h₁ : Red t u) (h₂ : Red u v) : Red t v := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact ih.tail hs

theorem head {t u v : Tm} (h : Step t u) (h' : Red u v) : Red t v := (single h).trans h'

/-- **Bridge to the abstract rewriting interface** (`Start/Rewriting.lean`): `Red` is the
reflexive–transitive closure of `Step`. -/
theorem iff_star {t u : Tm} : Red t u ↔ Rewriting.Star Step t u := by
  constructor
  · intro h
    induction h with
    | refl => exact Rewriting.Star.refl t
    | tail _ hs ih => exact ih.tail hs
  · intro h
    induction h with
    | refl => exact Red.refl t
    | tail _ hs ih => exact ih.tail hs

end Red

namespace Conv

theorem single {t u : Tm} (h : Step t u) : Conv t u := (Conv.refl t).step h

theorem ofRed {t u : Tm} (h : Red t u) : Conv t u := by
  induction h with
  | refl => exact Conv.refl _
  | tail _ hs ih => exact ih.step hs

theorem trans {t u v : Tm} (h₁ : Conv t u) (h₂ : Conv u v) : Conv t v := by
  induction h₂ with
  | refl => exact h₁
  | step _ hs ih => exact ih.step hs
  | stepInv _ hs ih => exact ih.stepInv hs

theorem symm {t u : Tm} (h : Conv t u) : Conv u t := by
  induction h with
  | refl => exact Conv.refl _
  | step _ hs ih => exact ((Conv.refl _).stepInv hs).trans ih
  | stepInv _ hs ih => exact ((Conv.refl _).step hs).trans ih

end Conv

/-! ### Congruence rules for reduction and conversion -/

theorem Red.appL {f f' : Tm} (a : Tm) (h : Red f f') : Red (Tm.app f a) (Tm.app f' a) := by
  induction h with
  | refl => exact Red.refl _
  | tail _ hs ih => exact ih.tail (Step.appL a hs)

theorem Red.appR (f : Tm) {a a' : Tm} (h : Red a a') : Red (Tm.app f a) (Tm.app f a') := by
  induction h with
  | refl => exact Red.refl _
  | tail _ hs ih => exact ih.tail (Step.appR f hs)

theorem Red.app {f f' a a' : Tm} (hf : Red f f') (ha : Red a a') :
    Red (Tm.app f a) (Tm.app f' a') :=
  (Red.appL a hf).trans (Red.appR f' ha)

theorem Red.lamL {A A' : Tm} (b : Tm) (h : Red A A') : Red (Tm.lam A b) (Tm.lam A' b) := by
  induction h with
  | refl => exact Red.refl _
  | tail _ hs ih => exact ih.tail (Step.lamL b hs)

theorem Red.lamR (A : Tm) {b b' : Tm} (h : Red b b') : Red (Tm.lam A b) (Tm.lam A b') := by
  induction h with
  | refl => exact Red.refl _
  | tail _ hs ih => exact ih.tail (Step.lamR A hs)

theorem Red.lam {A A' b b' : Tm} (hA : Red A A') (hb : Red b b') :
    Red (Tm.lam A b) (Tm.lam A' b') :=
  (Red.lamL b hA).trans (Red.lamR A' hb)

theorem Red.piL {A A' : Tm} (B : Tm) (h : Red A A') : Red (Tm.pi A B) (Tm.pi A' B) := by
  induction h with
  | refl => exact Red.refl _
  | tail _ hs ih => exact ih.tail (Step.piL B hs)

theorem Red.piR (A : Tm) {B B' : Tm} (h : Red B B') : Red (Tm.pi A B) (Tm.pi A B') := by
  induction h with
  | refl => exact Red.refl _
  | tail _ hs ih => exact ih.tail (Step.piR A hs)

theorem Red.pi {A A' B B' : Tm} (hA : Red A A') (hB : Red B B') :
    Red (Tm.pi A B) (Tm.pi A' B') :=
  (Red.piL B hA).trans (Red.piR A' hB)

theorem Conv.appL {f f' : Tm} (a : Tm) (h : Conv f f') : Conv (Tm.app f a) (Tm.app f' a) := by
  induction h with
  | refl => exact Conv.refl _
  | step _ hs ih => exact ih.step (Step.appL a hs)
  | stepInv _ hs ih => exact ih.stepInv (Step.appL a hs)

theorem Conv.appR (f : Tm) {a a' : Tm} (h : Conv a a') : Conv (Tm.app f a) (Tm.app f a') := by
  induction h with
  | refl => exact Conv.refl _
  | step _ hs ih => exact ih.step (Step.appR f hs)
  | stepInv _ hs ih => exact ih.stepInv (Step.appR f hs)

theorem Conv.app {f f' a a' : Tm} (hf : Conv f f') (ha : Conv a a') :
    Conv (Tm.app f a) (Tm.app f' a') :=
  (Conv.appL a hf).trans (Conv.appR f' ha)

theorem Conv.lamL {A A' : Tm} (b : Tm) (h : Conv A A') : Conv (Tm.lam A b) (Tm.lam A' b) := by
  induction h with
  | refl => exact Conv.refl _
  | step _ hs ih => exact ih.step (Step.lamL b hs)
  | stepInv _ hs ih => exact ih.stepInv (Step.lamL b hs)

theorem Conv.lamR (A : Tm) {b b' : Tm} (h : Conv b b') : Conv (Tm.lam A b) (Tm.lam A b') := by
  induction h with
  | refl => exact Conv.refl _
  | step _ hs ih => exact ih.step (Step.lamR A hs)
  | stepInv _ hs ih => exact ih.stepInv (Step.lamR A hs)

theorem Conv.lam {A A' b b' : Tm} (hA : Conv A A') (hb : Conv b b') :
    Conv (Tm.lam A b) (Tm.lam A' b') :=
  (Conv.lamL b hA).trans (Conv.lamR A' hb)

theorem Conv.piL {A A' : Tm} (B : Tm) (h : Conv A A') : Conv (Tm.pi A B) (Tm.pi A' B) := by
  induction h with
  | refl => exact Conv.refl _
  | step _ hs ih => exact ih.step (Step.piL B hs)
  | stepInv _ hs ih => exact ih.stepInv (Step.piL B hs)

theorem Conv.piR (A : Tm) {B B' : Tm} (h : Conv B B') : Conv (Tm.pi A B) (Tm.pi A B') := by
  induction h with
  | refl => exact Conv.refl _
  | step _ hs ih => exact ih.step (Step.piR A hs)
  | stepInv _ hs ih => exact ih.stepInv (Step.piR A hs)

theorem Conv.pi {A A' B B' : Tm} (hA : Conv A A') (hB : Conv B B') :
    Conv (Tm.pi A B) (Tm.pi A' B') :=
  (Conv.piL B hA).trans (Conv.piR A' hB)

/-! ### Reduction is stable under renaming and substitution -/

theorem Step.rename {t t' : Tm} (h : Step t t') (ρ : ℕ → ℕ) :
    Step (LambdaPi.rename ρ t) (LambdaPi.rename ρ t') := by
  induction h generalizing ρ with
  | beta A b a =>
      have hb := Step.beta (LambdaPi.rename ρ A) (LambdaPi.rename (upr ρ) b)
        (LambdaPi.rename ρ a)
      simpa [inst_rename] using hb
  | appL a _ ih => exact Step.appL _ (ih ρ)
  | appR f _ ih => exact Step.appR _ (ih ρ)
  | lamL b _ ih => exact Step.lamL _ (ih ρ)
  | lamR A _ ih => exact Step.lamR _ (ih (upr ρ))
  | piL B _ ih => exact Step.piL _ (ih ρ)
  | piR A _ ih => exact Step.piR _ (ih (upr ρ))

theorem Step.subst {t t' : Tm} (h : Step t t') (σ : ℕ → Tm) :
    Step (LambdaPi.subst σ t) (LambdaPi.subst σ t') := by
  induction h generalizing σ with
  | beta A b a =>
      have hb := Step.beta (LambdaPi.subst σ A) (LambdaPi.subst (up σ) b) (LambdaPi.subst σ a)
      simpa [inst_subst] using hb
  | appL a _ ih => exact Step.appL _ (ih σ)
  | appR f _ ih => exact Step.appR _ (ih σ)
  | lamL b _ ih => exact Step.lamL _ (ih σ)
  | lamR A _ ih => exact Step.lamR _ (ih (up σ))
  | piL B _ ih => exact Step.piL _ (ih σ)
  | piR A _ ih => exact Step.piR _ (ih (up σ))

theorem Red.subst {t t' : Tm} (h : Red t t') (σ : ℕ → Tm) :
    Red (LambdaPi.subst σ t) (LambdaPi.subst σ t') := by
  induction h with
  | refl => exact Red.refl _
  | tail _ hs ih => exact ih.tail (hs.subst σ)

theorem Conv.subst {t t' : Tm} (h : Conv t t') (σ : ℕ → Tm) :
    Conv (LambdaPi.subst σ t) (LambdaPi.subst σ t') := by
  induction h with
  | refl => exact Conv.refl _
  | step _ hs ih => exact ih.step (hs.subst σ)
  | stepInv _ hs ih => exact ih.stepInv (hs.subst σ)

theorem Red.rename {t t' : Tm} (h : Red t t') (ρ : ℕ → ℕ) :
    Red (LambdaPi.rename ρ t) (LambdaPi.rename ρ t') := by
  induction h with
  | refl => exact Red.refl _
  | tail _ hs ih => exact ih.tail (hs.rename ρ)

theorem Conv.rename {t t' : Tm} (h : Conv t t') (ρ : ℕ → ℕ) :
    Conv (LambdaPi.rename ρ t) (LambdaPi.rename ρ t') := by
  induction h with
  | refl => exact Conv.refl _
  | step _ hs ih => exact ih.step (hs.rename ρ)
  | stepInv _ hs ih => exact ih.stepInv (hs.rename ρ)

/-! ### Parallel reduction and confluence -/

/-- Takahashi's parallel reduction. -/
inductive Par : Tm → Tm → Prop
  | var (n : ℕ) : Par (var n) (var n)
  | sort (s : Srt) : Par (sort s) (sort s)
  | app {f f' a a' : Tm} : Par f f' → Par a a' → Par (Tm.app f a) (Tm.app f' a')
  | lam {A A' b b' : Tm} : Par A A' → Par b b' → Par (Tm.lam A b) (Tm.lam A' b')
  | pi {A A' B B' : Tm} : Par A A' → Par B B' → Par (Tm.pi A B) (Tm.pi A' B')
  | beta {A b b' a a' : Tm} : Par b b' → Par a a' → Par (Tm.app (Tm.lam A b) a) (b'[a'])

theorem Par.refl (t : Tm) : Par t t := by
  induction t with
  | var n => exact Par.var n
  | sort s => exact Par.sort s
  | app f a ihf iha => exact ihf.app iha
  | lam A b ihA ihb => exact ihA.lam ihb
  | pi A B ihA ihB => exact ihA.pi ihB

theorem Par.rename {t t' : Tm} (h : Par t t') (ρ : ℕ → ℕ) :
    Par (LambdaPi.rename ρ t) (LambdaPi.rename ρ t') := by
  induction h generalizing ρ with
  | var n => exact Par.var _
  | sort s => exact Par.sort _
  | app _ _ ihf iha => exact (ihf ρ).app (iha ρ)
  | lam _ _ ihA ihb => exact (ihA ρ).lam (ihb (upr ρ))
  | pi _ _ ihA ihB => exact (ihA ρ).pi (ihB (upr ρ))
  | @beta A b b' a a' _ _ ihb iha =>
      have hb := Par.beta (A := LambdaPi.rename ρ A) (ihb (upr ρ)) (iha ρ)
      simpa [inst_rename] using hb

/-- A substitution reduces pointwise. -/
def ParSub (σ σ' : ℕ → Tm) : Prop := ∀ n, Par (σ n) (σ' n)

theorem ParSub.up {σ σ' : ℕ → Tm} (h : ParSub σ σ') : ParSub (LambdaPi.up σ) (LambdaPi.up σ') := by
  intro n
  cases n with
  | zero => exact Par.var 0
  | succ n => exact (h n).rename Nat.succ

theorem Par.substs {t t' : Tm} (h : Par t t') {σ σ' : ℕ → Tm} (hσ : ParSub σ σ') :
    Par (LambdaPi.subst σ t) (LambdaPi.subst σ' t') := by
  induction h generalizing σ σ' with
  | var n => exact hσ n
  | sort s => exact Par.sort _
  | app _ _ ihf iha => exact (ihf hσ).app (iha hσ)
  | lam _ _ ihA ihb => exact (ihA hσ).lam (ihb hσ.up)
  | pi _ _ ihA ihB => exact (ihA hσ).pi (ihB hσ.up)
  | @beta A b b' a a' _ _ ihb iha =>
      have hb := Par.beta (A := LambdaPi.subst σ A) (ihb hσ.up) (iha hσ)
      simpa [inst_subst] using hb

theorem ParSub.scons {a a' : Tm} (h : Par a a') {σ σ' : ℕ → Tm} (hσ : ParSub σ σ') :
    ParSub (LambdaPi.scons a σ) (LambdaPi.scons a' σ') := by
  intro n
  cases n with
  | zero => exact h
  | succ n => exact hσ n

theorem ParSub.ids : ParSub LambdaPi.ids LambdaPi.ids := fun n => Par.var n

theorem Par.inst {b b' a a' : Tm} (hb : Par b b') (ha : Par a a') : Par (b[a]) (b'[a']) :=
  hb.substs (ParSub.scons ha ParSub.ids)

theorem Step.par {t t' : Tm} (h : Step t t') : Par t t' := by
  induction h with
  | beta A b a => exact Par.beta (Par.refl b) (Par.refl a)
  | appL a _ ih => exact ih.app (Par.refl a)
  | appR f _ ih => exact (Par.refl f).app ih
  | lamL b _ ih => exact ih.lam (Par.refl b)
  | lamR A _ ih => exact (Par.refl A).lam ih
  | piL B _ ih => exact ih.pi (Par.refl B)
  | piR A _ ih => exact (Par.refl A).pi ih

theorem Par.red {t t' : Tm} (h : Par t t') : Red t t' := by
  induction h with
  | var n => exact Red.refl _
  | sort s => exact Red.refl _
  | app _ _ ihf iha => exact Red.app ihf iha
  | lam _ _ ihA ihb => exact Red.lam ihA ihb
  | pi _ _ ihA ihB => exact Red.pi ihA ihB
  | @beta A b b' a a' _ _ ihb iha =>
      exact Red.trans (Red.app (Red.lamR A ihb) iha) (Red.single (Step.beta A b' a'))

/-- Takahashi's complete development: contract every β-redex present in the term. -/
def rho : Tm → Tm
  | var n => var n
  | sort s => sort s
  | app (lam _ b) a => (rho b)[rho a]
  | app f a => app (rho f) (rho a)
  | lam A b => lam (rho A) (rho b)
  | pi A B => pi (rho A) (rho B)

@[simp] theorem rho_var (n : ℕ) : rho (var n) = var n := rfl
@[simp] theorem rho_sort (s : Srt) : rho (sort s) = sort s := rfl
@[simp] theorem rho_lam (A b : Tm) : rho (lam A b) = lam (rho A) (rho b) := rfl
@[simp] theorem rho_pi (A B : Tm) : rho (pi A B) = pi (rho A) (rho B) := rfl
@[simp] theorem rho_app_lam (A b a : Tm) : rho (app (lam A b) a) = (rho b)[rho a] := rfl
@[simp] theorem rho_app_var (n : ℕ) (a : Tm) :
    rho (app (var n) a) = app (var n) (rho a) := rfl
@[simp] theorem rho_app_sort (s : Srt) (a : Tm) :
    rho (app (sort s) a) = app (sort s) (rho a) := rfl
@[simp] theorem rho_app_app (f g a : Tm) :
    rho (app (app f g) a) = app (rho (app f g)) (rho a) := rfl
@[simp] theorem rho_app_pi (A B a : Tm) :
    rho (app (pi A B) a) = app (pi (rho A) (rho B)) (rho a) := rfl

theorem Par.triangle {t t' : Tm} (h : Par t t') : Par t' (rho t) := by
  induction h with
  | var n => exact Par.var n
  | sort s => exact Par.sort s
  | @app f f' a a' hf _ ihf iha =>
      cases f with
      | lam A b =>
          cases hf with
          | @lam _ A₂ _ b₂ _ _ =>
              cases ihf with
              | @lam _ _ _ _ _ hb' => exact Par.beta hb' iha
      | var n => simpa using ihf.app iha
      | sort s => simpa using ihf.app iha
      | app g c => simpa using ihf.app iha
      | pi A B => simpa using ihf.app iha
  | lam _ _ ihA ihb => exact ihA.lam ihb
  | pi _ _ ihA ihB => exact ihA.pi ihB
  | @beta A b b' a a' _ _ ihb iha => exact ihb.inst iha

theorem Par.diamond {t t₁ t₂ : Tm} (h₁ : Par t t₁) (h₂ : Par t t₂) :
    ∃ u, Par t₁ u ∧ Par t₂ u :=
  ⟨rho t, h₁.triangle, h₂.triangle⟩

/-- Many-step parallel reduction. -/
inductive Pars : Tm → Tm → Prop
  | refl (t : Tm) : Pars t t
  | tail {t u v : Tm} : Pars t u → Par u v → Pars t v

theorem Pars.trans {t u v : Tm} (h₁ : Pars t u) (h₂ : Pars u v) : Pars t v := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact ih.tail hs

theorem Pars.ofRed {t u : Tm} (h : Red t u) : Pars t u := by
  induction h with
  | refl => exact Pars.refl _
  | tail _ hs ih => exact ih.tail hs.par

theorem Pars.red {t u : Tm} (h : Pars t u) : Red t u := by
  induction h with
  | refl => exact Red.refl _
  | tail _ hs ih => exact ih.trans hs.red

/-- The bridge for parallel reduction: `Pars` is the closure of `Par`. -/
theorem Pars.iff_star {t u : Tm} : Pars t u ↔ Rewriting.Star Par t u := by
  constructor
  · intro h
    induction h with
    | refl => exact Rewriting.Star.refl t
    | tail _ hs ih => exact ih.tail hs
  · intro h
    induction h with
    | refl => exact Pars.refl t
    | tail _ hs ih => exact ih.tail hs

theorem Pars.strip {t t₁ t₂ : Tm} (h₁ : Par t t₁) (h₂ : Pars t t₂) :
    ∃ u, Pars t₁ u ∧ Par t₂ u := by
  obtain ⟨u, hu₁, hu₂⟩ :=
    Rewriting.strip (fun _ _ _ k₁ k₂ => Par.diamond k₁ k₂) h₁ (Pars.iff_star.1 h₂)
  exact ⟨u, Pars.iff_star.2 hu₁, hu₂⟩

theorem Pars.confluent {t t₁ t₂ : Tm} (h₁ : Pars t t₁) (h₂ : Pars t t₂) :
    ∃ u, Pars t₁ u ∧ Pars t₂ u := by
  obtain ⟨u, hu₁, hu₂⟩ :=
    Rewriting.confluent_of_diamond (fun _ _ _ k₁ k₂ => Par.diamond k₁ k₂)
      (Pars.iff_star.1 h₁) (Pars.iff_star.1 h₂)
  exact ⟨u, Pars.iff_star.2 hu₁, Pars.iff_star.2 hu₂⟩

/-- β-reduction of `λΠ` is confluent, in the vocabulary of `Start/Rewriting.lean`: parallel
reduction lies between `Step` and `Red` and has the diamond property. -/
theorem confluent_step : Rewriting.Confluent Step :=
  Rewriting.confluent_of_diamond_of_between (fun _ _ _ k₁ k₂ => Par.diamond k₁ k₂)
    Step.par (fun h => Red.iff_star.1 h.red)

/-- **Church–Rosser**: β-reduction is confluent. -/
theorem church_rosser {t t₁ t₂ : Tm} (h₁ : Red t t₁) (h₂ : Red t t₂) :
    ∃ u, Red t₁ u ∧ Red t₂ u := by
  obtain ⟨u, hu₁, hu₂⟩ := confluent_step (Red.iff_star.1 h₁) (Red.iff_star.1 h₂)
  exact ⟨u, Red.iff_star.2 hu₁, Red.iff_star.2 hu₂⟩

/-- The bridge for conversion: `Conv` is the conversion generated by `Step`. -/
theorem Conv.iff_conv {t u : Tm} : Conv t u ↔ Rewriting.Conv Step t u := by
  constructor
  · intro h
    induction h with
    | refl => exact Rewriting.Conv.refl t
    | step _ hs ih => exact Rewriting.Star.tail ih (Or.inl hs)
    | stepInv _ hs ih => exact Rewriting.Star.tail ih (Or.inr hs)
  · intro h
    induction h with
    | refl => exact Conv.refl t
    | tail _ hs ih =>
        rcases hs with hs | hs
        · exact Conv.step ih hs
        · exact Conv.stepInv ih hs

/-- Conversion is exactly joinability, an instance of
`Rewriting.conv_iff_joins_of_confluent`. -/
theorem Conv.church_rosser {t u : Tm} (h : Conv t u) : ∃ v, Red t v ∧ Red u v := by
  obtain ⟨v, hv₁, hv₂⟩ :=
    (Rewriting.conv_iff_joins_of_confluent confluent_step).1 (Conv.iff_conv.1 h)
  exact ⟨v, Red.iff_star.2 hv₁, Red.iff_star.2 hv₂⟩

theorem Conv.ofJoin {t u v : Tm} (h₁ : Red t v) (h₂ : Red u v) : Conv t u :=
  (Conv.ofRed h₁).trans (Conv.ofRed h₂).symm

/-- Reduction in the argument of a single substitution. -/
theorem Red.instArg (t : Tm) {a a' : Tm} (h : Red a a') : Red (t[a]) (t[a']) := by
  induction h with
  | refl => exact Red.refl _
  | tail _ hs ih => exact ih.trans ((Par.inst (Par.refl t) hs.par).red)

/-- Conversion in the argument of a single substitution. -/
theorem Conv.instArg (t : Tm) {a a' : Tm} (h : Conv a a') : Conv (t[a]) (t[a']) := by
  obtain ⟨v, h₁, h₂⟩ := h.church_rosser
  exact Conv.ofJoin (Red.instArg t h₁) (Red.instArg t h₂)

/-! ### Shape analysis of reducts -/

theorem Red.sort_inv {s : Srt} {t : Tm} (h : Red (Tm.sort s) t) : t = Tm.sort s := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; cases hs

theorem Red.var_inv {n : ℕ} {t : Tm} (h : Red (Tm.var n) t) : t = Tm.var n := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; cases hs

theorem Red.pi_inv {A B t : Tm} (h : Red (Tm.pi A B) t) :
    ∃ A' B', t = Tm.pi A' B' ∧ Red A A' ∧ Red B B' := by
  induction h with
  | refl => exact ⟨A, B, rfl, Red.refl _, Red.refl _⟩
  | @tail u v _ hs ih =>
      obtain ⟨A', B', rfl, hA, hB⟩ := ih
      cases hs with
      | piL _ h => exact ⟨_, B', rfl, hA.tail h, hB⟩
      | piR _ h => exact ⟨A', _, rfl, hA, hB.tail h⟩

/-- Injectivity of `Π` for conversion, first component. -/
theorem pi_inj_left {A B A' B' : Tm} (h : Conv (Tm.pi A B) (Tm.pi A' B')) : Conv A A' := by
  obtain ⟨v, hv₁, hv₂⟩ := h.church_rosser
  obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := hv₁.pi_inv
  obtain ⟨A₂, B₂, heq, hA₂, hB₂⟩ := hv₂.pi_inv
  cases heq
  exact Conv.ofJoin hA₁ hA₂

/-- Injectivity of `Π` for conversion, second component. -/
theorem pi_inj_right {A B A' B' : Tm} (h : Conv (Tm.pi A B) (Tm.pi A' B')) : Conv B B' := by
  obtain ⟨v, hv₁, hv₂⟩ := h.church_rosser
  obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := hv₁.pi_inv
  obtain ⟨A₂, B₂, heq, hA₂, hB₂⟩ := hv₂.pi_inv
  cases heq
  exact Conv.ofJoin hB₁ hB₂

/-- Distinct sorts are not convertible. -/
theorem sort_conv_inj {s s' : Srt} (h : Conv (Tm.sort s) (Tm.sort s')) : s = s' := by
  obtain ⟨v, hv₁, hv₂⟩ := h.church_rosser
  have h₁ := hv₁.sort_inv
  have h₂ := hv₂.sort_inv
  rw [h₁] at h₂
  exact Tm.sort.inj h₂

/-- A sort is never convertible to a product. -/
theorem not_conv_sort_pi {s : Srt} {A B : Tm} (h : Conv (Tm.sort s) (Tm.pi A B)) : False := by
  obtain ⟨v, hv₁, hv₂⟩ := h.church_rosser
  obtain ⟨A', B', rfl, _, _⟩ := hv₂.pi_inv
  exact absurd hv₁.sort_inv (by simp)

/-- A variable is never convertible to a product. -/
theorem not_conv_var_pi {n : ℕ} {A B : Tm} (h : Conv (Tm.var n) (Tm.pi A B)) : False := by
  obtain ⟨v, hv₁, hv₂⟩ := h.church_rosser
  obtain ⟨A', B', rfl, _, _⟩ := hv₂.pi_inv
  exact absurd hv₁.var_inv (by simp)

/-- A variable is never convertible to a sort. -/
theorem not_conv_var_sort {n : ℕ} {s : Srt} (h : Conv (Tm.var n) (Tm.sort s)) : False := by
  obtain ⟨v, hv₁, hv₂⟩ := h.church_rosser
  have hv := hv₂.sort_inv
  rw [hv] at hv₁
  exact absurd hv₁.var_inv (by simp)

end LambdaPi
