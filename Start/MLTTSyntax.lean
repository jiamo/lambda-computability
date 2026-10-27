/-
**Martin-Löf type theory: syntax** — milestone M30 (`M30-MLTT-DECL`).

The raw terms of Martin-Löf type theory with dependent functions, a predicative hierarchy of
Russell universes `U 0 : U 1 : U 2 : …`, natural numbers with their eliminator, and the empty
type with its eliminator, in de Bruijn notation.  Abstractions carry no domain annotation
(Curry style), so that η-conversion is not entangled with annotations as in the Church-style
`λΠ` of `Start/LambdaPiEta.lean`.

* `MLTT.Tm` — the terms; `natrec P z s n` binds one variable in the motive `P` and two in the
  step `s` (the predecessor `var 1` and the induction hypothesis `var 0`);
* `MLTT.rename`, `MLTT.subst` — parallel renaming and substitution, with the usual algebra
  (`rename_rename`, `subst_rename`, `rename_subst`, `subst_subst`, `subst_ids`);
* `MLTT.inst` (`t[a]`) and `MLTT.inst2` (`t[a, b]`) — substitution of the last one and two
  variables, with the commutations the typing rules use.
-/

import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

/-- **Raw terms** of Martin-Löf type theory. -/
inductive Tm where
  | var : ℕ → Tm
  /-- The universe `U l`. -/
  | univ : ℕ → Tm
  /-- The dependent function type `Π A B`; `B` binds one variable. -/
  | pi : Tm → Tm → Tm
  /-- An abstraction `λ b`; `b` binds one variable. -/
  | lam : Tm → Tm
  | app : Tm → Tm → Tm
  | nat : Tm
  | zero : Tm
  | succ : Tm → Tm
  /-- `natrec P z s n`; `P` binds one variable, `s` binds two (`var 1` the predecessor, `var 0`
  the induction hypothesis). -/
  | natrec : Tm → Tm → Tm → Tm → Tm
  | empty : Tm
  /-- `emptyrec P e`, eliminating `e : ⊥` into the type `P`. -/
  | emptyrec : Tm → Tm → Tm
  deriving DecidableEq, Repr

open Tm

/-! ### Renaming -/

/-- Lift a renaming under a binder. -/
def upr (ρ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ρ n + 1

@[simp] theorem upr_zero (ρ : ℕ → ℕ) : upr ρ 0 = 0 := rfl
@[simp] theorem upr_succ (ρ : ℕ → ℕ) (n : ℕ) : upr ρ (n + 1) = ρ n + 1 := rfl

/-- Parallel renaming. -/
def rename (ρ : ℕ → ℕ) : Tm → Tm
  | var n => var (ρ n)
  | univ l => univ l
  | pi A B => pi (rename ρ A) (rename (upr ρ) B)
  | lam b => lam (rename (upr ρ) b)
  | app f a => app (rename ρ f) (rename ρ a)
  | nat => nat
  | zero => zero
  | succ n => succ (rename ρ n)
  | natrec P z s n => natrec (rename (upr ρ) P) (rename ρ z) (rename (upr (upr ρ)) s) (rename ρ n)
  | empty => empty
  | emptyrec P e => emptyrec (rename ρ P) (rename ρ e)

@[simp] theorem rename_var (ρ : ℕ → ℕ) (n : ℕ) : rename ρ (var n) = var (ρ n) := rfl
@[simp] theorem rename_univ (ρ : ℕ → ℕ) (l : ℕ) : rename ρ (univ l) = univ l := rfl
@[simp] theorem rename_pi (ρ : ℕ → ℕ) (A B : Tm) :
    rename ρ (pi A B) = pi (rename ρ A) (rename (upr ρ) B) := rfl
@[simp] theorem rename_lam (ρ : ℕ → ℕ) (b : Tm) : rename ρ (lam b) = lam (rename (upr ρ) b) := rfl
@[simp] theorem rename_app (ρ : ℕ → ℕ) (f a : Tm) :
    rename ρ (app f a) = app (rename ρ f) (rename ρ a) := rfl
@[simp] theorem rename_nat (ρ : ℕ → ℕ) : rename ρ nat = nat := rfl
@[simp] theorem rename_zero (ρ : ℕ → ℕ) : rename ρ zero = zero := rfl
@[simp] theorem rename_succ (ρ : ℕ → ℕ) (n : Tm) : rename ρ (succ n) = succ (rename ρ n) := rfl
@[simp] theorem rename_natrec (ρ : ℕ → ℕ) (P z s n : Tm) :
    rename ρ (natrec P z s n) =
      natrec (rename (upr ρ) P) (rename ρ z) (rename (upr (upr ρ)) s) (rename ρ n) := rfl
@[simp] theorem rename_empty (ρ : ℕ → ℕ) : rename ρ empty = empty := rfl
@[simp] theorem rename_emptyrec (ρ : ℕ → ℕ) (P e : Tm) :
    rename ρ (emptyrec P e) = emptyrec (rename ρ P) (rename ρ e) := rfl

theorem upr_congr {ρ ρ' : ℕ → ℕ} (h : ∀ n, ρ n = ρ' n) : ∀ n, upr ρ n = upr ρ' n
  | 0 => rfl
  | n + 1 => by simp [h n]

theorem rename_congr {ρ ρ' : ℕ → ℕ} (h : ∀ n, ρ n = ρ' n) (t : Tm) : rename ρ t = rename ρ' t := by
  induction t generalizing ρ ρ' with
  | var n => simp [h n]
  | univ l => rfl
  | pi A B ihA ihB => simp [ihA h, ihB (upr_congr h)]
  | lam b ih => simp [ih (upr_congr h)]
  | app f a ihf iha => simp [ihf h, iha h]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [ih h]
  | natrec P z s n ihP ihz ihs ihn =>
      simp [ihP (upr_congr h), ihz h, ihs (upr_congr (upr_congr h)), ihn h]
  | empty => rfl
  | emptyrec P e ihP ihe => simp [ihP h, ihe h]

theorem upr_id : ∀ n, upr id n = id n
  | 0 => rfl
  | _ + 1 => rfl

@[simp] theorem rename_id (t : Tm) : rename id t = t := by
  induction t with
  | var n => rfl
  | univ l => rfl
  | pi A B ihA ihB => rw [rename_pi, ihA, rename_congr upr_id, ihB]
  | lam b ih => rw [rename_lam, rename_congr upr_id, ih]
  | app f a ihf iha => simp [ihf, iha]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [ih]
  | natrec P z s n ihP ihz ihs ihn =>
      rw [rename_natrec, rename_congr upr_id P, ihP, ihz, ihn,
        rename_congr (upr_congr upr_id) s, rename_congr upr_id s, ihs]
  | empty => rfl
  | emptyrec P e ihP ihe => simp [ihP, ihe]

theorem upr_comp (ρ ρ' : ℕ → ℕ) : ∀ n, upr ρ (upr ρ' n) = upr (fun k => ρ (ρ' k)) n
  | 0 => rfl
  | _ + 1 => rfl

theorem rename_rename (ρ ρ' : ℕ → ℕ) (t : Tm) :
    rename ρ (rename ρ' t) = rename (fun n => ρ (ρ' n)) t := by
  induction t generalizing ρ ρ' with
  | var n => rfl
  | univ l => rfl
  | pi A B ihA ihB => simp [ihA, ihB, rename_congr (upr_comp ρ ρ')]
  | lam b ih => simp [ih, rename_congr (upr_comp ρ ρ')]
  | app f a ihf iha => simp [ihf, iha]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [ih]
  | natrec P z s n ihP ihz ihs ihn =>
      simp only [rename_natrec, ihP, ihz, ihs, ihn]
      rw [rename_congr (upr_comp ρ ρ') P, rename_congr (fun k =>
        (upr_comp (upr ρ) (upr ρ') k).trans (upr_congr (upr_comp ρ ρ') k)) s]
  | empty => rfl
  | emptyrec P e ihP ihe => simp [ihP, ihe]

/-! ### Substitution -/

/-- Lift a substitution under a binder. -/
def up (σ : ℕ → Tm) : ℕ → Tm
  | 0 => var 0
  | n + 1 => rename Nat.succ (σ n)

@[simp] theorem up_zero (σ : ℕ → Tm) : up σ 0 = var 0 := rfl
@[simp] theorem up_succ (σ : ℕ → Tm) (n : ℕ) : up σ (n + 1) = rename Nat.succ (σ n) := rfl

/-- Parallel substitution. -/
def subst (σ : ℕ → Tm) : Tm → Tm
  | var n => σ n
  | univ l => univ l
  | pi A B => pi (subst σ A) (subst (up σ) B)
  | lam b => lam (subst (up σ) b)
  | app f a => app (subst σ f) (subst σ a)
  | nat => nat
  | zero => zero
  | succ n => succ (subst σ n)
  | natrec P z s n => natrec (subst (up σ) P) (subst σ z) (subst (up (up σ)) s) (subst σ n)
  | empty => empty
  | emptyrec P e => emptyrec (subst σ P) (subst σ e)

@[simp] theorem subst_var (σ : ℕ → Tm) (n : ℕ) : subst σ (var n) = σ n := rfl
@[simp] theorem subst_univ (σ : ℕ → Tm) (l : ℕ) : subst σ (univ l) = univ l := rfl
@[simp] theorem subst_pi (σ : ℕ → Tm) (A B : Tm) :
    subst σ (pi A B) = pi (subst σ A) (subst (up σ) B) := rfl
@[simp] theorem subst_lam (σ : ℕ → Tm) (b : Tm) : subst σ (lam b) = lam (subst (up σ) b) := rfl
@[simp] theorem subst_app (σ : ℕ → Tm) (f a : Tm) :
    subst σ (app f a) = app (subst σ f) (subst σ a) := rfl
@[simp] theorem subst_nat (σ : ℕ → Tm) : subst σ nat = nat := rfl
@[simp] theorem subst_zero (σ : ℕ → Tm) : subst σ zero = zero := rfl
@[simp] theorem subst_succ (σ : ℕ → Tm) (n : Tm) : subst σ (succ n) = succ (subst σ n) := rfl
@[simp] theorem subst_natrec (σ : ℕ → Tm) (P z s n : Tm) :
    subst σ (natrec P z s n) =
      natrec (subst (up σ) P) (subst σ z) (subst (up (up σ)) s) (subst σ n) := rfl
@[simp] theorem subst_empty (σ : ℕ → Tm) : subst σ empty = empty := rfl
@[simp] theorem subst_emptyrec (σ : ℕ → Tm) (P e : Tm) :
    subst σ (emptyrec P e) = emptyrec (subst σ P) (subst σ e) := rfl

theorem up_congr {σ σ' : ℕ → Tm} (h : ∀ n, σ n = σ' n) : ∀ n, up σ n = up σ' n
  | 0 => rfl
  | n + 1 => by simp [h n]

theorem subst_congr {σ σ' : ℕ → Tm} (h : ∀ n, σ n = σ' n) (t : Tm) : subst σ t = subst σ' t := by
  induction t generalizing σ σ' with
  | var n => simp [h n]
  | univ l => rfl
  | pi A B ihA ihB => simp [ihA h, ihB (up_congr h)]
  | lam b ih => simp [ih (up_congr h)]
  | app f a ihf iha => simp [ihf h, iha h]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [ih h]
  | natrec P z s n ihP ihz ihs ihn =>
      simp [ihP (up_congr h), ihz h, ihs (up_congr (up_congr h)), ihn h]
  | empty => rfl
  | emptyrec P e ihP ihe => simp [ihP h, ihe h]

/-- The identity substitution. -/
def ids : ℕ → Tm := fun n => var n

@[simp] theorem ids_apply (n : ℕ) : ids n = var n := rfl

theorem up_ids : ∀ n, up ids n = ids n
  | 0 => rfl
  | _ + 1 => rfl

@[simp] theorem subst_ids (t : Tm) : subst ids t = t := by
  induction t with
  | var n => rfl
  | univ l => rfl
  | pi A B ihA ihB => rw [subst_pi, ihA, subst_congr up_ids, ihB]
  | lam b ih => rw [subst_lam, subst_congr up_ids, ih]
  | app f a ihf iha => simp [ihf, iha]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [ih]
  | natrec P z s n ihP ihz ihs ihn =>
      rw [subst_natrec, subst_congr up_ids P, ihP, ihz, ihn,
        subst_congr (up_congr up_ids) s, subst_congr up_ids s, ihs]
  | empty => rfl
  | emptyrec P e ihP ihe => simp [ihP, ihe]

@[simp] theorem subst_var_eta (t : Tm) : subst (fun n => var n) t = t := subst_ids t

theorem up_rename_eq (ρ : ℕ → ℕ) : ∀ n, up (fun k => var (ρ k)) n = var (upr ρ n)
  | 0 => rfl
  | _ + 1 => rfl

theorem rename_eq_subst (ρ : ℕ → ℕ) (t : Tm) : rename ρ t = subst (fun n => var (ρ n)) t := by
  induction t generalizing ρ with
  | var n => rfl
  | univ l => rfl
  | pi A B ihA ihB => simp [ihA, ihB, subst_congr (up_rename_eq ρ)]
  | lam b ih => simp [ih, subst_congr (up_rename_eq ρ)]
  | app f a ihf iha => simp [ihf, iha]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [ih]
  | natrec P z s n ihP ihz ihs ihn =>
      have h2 : ∀ n, up (up fun k => var (ρ k)) n = var (upr (upr ρ) n) := by
        intro n
        rw [up_congr (up_rename_eq ρ) n]
        exact up_rename_eq (upr ρ) n
      simp [ihP, ihz, ihs, ihn, subst_congr (up_rename_eq ρ), subst_congr h2]
  | empty => rfl
  | emptyrec P e ihP ihe => simp [ihP, ihe]

theorem up_upr (σ : ℕ → Tm) (ρ : ℕ → ℕ) : ∀ n, up σ (upr ρ n) = up (fun k => σ (ρ k)) n
  | 0 => rfl
  | _ + 1 => rfl

theorem subst_rename (σ : ℕ → Tm) (ρ : ℕ → ℕ) (t : Tm) :
    subst σ (rename ρ t) = subst (fun n => σ (ρ n)) t := by
  induction t generalizing σ ρ with
  | var n => rfl
  | univ l => rfl
  | pi A B ihA ihB => simp [ihA, ihB, subst_congr (up_upr σ ρ)]
  | lam b ih => simp [ih, subst_congr (up_upr σ ρ)]
  | app f a ihf iha => simp [ihf, iha]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [ih]
  | natrec P z s n ihP ihz ihs ihn =>
      have h2 : ∀ n, up (up σ) (upr (upr ρ) n) = up (up fun k => σ (ρ k)) n := by
        intro n
        rw [up_upr]
        exact up_congr (up_upr σ ρ) n
      simp [ihP, ihz, ihs, ihn, subst_congr (up_upr σ ρ), subst_congr h2]
  | empty => rfl
  | emptyrec P e ihP ihe => simp [ihP, ihe]

theorem rename_up (ρ : ℕ → ℕ) (σ : ℕ → Tm) :
    ∀ n, rename (upr ρ) (up σ n) = up (fun k => rename ρ (σ k)) n
  | 0 => rfl
  | n + 1 => by
      simp only [up_succ, rename_rename]
      exact rename_congr (fun _ => rfl) (σ n)

theorem rename_subst (ρ : ℕ → ℕ) (σ : ℕ → Tm) (t : Tm) :
    rename ρ (subst σ t) = subst (fun n => rename ρ (σ n)) t := by
  induction t generalizing ρ σ with
  | var n => rfl
  | univ l => rfl
  | pi A B ihA ihB => simp [ihA, ihB, subst_congr (rename_up ρ σ)]
  | lam b ih => simp [ih, subst_congr (rename_up ρ σ)]
  | app f a ihf iha => simp [ihf, iha]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [ih]
  | natrec P z s n ihP ihz ihs ihn =>
      have h2 : ∀ n, rename (upr (upr ρ)) (up (up σ) n) = up (up fun k => rename ρ (σ k)) n := by
        intro n
        rw [rename_up]
        exact up_congr (rename_up ρ σ) n
      simp [ihP, ihz, ihs, ihn, subst_congr (rename_up ρ σ), subst_congr h2]
  | empty => rfl
  | emptyrec P e ihP ihe => simp [ihP, ihe]

theorem subst_up (σ τ : ℕ → Tm) : ∀ n, subst (up σ) (up τ n) = up (fun k => subst σ (τ k)) n
  | 0 => rfl
  | n + 1 => by simp only [up_succ, subst_rename, rename_subst]

theorem subst_subst (σ τ : ℕ → Tm) (t : Tm) :
    subst σ (subst τ t) = subst (fun n => subst σ (τ n)) t := by
  induction t generalizing σ τ with
  | var n => rfl
  | univ l => rfl
  | pi A B ihA ihB => simp [ihA, ihB, subst_congr (subst_up σ τ)]
  | lam b ih => simp [ih, subst_congr (subst_up σ τ)]
  | app f a ihf iha => simp [ihf, iha]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [ih]
  | natrec P z s n ihP ihz ihs ihn =>
      have h2 : ∀ n, subst (up (up σ)) (up (up τ) n) = up (up fun k => subst σ (τ k)) n := by
        intro n
        rw [subst_up]
        exact up_congr (subst_up σ τ) n
      simp [ihP, ihz, ihs, ihn, subst_congr (subst_up σ τ), subst_congr h2]
  | empty => rfl
  | emptyrec P e ihP ihe => simp [ihP, ihe]

/-! ### Single and double substitution -/

/-- Extend a substitution by a term for the variable `0`. -/
def scons (a : Tm) (σ : ℕ → Tm) : ℕ → Tm
  | 0 => a
  | n + 1 => σ n

@[simp] theorem scons_zero (a : Tm) (σ : ℕ → Tm) : scons a σ 0 = a := rfl
@[simp] theorem scons_succ (a : Tm) (σ : ℕ → Tm) (n : ℕ) : scons a σ (n + 1) = σ n := rfl

/-- Weakening by one variable. -/
def shift (t : Tm) : Tm := rename Nat.succ t

/-- Substitution of the variable `0`. -/
def inst (a t : Tm) : Tm := subst (scons a ids) t

@[inherit_doc] notation:max t "[" a "]" => inst a t

/-- Substitution of the variables `1` and `0` by `a` and `b`. -/
def inst2 (a b t : Tm) : Tm := subst (scons b (scons a ids)) t

@[simp] theorem inst_shift (a t : Tm) : (shift t)[a] = t := by
  simp only [shift, inst, subst_rename]
  exact subst_ids t

theorem inst2_shift2 (a b t : Tm) : inst2 a b (rename (· + 2) t) = t := by
  simp only [inst2, subst_rename]
  exact subst_ids t

/-- Pushing a substitution inside a single substitution. -/
theorem subst_inst (σ : ℕ → Tm) (a t : Tm) : subst σ (t[a]) = (subst (up σ) t)[subst σ a] := by
  simp only [inst, subst_subst]
  refine subst_congr ?_ t
  intro n
  cases n with
  | zero => rfl
  | succ n => simp [subst_rename]

theorem rename_inst (ρ : ℕ → ℕ) (a t : Tm) : rename ρ (t[a]) = (rename (upr ρ) t)[rename ρ a] := by
  simp only [inst, rename_subst, subst_rename]
  refine subst_congr ?_ t
  intro n
  cases n <;> rfl

/-- Pushing a substitution inside a double substitution. -/
theorem subst_inst2 (σ : ℕ → Tm) (a b t : Tm) :
    subst σ (inst2 a b t) = inst2 (subst σ a) (subst σ b) (subst (up (up σ)) t) := by
  simp only [inst2, subst_subst]
  refine subst_congr ?_ t
  intro n
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => simp [subst_rename]

theorem rename_inst2 (ρ : ℕ → ℕ) (a b t : Tm) :
    rename ρ (inst2 a b t) = inst2 (rename ρ a) (rename ρ b) (rename (upr (upr ρ)) t) := by
  simp only [inst2, rename_subst, subst_rename]
  refine subst_congr ?_ t
  intro n
  match n with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- The substitution `subst (up σ) t` followed by `[a]` is `subst (scons a σ) t`. -/
theorem subst_up_inst (σ : ℕ → Tm) (a t : Tm) : (subst (up σ) t)[a] = subst (scons a σ) t := by
  simp only [inst, subst_subst]
  refine subst_congr ?_ t
  intro n
  cases n with
  | zero => rfl
  | succ n => simp [subst_rename]

/-- A substitution followed by a single substitution. -/
theorem subst_inst_scons (τ : ℕ → Tm) (a t : Tm) :
    subst τ (t[a]) = subst (scons (subst τ a) τ) t := by
  simp only [inst, subst_subst]
  refine subst_congr ?_ t
  intro n
  cases n <;> rfl

theorem shift_inst_rename (t : Tm) : (rename (upr Nat.succ) t)[var 0] = t := by
  simp only [inst, subst_rename]
  rw [subst_congr (σ' := ids) (fun n => by cases n <;> rfl) t, subst_ids]

/-- The type of the step of `natrec`: `P[succ (var 1)]` in the context extended by `ℕ` and `P`. -/
def stepTy (P : Tm) : Tm := subst (scons (succ (var 1)) (fun k => var (k + 2))) P

theorem subst_stepTy (σ : ℕ → Tm) (P : Tm) :
    subst (up (up σ)) (stepTy P) = stepTy (subst (up σ) P) := by
  simp only [stepTy, subst_subst]
  refine subst_congr ?_ P
  intro n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [scons_succ, subst_var, up_succ, subst_rename, rename_rename]
      rw [rename_eq_subst]

theorem rename_stepTy (ρ : ℕ → ℕ) (P : Tm) :
    rename (upr (upr ρ)) (stepTy P) = stepTy (rename (upr ρ) P) := by
  simp only [stepTy, rename_subst, subst_rename]
  refine subst_congr ?_ P
  intro n
  cases n <;> rfl

theorem inst2_stepTy (P n r : Tm) : inst2 n r (stepTy P) = P[succ n] := by
  simp only [inst2, stepTy, inst, subst_subst]
  refine subst_congr ?_ P
  intro k
  cases k <;> rfl

end MLTT
