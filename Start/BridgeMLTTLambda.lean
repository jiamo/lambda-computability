/-
**Bridge: MLTT erases to the untyped λ core** — milestone M31 (`M31-FOUND-MLTT-LAMBDA`).

`Start/MLTT*.lean` develop Martin-Löf type theory with `Π`, a universe hierarchy, `ℕ` and `⊥`, its
full reduction `MLTT.FStep` and weak normalization of typed terms (`MLTT.HasTy.wn`).  This module
erases MLTT terms to the λ core and transfers normalization.

* `MLTT.Tm.erase` — the erasure: variables, abstractions and applications are kept, `emptyrec P e`
  becomes the erasure of `e`, and the type formers become the identity `λx. x` (as do `zero`,
  `succ` and `natrec`, which lie outside the pure fragment);
* `MLTT.Tm.erase_rename`, `MLTT.Tm.erase_subst`, **`MLTT.Tm.erase_inst`** — erasure commutes with
  renaming, parallel substitution and the substitution of a β-step, for every term;
* `MLTT.Tm.Pure` — the pure fragment: no `zero`, `succ` or `natrec` (`Π`, universes, `ℕ` and `⊥`
  as types, and `emptyrec`, are allowed); it is closed under substitution and full reduction;
* **`MLTT.FStep.erase`** — a full-reduction step of a pure term is simulated by λ-core
  reduction (one β-step for a β-redex, none for a step inside a type);
* `MLTT.NfB.erase_normal` — the erasure of a pure MLTT normal form is β-normal;
* **`MLTT.HasTy.erase_hasNormalForm`** — **the erasure of a typable pure term has a β-normal form**,
  from the weak normalization of MLTT.
-/

import Start.MLTTNormalize
import Start.BridgeLambdaEnv
import Start.NormalizationUndecidable

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-- **The erasure** of an MLTT term to the λ core. -/
def Tm.erase : Tm → Lambda
  | var n => .var n
  | lam b => .lam b.erase
  | app f a => .app f.erase a.erase
  | emptyrec _ e => e.erase
  | _ => .lam (.var 0)

theorem upr_eq_upRen (ρ : ℕ → ℕ) : upr ρ = Lambda.upRen ρ := by
  funext n
  cases n <;> rfl

theorem Tm.erase_rename (t : Tm) :
    ∀ ρ : ℕ → ℕ, (rename ρ t).erase = Lambda.substEnv (Lambda.renEnv ρ) t.erase := by
  induction t with
  | var n => intro ρ; rfl
  | lam b ih =>
      intro ρ
      simp only [rename, erase, Lambda.substEnv, ih, Lambda.envCons_renEnv, upr_eq_upRen]
  | app f a ihf iha => intro ρ; simp only [rename, erase, Lambda.substEnv, ihf, iha]
  | emptyrec P e _ ihe => intro ρ; simp only [rename, erase, ihe]
  | univ => intro ρ; rfl
  | pi => intro ρ; rfl
  | nat => intro ρ; rfl
  | zero => intro ρ; rfl
  | succ => intro ρ; rfl
  | natrec => intro ρ; rfl
  | empty => intro ρ; rfl

theorem Tm.erase_subst (t : Tm) :
    ∀ σ : ℕ → Tm, (subst σ t).erase = Lambda.substEnv (fun n => (σ n).erase) t.erase := by
  induction t with
  | var n => intro σ; rfl
  | lam b ih =>
      intro σ
      have hup : (fun n => (up σ n).erase) = Lambda.envCons (fun n => (σ n).erase) := by
        funext n
        cases n with
        | zero => rfl
        | succ n => simp only [up_succ, Lambda.envCons, erase_rename, Lambda.lift_one_zero]
      simp only [subst, erase, Lambda.substEnv, ih, hup]
  | app f a ihf iha => intro σ; simp only [subst, erase, Lambda.substEnv, ihf, iha]
  | emptyrec P e _ ihe => intro σ; simp only [subst, erase, ihe]
  | univ => intro σ; rfl
  | pi => intro σ; rfl
  | nat => intro σ; rfl
  | zero => intro σ; rfl
  | succ => intro σ; rfl
  | natrec => intro σ; rfl
  | empty => intro σ; rfl

/-- **The substitution of a β-step is the core's substitution.** -/
theorem Tm.erase_inst (b a : Tm) : (b[a]).erase = Lambda.subst a.erase 0 b.erase := by
  rw [inst, erase_subst, Lambda.subst_zero_eq_substEnv]
  congr 1
  funext n
  cases n <;> rfl

/-- The pure fragment: no `zero`, `succ` or `natrec`. -/
def Tm.Pure : Tm → Prop
  | var _ => True
  | univ _ => True
  | pi A B => A.Pure ∧ B.Pure
  | lam b => b.Pure
  | app f a => f.Pure ∧ a.Pure
  | nat => True
  | zero => False
  | succ _ => False
  | natrec _ _ _ _ => False
  | empty => True
  | emptyrec P e => P.Pure ∧ e.Pure

theorem Tm.Pure.rename {t : Tm} (h : t.Pure) : ∀ ρ : ℕ → ℕ, (MLTT.rename ρ t).Pure := by
  induction t with
  | var n => intro ρ; trivial
  | univ => intro ρ; trivial
  | pi A B ihA ihB => intro ρ; exact ⟨ihA h.1 _, ihB h.2 _⟩
  | lam b ih => intro ρ; exact ih h _
  | app f a ihf iha => intro ρ; exact ⟨ihf h.1 _, iha h.2 _⟩
  | nat => intro ρ; trivial
  | zero => exact h.elim
  | succ => exact h.elim
  | natrec => exact h.elim
  | empty => intro ρ; trivial
  | emptyrec P e ihP ihe => intro ρ; exact ⟨ihP h.1 _, ihe h.2 _⟩

theorem Tm.Pure.subst {t : Tm} (h : t.Pure) :
    ∀ σ : ℕ → Tm, (∀ n, (σ n).Pure) → (MLTT.subst σ t).Pure := by
  induction t with
  | var n => intro σ hσ; exact hσ n
  | univ => intro σ _; trivial
  | pi A B ihA ihB =>
      intro σ hσ
      refine ⟨ihA h.1 σ hσ, ihB h.2 (up σ) fun n => ?_⟩
      cases n with
      | zero => trivial
      | succ n => exact (hσ n).rename _
  | lam b ih =>
      intro σ hσ
      refine ih h (up σ) fun n => ?_
      cases n with
      | zero => trivial
      | succ n => exact (hσ n).rename _
  | app f a ihf iha => intro σ hσ; exact ⟨ihf h.1 σ hσ, iha h.2 σ hσ⟩
  | nat => intro σ _; trivial
  | zero => exact h.elim
  | succ => exact h.elim
  | natrec => exact h.elim
  | empty => intro σ _; trivial
  | emptyrec P e ihP ihe => intro σ hσ; exact ⟨ihP h.1 σ hσ, ihe h.2 σ hσ⟩

theorem Tm.Pure.inst {b a : Tm} (hb : b.Pure) (ha : a.Pure) : (b[a]).Pure :=
  hb.subst _ fun n => by cases n with
    | zero => exact ha
    | succ n => trivial

/-- **A full-reduction step of a pure term is simulated by λ-core reduction**, and the reduct is
pure. -/
theorem FStep.erase {t t' : Tm} (h : FStep t t') (hp : t.Pure) :
    Lambda.reduces t.erase t'.erase ∧ t'.Pure := by
  induction h with
  | beta b a =>
      refine ⟨Lambda.reduces.step _ _ _ (Lambda.step.beta _ _) ?_,
    Tm.Pure.inst (b := b) hp.1 hp.2⟩
      rw [Tm.erase_inst]
      exact .refl _
  | natrecZero => exact hp.elim
  | natrecSucc => exact hp.elim
  | piL G _ ih => exact ⟨.refl _, (ih hp.1).2, hp.2⟩
  | piR F _ ih => exact ⟨.refl _, hp.1, (ih hp.2).2⟩
  | lam _ ih => exact ⟨Lambda.reduces_lam (ih hp).1, (ih hp).2⟩
  | appL a _ ih => exact ⟨Lambda.reduces_app_left (ih hp.1).1, (ih hp.1).2, hp.2⟩
  | appR f _ ih => exact ⟨Lambda.reduces_app_right (ih hp.2).1, hp.1, (ih hp.2).2⟩
  | succ => exact hp.elim
  | natrecP => exact hp.elim
  | natrecZ => exact hp.elim
  | natrecS => exact hp.elim
  | natrecN => exact hp.elim
  | emptyrecP e _ ih => exact ⟨.refl _, (ih hp.1).2, hp.2⟩
  | emptyrecE P _ ih => exact ⟨(ih hp.2).1, hp.1, (ih hp.2).2⟩

theorem FSteps.erase {t t' : Tm} (h : FSteps t t') (hp : t.Pure) :
    Lambda.reduces t.erase t'.erase ∧ t'.Pure := by
  induction h with
  | refl => exact ⟨.refl _, hp⟩
  | tail _ hs ih =>
      have h2 := FStep.erase hs ih.2
      exact ⟨Lambda.reduces_trans ih.1 h2.1, h2.2⟩

theorem lam_var_normal : Lambda.is_normal (.lam (.var 0)) := by
  intro t' h
  cases h with
  | lam _ _ h' => exact Lambda.var_normal 0 _ h'

/-- **The erasure of a pure normal form is β-normal**, and that of a pure neutral normal form is
not an abstraction. -/
theorem NfB.erase_normal {b : Bool} {t : Tm} (h : NfB b t) (hp : t.Pure) :
    Lambda.is_normal t.erase ∧ (b = true → ∀ u, t.erase ≠ .lam u) := by
  induction h with
  | var i => exact ⟨Lambda.var_normal i, fun _ u h => by cases h⟩
  | app _ _ ihf iha =>
      obtain ⟨hf, hfl⟩ := ihf hp.1
      have ha := (iha hp.2).1
      refine ⟨fun t' hs => ?_, fun _ u h => by cases h⟩
      simp only [Tm.erase] at hs
      generalize hF : Tm.erase _ = F at hs hf hfl
      generalize hA : Tm.erase _ = A at hs ha
      cases hs with
      | beta t₁ _ => exact hfl rfl t₁ rfl
      | app_left _ _ _ hs => exact hf _ hs
      | app_right _ _ _ hs => exact ha _ hs
  | natrec => exact hp.elim
  | emptyrec _ _ _ ihe => exact ihe hp.2
  | ne _ ih => exact ⟨(ih hp).1, fun h => by cases h⟩
  | univ => exact ⟨lam_var_normal, fun h => by cases h⟩
  | pi => exact ⟨lam_var_normal, fun h => by cases h⟩
  | lam _ ih =>
      refine ⟨fun t' hs => ?_, fun h => by cases h⟩
      cases hs with
      | lam _ _ hs => exact (ih hp).1 _ hs
  | nat => exact ⟨lam_var_normal, fun h => by cases h⟩
  | zero => exact hp.elim
  | succ => exact hp.elim
  | empty => exact ⟨lam_var_normal, fun h => by cases h⟩

/-- **The erasure of a typable pure term has a β-normal form**: MLTT's weak normalization
(`MLTT.HasTy.wn`) transfers along the erasure. -/
theorem HasTy.erase_hasNormalForm {Γ : Ctx} {t A : Tm} (h : HasTy Γ t A) (hp : t.Pure) :
    Lambda.HasNormalForm t.erase := by
  obtain ⟨n, hsteps, hn⟩ := h.wn
  obtain ⟨hred, hnp⟩ := FSteps.erase hsteps hp
  exact ⟨n.erase, hred, (NfB.erase_normal hn hnp).1⟩

end MLTT
