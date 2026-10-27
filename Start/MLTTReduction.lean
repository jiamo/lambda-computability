/-
**Martin-Löf type theory: weak head reduction** — milestone M30 (`M30-MLTT-DECL`).

As in Abel, Öhman and Vezzosi's formalization of decidability of conversion, reduction is
*typed*: `Γ ⊢ t ⇒ u : A` carries the typing premises of the rule it uses, so that it is a
definitional equality (`TRed.deq`) and its source is typable (`TRed.tyLeft`) without any
metatheory of the declarative system.

* `MLTT.Neutral`, `MLTT.Whnf` — neutral terms (a variable under eliminators) and weak head
  normal forms;
* `MLTT.WhStep` — untyped weak head reduction; it is deterministic (`WhStep.det`) and a weak
  head normal form has no step (`Whnf.no_step`);
* `MLTT.TRed`, `MLTT.TReds` — typed weak head reduction and its reflexive–transitive closure;
  `TRed.whStep` (the underlying untyped step), `TRed.deq`, `TReds.deq`, `TRed.tyLeft`,
  `TRed.rename` (weakening), `TReds.whnf_unique` (two reductions to weak head normal forms end
  at the same term).
-/

import Start.MLTTTyping

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Neutral terms and weak head normal forms -/

/-- Neutral terms: a variable under eliminators. -/
inductive Neutral : Tm → Prop
  | var (n : ℕ) : Neutral (var n)
  | app {f : Tm} (a : Tm) : Neutral f → Neutral (app f a)
  | natrec (P z s : Tm) {n : Tm} : Neutral n → Neutral (natrec P z s n)
  | emptyrec (P : Tm) {e : Tm} : Neutral e → Neutral (emptyrec P e)

/-- Weak head normal forms. -/
inductive Whnf : Tm → Prop
  | univ (l : ℕ) : Whnf (univ l)
  | pi (A B : Tm) : Whnf (pi A B)
  | lam (b : Tm) : Whnf (lam b)
  | nat : Whnf nat
  | zero : Whnf zero
  | succ (n : Tm) : Whnf (succ n)
  | empty : Whnf empty
  | ne {t : Tm} : Neutral t → Whnf t

theorem Neutral.rename {t : Tm} (h : Neutral t) (ρ : ℕ → ℕ) : Neutral (rename ρ t) := by
  induction h with
  | var n => exact Neutral.var _
  | app a _ ih => exact Neutral.app _ ih
  | natrec P z s _ ih => exact Neutral.natrec _ _ _ ih
  | emptyrec P _ ih => exact Neutral.emptyrec _ ih

theorem Whnf.rename {t : Tm} (h : Whnf t) (ρ : ℕ → ℕ) : Whnf (rename ρ t) := by
  cases h with
  | ne hn => exact Whnf.ne (hn.rename ρ)
  | _ => constructor

/-! ### Untyped weak head reduction -/

/-- One step of untyped weak head reduction. -/
inductive WhStep : Tm → Tm → Prop
  | beta (b a : Tm) : WhStep (app (lam b) a) (b[a])
  | appL {f f' : Tm} (a : Tm) : WhStep f f' → WhStep (app f a) (app f' a)
  | natrecZero (P z s : Tm) : WhStep (natrec P z s zero) z
  | natrecSucc (P z s n : Tm) : WhStep (natrec P z s (succ n)) (inst2 n (natrec P z s n) s)
  | natrecS (P z s : Tm) {n n' : Tm} : WhStep n n' → WhStep (natrec P z s n) (natrec P z s n')
  | emptyrecS (P : Tm) {e e' : Tm} : WhStep e e' → WhStep (emptyrec P e) (emptyrec P e')

theorem Neutral.no_step {t u : Tm} (h : Neutral t) (hs : WhStep t u) : False := by
  induction h generalizing u with
  | var n => cases hs
  | app a hf ih =>
      cases hs with
      | beta => cases hf
      | appL _ h => exact ih h
  | natrec P z s hn ih =>
      cases hs with
      | natrecZero => cases hn
      | natrecSucc => cases hn
      | natrecS _ _ _ h => exact ih h
  | emptyrec P _ ih =>
      cases hs with
      | emptyrecS _ h => exact ih h

/-- A weak head normal form has no step. -/
theorem Whnf.no_step {t u : Tm} (h : Whnf t) (hs : WhStep t u) : False := by
  cases h with
  | ne hn => exact hn.no_step hs
  | _ => cases hs

/-- **Weak head reduction is deterministic.** -/
theorem WhStep.det {t u v : Tm} (hu : WhStep t u) (hv : WhStep t v) : u = v := by
  induction hu generalizing v with
  | beta b a =>
      cases hv with
      | beta => rfl
      | appL _ h => cases h
  | appL a h ih =>
      cases hv with
      | beta => cases h
      | appL _ h' => rw [ih h']
  | natrecZero P z s =>
      cases hv with
      | natrecZero => rfl
      | natrecS _ _ _ h => cases h
  | natrecSucc P z s n =>
      cases hv with
      | natrecSucc => rfl
      | natrecS _ _ _ h => cases h
  | natrecS P z s h ih =>
      cases hv with
      | natrecZero => cases h
      | natrecSucc => cases h
      | natrecS _ _ _ h' => rw [ih h']
  | emptyrecS P h ih =>
      cases hv with
      | emptyrecS _ h' => rw [ih h']

/-! ### Typed weak head reduction -/

/-- **Typed weak head reduction** `Γ ⊢ t ⇒ u : A`. -/
inductive TRed : Ctx → Tm → Tm → Tm → Prop
  | conv {Γ : Ctx} {t u A B : Tm} : TRed Γ t u A → TyEq Γ A B → TRed Γ t u B
  | appL {Γ : Ctx} {t u a A B : Tm} : TRed Γ t u (pi A B) → HasTy Γ a A →
      TRed Γ (app t a) (app u a) (B[a])
  | beta {Γ : Ctx} {A B b a : Tm} : WfTy Γ A → HasTy (A :: Γ) b B →
      HasTy Γ a A → TRed Γ (app (lam b) a) (b[a]) (B[a])
  | natrecS {Γ : Ctx} {P z s n n' : Tm} : WfTy (Tm.nat :: Γ) P →
      HasTy Γ z (P[zero]) → HasTy (P :: Tm.nat :: Γ) s (stepTy P) → TRed Γ n n' Tm.nat →
      TRed Γ (natrec P z s n) (natrec P z s n') (P[n])
  | natrecZero {Γ : Ctx} {P z s : Tm} : WfTy (Tm.nat :: Γ) P →
      HasTy Γ z (P[zero]) → HasTy (P :: Tm.nat :: Γ) s (stepTy P) →
      TRed Γ (natrec P z s zero) z (P[zero])
  | natrecSucc {Γ : Ctx} {P z s n : Tm} : WfTy (Tm.nat :: Γ) P →
      HasTy Γ z (P[zero]) → HasTy (P :: Tm.nat :: Γ) s (stepTy P) → HasTy Γ n Tm.nat →
      TRed Γ (natrec P z s (succ n)) (inst2 n (natrec P z s n) s) (P[succ n])
  | emptyrecS {Γ : Ctx} {P e e' : Tm} : WfTy Γ P → TRed Γ e e' Tm.empty →
      TRed Γ (emptyrec P e) (emptyrec P e') P

/-- The untyped step underlying a typed one. -/
theorem TRed.whStep {Γ : Ctx} {t u A : Tm} (h : TRed Γ t u A) : WhStep t u := by
  induction h with
  | conv _ _ ih => exact ih
  | appL _ _ ih => exact WhStep.appL _ ih
  | beta => exact WhStep.beta _ _
  | natrecS _ _ _ _ ih => exact WhStep.natrecS _ _ _ ih
  | natrecZero => exact WhStep.natrecZero _ _ _
  | natrecSucc => exact WhStep.natrecSucc _ _ _ _
  | emptyrecS _ _ ih => exact WhStep.emptyrecS _ ih

/-- A typed reduction is a definitional equality. -/
theorem TRed.deq {Γ : Ctx} {t u A : Tm} (h : TRed Γ t u A) : DEq Γ t u A := by
  induction h with
  | conv _ he ih => exact Der.eqConv ih he
  | appL _ ha ih => exact Der.appCong ih (Der.refl ha)
  | beta hA hb ha => exact Der.beta hA hb ha
  | natrecS hP hz hs _ ih =>
      exact Der.natrecCong hP (Der.reflT hP) (Der.refl hz) (Der.refl hs) ih
  | natrecZero hP hz hs => exact Der.natrecZero hP hz hs
  | natrecSucc hP hz hs hn => exact Der.natrecSucc hP hz hs hn
  | emptyrecS hP _ ih => exact Der.emptyrecCong (Der.reflT hP) ih

/-- The source of a typed reduction is typable. -/
theorem TRed.tyLeft {Γ : Ctx} {t u A : Tm} (h : TRed Γ t u A) : HasTy Γ t A := by
  induction h with
  | conv _ he ih => exact Der.conv ih he
  | appL _ ha ih => exact Der.app ih ha
  | beta hA hb ha => exact Der.app (Der.lam hA hb) ha
  | natrecS hP hz hs _ ih => exact Der.natrec hP hz hs ih
  | natrecZero hP hz hs => exact Der.natrec hP hz hs (Der.zero hz.wf)
  | natrecSucc hP hz hs hn => exact Der.natrec hP hz hs (Der.succ hn)
  | emptyrecS hP _ ih => exact Der.emptyrec hP ih

/-- A weak head normal form does not reduce. -/
theorem Whnf.no_tred {Γ : Ctx} {t u A : Tm} (h : Whnf t) (hr : TRed Γ t u A) : False :=
  h.no_step hr.whStep

/-- Typed reduction is deterministic. -/
theorem TRed.det {Γ Γ' : Ctx} {t u v A B : Tm} (hu : TRed Γ t u A) (hv : TRed Γ' t v B) : u = v :=
  WhStep.det hu.whStep hv.whStep

/-- Weakening of typed reduction. -/
theorem TRed.rename {Γ Δ : Ctx} {t u A : Tm} {ρ : ℕ → ℕ} (h : TRed Γ t u A) (hρ : RenOk ρ Γ Δ)
    (hΔ : WfCtx Δ) : TRed Δ (MLTT.rename ρ t) (MLTT.rename ρ u) (MLTT.rename ρ A) := by
  induction h generalizing Δ ρ with
  | conv _ he ih => exact TRed.conv (ih hρ hΔ) (he.rename hρ hΔ)
  | appL _ ha ih =>
      have := TRed.appL (ih hρ hΔ) (ha.rename hρ hΔ)
      rwa [← rename_inst] at this
  | beta hA hb ha =>
      have hA' := hA.rename hρ hΔ
      have := TRed.beta hA' (hb.rename (hρ.up _) (Der.cons hΔ hA')) (ha.rename hρ hΔ)
      rwa [← rename_inst, ← rename_inst] at this
  | @natrecS P z s n n' hP hz hs _ ih =>
      have hN : WfCtx (Tm.nat :: Δ) := Der.cons hΔ (Der.natT hΔ)
      have hP' := hP.rename (hρ.up Tm.nat) hN
      have hz' := hz.rename hρ hΔ
      rw [rename_inst] at hz'
      have hs' := hs.rename ((hρ.up Tm.nat).up P) (Der.cons hN hP')
      rw [rename_stepTy] at hs'
      have := TRed.natrecS hP' hz' hs' (ih hρ hΔ)
      rwa [← rename_inst] at this
  | @natrecZero P z s hP hz hs =>
      have hN : WfCtx (Tm.nat :: Δ) := Der.cons hΔ (Der.natT hΔ)
      have hP' := hP.rename (hρ.up Tm.nat) hN
      have hz' := hz.rename hρ hΔ
      rw [rename_inst] at hz'
      have hs' := hs.rename ((hρ.up Tm.nat).up P) (Der.cons hN hP')
      rw [rename_stepTy] at hs'
      have := TRed.natrecZero hP' hz' hs'
      simpa [rename_inst] using this
  | @natrecSucc P z s n hP hz hs hn =>
      have hN : WfCtx (Tm.nat :: Δ) := Der.cons hΔ (Der.natT hΔ)
      have hP' := hP.rename (hρ.up Tm.nat) hN
      have hz' := hz.rename hρ hΔ
      rw [rename_inst] at hz'
      have hs' := hs.rename ((hρ.up Tm.nat).up P) (Der.cons hN hP')
      rw [rename_stepTy] at hs'
      have := TRed.natrecSucc hP' hz' hs' (hn.rename hρ hΔ)
      simpa [rename_inst, rename_inst2] using this
  | emptyrecS hP _ ih => exact TRed.emptyrecS (hP.rename hρ hΔ) (ih hρ hΔ)

/-! ### Many-step typed reduction -/

/-- Many-step typed weak head reduction `Γ ⊢ t ⇒* u : A`. -/
inductive TReds : Ctx → Tm → Tm → Tm → Prop
  | refl {Γ : Ctx} {t A : Tm} : HasTy Γ t A → TReds Γ t t A
  | step {Γ : Ctx} {t t' u A : Tm} : TRed Γ t t' A → TReds Γ t' u A → TReds Γ t u A

theorem TReds.deq {Γ : Ctx} {t u A : Tm} (h : TReds Γ t u A) : DEq Γ t u A := by
  induction h with
  | refl ht => exact Der.refl ht
  | step hs _ ih => exact Der.trans hs.deq ih

theorem TReds.tyLeft {Γ : Ctx} {t u A : Tm} (h : TReds Γ t u A) : HasTy Γ t A := by
  cases h with
  | refl ht => exact ht
  | step hs _ => exact hs.tyLeft

theorem TReds.trans {Γ : Ctx} {t u v A : Tm} (h₁ : TReds Γ t u A) (h₂ : TReds Γ u v A) :
    TReds Γ t v A := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact TReds.step hs (ih h₂)

theorem TReds.conv {Γ : Ctx} {t u A B : Tm} (h : TReds Γ t u A)
    (he : TyEq Γ A B) : TReds Γ t u B := by
  induction h with
  | refl ht => exact TReds.refl (Der.conv ht he)
  | step hs _ ih => exact TReds.step (TRed.conv hs he) (ih he)

theorem TReds.rename {Γ Δ : Ctx} {t u A : Tm} {ρ : ℕ → ℕ} (h : TReds Γ t u A) (hρ : RenOk ρ Γ Δ)
    (hΔ : WfCtx Δ) : TReds Δ (MLTT.rename ρ t) (MLTT.rename ρ u) (MLTT.rename ρ A) := by
  induction h with
  | refl ht => exact TReds.refl (ht.rename hρ hΔ)
  | step hs _ ih => exact TReds.step (hs.rename hρ hΔ) ih

/-- From a weak head normal form, reduction is trivial. -/
theorem TReds.of_whnf {Γ : Ctx} {t u A : Tm} (h : TReds Γ t u A) (ht : Whnf t) : u = t := by
  cases h with
  | refl => rfl
  | step hs _ => exact (ht.no_tred hs).elim

/-- **Two reductions to weak head normal forms end at the same term.** -/
theorem TReds.whnf_unique {Γ Γ' : Ctx} {t u v A B : Tm} (hu : TReds Γ t u A) (hv : TReds Γ' t v B)
    (hnu : Whnf u) (hnv : Whnf v) : u = v := by
  induction hu generalizing v with
  | refl => exact (hv.of_whnf hnu).symm
  | step hs _ ih =>
      cases hv with
      | refl => exact (hnv.no_tred hs).elim
      | step hs' hv' =>
          rw [TRed.det hs hs'] at ih
          exact ih hv' hnu hnv

/-- `Γ ⊢ t :⇒*: u : A`: a typed reduction between typable terms. -/
structure TRedsT (Γ : Ctx) (t u A : Tm) : Prop where
  tyL : HasTy Γ t A
  tyR : HasTy Γ u A
  red : TReds Γ t u A

theorem TRedsT.refl {Γ : Ctx} {t A : Tm} (h : HasTy Γ t A) : TRedsT Γ t t A :=
  ⟨h, h, TReds.refl h⟩

theorem TRedsT.rename {Γ Δ : Ctx} {t u A : Tm} {ρ : ℕ → ℕ} (h : TRedsT Γ t u A) (hρ : RenOk ρ Γ Δ)
    (hΔ : WfCtx Δ) : TRedsT Δ (MLTT.rename ρ t) (MLTT.rename ρ u) (MLTT.rename ρ A) :=
  ⟨h.tyL.rename hρ hΔ, h.tyR.rename hρ hΔ, h.red.rename hρ hΔ⟩

theorem TRedsT.conv {Γ : Ctx} {t u A B : Tm} (h : TRedsT Γ t u A)
    (he : TyEq Γ A B) : TRedsT Γ t u B :=
  ⟨Der.conv h.tyL he, Der.conv h.tyR he, h.red.conv he⟩

end MLTT
