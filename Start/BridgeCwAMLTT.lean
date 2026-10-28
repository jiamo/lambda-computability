/-
**Bridge: λΠ embeds into MLTT, and its categorical semantics applies to the image** — milestone
M31 (`M31-FOUND-CWA-MLTT`).

The categorical-models development interprets the calculus `λΠ` (`Start/LambdaPi*.lean`: sorts
`∗ : □`, products `(∗,∗)` and `(∗,□)`, untyped β-conversion) in every category with attributes
with a universe and small products (`LambdaPi.Model`), and proves initiality
(`LambdaPi.Typing.interp_total`, `LambdaPi.interp_exists_unique`, `LambdaPiInitial.mor`).
`Start/MLTTPTS.lean` shows that derivations of the pure type system `MLTT.mlttPTS` (sorts the
universe levels, axioms `l : l + 1`, rules `(i, j, max i j)`) erase to MLTT derivations
(`MLTT.HasType.toTm`).  This module embeds `λΠ` into that pure type system, and hence into MLTT.

* `LambdaPi.Tm.toPTS` — `∗` becomes the level `0`, `□` the level `1`; it commutes with renaming,
  substitution and instantiation (`Tm.toPTS_rename`, `Tm.toPTS_subst`, `Tm.toPTS_inst`), maps
  β-steps to β-steps and conversion to conversion (`Step.toPTS`, `Conv.toPTS`);
* `LambdaPi.Typing.toPTS`, `LambdaPi.Wf.toPTS` — derivations of `λΠ` become derivations of
  `mlttPTS` (the rules `(∗,∗)` and `(∗,□)` become `(0,0,0)` and `(0,1,1)`);
* **`LambdaPi.Typing.toMLTT`** — **every derivation of `λΠ` in a well-formed context is a
  derivation of MLTT** (with domain annotations erased, `∗` read as `U 0` and `□` as `U 1`);
* **`LambdaPi.Typing.mltt_and_model`** — a derivable `λΠ` judgement is both an MLTT judgement
  and interpreted, uniquely, in every model with injective products: the categorical semantics
  of `λΠ` covers the image of `λΠ` in MLTT.
-/

import Start.MLTTPTS
import Start.LambdaPiInterpTotal
import Start.PTSTyping

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory

namespace LambdaPi

open PureTypeSystem

/-- The universe level of a sort. -/
def Srt.lev : Srt → ℕ
  | .star => 0
  | .box => 1

/-- **The embedding** of `λΠ` into the pure type system of MLTT. -/
def Tm.toPTS : Tm → Expr ℕ
  | .var n => .var n
  | .sort s => .sort s.lev
  | .app f a => .app f.toPTS a.toPTS
  | .lam A b => .lam A.toPTS b.toPTS
  | .pi A B => .pi A.toPTS B.toPTS

theorem upr_eq_liftRen (ρ : ℕ → ℕ) : upr ρ = Expr.liftRen ρ := by
  funext n
  cases n <;> rfl

theorem Tm.toPTS_rename (t : Tm) : ∀ ρ : ℕ → ℕ, (rename ρ t).toPTS = t.toPTS.rename ρ := by
  induction t with
  | var n => intro ρ; rfl
  | sort s => intro ρ; rfl
  | app f a ihf iha => intro ρ; simp only [rename, toPTS, Expr.rename, ihf, iha]
  | lam A b ihA ihb => intro ρ; simp only [rename, toPTS, Expr.rename, ihA, ihb, upr_eq_liftRen]
  | pi A B ihA ihB => intro ρ; simp only [rename, toPTS, Expr.rename, ihA, ihB, upr_eq_liftRen]

theorem Tm.toPTS_up (σ : ℕ → Tm) :
    (fun n => (up σ n).toPTS) = Expr.liftSub (fun n => (σ n).toPTS) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [up, Expr.liftSub, toPTS_rename]

theorem Tm.toPTS_subst (t : Tm) :
    ∀ σ : ℕ → Tm, (subst σ t).toPTS = t.toPTS.subst (fun n => (σ n).toPTS) := by
  induction t with
  | var n => intro σ; rfl
  | sort s => intro σ; rfl
  | app f a ihf iha => intro σ; simp only [subst, toPTS, Expr.subst, ihf, iha]
  | lam A b ihA ihb => intro σ; simp only [subst, toPTS, Expr.subst, ihA, ihb, toPTS_up]
  | pi A B ihA ihB => intro σ; simp only [subst, toPTS, Expr.subst, ihA, ihB, toPTS_up]

theorem Tm.toPTS_inst (b a : Tm) : (b[a]).toPTS = b.toPTS.instantiate a.toPTS := by
  rw [inst, toPTS_subst, Expr.instantiate]
  congr 1
  funext n
  cases n <;> rfl

/-- A β-step of `λΠ` is a β-step of the pure type system. -/
theorem Step.toPTS {t t' : Tm} (h : Step t t') : Beta t.toPTS t'.toPTS := by
  induction h with
  | beta A b a =>
      rw [Tm.toPTS_inst]
      exact Beta.head _ _ _
  | appL a _ ih => exact Beta.app_left ih
  | appR f _ ih => exact Beta.app_right ih
  | lamL b _ ih => exact Beta.lam_domain ih
  | lamR A _ ih => exact Beta.lam_body ih
  | piL B _ ih => exact Beta.pi_domain ih
  | piR A _ ih => exact Beta.pi_body ih

/-- Conversion of `λΠ` is conversion of the pure type system. -/
theorem Conv.toPTS {t t' : Tm} (h : Conv t t') : Converts t.toPTS t'.toPTS := by
  induction h with
  | refl => exact .refl _
  | step _ hs ih => exact .trans _ _ _ ih (.rel _ _ hs.toPTS)
  | stepInv _ hs ih => exact .trans _ _ _ ih (.symm _ _ (.rel _ _ hs.toPTS))

theorem Lookup.toPTS {Γ : Ctx} {n : ℕ} {A : Tm} (h : Lookup Γ n A) :
    PureTypeSystem.Lookup (Γ.map Tm.toPTS) n A.toPTS := by
  induction h with
  | zero Γ A =>
      rw [shift, Tm.toPTS_rename]
      exact .zero _ _
  | succ B _ ih =>
      rw [shift, Tm.toPTS_rename]
      exact .succ _ ih

/-- **Derivations of `λΠ` are derivations of the pure type system of MLTT.** -/
theorem Typing.toPTS {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) :
    ValidContext MLTT.mlttPTS (Γ.map Tm.toPTS) →
      HasType MLTT.mlttPTS (Γ.map Tm.toPTS) t.toPTS A.toPTS := by
  induction h with
  | ax Γ => intro hΓ; exact HasType.sort_of_valid hΓ (show (1 : ℕ) = 0 + 1 from rfl)
  | var hn => intro hΓ; exact HasType.lookup hΓ hn.toPTS
  | @pi Γ A B s t hrule _ _ ihA ihB =>
      intro hΓ
      have hA := ihA hΓ
      have hB := ihB (.cons hΓ hA)
      refine .product hA hB ?_
      subst hrule
      show t.lev = max 0 t.lev
      simp
  | lam _ _ ihP ihb =>
      intro hΓ
      have hP := ihP hΓ
      obtain ⟨s₁, -, -, hA, -, -, -⟩ := HasType.generation_pi hP
      exact .abstraction (ihb (.cons hΓ hA)) hP
  | app _ _ ihf iha =>
      intro hΓ
      rw [Tm.toPTS_inst]
      exact .application (ihf hΓ) (iha hΓ)
  | conv _ _ hc iht ihB =>
      intro hΓ
      exact .conversion (iht hΓ) (ihB hΓ) hc.toPTS

theorem Wf.toPTS {Γ : Ctx} (h : Wf Γ) : ValidContext MLTT.mlttPTS (Γ.map Tm.toPTS) := by
  induction h with
  | nil => exact .nil
  | cons _ hA ih => exact .cons ih (hA.toPTS ih)

/-- **Every derivation of `λΠ` is a derivation of MLTT**: the erasure of its image in `mlttPTS`
is a typing judgement of MLTT in a well-formed context. -/
theorem Typing.toMLTT {Γ : Ctx} {t A : Tm} (hΓ : Wf Γ) (h : Typing Γ t A) :
    MLTT.WfCtx (MLTT.toCtx (Γ.map Tm.toPTS)) ∧
      MLTT.HasTy (MLTT.toCtx (Γ.map Tm.toPTS)) (MLTT.toTm t.toPTS) (MLTT.toTm A.toPTS) :=
  MLTT.HasType.toTm (h.toPTS hΓ.toPTS)

/-- **A derivable `λΠ` judgement is an MLTT judgement with a categorical semantics**: its image
is derivable in MLTT, and in every model of `λΠ` with injective products its context is
interpreted and its term denotes a unique term of the model. -/
theorem Typing.mltt_and_model {Γ : Ctx} {t A : Tm} (hΓ : Wf Γ) (h : Typing Γ t A)
    (hA : A ≠ Tm.sort Srt.box) :
    (MLTT.WfCtx (MLTT.toCtx (Γ.map Tm.toPTS)) ∧
      MLTT.HasTy (MLTT.toCtx (Γ.map Tm.toPTS)) (MLTT.toTm t.toPTS) (MLTT.toTm A.toPTS)) ∧
    ∀ (C : Type u) [Category.{v} C] (M : Model.{u, v, w} C), M.PiInj →
      ∃ (Γ' : C) (sc : SemCtx M Γ'), CtxI Γ sc ∧ ∃! p : TmVal M Γ', TmI sc t p.1 p.2 := by
  refine ⟨h.toMLTT hΓ, fun C _ M hinj => ?_⟩
  obtain ⟨Γ', sc, hc⟩ := CtxI.total hinj hΓ
  exact ⟨Γ', sc, hc, interp_exists_unique hinj h hA hc⟩

end LambdaPi
