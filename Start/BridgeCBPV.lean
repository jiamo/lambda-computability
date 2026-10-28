/-
**Bridge: the source calculus of call-by-push-value is the λ core** — milestone M31
(`M31-BRIDGE-CBPV`).

The source of the translations of `Start/CBPV.lean` is a simply typed λ-calculus `CBPV.STm` with
call-by-name (`CBPV.NStep`) and call-by-value (`CBPV.VStep`) reduction.  Its terms are the
untyped λ-terms of the core (`Start/Syntax.lean`), with parallel substitution instead of the
core's single substitution.

* `CBPV.STm.toLambda` — the identification of the syntaxes;
* `CBPV.STm.toLambda_ren`, `CBPV.STm.toLambda_subst` — it commutes with renaming and parallel
  substitution (`Lambda.substEnv`), and **`CBPV.STm.toLambda_beta`** — with the substitution of a
  β-step;
* **`CBPV.NStep.toLambda`**, **`CBPV.VStep.toLambda`** — call-by-name and call-by-value steps
  are β-steps of the λ core, so the CBPV translations simulate reductions of the core.
-/

import Start.CBPV
import Start.BridgeLambdaEnv

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace CBPV

/-- A source term as a term of the λ core. -/
def STm.toLambda : STm → Lambda
  | .var n => Lambda.var n
  | .lam t => Lambda.lam t.toLambda
  | .app t u => Lambda.app t.toLambda u.toLambda

theorem up_eq_upRen (ξ : ℕ → ℕ) : up ξ = Lambda.upRen ξ := by
  funext n
  cases n <;> rfl

theorem STm.toLambda_ren (t : STm) :
    ∀ ξ : ℕ → ℕ, (t.ren ξ).toLambda = Lambda.substEnv (Lambda.renEnv ξ) t.toLambda := by
  induction t with
  | var n => intro ξ; rfl
  | lam t ih =>
      intro ξ
      simp only [STm.ren, STm.toLambda, Lambda.substEnv, ih, Lambda.envCons_renEnv, up_eq_upRen]
  | app t u iht ihu => intro ξ; simp only [STm.ren, STm.toLambda, Lambda.substEnv, iht, ihu]

theorem STm.toLambda_subst (t : STm) :
    ∀ σ : ℕ → STm, (t.subst σ).toLambda = Lambda.substEnv (fun n => (σ n).toLambda) t.toLambda := by
  induction t with
  | var n => intro σ; rfl
  | lam t ih =>
      intro σ
      have hup : (fun n => (upSS σ n).toLambda) = Lambda.envCons (fun n => (σ n).toLambda) := by
        funext n
        cases n with
        | zero => rfl
        | succ n =>
            simp only [upSS, Lambda.envCons, STm.toLambda_ren, Lambda.lift_one_zero]
      simp only [STm.subst, STm.toLambda, Lambda.substEnv, ih, hup]
  | app t u iht ihu => intro σ; simp only [STm.subst, STm.toLambda, Lambda.substEnv, iht, ihu]

/-- **The substitution of a β-step is the core's substitution.** -/
theorem STm.toLambda_beta (t u : STm) :
    (t.subst (cons u STm.var)).toLambda = Lambda.subst u.toLambda 0 t.toLambda := by
  rw [STm.toLambda_subst, Lambda.subst_zero_eq_substEnv]
  congr 1
  funext n
  cases n <;> rfl

/-- **A call-by-name step is a β-step of the λ core.** -/
theorem NStep.toLambda {t t' : STm} (h : NStep t t') : Lambda.step t.toLambda t'.toLambda := by
  induction h with
  | beta t u =>
      rw [STm.toLambda_beta]
      exact Lambda.step.beta _ _
  | appL u _ ih => exact Lambda.step.app_left _ _ _ ih

/-- **A call-by-value step is a β-step of the λ core.** -/
theorem VStep.toLambda {t t' : STm} (h : VStep t t') : Lambda.step t.toLambda t'.toLambda := by
  induction h with
  | beta t w _ =>
      rw [STm.toLambda_beta]
      exact Lambda.step.beta _ _
  | appL u _ ih => exact Lambda.step.app_left _ _ _ ih
  | appR _ _ ih => exact Lambda.step.app_right _ _ _ ih

end CBPV
