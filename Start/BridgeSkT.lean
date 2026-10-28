/-
**Bridge: the skeleton calculus of `CC^ω` is strongly normalizing, through the λ core** —
milestone M31 (`M31-BRIDGE-SKELETON`).

`Start/PTSExpansionCCOSkelFun.lean` gives the intrinsically typed calculus `SkT` of skeletons of
kind-level functions of `CC^ω` (one base sort per level), with β-steps `SkT.Step` and a
set-theoretic model, and it bypasses normalization by evaluating in the model.  This module
erases skeleton terms to the λ core and obtains normalization from the core's Tait theorem.

* `SkT.erase` — the erasure (a constant becomes the identity `λx. x`), `SkTy.toTy` — the simple
  type of a skeleton type (`base ℓ` becomes `base ⇒ base`);
* `SkT.erase_rename`, `SkT.erase_subst`, `SkT.erase_beta` — erasure commutes with renaming,
  substitution and the substitution of a β-step;
* **`SkT.Step.erase`** — every skeleton β-step is a β-step of the λ core;
* `SkT.erase_typing` — erasures are simply typed (`Lambda.Typing`);
* **`SkT.sn`** — **every skeleton term is strongly normalizing**, from `Lambda.sn_of_typing`.
-/

import Start.PTSExpansionCCOSkelFun
import Start.SimpleTypes
import Start.BridgeLambdaEnv

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem.CCO.SkF

/-- The de Bruijn index of a typed variable. -/
def Var.idx : {Γ : List SkTy} → {a : SkTy} → Var Γ a → ℕ
  | _, _, .zero => 0
  | _, _, .succ v => v.idx + 1

/-- The simple type of a skeleton type. -/
def SkTy.toTy : SkTy → Lambda.Ty
  | .base _ => .arrow .base .base
  | .arr a b => .arrow a.toTy b.toTy

namespace SkT

/-- **The erasure** of a skeleton term to the λ core. -/
def erase : {Γ : List SkTy} → {a : SkTy} → SkT Γ a → Lambda
  | _, _, .var v => .var v.idx
  | _, _, .cst _ => .lam (.var 0)
  | _, _, .lam t => .lam t.erase
  | _, _, .app t u => .app t.erase u.erase

theorem erase_rename : ∀ {Γ : List SkTy} {a : SkTy} (t : SkT Γ a) {Δ : List SkTy} (r : Ren Γ Δ)
    (ξ : ℕ → ℕ), (∀ {b : SkTy} (v : Var Γ b), (r v).idx = ξ v.idx) →
      (rename r t).erase = Lambda.substEnv (Lambda.renEnv ξ) t.erase := by
  intro Γ a t
  induction t with
  | var v => intro Δ r ξ hr; simp only [rename, erase, hr]; rfl
  | cst ℓ => intro Δ r ξ hr; rfl
  | lam t ih =>
      intro Δ r ξ hr
      simp only [rename, erase, Lambda.substEnv, Lambda.envCons_renEnv]
      congr 1
      refine ih (Ren.up r) (Lambda.upRen ξ) ?_
      intro b v
      cases v with
      | zero => rfl
      | succ v => simp only [Ren.up, Var.idx, hr, Lambda.upRen]
  | app t u iht ihu =>
      intro Δ r ξ hr
      simp only [rename, erase, Lambda.substEnv, iht r ξ hr, ihu r ξ hr]

theorem erase_subst : ∀ {Γ : List SkTy} {a : SkTy} (t : SkT Γ a) {Δ : List SkTy} (σ : Sub Γ Δ)
    (ρ : ℕ → Lambda), (∀ {b : SkTy} (v : Var Γ b), (σ v).erase = ρ v.idx) →
      (subst σ t).erase = Lambda.substEnv ρ t.erase := by
  intro Γ a t
  induction t with
  | var v => intro Δ σ ρ hσ; simp only [subst, erase, hσ]; rfl
  | cst ℓ => intro Δ σ ρ hσ; rfl
  | lam t ih =>
      intro Δ σ ρ hσ
      simp only [subst, erase, Lambda.substEnv]
      congr 1
      refine ih (Sub.up σ) (Lambda.envCons ρ) ?_
      intro b v
      cases v with
      | zero => rfl
      | succ v =>
          simp only [Sub.up, Var.idx, Lambda.envCons]
          rw [erase_rename (σ v) (fun w => .succ w) Nat.succ (fun _ => rfl), hσ,
            Lambda.lift_one_zero]
  | app t u iht ihu =>
      intro Δ σ ρ hσ
      simp only [subst, erase, Lambda.substEnv, iht σ ρ hσ, ihu σ ρ hσ]

/-- **The substitution of a β-step is the core's substitution.** -/
theorem erase_beta {Γ : List SkTy} {a b : SkTy} (t : SkT (a :: Γ) b) (u : SkT Γ a) :
    (subst (sub0 u) t).erase = Lambda.subst u.erase 0 t.erase := by
  rw [erase_subst t (sub0 u) (Lambda.envScons u.erase fun k => Lambda.var k),
    Lambda.subst_zero_eq_substEnv]
  intro c v
  cases v with
  | zero => rfl
  | succ v => rfl

/-- **A skeleton β-step is a β-step of the λ core.** -/
theorem Step.erase {Γ : List SkTy} {a : SkTy} {t t' : SkT Γ a} (h : Step t t') :
    Lambda.step t.erase t'.erase := by
  induction h with
  | beta t u =>
      simp only [SkT.erase]
      rw [erase_beta]
      exact Lambda.step.beta _ _
  | lam _ ih => exact Lambda.step.lam _ _ ih
  | appL u _ ih => exact Lambda.step.app_left _ _ _ ih
  | appR t _ ih => exact Lambda.step.app_right _ _ _ ih

theorem idx_typing : ∀ {Γ : List SkTy} {a : SkTy} (v : Var Γ a),
    (Γ.map SkTy.toTy)[v.idx]? = some a.toTy
  | _, _, .zero => rfl
  | _, _, .succ v => by simpa [Var.idx] using idx_typing v

/-- **Erasures are simply typed.** -/
theorem erase_typing : ∀ {Γ : List SkTy} {a : SkTy} (t : SkT Γ a),
    Lambda.Typing (Γ.map SkTy.toTy) t.erase a.toTy
  | _, _, .var v => .var (idx_typing v)
  | _, _, .cst _ => .lam (.var rfl)
  | _, _, .lam t => .lam (erase_typing t)
  | _, _, .app t u => .app (erase_typing t) (erase_typing u)

/-- **Strong normalization of skeleton terms**: no infinite sequence of skeleton β-steps starts
from any term. -/
theorem sn {Γ : List SkTy} {a : SkTy} (t : SkT Γ a) : Acc (fun u v => Step v u) t := by
  suffices h : ∀ e : Lambda, Acc (fun x y => Lambda.step y x) e →
      ∀ t : SkT Γ a, t.erase = e → Acc (fun u v => Step v u) t from
    h _ (Lambda.sn_of_typing (erase_typing t)) t rfl
  intro e he
  induction he with
  | intro e _ ih =>
      intro t ht
      refine Acc.intro t fun t' hs => ?_
      exact ih t'.erase (ht ▸ Step.erase hs) t' rfl

end SkT

end PureTypeSystem.CCO.SkF
