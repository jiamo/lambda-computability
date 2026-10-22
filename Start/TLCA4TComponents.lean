import Start.TLCA4TUnfold

/-!
# Series V, round 4, run 1, part A1: the components of the reducts of `T x`
(row M20-TLCA4-T-NOT-FIXPOINT)

The reducts of `T x` (`T = B M (B (B M) B)`, `Start/TLCA4TUnfold.lean`) contain *components*: the
terms `A₀ = B M (B x)`, `Aₙ₊₁ = B x Aₙ` of `TLCA4.tA` and all their βη-reducts.  This module
defines the component families and proves that their index is well defined:

* `xPow f k t = fᵏ t` and `tAnf x n = aₙ = λz. xⁿ⁺¹ (z (λw. x (z w)))` (de Bruijn, `x` free);
* **`tAnf_nf`** — every `aₙ` is βη-normal; **`tAnf_injective`** — `aₙ = aₘ → n = m`;
* `TComp x n` — the least family containing `toLam A₀` at index `0`, containing `B x P` at index
  `n + 1` for `P` at index `n`, and closed under βη-reduction;
* **`TComp.reduces_tAnf`** — every component of index `n` βη-reduces to `aₙ`;
* **`TComp.index_unique`** — the index of a component is unique;
* **`TComp.lamx`** — `λw. x (P w)` is a component of index `n + 1` when `P` has index `n`;
* **`TComp.not_xHeaded`** — no component is of the form `x R`.

The abstraction lemma (A2: the shape of `b[Q/c]` for a component `λc. b`) is not proved here.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep etaStep betaEta_church_rosser)

/-- `xPow f k t = f (f (… (f t)))` with `k` applications. -/
def xPow (f : Lambda) : ℕ → Lambda → Lambda
  | 0, t => t
  | k + 1, t => .app f (xPow f k t)

/-- `aₙ = λz. xⁿ⁺¹ (z (λw. x (z w)))`, with `x` the free de Bruijn variable `x`. -/
def tAnf (x n : ℕ) : Lambda :=
  .lam (xPow (.var (x + 1)) (n + 1)
    (.app (.var 0) (.lam (.app (.var (x + 2)) (.app (.var 1) (.var 0))))))

/-! ### Normality and injectivity -/

theorem betaEtaNf_app_var {i : ℕ} {t : Lambda} (h : BetaEtaNf t) :
    BetaEtaNf (.app (.var i) t) := by
  intro u hu
  cases hu with
  | beta hb =>
    cases hb with
    | app_left _ _ _ h' => cases h'
    | app_right _ _ t' h' => exact h t' (.beta h')
  | eta he =>
    cases he with
    | app_left _ h' => cases h'
    | app_right _ h' => exact h _ (.eta h')

theorem betaEtaNf_var (i : ℕ) : BetaEtaNf (.var i) := by
  intro u hu
  cases hu with
  | beta hb => cases hb
  | eta he => cases he

theorem betaEtaNf_lam {b : Lambda} (h : BetaEtaNf b)
    (hne : ∀ f, b ≠ .app (Lambda.lift 1 0 f) (.var 0)) : BetaEtaNf (.lam b) := by
  intro u hu
  cases hu with
  | beta hb =>
    cases hb with
    | lam _ t' h' => exact h t' (.beta h')
  | eta he =>
    cases he with
    | eta f => exact hne _ rfl
    | lam h' => exact h _ (.eta h')

theorem betaEtaNf_xPow (i : ℕ) : ∀ (k : ℕ) {t : Lambda}, BetaEtaNf t →
    BetaEtaNf (xPow (.var i) k t)
  | 0, _, h => h
  | k + 1, _, h => betaEtaNf_app_var (betaEtaNf_xPow i k h)

theorem xPow_succ_ne_var (f : Lambda) (k : ℕ) (t : Lambda) (j : ℕ) :
    xPow f (k + 1) t ≠ .var j := by
  simp [xPow]

theorem xPow_app_ne_var (f a b : Lambda) : ∀ (k : ℕ) (j : ℕ), xPow f k (.app a b) ≠ .var j
  | 0, _ => by simp [xPow]
  | k + 1, _ => by simp [xPow]

/-- **Every `aₙ` is βη-normal.** -/
theorem tAnf_nf (x n : ℕ) : BetaEtaNf (tAnf x n) := by
  unfold tAnf
  refine betaEtaNf_lam (betaEtaNf_xPow _ _ (betaEtaNf_app_var
    (betaEtaNf_lam (betaEtaNf_app_var (betaEtaNf_app_var (betaEtaNf_var 0))) ?_))) ?_
  · intro f h
    simp at h
  · intro f h
    simp only [xPow] at h
    injection h with _ h2
    exact xPow_app_ne_var _ _ _ n 0 h2

theorem xPow_inj (x : ℕ) (a b : Lambda) : ∀ n m : ℕ,
    xPow (.var (x + 1)) n (.app (.var 0) a) = xPow (.var (x + 1)) m (.app (.var 0) b) →
      n = m
  | 0, 0, _ => rfl
  | 0, m + 1, h => by
    simp only [xPow, Lambda.app.injEq] at h
    simp at h
  | n + 1, 0, h => by
    simp only [xPow, Lambda.app.injEq] at h
    simp at h
  | n + 1, m + 1, h => by
    simp only [xPow, Lambda.app.injEq] at h
    rw [xPow_inj x a b n m h.2]

/-- **`aₙ = aₘ → n = m`.** -/
theorem tAnf_injective (x : ℕ) {n m : ℕ} (h : tAnf x n = tAnf x m) : n = m := by
  unfold tAnf at h
  injection h with h
  have := xPow_inj x _ _ (n + 1) (m + 1) h
  omega

/-! ### βη-reduction congruences used below -/

theorem betaEtaReduces_app_right (f : Lambda) {a a' : Lambda} (h : betaEtaReduces a a') :
    betaEtaReduces (.app f a) (.app f a') := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih =>
    refine ih.tail ?_
    cases hs with
    | beta hb => exact .beta (.app_right _ _ _ hb)
    | eta he => exact .eta (.app_right _ he)

/-- The reducts of a variable-headed application are variable-headed applications. -/
theorem betaEtaReduces_app_var {i : ℕ} {R T : Lambda} (h : betaEtaReduces (.app (.var i) R) T) :
    ∃ R', T = .app (.var i) R' := by
  induction h with
  | refl => exact ⟨R, rfl⟩
  | tail _ hs ih =>
    obtain ⟨R', rfl⟩ := ih
    cases hs with
    | beta hb =>
      cases hb with
      | app_left _ _ _ h' => cases h'
      | app_right _ _ t' _ => exact ⟨t', rfl⟩
    | eta he =>
      cases he with
      | app_left _ h' => cases h'
      | app_right _ h' => exact ⟨_, rfl⟩

/-! ### Lifting and substitution through `xPow` -/

theorem lift_xPow (n k : ℕ) (f : Lambda) : ∀ (m : ℕ) (t : Lambda),
    Lambda.lift n k (xPow f m t) = xPow (Lambda.lift n k f) m (Lambda.lift n k t)
  | 0, _ => rfl
  | m + 1, t => by simp [xPow, lift_xPow n k f m t]

theorem subst_xPow (s : Lambda) (j : ℕ) (f : Lambda) : ∀ (m : ℕ) (t : Lambda),
    Lambda.subst s j (xPow f m t) = xPow (Lambda.subst s j f) m (Lambda.subst s j t)
  | 0, _ => rfl
  | m + 1, t => by simp [xPow, Lambda.subst, subst_xPow s j f m t]

theorem lift_tAnf (x n : ℕ) : Lambda.lift 1 0 (tAnf x n) = tAnf (x + 1) n := by
  simp [tAnf, Lambda.lift, lift_xPow]

/-- `aₙ` applied to the bound variable: `(λz. xⁿ⁺¹ (z (λw. x (z w)))) v → xⁿ⁺¹ (v (λw. x (v w)))`,
here under one binder (`x` lifted). -/
theorem tAnf_app_var0 (x n : ℕ) :
    Lambda.step (.app (tAnf (x + 1) n) (.var 0))
      (xPow (.var (x + 1)) (n + 1)
        (.app (.var 0) (.lam (.app (.var (x + 2)) (.app (.var 1) (.var 0)))))) := by
  have := Lambda.step.beta (xPow (.var (x + 1 + 1)) (n + 1)
    (.app (.var 0) (.lam (.app (.var (x + 1 + 2)) (.app (.var 1) (.var 0)))))) (.var 0)
  simpa [tAnf, subst_xPow, Lambda.subst, Lambda.lift] using this

/-- `B x aₙ →β aₙ₊₁`. -/
theorem Bx_tAnf_reduces (x n : ℕ) :
    Lambda.reduces (.app (.app lamB (.var x)) (tAnf x n)) (tAnf x (n + 1)) := by
  refine Lambda.reduces_trans (reduces_B2 _ _) ?_
  rw [lift_tAnf]
  have h := Lambda.reduces_lam (Lambda.reduces_app_right (t1 := .var (x + 1))
    (Lambda.reduces.step _ _ _ (tAnf_app_var0 x n) (.refl _)))
  simpa [Lambda.lift, tAnf, xPow] using h

/-- `toLam A₀ = B M (B x) →β a₀`. -/
theorem tA0_reduces (x : ℕ) : Lambda.reduces (toLam (tA x 0)) (tAnf x 0) := by
  show Lambda.reduces (.app (.app lamB lamM) (.app lamB (.var x))) _
  refine Lambda.reduces_trans (reduces_B2 _ _) ?_
  -- `λz. M (B x z)`
  have hM : Lambda.lift 1 0 lamM = lamM := rfl
  rw [hM]
  apply Lambda.reduces_lam
  have hW : Lambda.reduces (.app (Lambda.lift 1 0 (.app lamB (.var x))) (.var 0))
      (.lam (.app (.var (x + 2)) (.app (.var 1) (.var 0)))) := by
    have := reduces_B2 (.var (x + 1)) (.var 0)
    simpa [Lambda.lift, lamB] using this
  -- `M W → W W`
  refine Lambda.reduces.step _ _ _ (Lambda.step.beta _ _) ?_
  simp only [Lambda.subst, if_pos]
  refine Lambda.reduces_trans (Lambda.reduces_app hW hW) ?_
  refine Lambda.reduces.step _ _ _ (Lambda.step.beta _ _) ?_
  simp [Lambda.subst, xPow]
  exact .refl _

/-! ### The component families -/

/-- `TComp x n P`: `P` is a component of index `n` (the βη-reducts of `A₀`, of `B x P'`, …). -/
inductive TComp (x : ℕ) : ℕ → Lambda → Prop
  | base : TComp x 0 (toLam (tA x 0))
  | bx {n : ℕ} {P : Lambda} : TComp x n P → TComp x (n + 1) (.app (.app lamB (.var x)) P)
  | red {n : ℕ} {P Q : Lambda} : TComp x n P → betaEtaReduces P Q → TComp x n Q

theorem TComp.toLam_tA (x : ℕ) : ∀ n : ℕ, TComp x n (toLam (tA x n))
  | 0 => .base
  | n + 1 => .bx (TComp.toLam_tA x n)

/-- **Every component of index `n` βη-reduces to `aₙ`.** -/
theorem TComp.reduces_tAnf {x n : ℕ} {P : Lambda} (h : TComp x n P) :
    betaEtaReduces P (tAnf x n) := by
  induction h with
  | base => exact .of_reduces (tA0_reduces x)
  | bx _ ih =>
    exact (betaEtaReduces_app_right _ ih).trans (.of_reduces (Bx_tAnf_reduces x _))
  | red _ hPQ ih =>
    obtain ⟨w, h1, h2⟩ := betaEta_church_rosser ih hPQ
    rw [← h1.eq_of_nf (tAnf_nf x _)] at h2
    exact h2

/-- **The index of a component is unique.** -/
theorem TComp.index_unique {x n m : ℕ} {P : Lambda} (hn : TComp x n P) (hm : TComp x m P) :
    n = m := by
  obtain ⟨w, h1, h2⟩ := betaEta_church_rosser hn.reduces_tAnf hm.reduces_tAnf
  exact tAnf_injective x ((h1.eq_of_nf (tAnf_nf x n)).trans (h2.eq_of_nf (tAnf_nf x m)).symm)

/-- `λw. x (P w)` is a component of index `n + 1`. -/
theorem TComp.lamx {x n : ℕ} {P : Lambda} (h : TComp x n P) :
    TComp x (n + 1) (.lam (.app (.var (x + 1)) (.app (Lambda.lift 1 0 P) (.var 0)))) := by
  have := reduces_B2 (.var x) P
  simp only [Lambda.lift] at this
  exact .red (.bx h) (.of_reduces (by simpa using this))

/-- **No component is `x`-headed.** -/
theorem TComp.not_xHeaded {x n : ℕ} {R : Lambda} (h : TComp x n (.app (.var x) R)) : False := by
  obtain ⟨R', hR'⟩ := betaEtaReduces_app_var h.reduces_tAnf
  simp [tAnf] at hR'

end TLCA4
