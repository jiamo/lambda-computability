import Start.TLCA4BMFixpoint
import Start.LambdaBetaEta

/-!
# TLCA open problem 4 under βη: the bridge to the λ-calculus (row M20-TLCA4-BETAETA)

Imamura's Problem 5.1 asks whether some applicative combination `Y` of `B`, `M`, `I` satisfies
`Y x =βη x (Y x)`.  It is open.  This module supplies the formal bridge from the combinatory terms
of `Start/TLCA4BMFixpoint.lean` to the untyped λ-calculus with βη (`Start/LambdaBetaEta.lean`):

* `TLCA4.toLam` — `B ↦ λxyz.x(yz)`, `M ↦ λx.xx`, `I ↦ λx.x`, the variable `x` to the free de
  Bruijn variable `x`;
* `TLCA4.toLam_wstep`, **`TLCA4.toLam_weq`** — weak equivalence is sound for βη-conversion (in fact
  every weak step is a β-reduction);
* **`TLCA4.BII_betaReduces_I`** and **`TLCA4.not_weq_BII_I`** — the incompatibility: `B I I`
  β-reduces to `I` in the λ-calculus, but `B I I` and `I` are not weakly equivalent, so the trace
  invariant of the weak calculus does not transfer to βη;
* `TLCA4.not_agree_BII_I` (the trace invariant itself separates `B I I` and `I`) and the η-instance
  `TLCA4.BxI_betaEtaReduces_x`, `TLCA4.not_agree_BxI_x`, `TLCA4.not_weq_BxI_x`;
* `TLCA4.ProblemFiveOne` — Problem 5.1 stated over the bridge (no claim either way).
-/

set_option autoImplicit false

namespace TLCA4

open Tm

/-- The λ-term of `B`: `λxyz. x (y z)`. -/
def lamB : Lambda :=
  .lam (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0)))))

/-- The λ-term of `M`: `λx. x x`. -/
def lamM : Lambda := .lam (.app (.var 0) (.var 0))

/-- The λ-term of `I`: `λx. x`. -/
def lamI : Lambda := .lam (.var 0)

/-- Translation of combinatory terms into untyped λ-terms. -/
def toLam : Tm → Lambda
  | .B => lamB
  | .M => lamM
  | .I => lamI
  | .var n => .var n
  | .app u v => .app (toLam u) (toLam v)

theorem lift_lift_zero_one (u : Lambda) :
    Lambda.lift 1 0 (Lambda.lift 1 0 u) = Lambda.lift 1 1 (Lambda.lift 1 0 u) := by
  have := Lambda.lift_lift u 1 1 0 0 (le_refl 0)
  simpa using this

/-- Two arguments of `B`: `B u v` β-reduces to `λz. u (v z)`. -/
theorem reduces_B2 (u v : Lambda) :
    Lambda.reduces (.app (.app lamB u) v)
      (.lam (.app (Lambda.lift 1 0 u) (.app (Lambda.lift 1 0 v) (.var 0)))) := by
  have h1 : Lambda.step (.app lamB u)
      (.lam (.lam (.app (Lambda.lift 1 1 (Lambda.lift 1 0 u)) (.app (.var 1) (.var 0))))) := by
    have := Lambda.step.beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) u
    simp only [Lambda.subst, lift_lift_zero_one] at this
    simpa [lamB] using this
  have h2 : Lambda.step
      (.app (.lam (.lam (.app (Lambda.lift 1 1 (Lambda.lift 1 0 u)) (.app (.var 1) (.var 0)))))
        v)
      (.lam (.app (Lambda.lift 1 0 u) (.app (Lambda.lift 1 0 v) (.var 0)))) := by
    have := Lambda.step.beta
      (.lam (.app (Lambda.lift 1 1 (Lambda.lift 1 0 u)) (.app (.var 1) (.var 0)))) v
    simpa [Lambda.subst, Lambda.subst_lift] using this
  refine Lambda.reduces.step _ _ _ (.app_left _ _ _ h1) ?_
  exact Lambda.reduces.step _ _ _ h2 (.refl _)

/-- The `B`-contraction is a β-reduction. -/
theorem reduces_B (u v w : Lambda) :
    Lambda.reduces (.app (.app (.app lamB u) v) w) (.app u (.app v w)) := by
  have h3 : Lambda.step
      (.app (.lam (.app (Lambda.lift 1 0 u) (.app (Lambda.lift 1 0 v) (.var 0)))) w)
      (.app u (.app v w)) := by
    have := Lambda.step.beta (.app (Lambda.lift 1 0 u) (.app (Lambda.lift 1 0 v) (.var 0))) w
    simpa [Lambda.subst, Lambda.subst_lift] using this
  exact Lambda.reduces_trans (Lambda.reduces_app_left (reduces_B2 u v))
    (Lambda.reduces.step _ _ _ h3 (.refl _))

theorem reduces_M (u : Lambda) : Lambda.reduces (.app lamM u) (.app u u) := by
  refine Lambda.reduces.step _ _ _ ?_ (.refl _)
  have := Lambda.step.beta (.app (.var 0) (.var 0)) u
  simpa [lamM, Lambda.subst] using this

theorem reduces_I (u : Lambda) : Lambda.reduces (.app lamI u) u := by
  refine Lambda.reduces.step _ _ _ ?_ (.refl _)
  have := Lambda.step.beta (.var 0) u
  simpa [lamI, Lambda.subst] using this

/-- **Every weak step is a β-reduction** of the translations. -/
theorem toLam_wstep {u v : Tm} (h : WStep u v) : Lambda.reduces (toLam u) (toLam v) := by
  induction h with
  | b u v w => exact reduces_B _ _ _
  | m u => exact reduces_M _
  | i u => exact reduces_I _
  | appL v _ ih => exact Lambda.reduces_app_left ih
  | appR u _ ih => exact Lambda.reduces_app_right ih

theorem betaEtaConv_symm {t u : Lambda} (h : Lambda.betaEtaConv t u) :
    Lambda.betaEtaConv u t := by
  induction h with
  | refl => exact .refl _
  | step _ hs ih =>
      exact (Lambda.betaEtaConv.symm_step (.refl _) hs).trans ih
  | symm_step _ hs ih =>
      exact (Lambda.betaEtaConv.step (.refl _) hs).trans ih

/-- **Soundness**: weakly equivalent combinatory terms have βη-convertible translations. -/
theorem toLam_weq {u v : Tm} (h : WEq u v) : Lambda.betaEtaConv (toLam u) (toLam v) := by
  induction h with
  | step hs =>
      exact Lambda.betaEtaConv.of_reduces
        (Lambda.betaEtaReduces.of_reduces (toLam_wstep hs))
  | refl u => exact .refl _
  | symm _ ih => exact betaEtaConv_symm ih
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **`B I I` β-reduces to `I`** in the λ-calculus. -/
theorem BII_betaReduces_I :
    Lambda.reduces (toLam (.app (.app .B .I) .I)) (toLam .I) := by
  have hl : Lambda.lift 1 0 lamI = lamI := by simp [lamI, Lambda.lift]
  have h1 := reduces_B2 lamI lamI
  rw [hl] at h1
  refine Lambda.reduces_trans h1 (Lambda.reduces_lam ?_)
  exact Lambda.reduces_trans (reduces_I _) (reduces_I _)

/-- **`B I I` and `I` are not weakly equivalent**: both are weak normal forms, and the trace
invariant identifies weakly equivalent normalizing terms with their common normal form. -/
theorem not_weq_BII_I : ¬ WEq (.app (.app .B .I) .I) .I := by
  intro h
  have hA := agree_of_weq 0 h
  have hn1 : li (.app (.app .B .I) .I) = none := rfl
  have hn2 : li .I = none := rfl
  rcases hA with ⟨N, -, ⟨n, hn⟩, ⟨k, hk⟩⟩ | ⟨-, hI, -⟩
  · rw [seq_normal hn1] at hn
    rw [seq_normal hn2] at hk
    rw [← hk] at hn
    cases hn
  · exact hI ⟨0, hn2⟩

/-- **The incompatibility at `B I I = I`**: β-convertible translations, not weakly equivalent. -/
theorem BII_incompatible :
    Lambda.betaEtaConv (toLam (.app (.app .B .I) .I)) (toLam .I) ∧
      ¬ WEq (.app (.app .B .I) .I) .I :=
  ⟨Lambda.betaEtaConv.of_reduces (Lambda.betaEtaReduces.of_reduces BII_betaReduces_I),
    not_weq_BII_I⟩

/-- **The trace invariant separates `B I I` from `I`** (both are weak normal forms with different
values), although their translations are β-convertible: the analogue of Theorem 2.11 for β fails
at this pair. -/
theorem not_agree_BII_I (x : ℕ) : ¬ Agree x (.app (.app .B .I) .I) .I := by
  have hn1 : li (.app (.app .B .I) .I) = none := rfl
  have hn2 : li .I = none := rfl
  rintro (⟨N, -, ⟨n, hn⟩, ⟨k, hk⟩⟩ | ⟨-, hI, -⟩)
  · rw [seq_normal hn1] at hn
    rw [seq_normal hn2] at hk
    rw [← hk] at hn
    cases hn
  · exact hI ⟨0, hn2⟩

/-- **The η-instance**: `B x I` βη-reduces to `x` (two β-steps and one η-step). -/
theorem BxI_betaEtaReduces_x (x : ℕ) :
    Lambda.betaEtaReduces (toLam (.app (.app .B (.var x)) .I)) (toLam (.var x)) := by
  have hl : Lambda.lift 1 0 lamI = lamI := by simp [lamI, Lambda.lift]
  have h1 := reduces_B2 (.var x) lamI
  rw [hl] at h1
  have h2 : Lambda.reduces
      (.lam (.app (Lambda.lift 1 0 (.var x)) (.app lamI (.var 0))))
      (.lam (.app (Lambda.lift 1 0 (.var x)) (.var 0))) :=
    Lambda.reduces_lam (Lambda.reduces_app_right (reduces_I _))
  refine (Lambda.betaEtaReduces.of_reduces (Lambda.reduces_trans h1 h2)).trans ?_
  exact Lambda.betaEtaReduces.single (.eta (.eta (.var x)))

/-- **`B x I` and `x` are not weakly equivalent**, and the trace invariant separates them. -/
theorem not_agree_BxI_x (x : ℕ) : ¬ Agree x (.app (.app .B (.var x)) .I) (.var x) := by
  have hn1 : li (.app (.app .B (.var x)) .I) = none := rfl
  have hn2 : li (.var x) = none := rfl
  rintro (⟨N, -, ⟨n, hn⟩, ⟨k, hk⟩⟩ | ⟨-, hI, -⟩)
  · rw [seq_normal hn1] at hn
    rw [seq_normal hn2] at hk
    rw [← hk] at hn
    cases hn
  · exact hI ⟨0, hn2⟩

theorem not_weq_BxI_x (x : ℕ) : ¬ WEq (.app (.app .B (.var x)) .I) (.var x) :=
  fun h => not_agree_BxI_x x (agree_of_weq x h)

/-- Imamura's Problem 5.1 (open), stated over the bridge: some closed `B`,`M`,`I`-combination `Y`
satisfies `Y x =βη x (Y x)`.  Stated only; not claimed either way. -/
def ProblemFiveOne : Prop :=
  ∃ Y : Tm, IsBMI Y ∧ Lambda.betaEtaConv (toLam (.app Y (.var 0)))
    (toLam (.app (.var 0) (.app Y (.var 0))))

end TLCA4
