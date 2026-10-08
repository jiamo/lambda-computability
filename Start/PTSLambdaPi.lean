import Start.PTSNormalization
import Start.LambdaPiSN

/-
**`λΠ` as a pure type system.**

The pure type systems of `Start/PTSBasic.lean` are absorbed from github.com/openai/math
(directory `lean/OAI/Computability/TypeSystem`, family 245, paper "Weak and strong normalization
in pure type systems"; see `NOTICE`).  This module is this library's own: it places the library's
`λΠ` (`Start/LambdaPi.lean`, `Start/LambdaPiTyping.lean`) inside that framework.

* `PureTypeSystem.lambdaPiSpec` — the specification with sorts `∗ : □` and rules `(∗,s,s)`;
* `PureTypeSystem.toTm` — the syntax `Expr Srt` of the framework is the syntax `LambdaPi.Tm`,
  constructor for constructor; `toTm` commutes with renaming, substitution and instantiation,
  and sends a framework β-step to a `λΠ` β-step (`beta_toTm`);
* `PureTypeSystem.HasType.toTyping` — every framework derivation for `lambdaPiSpec` is a `λΠ`
  derivation, and valid contexts are well formed;
* `PureTypeSystem.lambdaPi_systemStronglyNormalizing` — **`lambdaPiSpec` is strongly normalizing
  in the framework's sense**, obtained from `LambdaPi.Typing.sn` of `Start/LambdaPiSN.lean`.

`Start/LambdaPiSN.lean` is *not* re-derived from `PureTypeSystem.weak_implies_strong`: that
theorem assumes system-wide weak normalization, and the only proof of weak normalization of `λΠ`
available is itself a corollary of strong normalization, so routing through it would be circular.
The Tait-style proof stays independent; this module only shows the two statements are about the
same system (`lambdaPi_weak_implies_strong_consistent` records that the framework theorem
applies to it).
-/

set_option autoImplicit false

namespace PureTypeSystem

open LambdaPi (Srt Tm)

/-- The specification of `λΠ`: axiom `∗ : □`, and products `(∗, s, s)` for both sorts `s`. -/
def lambdaPiSpec : Specification Srt where
  axioms s t := s = Srt.star ∧ t = Srt.box
  rule s₁ s₂ s₃ := s₁ = Srt.star ∧ s₃ = s₂

/-- The framework syntax over the sorts of `λΠ` is the `λΠ` syntax. -/
def toTm : Expr Srt → Tm
  | .var n => Tm.var n
  | .sort s => Tm.sort s
  | .app f a => Tm.app (toTm f) (toTm a)
  | .lam A b => Tm.lam (toTm A) (toTm b)
  | .pi A B => Tm.pi (toTm A) (toTm B)

theorem liftRen_eq_upr (ρ : ℕ → ℕ) : Expr.liftRen ρ = LambdaPi.upr ρ := by
  funext n; cases n <;> rfl

theorem toTm_rename (M : Expr Srt) (ρ : ℕ → ℕ) :
    toTm (M.rename ρ) = LambdaPi.rename ρ (toTm M) := by
  induction M generalizing ρ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [Expr.rename, toTm, ihf, iha, LambdaPi.rename]
  | lam A b ihA ihb => simp only [Expr.rename, toTm, ihA, ihb, LambdaPi.rename, liftRen_eq_upr]
  | pi A B ihA ihB => simp only [Expr.rename, toTm, ihA, ihB, LambdaPi.rename, liftRen_eq_upr]

theorem toTm_liftSub (σ : ℕ → Expr Srt) :
    (fun n => toTm (Expr.liftSub σ n)) = LambdaPi.up (fun n => toTm (σ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [Expr.liftSub_succ, toTm_rename]; rfl

theorem toTm_subst (M : Expr Srt) (σ : ℕ → Expr Srt) :
    toTm (M.subst σ) = LambdaPi.subst (fun n => toTm (σ n)) (toTm M) := by
  induction M generalizing σ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [Expr.subst, toTm, ihf, iha, LambdaPi.subst]
  | lam A b ihA ihb => simp only [Expr.subst, toTm, ihA, ihb, LambdaPi.subst, toTm_liftSub]
  | pi A B ihA ihB => simp only [Expr.subst, toTm, ihA, ihB, LambdaPi.subst, toTm_liftSub]

theorem toTm_instantiate (b a : Expr Srt) :
    toTm (b.instantiate a) = LambdaPi.inst (toTm a) (toTm b) := by
  rw [Expr.instantiate, toTm_subst, LambdaPi.inst]
  congr 1
  funext n
  cases n <;> rfl

/-- A framework β-step is a `λΠ` β-step. -/
theorem beta_toTm {M N : Expr Srt} (h : Beta M N) : LambdaPi.Step (toTm M) (toTm N) := by
  induction h with
  | head A b a => rw [toTm_instantiate]; exact LambdaPi.Step.beta _ _ _
  | app_left _ ih => exact LambdaPi.Step.appL _ ih
  | app_right _ ih => exact LambdaPi.Step.appR _ ih
  | lam_domain _ ih => exact LambdaPi.Step.lamL _ ih
  | lam_body _ ih => exact LambdaPi.Step.lamR _ ih
  | pi_domain _ ih => exact LambdaPi.Step.piL _ ih
  | pi_body _ ih => exact LambdaPi.Step.piR _ ih

theorem converts_toTm {M N : Expr Srt} (h : Converts M N) : LambdaPi.Conv (toTm M) (toTm N) := by
  induction h with
  | rel _ _ h => exact LambdaPi.Conv.single (beta_toTm h)
  | refl _ => exact LambdaPi.Conv.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Strong normalization of the image in `λΠ` gives strong normalization in the framework. -/
theorem stronglyNormalizing_of_sn {M : Expr Srt} (h : LambdaPi.SN (toTm M)) :
    StronglyNormalizing M := by
  have hacc : Acc (InvImage (fun a b : Tm => LambdaPi.Step b a) toTm) M :=
    InvImage.accessible toTm h
  exact Subrelation.accessible (fun hb => beta_toTm hb) hacc

/-- Every framework derivation for `lambdaPiSpec` is a `λΠ` derivation. -/
theorem HasType.toTyping {Γ : List (Expr Srt)} {M A : Expr Srt}
    (h : HasType lambdaPiSpec Γ M A) : LambdaPi.Typing (Γ.map toTm) (toTm M) (toTm A) := by
  induction h with
  | ax hst =>
      obtain ⟨rfl, rfl⟩ := hst
      exact LambdaPi.Typing.ax _
  | var _ _ =>
      rw [toTm_rename]
      exact LambdaPi.Typing.var (LambdaPi.Lookup.zero _ _)
  | weaken _ _ ihM _ =>
      rw [toTm_rename, toTm_rename]
      exact ihM.weaken _
  | product _ _ hr ihA ihB =>
      obtain ⟨h₁, rfl⟩ := hr
      exact LambdaPi.Typing.pi h₁ ihA ihB
  | abstraction _ _ ihb ihT => exact LambdaPi.Typing.lam ihT ihb
  | application _ _ ihf iha =>
      rw [toTm_instantiate]
      exact LambdaPi.Typing.app ihf iha
  | conversion _ _ hc ihM ihB => exact LambdaPi.Typing.conv ihM ihB (converts_toTm hc)

theorem ValidContext.toWf {Γ : List (Expr Srt)} (h : ValidContext lambdaPiSpec Γ) :
    LambdaPi.Wf (Γ.map toTm) := by
  induction h with
  | nil => exact LambdaPi.Wf.nil
  | cons _ hA ih => exact LambdaPi.Wf.cons ih hA.toTyping

/-- **`λΠ` is strongly normalizing as a pure type system**: every legal term of `lambdaPiSpec`
in a valid context is strongly normalizing, reductions inside type annotations included. -/
theorem lambdaPi_systemStronglyNormalizing : SystemStronglyNormalizing lambdaPiSpec := by
  intro Γ hΓ M ⟨A, hA⟩
  have hwf := hΓ.toWf
  apply stronglyNormalizing_of_sn
  rcases hA with hM | hM
  · exact hM.toTyping.sn hwf
  · rcases hM.toTyping.validity hwf with he | ⟨s, hs⟩
    · rw [he]; exact LambdaPi.sn_sort _
    · exact hs.sn hwf

/-- A strongly normalizing term has a normal form. -/
theorem weaklyNormalizing_of_stronglyNormalizing {S : Type*} {M : Expr S}
    (h : StronglyNormalizing M) : WeaklyNormalizing M := by
  induction h with
  | intro M _ ih =>
      by_cases hn : Normal M
      · exact ⟨M, Relation.ReflTransGen.refl, hn⟩
      · simp only [Normal, not_forall, not_not] at hn
        obtain ⟨N, hN⟩ := hn
        obtain ⟨K, hK, hKn⟩ := ih N hN
        exact ⟨K, Relation.ReflTransGen.head hN hK, hKn⟩

/-- Weak normalization of `lambdaPiSpec` follows from strong normalization. -/
theorem lambdaPi_systemWeaklyNormalizing : SystemWeaklyNormalizing lambdaPiSpec :=
  fun Γ hΓ M hM =>
    weaklyNormalizing_of_stronglyNormalizing (lambdaPi_systemStronglyNormalizing Γ hΓ M hM)

/-- The absorbed theorem `weak_implies_strong` applies to `λΠ`; its conclusion agrees with
`lambdaPi_systemStronglyNormalizing` (which does not use it). -/
theorem lambdaPi_weak_implies_strong_consistent : SystemStronglyNormalizing lambdaPiSpec :=
  weak_implies_strong lambdaPiSpec lambdaPi_systemWeaklyNormalizing

end PureTypeSystem
