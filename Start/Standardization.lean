/-
Standardization for weak head reduction.

A *standard* reduction performs weak head steps first and only then reduces
inside the arguments and under abstractions.  `Lambda.SRed` is the usual
inductive presentation of this notion, with `Lambda.SRed true` the standard
reductions and `Lambda.SRed false` the *internal* ones (those that contract no
weak head redex at all).

The two results exported by this file are

* `Lambda.sred_of_reduces` — every reduction can be standardized;
* `Lambda.hasWhnfEval_of_reduces_whnf` — **the weak head strategy is
  normalizing**: if some reduction of `t` reaches a weak head normal form, then
  the weak head strategy itself terminates on `t`.

The second statement is what makes it possible to prove that a term has *no*
normal form, by exhibiting an infinite descent along the weak head strategy.
-/

import Start.WeakHead

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- Standard reductions.  `SRed true M N` is a standard reduction: some weak head
steps, followed by a reduction that contracts no weak head redex.  `SRed false M N`
is such an *internal* reduction. -/
inductive SRed : Bool → Lambda → Lambda → Prop
  | head {M M' N : Lambda} : wstep M M' → SRed true M' N → SRed true M N
  | int {M N : Lambda} : SRed false M N → SRed true M N
  | var (n : ℕ) : SRed false (Lambda.var n) (Lambda.var n)
  | lam {P P' : Lambda} : SRed true P P' → SRed false (Lambda.lam P) (Lambda.lam P')
  | app {M M' N N' : Lambda} : SRed false M M' → SRed true N N' →
      SRed false (Lambda.app M N) (Lambda.app M' N')

------------------------------------------------------------------------
-- Basic properties
------------------------------------------------------------------------

/-- Standard and internal reduction are reflexive. -/
theorem sred_refl : ∀ (b : Bool) (t : Lambda), SRed b t t := by
  have key : ∀ t : Lambda, SRed false t t := by
    intro t
    induction t with
    | var n => exact SRed.var n
    | lam P ih => exact SRed.lam (SRed.int ih)
    | app A B ihA ihB => exact SRed.app ihA (SRed.int ihB)
  intro b t
  cases b with
  | false => exact key t
  | true => exact SRed.int (key t)

/-- Standard reductions are reductions. -/
theorem reduces_of_sred {b : Bool} {M N : Lambda} (h : SRed b M N) : Lambda.reduces M N := by
  induction h with
  | head hw _ ih =>
      exact Lambda.reduces.step _ _ _ (wstep_imp_step hw) ih
  | int _ ih => exact ih
  | var n => exact Lambda.reduces.refl _
  | lam _ ih => exact Lambda.reduces_lam ih
  | app _ _ ih1 ih2 => exact Lambda.reduces_app ih1 ih2

/-- Standard reductions of the two parts of an application compose into a standard
reduction of the application. -/
theorem sred_app {A A' B B' : Lambda} (hA : SRed true A A') (hB : SRed true B B') :
    SRed true (Lambda.app A B) (Lambda.app A' B') := by
  generalize hb : true = b at hA
  induction hA with
  | @head M M' N hw _ ih =>
      exact SRed.head (wstep.app B hw) (ih hb)
  | int hi => exact SRed.int (SRed.app hi hB)
  | var n => exact absurd hb (by simp)
  | lam _ _ => exact absurd hb (by simp)
  | app _ _ _ _ => exact absurd hb (by simp)

------------------------------------------------------------------------
-- Lifting and substitution
------------------------------------------------------------------------

/-- Weak head steps are preserved by lifting. -/
theorem wstep_lift {M M' : Lambda} (h : wstep M M') (n k : ℕ) :
    wstep (Lambda.lift n k M) (Lambda.lift n k M') := by
  induction h generalizing k with
  | beta P Q =>
      rw [Lambda.lift_subst_zero]
      exact wstep.beta _ _
  | app N _ ih => exact wstep.app _ (ih k)

/-- Weak head steps are preserved by substitution in the reduced term. -/
theorem wstep_subst {M M' : Lambda} (h : wstep M M') (Q : Lambda) (x : ℕ) :
    wstep (Lambda.subst Q x M) (Lambda.subst Q x M') := by
  induction h generalizing x with
  | beta P R =>
      rw [Lambda.subst_subst_zero]
      exact wstep.beta _ _
  | app N _ ih => exact wstep.app _ (ih x)

/-- Standard reductions are preserved by lifting. -/
theorem sred_lift {b : Bool} {M N : Lambda} (h : SRed b M N) (n k : ℕ) :
    SRed b (Lambda.lift n k M) (Lambda.lift n k N) := by
  induction h generalizing k with
  | head hw _ ih => exact SRed.head (wstep_lift hw n k) (ih k)
  | int _ ih => exact SRed.int (ih k)
  | var m =>
      simp only [Lambda.lift]
      split_ifs <;> exact SRed.var _
  | lam _ ih => exact SRed.lam (ih (k + 1))
  | app _ _ ih1 ih2 => exact SRed.app (ih1 k) (ih2 k)

/-- **Standard reductions are closed under substitution.** -/
theorem sred_subst {b : Bool} {P P' : Lambda} (hP : SRed b P P') :
    ∀ {Q Q' : Lambda} (x : ℕ), SRed true Q Q' →
      SRed true (Lambda.subst Q x P) (Lambda.subst Q' x P') := by
  induction hP with
  | head hw _ ih =>
      intro Q Q' x hQ
      exact SRed.head (wstep_subst hw Q x) (ih x hQ)
  | int _ ih => intro Q Q' x hQ; exact ih x hQ
  | var n =>
      intro Q Q' x hQ
      simp only [Lambda.subst]
      split_ifs
      · exact hQ
      · exact sred_refl _ _
      · exact sred_refl _ _
  | @lam A A' _ ih =>
      intro Q Q' x hQ
      simp only [Lambda.subst]
      exact SRed.int (SRed.lam (ih (x + 1) (sred_lift hQ 1 0)))
  | app _ _ ih1 ih2 =>
      intro Q Q' x hQ
      simp only [Lambda.subst]
      exact sred_app (ih1 x hQ) (ih2 x hQ)

------------------------------------------------------------------------
-- Standardization
------------------------------------------------------------------------

/-- An internal reduction whose target is an abstraction starts from an abstraction. -/
theorem eq_lam_of_sred_false_lam {A P : Lambda} (h : SRed false A (Lambda.lam P)) :
    ∃ P₀, A = Lambda.lam P₀ ∧ SRed true P₀ P := by
  cases h with
  | lam h => exact ⟨_, rfl, h⟩

/-- A standard reduction can be extended by one beta step. -/
theorem sred_step {b : Bool} {M N : Lambda} (h : SRed b M N) :
    ∀ {L : Lambda}, Lambda.step N L → SRed true M L := by
  induction h with
  | head hw _ ih => intro L hst; exact SRed.head hw (ih hst)
  | int _ ih => intro L hst; exact ih hst
  | var n => intro L hst; cases hst
  | @lam A A' _ ih =>
      intro L hst
      cases hst with
      | lam _ B' hB => exact SRed.int (SRed.lam (ih hB))
  | @app A A' B B' hA hB ihA ihB =>
      intro L hst
      cases hst with
      | beta P Q =>
          obtain ⟨P₀, rfl, hP₀⟩ := eq_lam_of_sred_false_lam hA
          exact SRed.head (wstep.beta P₀ B) (sred_subst hP₀ 0 hB)
      | app_left a a' b hstep => exact sred_app (ihA hstep) hB
      | app_right a b b' hstep => exact SRed.int (SRed.app hA (ihB hstep))

/-- A standard reduction can be extended by a reduction. -/
theorem sred_reduces {M N L : Lambda} (h : SRed true M N) (hr : Lambda.reduces N L) :
    SRed true M L := by
  induction hr generalizing M with
  | refl _ => exact h
  | step a b c hst _ ih => exact ih (sred_step h hst)

/-- **Standardization**: every reduction is standard. -/
theorem sred_of_reduces {M N : Lambda} (h : Lambda.reduces M N) : SRed true M N :=
  sred_reduces (sred_refl true M) h

------------------------------------------------------------------------
-- The weak head strategy is normalizing
------------------------------------------------------------------------

/-- An internal reduction cannot create a weak head normal form. -/
theorem isWhnf_of_sred_false {b : Bool} {M N : Lambda} (h : SRed b M N) :
    b = false → IsWhnf N → IsWhnf M := by
  induction h with
  | head _ _ _ => intro hb; exact absurd hb (by simp)
  | int _ _ => intro hb; exact absurd hb (by simp)
  | var n => intro _ _; exact isWhnf_var n
  | lam _ _ => intro _ _; exact isWhnf_lam _
  | @app A A' B B' hA _ ihA _ =>
      intro _ hN
      rw [isWhnf_app_iff] at hN ⊢
      obtain ⟨h1, h2⟩ := hN
      refine ⟨ihA rfl h1, ?_⟩
      rintro P rfl
      cases hA with
      | lam _ => exact h2 _ rfl

/-- If a standard reduction reaches a weak head normal form, the weak head strategy
terminates on its source. -/
theorem hasWhnfEval_of_sred {b : Bool} {t u : Lambda} (hs : SRed b t u) :
    b = true → IsWhnf u → HasWhnfEval t := by
  induction hs with
  | head hw _ ih => intro hb hu; exact hasWhnfEval_of_wstep hw (ih hb hu)
  | int hi _ => intro _ hu; exact hasWhnfEval_of_isWhnf (isWhnf_of_sred_false hi rfl hu)
  | var n => intro hb; exact absurd hb (by simp)
  | lam _ _ => intro hb; exact absurd hb (by simp)
  | app _ _ _ _ => intro hb; exact absurd hb (by simp)

/-- **The weak head strategy is normalizing.**  If some reduction of `t` reaches a
weak head normal form, the weak head strategy terminates on `t`. -/
theorem hasWhnfEval_of_reduces_whnf {t u : Lambda} (h : Lambda.reduces t u) (hu : IsWhnf u) :
    HasWhnfEval t :=
  hasWhnfEval_of_sred (sred_of_reduces h) rfl hu

end Lambda

end
