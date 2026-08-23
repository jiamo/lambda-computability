/-
De Bruijn ⟺ locally nameless.

This module connects the de Bruijn representation of the untyped λ-calculus used throughout
this library (`Lambda`, `Start/Syntax.lean`) with the *locally nameless* representation of
`cslib` (`Cslib.LambdaCalculus.LocallyNameless.Untyped.Term`), where bound variables are de
Bruijn indices and free variables are atoms.

The translation is canonical: the free de Bruijn indices of a term are interpreted as *de Bruijn
levels*, i.e. as the atoms `0, 1, …, D-1` of an ambient context of `D` binders.  This removes any
need for an environment of names, and makes the atom `D` canonically fresh, which is what makes
the cofinitely quantified `ξ`-rule of `cslib` usable in both directions.

Main results:

* `Lambda.ofLN_toLN`, `Lambda.toLN_ofLN` — the translations are mutually inverse;
* `Lambda.closedEquiv` — closed de Bruijn terms are in bijection with closed, locally closed
  locally nameless terms;
* `Lambda.step_toLN`, `Lambda.reflect_step` — a step in one representation is exactly a step in
  the other;
* `Lambda.confluence_of_cslib` — `cslib`'s `confluent_fullBeta` transported to this library's
  reduction, and `Lambda.cslib_confluence_of_lambda` — this library's `confluence_theorem`
  transported to `cslib`'s reduction.
-/

import Start.CodeArith
import Start.BLC
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence

set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Cslib.LambdaCalculus.LocallyNameless.Untyped
open scoped Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

namespace Lambda

/-- Locally nameless λ-terms with natural numbers as atoms — the representation used by
`cslib`. -/
abbrev LNTerm := Term ℕ

/-- Translation from de Bruijn terms to locally nameless terms.  `toLN D d t` translates `t`
sitting under `d` binders of its own, inside an ambient context of `D` binders whose variables
are represented by the atoms `0, …, D-1` (de Bruijn *levels*: the innermost ambient binder is the
atom `D-1`). -/
def toLN (D : ℕ) : ℕ → Lambda → LNTerm
  | d, Lambda.var i => if i < d then Term.bvar i else Term.fvar (D - 1 - (i - d))
  | d, Lambda.app a b => Term.app (toLN D d a) (toLN D d b)
  | d, Lambda.lam u => Term.abs (toLN D (d + 1) u)

/-- Translation from locally nameless terms back to de Bruijn terms, inverse to `Lambda.toLN`. -/
def ofLN (D : ℕ) : ℕ → LNTerm → Lambda
  | _, Term.bvar i => Lambda.var i
  | d, Term.fvar a => Lambda.var (d + (D - 1 - a))
  | d, Term.app l r => Lambda.app (ofLN D d l) (ofLN D d r)
  | d, Term.abs m => Lambda.lam (ofLN D (d + 1) m)

@[simp] theorem toLN_var (D d i : ℕ) :
    toLN D d (Lambda.var i) = if i < d then Term.bvar i else Term.fvar (D - 1 - (i - d)) := rfl

@[simp] theorem toLN_app (D d : ℕ) (a b : Lambda) :
    toLN D d (Lambda.app a b) = Term.app (toLN D d a) (toLN D d b) := rfl

@[simp] theorem toLN_lam (D d : ℕ) (u : Lambda) :
    toLN D d (Lambda.lam u) = Term.abs (toLN D (d + 1) u) := rfl

@[simp] theorem ofLN_bvar (D d i : ℕ) : ofLN D d (Term.bvar i) = Lambda.var i := rfl

@[simp] theorem ofLN_fvar (D d a : ℕ) :
    ofLN D d (Term.fvar a) = Lambda.var (d + (D - 1 - a)) := rfl

@[simp] theorem ofLN_app (D d : ℕ) (l r : LNTerm) :
    ofLN D d (Term.app l r) = Lambda.app (ofLN D d l) (ofLN D d r) := rfl

@[simp] theorem ofLN_abs (D d : ℕ) (m : LNTerm) :
    ofLN D d (Term.abs m) = Lambda.lam (ofLN D (d + 1) m) := rfl

/-! ### Opening, lifting and substitution -/

/-- Opening the translation of a term with the canonically fresh atom `D` is the same as
translating it in an ambient context with one more binder. -/
theorem toLN_openRec_fvar (D : ℕ) : ∀ (d : ℕ) (u : Lambda),
    (toLN D (d + 1) u)⟦d ↝ Term.fvar D⟧ = toLN (D + 1) d u := by
  intro d u
  induction u generalizing d with
  | var i =>
      rcases lt_trichotomy i d with h | h | h
      · have h1 : i < d + 1 := by omega
        have h2 : ¬ d = i := by omega
        simp [toLN, Term.openRec, h, h1, h2]
      · subst h
        simp [toLN, Term.openRec]
      · have h1 : ¬ i < d := by omega
        have h2 : ¬ i < d + 1 := by omega
        simp only [toLN, h1, h2, if_false, Term.openRec, Term.fvar.injEq]
        omega
  | app a b iha ihb => simp [toLN, Term.openRec, iha, ihb]
  | lam u ih => simp [toLN, Term.openRec, ih]

/-- Opening at the outermost binder with the canonically fresh atom `D`. -/
theorem toLN_open_fvar (D : ℕ) (u : Lambda) :
    (toLN D 1 u) ^ Term.fvar D = toLN (D + 1) 0 u :=
  toLN_openRec_fvar D 0 u

/-- Lifting is invisible to the translation. -/
theorem toLN_lift (D : ℕ) : ∀ (e d : ℕ) (s : Lambda),
    toLN D (e + d) (Lambda.lift d e s) = toLN D e s := by
  intro e d s
  induction s generalizing e with
  | var y =>
      by_cases h : y < e
      · have h1 : y < e + d := by omega
        simp [Lambda.lift, toLN, h, h1]
      · have h1 : ¬ y + d < e + d := by omega
        simp only [Lambda.lift, h, if_false, toLN, h1, Term.fvar.injEq]
        omega
  | app a b iha ihb => simp [Lambda.lift, toLN, iha, ihb]
  | lam u ih =>
      have := ih (e + 1)
      simp only [Lambda.lift, toLN, Term.abs.injEq]
      rw [show e + d + 1 = e + 1 + d by omega]
      exact this

/-- The de Bruijn substitution of this library corresponds to `cslib`'s opening. -/
theorem toLN_subst (D : ℕ) (s : Lambda) : ∀ (d : ℕ) (t : Lambda),
    toLN D d (Lambda.subst (Lambda.lift d 0 s) d t)
      = (toLN D (d + 1) t)⟦d ↝ toLN D 0 s⟧ := by
  intro d t
  induction t generalizing d with
  | var y =>
      rcases lt_trichotomy y d with h | h | h
      · have h1 : ¬ y = d := by omega
        have h2 : ¬ y > d := by omega
        have h3 : y < d + 1 := by omega
        have h4 : ¬ d = y := by omega
        simp [Lambda.subst, toLN, h, h1, h2, h3, h4, Term.openRec]
      · subst h
        have h1 : ¬ y < y + 1 - 1 := by omega
        simp only [Lambda.subst, toLN, Nat.lt_succ_self, if_true, Term.openRec]
        have := toLN_lift D 0 y s
        simpa using this
      · have h1 : ¬ y = d := by omega
        have h2 : y > d := h
        have h3 : ¬ y - 1 < d := by omega
        have h4 : ¬ y < d + 1 := by omega
        simp only [Lambda.subst, h1, if_false, h2, if_true, toLN, h3, h4, Term.openRec,
          Term.fvar.injEq]
        omega
  | app a b iha ihb => simp [Lambda.subst, toLN, Term.openRec, iha, ihb]
  | lam u ih =>
      have hlift : Lambda.lift 1 0 (Lambda.lift d 0 s) = Lambda.lift (d + 1) 0 s := by
        rw [show d + 1 = 1 + d by omega, Lambda.lift_add]
      simp only [Lambda.subst, toLN, Term.openRec, Term.abs.injEq, hlift]
      exact ih (d + 1)

/-- The instance of `Lambda.toLN_subst` used by the β-rule. -/
theorem toLN_subst_zero (D : ℕ) (s t : Lambda) :
    toLN D 0 (Lambda.subst s 0 t) = (toLN D 1 t) ^ (toLN D 0 s) := by
  have := toLN_subst D s 0 t
  rwa [Lambda.lift_zero] at this

/-! ### Local closure and free atoms -/

/-- Translations are locally closed at the depth they are translated at. -/
theorem lcAt_toLN (D : ℕ) : ∀ (d : ℕ) (t : Lambda), Term.LcAt d (toLN D d t) = Bool.true := by
  intro d t
  induction t generalizing d with
  | var i =>
      by_cases h : i < d <;> simp [toLN, Term.LcAt, h]
  | app a b iha ihb => simp [toLN, Term.LcAt, iha, ihb]
  | lam u ih => simp [toLN, Term.LcAt, ih]

/-- Translations at depth `0` are locally closed. -/
theorem lc_toLN (D : ℕ) (t : Lambda) : (toLN D 0 t).LC :=
  (Term.lcAt_iff_LC _).1 (lcAt_toLN D 0 t)

/-- The atoms of a translation are the levels of the ambient context. -/
theorem fv_toLN (D : ℕ) : ∀ (d : ℕ) (t : Lambda), freeMax t ≤ d + D →
    ∀ a ∈ (toLN D d t).fv, a < D := by
  intro d t
  induction t generalizing d with
  | var i =>
      intro hle a ha
      by_cases h : i < d
      · simp [toLN, h] at ha
      · simp only [toLN, h, if_false, Term.fv, Finset.mem_singleton] at ha
        simp only [freeMax_var] at hle
        omega
  | app a b iha ihb =>
      intro hle x hx
      simp only [toLN, Term.fv, Finset.mem_union] at hx
      simp only [freeMax_app, max_le_iff] at hle
      rcases hx with hx | hx
      · exact iha d hle.1 x hx
      · exact ihb d hle.2 x hx
  | lam u ih =>
      intro hle x hx
      simp only [toLN, Term.fv] at hx
      simp only [freeMax_lam] at hle
      exact ih (d + 1) (by omega) x hx

/-- Free indices bound the atoms used: a closed term uses no atoms. -/
theorem fv_toLN_closed (t : Lambda) (h : freeMax t = 0) : (toLN 0 0 t).fv = ∅ := by
  refine Finset.eq_empty_of_forall_notMem ?_
  intro a ha
  have := fv_toLN 0 0 t (by omega) a ha
  omega

/-! ### The two translations are mutually inverse -/

/-- `Lambda.ofLN` undoes `Lambda.toLN`. -/
theorem ofLN_toLN (D : ℕ) : ∀ (d : ℕ) (t : Lambda), freeMax t ≤ d + D →
    ofLN D d (toLN D d t) = t := by
  intro d t
  induction t generalizing d with
  | var i =>
      intro hle
      simp only [freeMax_var] at hle
      by_cases h : i < d
      · simp [toLN, h]
      · simp only [toLN, h, if_false, ofLN_fvar, Lambda.var.injEq]
        omega
  | app a b iha ihb =>
      intro hle
      simp only [freeMax_app, max_le_iff] at hle
      simp [toLN, iha d hle.1, ihb d hle.2]
  | lam u ih =>
      intro hle
      simp only [freeMax_lam] at hle
      simp [toLN, ih (d + 1) (by omega)]

/-- `Lambda.toLN` undoes `Lambda.ofLN` on locally closed terms whose atoms are levels. -/
theorem toLN_ofLN (D : ℕ) : ∀ (d : ℕ) (M : LNTerm), Term.LcAt d M = Bool.true →
    (∀ a ∈ M.fv, a < D) → toLN D d (ofLN D d M) = M := by
  intro d M
  induction M generalizing d with
  | bvar i =>
      intro hlc _
      simp only [Term.LcAt, decide_eq_true_eq] at hlc
      simp [hlc]
  | fvar a =>
      intro _ hfv
      have ha : a < D := hfv a (by simp [Term.fv])
      have h1 : ¬ d + (D - 1 - a) < d := by omega
      simp only [ofLN_fvar, toLN, h1, if_false, Term.fvar.injEq]
      omega
  | app l r ihl ihr =>
      intro hlc hfv
      simp only [Term.LcAt, Bool.and_eq_true] at hlc
      simp only [ofLN_app, toLN, Term.app.injEq]
      refine ⟨ihl d hlc.1 ?_, ihr d hlc.2 ?_⟩ <;> intro a ha <;> exact hfv a (by simp [Term.fv, ha])
  | abs m ih =>
      intro hlc hfv
      simp only [Term.LcAt] at hlc
      simp only [ofLN_abs, toLN, Term.abs.injEq]
      exact ih (d + 1) hlc (by intro a ha; exact hfv a (by simpa [Term.fv] using ha))

/-- The de Bruijn indices of a back-translation are bounded. -/
theorem freeMax_ofLN (D : ℕ) : ∀ (d : ℕ) (M : LNTerm), Term.LcAt d M = Bool.true →
    (∀ a ∈ M.fv, a < D) → freeMax (ofLN D d M) ≤ d + D := by
  intro d M
  induction M generalizing d with
  | bvar i =>
      intro hlc _
      simp only [Term.LcAt, decide_eq_true_eq] at hlc
      simp only [ofLN_bvar, freeMax_var]
      omega
  | fvar a =>
      intro _ hfv
      have ha : a < D := hfv a (by simp [Term.fv])
      simp only [ofLN_fvar, freeMax_var]
      omega
  | app l r ihl ihr =>
      intro hlc hfv
      simp only [Term.LcAt, Bool.and_eq_true] at hlc
      simp only [ofLN_app, freeMax_app, max_le_iff]
      refine ⟨ihl d hlc.1 ?_, ihr d hlc.2 ?_⟩ <;> intro a ha <;> exact hfv a (by simp [Term.fv, ha])
  | abs m ih =>
      intro hlc hfv
      simp only [Term.LcAt] at hlc
      have := ih (d + 1) hlc (by intro a ha; exact hfv a (by simpa [Term.fv] using ha))
      simp only [ofLN_abs, freeMax_lam]
      omega

/-- **Closed de Bruijn terms are exactly closed locally closed terms.** -/
def closedEquiv : {t : Lambda // freeMax t = 0} ≃ {M : LNTerm // M.LC ∧ M.fv = ∅} where
  toFun t := ⟨toLN 0 0 t.1, lc_toLN 0 t.1, fv_toLN_closed t.1 t.2⟩
  invFun M := ⟨ofLN 0 0 M.1, by
    have hlc : Term.LcAt 0 M.1 = Bool.true := (Term.lcAt_iff_LC _).2 M.2.1
    have hfv : ∀ a ∈ M.1.fv, a < 0 := by
      intro a ha
      rw [M.2.2] at ha
      simp at ha
    have := freeMax_ofLN 0 0 M.1 hlc hfv
    omega⟩
  left_inv := by
    intro t
    ext
    exact ofLN_toLN 0 0 t.1 (by omega)
  right_inv := by
    intro M
    ext
    refine toLN_ofLN 0 0 M.1 ((Term.lcAt_iff_LC _).2 M.2.1) ?_
    intro a ha
    rw [M.2.2] at ha
    simp at ha

/-! ### Reduction -/

/-- Lifting increases the free indices by at most `n`. -/
theorem freeMax_lift_le (n : ℕ) : ∀ (k : ℕ) (t : Lambda),
    freeMax (Lambda.lift n k t) ≤ freeMax t + n := by
  intro k t
  induction t generalizing k with
  | var i =>
      by_cases h : i < k <;> simp only [Lambda.lift, h, if_true, if_false, freeMax_var] <;> omega
  | app a b iha ihb =>
      have ha := iha k
      have hb := ihb k
      simp only [Lambda.lift, freeMax_app, max_le_iff]
      omega
  | lam u ih =>
      have := ih (k + 1)
      simp only [Lambda.lift, freeMax_lam]
      omega

/-- Free indices do not increase under substitution. -/
theorem freeMax_subst_le : ∀ (t s : Lambda) (x : ℕ),
    freeMax (Lambda.subst s x t) ≤ max (freeMax t - 1) (max (freeMax s) x) := by
  intro t
  induction t with
  | var y =>
      intro s x
      rcases lt_trichotomy y x with h | h | h
      · have h1 : ¬ y = x := by omega
        have h2 : ¬ y > x := by omega
        simp only [Lambda.subst, h1, if_false, h2, freeMax_var]
        omega
      · subst h
        have hs : Lambda.subst s y (Lambda.var y) = s := by simp [Lambda.subst]
        rw [hs]
        omega
      · have h1 : ¬ y = x := by omega
        simp only [Lambda.subst, h1, if_false, h, if_true, freeMax_var]
        omega
  | app a b iha ihb =>
      intro s x
      have ha := iha s x
      have hb := ihb s x
      simp only [Lambda.subst, freeMax_app]
      omega
  | lam u ih =>
      intro s x
      have h := ih (Lambda.lift 1 0 s) (x + 1)
      have hl := freeMax_lift_le 1 0 s
      simp only [Lambda.subst, freeMax_lam]
      omega

/-- Free indices do not increase along a reduction step. -/
theorem freeMax_step_le {t t' : Lambda} (h : Lambda.step t t') : freeMax t' ≤ freeMax t := by
  induction h with
  | beta t₁ t₂ =>
      have := freeMax_subst_le t₁ t₂ 0
      simp only [freeMax_app, freeMax_lam]
      omega
  | app_left t₁ t₁' t₂ _ ih => simp only [freeMax_app]; omega
  | app_right t₁ t₂ t₂' _ ih => simp only [freeMax_app]; omega
  | lam u u' _ ih => simp only [freeMax_lam]; omega

/-- **Forward simulation**: a de Bruijn β-step translates to a `cslib` β-step. -/
theorem step_toLN {t t' : Lambda} (h : Lambda.step t t') :
    ∀ D : ℕ, freeMax t ≤ D → (toLN D 0 t) ⭢βᶠ (toLN D 0 t') := by
  induction h with
  | beta t₁ t₂ =>
      intro D _
      rw [toLN_app, toLN_lam, toLN_subst_zero]
      exact Term.Xi.base (Term.Beta.beta (lc_toLN D (Lambda.lam t₁)) (lc_toLN D t₂))
  | app_left t₁ t₁' t₂ _ ih =>
      intro D hD
      simp only [freeMax_app, max_le_iff] at hD
      exact Term.Xi.appR (lc_toLN D t₂) (ih D hD.1)
  | app_right t₁ t₂ t₂' _ ih =>
      intro D hD
      simp only [freeMax_app, max_le_iff] at hD
      exact Term.Xi.appL (lc_toLN D t₁) (ih D hD.2)
  | lam u u' hstep ih =>
      intro D hD
      simp only [freeMax_lam] at hD
      have hu' : freeMax u' ≤ 1 + D := by
        have := freeMax_step_le hstep
        omega
      have key : ((toLN D 1 u) ^ Term.fvar D) ⭢βᶠ ((toLN D 1 u') ^ Term.fvar D) := by
        have h1 := toLN_openRec_fvar D 0 u
        have h2 := toLN_openRec_fvar D 0 u'
        have h3 := ih (D + 1) (by omega)
        rw [show ((toLN D 1 u) ^ Term.fvar D) = toLN (D + 1) 0 u from h1,
          show ((toLN D 1 u') ^ Term.fvar D) = toLN (D + 1) 0 u' from h2]
        exact h3
      refine Term.Xi.abs ∅ ?_
      intro x _
      have hfvu : D ∉ (toLN D 1 u).fv := by
        intro hmem
        have := fv_toLN D 1 u (by omega) D hmem
        omega
      have hfvu' : D ∉ (toLN D 1 u').fv := by
        intro hmem
        have := fv_toLN D 1 u' (by omega) D hmem
        omega
      rw [Term.subst_intro D (Term.fvar x) (toLN D 1 u) hfvu,
        Term.subst_intro D (Term.fvar x) (toLN D 1 u') hfvu']
      exact Term.FullBeta.redex_subst_cong _ _ D x key

/-- **Forward simulation**, multi-step version. -/
theorem reduces_toLN {t t' : Lambda} (h : Lambda.reduces t t') (D : ℕ) (hD : freeMax t ≤ D) :
    (toLN D 0 t) ↠βᶠ (toLN D 0 t') := by
  induction h with
  | refl t => exact Relation.ReflTransGen.refl
  | step t₁ t₂ t₃ hs _ ih =>
      have h1 : freeMax t₂ ≤ D := le_trans (freeMax_step_le hs) hD
      exact Relation.ReflTransGen.head (step_toLN hs D hD) (ih h1)

/-- **Reflection**: every `cslib` β-step out of a translated term is the translation of a
de Bruijn β-step. -/
theorem reflect_step : ∀ (t : Lambda) (D : ℕ) (N : LNTerm), freeMax t ≤ D →
    (toLN D 0 t) ⭢βᶠ N → ∃ t', toLN D 0 t' = N ∧ Lambda.step t t' := by
  intro t
  induction t with
  | var i =>
      intro D N _ hstep
      simp only [toLN, Nat.not_lt_zero, if_false] at hstep
      exact absurd hstep (by rintro (_ | _ | _ | _); rename_i h; cases h)
  | app a b iha ihb =>
      intro D N hD hstep
      simp only [freeMax_app, max_le_iff] at hD
      rw [toLN_app] at hstep
      cases hstep with
      | base hbeta =>
          cases a with
          | var i =>
              exfalso
              simp only [toLN, Nat.not_lt_zero, if_false] at hbeta
              cases hbeta
          | app c d =>
              exfalso
              simp only [toLN_app] at hbeta
              cases hbeta
          | lam u =>
              simp only [toLN_lam] at hbeta
              cases hbeta with
              | beta =>
                  exact ⟨Lambda.subst b 0 u, (toLN_subst_zero D b u).symm ▸ rfl,
                    Lambda.step.beta u b⟩
      | appL hlc hxi =>
          obtain ⟨b', hb', hstepb⟩ := ihb D _ hD.2 hxi
          exact ⟨Lambda.app a b', by rw [toLN_app, hb'], Lambda.step.app_right a b b' hstepb⟩
      | appR hlc hxi =>
          obtain ⟨a', ha', hstepa⟩ := iha D _ hD.1 hxi
          exact ⟨Lambda.app a' b, by rw [toLN_app, ha'], Lambda.step.app_left a a' b hstepa⟩
  | lam u ih =>
      intro D N hD hstep
      simp only [freeMax_lam] at hD
      have hu : freeMax u ≤ 1 + D := by omega
      rw [toLN_lam] at hstep
      cases hstep with
      | base hbeta => cases hbeta
      | abs xs hcof =>
          rename_i N₀
          -- the atoms of `N₀` are among those of the source
          have hsub : N₀.fv ⊆ (toLN D 1 u).fv := by
            have := Term.FullBeta.step_not_fv (M := Term.abs (toLN D 1 u)) (N := Term.abs N₀)
              (Term.Xi.abs xs hcof)
            simpa [Term.fv] using this
          have hDu : D ∉ (toLN D 1 u).fv := by
            intro hmem
            have := fv_toLN D 1 u hu D hmem
            omega
          have hDN : D ∉ N₀.fv := fun hmem => hDu (hsub hmem)
          obtain ⟨x₀, hx₀⟩ :=
            Cslib.HasFresh.fresh_exists (xs ∪ (toLN D 1 u).fv ∪ N₀.fv)
          simp only [Finset.mem_union, not_or] at hx₀
          obtain ⟨⟨hx₀xs, hx₀u⟩, hx₀N⟩ := hx₀
          have hstep₀ := hcof x₀ hx₀xs
          have hrename := Term.FullBeta.redex_subst_cong _ _ x₀ D hstep₀
          rw [← Term.subst_intro x₀ (Term.fvar D) (toLN D 1 u) hx₀u,
            ← Term.subst_intro x₀ (Term.fvar D) N₀ hx₀N] at hrename
          rw [toLN_open_fvar D u] at hrename
          obtain ⟨u', hu'eq, hu'step⟩ := ih (D + 1) _ (by omega) hrename
          have hu'free : freeMax u' ≤ 1 + D := by
            have := freeMax_step_le hu'step
            omega
          have hDu' : D ∉ (toLN D 1 u').fv := by
            intro hmem
            have := fv_toLN D 1 u' hu'free D hmem
            omega
          have hopen : (toLN D 1 u') ^ Term.fvar D = N₀ ^ Term.fvar D := by
            rw [toLN_open_fvar D u']
            exact hu'eq
          have : toLN D 1 u' = N₀ := Term.open_injective D _ _ hDu' hDN hopen
          exact ⟨Lambda.lam u', by rw [toLN_lam, this], Lambda.step.lam u u' hu'step⟩

/-- **Reflection**, multi-step version. -/
theorem freeMax_reduces_le {t t' : Lambda} (h : Lambda.reduces t t') : freeMax t' ≤ freeMax t := by
  induction h with
  | refl t => exact le_rfl
  | step t₁ t₂ t₃ hs _ ih => exact le_trans ih (freeMax_step_le hs)

/-- **Reflection**, multi-step version. -/
theorem reflect_reduces (D : ℕ) : ∀ (t : Lambda) (N : LNTerm), freeMax t ≤ D →
    (toLN D 0 t) ↠βᶠ N → ∃ t', toLN D 0 t' = N ∧ Lambda.reduces t t' := by
  intro t N hD h
  induction h with
  | refl => exact ⟨t, rfl, Lambda.reduces.refl t⟩
  | tail hred hstep ih =>
      obtain ⟨t₁, ht₁, hred₁⟩ := ih
      have hfree₁ : freeMax t₁ ≤ D := le_trans (freeMax_reduces_le hred₁) hD
      subst ht₁
      obtain ⟨t₂, ht₂, hstep₂⟩ := reflect_step t₁ D _ hfree₁ hstep
      exact ⟨t₂, ht₂, Lambda.reduces_trans hred₁ (Lambda.reduces.step t₁ t₂ t₂ hstep₂
        (Lambda.reduces.refl t₂))⟩

/-- **Church–Rosser for this library, obtained from `cslib`'s confluence of full β-reduction.**
This is an independent proof of `Lambda.confluence_theorem` through the bridge. -/
theorem confluence_of_cslib : Lambda.Confluence := by
  intro t t₁ t₂ h₁ h₂
  have hD₁ : freeMax t ≤ freeMax t := le_rfl
  have H₁ := reduces_toLN h₁ (freeMax t) hD₁
  have H₂ := reduces_toLN h₂ (freeMax t) hD₁
  obtain ⟨M₃, hM₁, hM₂⟩ := Term.confluent_fullBeta H₁ H₂
  have hf₁ : freeMax t₁ ≤ freeMax t := freeMax_reduces_le h₁
  have hf₂ : freeMax t₂ ≤ freeMax t := freeMax_reduces_le h₂
  obtain ⟨u₁, hu₁, hru₁⟩ := reflect_reduces (freeMax t) t₁ M₃ hf₁ hM₁
  obtain ⟨u₂, hu₂, hru₂⟩ := reflect_reduces (freeMax t) t₂ M₃ hf₂ hM₂
  have hfu₁ : freeMax u₁ ≤ freeMax t := le_trans (freeMax_reduces_le hru₁) hf₁
  have hfu₂ : freeMax u₂ ≤ freeMax t := le_trans (freeMax_reduces_le hru₂) hf₂
  have hsame : u₁ = u₂ := by
    have e₁ := ofLN_toLN (freeMax t) 0 u₁ (by omega)
    have e₂ := ofLN_toLN (freeMax t) 0 u₂ (by omega)
    rw [hu₁] at e₁
    rw [hu₂] at e₂
    rw [← e₁, ← e₂]
  exact ⟨u₁, hru₁, hsame ▸ hru₂⟩

/-- **Confluence of `cslib`'s full β-reduction, obtained from this library's
`Lambda.confluence_theorem`** — the transport in the other direction, for terms that are locally
closed and whose atoms lie below `D`. -/
theorem cslib_confluence_of_lambda (D : ℕ) (M M₁ M₂ : LNTerm)
    (hlc : Term.LcAt 0 M = Bool.true) (hfv : ∀ a ∈ M.fv, a < D)
    (h₁ : M ↠βᶠ M₁) (h₂ : M ↠βᶠ M₂) : ∃ M₃, (M₁ ↠βᶠ M₃) ∧ (M₂ ↠βᶠ M₃) := by
  have hM : toLN D 0 (ofLN D 0 M) = M := toLN_ofLN D 0 M hlc hfv
  have hfree : freeMax (ofLN D 0 M) ≤ D := by
    have := freeMax_ofLN D 0 M hlc hfv
    omega
  rw [← hM] at h₁ h₂
  obtain ⟨t₁, ht₁, hr₁⟩ := reflect_reduces D _ M₁ hfree h₁
  obtain ⟨t₂, ht₂, hr₂⟩ := reflect_reduces D _ M₂ hfree h₂
  obtain ⟨t₃, hr₁₃, hr₂₃⟩ := Lambda.confluence_theorem hr₁ hr₂
  refine ⟨toLN D 0 t₃, ?_, ?_⟩
  · rw [← ht₁]
    exact reduces_toLN hr₁₃ D (le_trans (freeMax_reduces_le hr₁) hfree)
  · rw [← ht₂]
    exact reduces_toLN hr₂₃ D (le_trans (freeMax_reduces_le hr₂) hfree)

/-! ### Three representations -/

/-- Closed locally nameless terms are in bijection with the closed binary-λ-calculus strings:
the three representations of this library (de Bruijn, locally nameless, BLC) agree. -/
def closedBitsEquiv :
    {M : LNTerm // M.LC ∧ M.fv = ∅} ≃
      {bs : {bs : List Bool // isBLC bs = Bool.true} // freeMax (bitsEquiv.symm bs) = 0} :=
  closedEquiv.symm.trans (Equiv.subtypeEquiv bitsEquiv (by simp))

end Lambda
