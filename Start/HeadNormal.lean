/-
Head normal forms.

A *head normal form* is a term `λx₁ … xₙ. y M₁ … Mₘ`: an abstraction prefix over a term whose
head is a variable.  Head normal forms are the syntactic side of the semantic dividing line
between terms that carry information and terms that do not, and they are what the adequacy
theorem for the denotational models talks about.

This module defines the notion and its basic closure properties:

* `Lambda.IsHnf` — being a head normal form, defined over the neutral terms `y M₁ … Mₘ` of
  `Start/Leftmost.lean`;
* `Lambda.HasHnf` — reducing to a head normal form;
* `Lambda.HasHnf.of_reduces` — head normalizability is inherited backwards along a reduction
  (if `t ↠ u` and `u` has a head normal form, so does `t`);
* `Lambda.hasHnf_lam`, `Lambda.hasHnf_of_neutral` — the two ways of building one.
-/

import Start.Leftmost

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- A *head normal form* is a term `λx₁ … xₙ. y M₁ … Mₘ`: some abstractions in front of a
neutral term. -/
inductive IsHnf : Lambda → Prop
  | neutral {t : Lambda} : Neutral t → IsHnf t
  | lam {t : Lambda} : IsHnf t → IsHnf (Lambda.lam t)

/-- A term *has* a head normal form when some reduction of it is one. -/
def HasHnf (t : Lambda) : Prop := ∃ u, Lambda.reduces t u ∧ IsHnf u

theorem hasHnf_of_isHnf {t : Lambda} (h : IsHnf t) : HasHnf t :=
  ⟨t, Lambda.reduces.refl t, h⟩

theorem hasHnf_of_neutral {t : Lambda} (h : Neutral t) : HasHnf t :=
  hasHnf_of_isHnf (IsHnf.neutral h)

theorem hasHnf_var (n : ℕ) : HasHnf (Lambda.var n) :=
  hasHnf_of_neutral (Neutral.var n)

/-- Head normalizability travels backwards along reductions. -/
theorem HasHnf.of_reduces {t u : Lambda} (hr : Lambda.reduces t u) (h : HasHnf u) : HasHnf t := by
  obtain ⟨v, hv, hhnf⟩ := h
  exact ⟨v, Lambda.reduces_trans hr hv, hhnf⟩

/-- An abstraction has a head normal form as soon as its body does. -/
theorem hasHnf_lam {t : Lambda} (h : HasHnf t) : HasHnf (Lambda.lam t) := by
  obtain ⟨u, hu, hhnf⟩ := h
  exact ⟨Lambda.lam u, Lambda.reduces_lam hu, IsHnf.lam hhnf⟩

/-- Applying a neutral term to anything is again neutral, so it is a head normal form. -/
theorem hasHnf_app_of_neutral {t : Lambda} (h : Neutral t) (s : Lambda) :
    HasHnf (Lambda.app t s) :=
  hasHnf_of_neutral (Neutral.app s h)

end Lambda
