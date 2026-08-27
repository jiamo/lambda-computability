/-
Finite approximants of untyped terms, and their denotations in Scott's graph model.

`Start/GraphAdequacy.lean` pins down the least element of the graph model: a closed term denotes
`∅` exactly when it has no head normal form.  This module introduces the syntactic side of the
approximation theory that the classical proof of full abstraction rests on:

* `Lambda.Approx` — the *approximation order* `A ⊑ M`: `A` is obtained from `M` by replacing
  subterms with the divergent term `Ω`;
* `Lambda.direct` — the **direct approximant** `ω(M)` of a term: the abstraction prefix and the
  variable head of `M` are kept and everything below a head redex is erased to `Ω`;
* `GraphModel.denot_approx_subset` — the denotation is monotone for `⊑`, so an approximant of a
  term denotes less than the term (`GraphModel.denot_direct_subset`), and the same holds for the
  approximant of any reduct (`GraphModel.denot_direct_reduct_subset`,
  `GraphModel.iUnion_denot_direct_subset`): the *soundness* half of the approximation theorem;
* `GraphModel.denot_ne_empty_iff_exists_reduct_direct` — for a closed term, the denotation is
  nonempty exactly when the direct approximant of some reduct already has a nonempty denotation.
  This is the approximation theorem at the level of the least element: no information of a term
  is invisible to all of its finite approximants.

Boundary: the full approximation theorem — that the denotation of a term is the *union* of the
denotations of the direct approximants of its reducts, and not merely nonempty together with it —
is not proved here.  Only the inclusion `⋃ ⟦ω(M')⟧ ⊆ ⟦M⟧` is, together with the equality of the
two sides being empty.
-/

import Start.GraphAdequacy
import Start.FreeVars

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-! ## Terms whose head is a variable -/

/-- Whether the head of a term is a variable; this is the decidable form of `Lambda.Neutral`. -/
def headVar : Lambda → Bool
  | Lambda.var _ => Bool.true
  | Lambda.app s _ => headVar s
  | Lambda.lam _ => Bool.false

@[simp] theorem headVar_var (n : ℕ) : headVar (Lambda.var n) = Bool.true := rfl
@[simp] theorem headVar_app (s t : Lambda) : headVar (Lambda.app s t) = headVar s := rfl
@[simp] theorem headVar_lam (s : Lambda) : headVar (Lambda.lam s) = Bool.false := rfl

theorem neutral_iff_headVar {t : Lambda} : Neutral t ↔ headVar t = Bool.true := by
  constructor
  · intro h
    induction h with
    | var n => rfl
    | app N _ ih => simpa using ih
  · intro h
    induction t with
    | var n => exact Neutral.var n
    | lam s _ => simp at h
    | app s u ihs _ => exact Neutral.app u (ihs (by simpa using h))

@[simp] theorem headVar_omega : headVar Lambda.omega = Bool.false := rfl

/-! ## The approximation order and the direct approximant -/

/-- `Approx A M` — written `A ⊑ M` in the literature — says that `A` is obtained from `M` by
replacing some subterms with the divergent term `Ω`. -/
inductive Approx : Lambda → Lambda → Prop
  | omega (t : Lambda) : Approx Lambda.omega t
  | var (n : ℕ) : Approx (Lambda.var n) (Lambda.var n)
  | app {a b s t : Lambda} : Approx a s → Approx b t → Approx (Lambda.app a b) (Lambda.app s t)
  | lam {a s : Lambda} : Approx a s → Approx (Lambda.lam a) (Lambda.lam s)

theorem Approx.refl : ∀ t : Lambda, Approx t t
  | Lambda.var n => Approx.var n
  | Lambda.app s t => Approx.app (Approx.refl s) (Approx.refl t)
  | Lambda.lam s => Approx.lam (Approx.refl s)

/-- The **direct approximant** of a term: keep the abstraction prefix and the variable head,
and erase to `Ω` everything under a head redex. -/
def direct : Lambda → Lambda
  | Lambda.var n => Lambda.var n
  | Lambda.lam s => Lambda.lam (direct s)
  | Lambda.app s t => if headVar s then Lambda.app (direct s) (direct t) else Lambda.omega

@[simp] theorem direct_var (n : ℕ) : direct (Lambda.var n) = Lambda.var n := rfl
@[simp] theorem direct_lam (s : Lambda) : direct (Lambda.lam s) = Lambda.lam (direct s) := rfl

theorem direct_app (s t : Lambda) :
    direct (Lambda.app s t) =
      if headVar s then Lambda.app (direct s) (direct t) else Lambda.omega := rfl

/-- The direct approximant is an approximant. -/
theorem approx_direct : ∀ t : Lambda, Approx (direct t) t
  | Lambda.var n => Approx.var n
  | Lambda.lam s => Approx.lam (approx_direct s)
  | Lambda.app s t => by
      rw [direct_app]
      by_cases h : headVar s
      · rw [if_pos h]
        exact Approx.app (approx_direct s) (approx_direct t)
      · rw [if_neg h]
        exact Approx.omega _

/-- The direct approximant of a neutral term is neutral. -/
theorem neutral_direct {t : Lambda} (h : Neutral t) : Neutral (direct t) := by
  induction h with
  | var n => exact Neutral.var n
  | @app M N hM ih =>
      have hh : headVar M = Bool.true := neutral_iff_headVar.1 hM
      rw [direct_app, if_pos hh]
      exact Neutral.app _ ih

/-- The direct approximant of a head normal form is a head normal form. -/
theorem isHnf_direct {t : Lambda} (h : IsHnf t) : IsHnf (direct t) := by
  induction h with
  | neutral hn => exact IsHnf.neutral (neutral_direct hn)
  | lam _ ih => exact IsHnf.lam ih

theorem freeBelow_omega (k : ℕ) : freeBelow k Lambda.omega := by
  refine ⟨?_, ?_⟩ <;> exact ⟨Nat.zero_lt_succ k, Nat.zero_lt_succ k⟩

/-- Taking the direct approximant does not create free variables. -/
theorem freeBelow_direct : ∀ {t : Lambda} {k : ℕ}, freeBelow k t → freeBelow k (direct t) := by
  intro t
  induction t with
  | var n => intro k h; exact h
  | lam s ih => intro k h; exact ih h
  | app s u ihs ihu =>
      intro k h
      rw [direct_app]
      by_cases hh : headVar s
      · rw [if_pos hh]
        exact ⟨ihs h.1, ihu h.2⟩
      · rw [if_neg hh]
        exact freeBelow_omega k

/-- The direct approximant of a closed term is closed. -/
theorem IsClosed.direct {t : Lambda} (h : Lambda.IsClosed t) : Lambda.IsClosed (direct t) :=
  (freeBelow_zero_iff_isClosed _).1 (freeBelow_direct ((freeBelow_zero_iff_isClosed t).2 h))

end Lambda

namespace GraphModel

open Lambda

/-! ## Approximants denote less -/

/-- **The denotation is monotone for the approximation order.** -/
theorem denot_approx_subset {a t : Lambda} (h : Approx a t) (ρ : Env) :
    denot a ρ ⊆ denot t ρ := by
  induction h generalizing ρ with
  | omega t => rw [denot_omega]; exact Set.empty_subset _
  | var n => exact subset_rfl
  | app _ _ ihf iha => exact appD_mono (ihf ρ) (iha ρ)
  | lam _ ih => exact graph_mono fun X => ih (cons X ρ)

/-- The direct approximant of a term denotes less than the term. -/
theorem denot_direct_subset (t : Lambda) (ρ : Env) : denot (direct t) ρ ⊆ denot t ρ :=
  denot_approx_subset (approx_direct t) ρ

/-- The direct approximant of a *reduct* also denotes less than the term. -/
theorem denot_direct_reduct_subset {t t' : Lambda} (h : Lambda.reduces t t') (ρ : Env) :
    denot (direct t') ρ ⊆ denot t ρ := by
  rw [denot_reduces h ρ]
  exact denot_direct_subset t' ρ

/-- **Soundness of approximation**: the denotations of the direct approximants of the reducts of
a term are all contained in the denotation of the term. -/
theorem iUnion_denot_direct_subset (t : Lambda) (ρ : Env) :
    (⋃ t' ∈ {u : Lambda | Lambda.reduces t u}, denot (direct t') ρ) ⊆ denot t ρ := by
  refine Set.iUnion₂_subset fun t' ht' => denot_direct_reduct_subset ?_ ρ
  exact ht'

/-! ## Approximants see all the information of a closed term -/

/-- If a closed term denotes something, then already the direct approximant of one of its
reducts does. -/
theorem exists_reduct_denot_direct_ne_empty {t : Lambda} (hcl : Lambda.IsClosed t) (ρ : Env)
    (h : denot t ρ ≠ (∅ : D)) :
    ∃ t', Lambda.reduces t t' ∧ denot (direct t') ρ ≠ (∅ : D) := by
  obtain ⟨u, hu, hhnf⟩ := hasHnf_of_denot_ne_empty h
  refine ⟨u, hu, ?_⟩
  exact denot_ne_empty_of_hasHnf (Lambda.IsClosed.direct (hcl.reduces hu))
    (Lambda.hasHnf_of_isHnf (isHnf_direct hhnf)) ρ

/-- **The approximation theorem at the least element.**  A closed term has a nonempty denotation
exactly when the direct approximant of one of its reducts has. -/
theorem denot_ne_empty_iff_exists_reduct_direct {t : Lambda} (hcl : Lambda.IsClosed t) (ρ : Env) :
    denot t ρ ≠ (∅ : D) ↔ ∃ t', Lambda.reduces t t' ∧ denot (direct t') ρ ≠ (∅ : D) := by
  refine ⟨exists_reduct_denot_direct_ne_empty hcl ρ, ?_⟩
  rintro ⟨t', ht', hne⟩
  intro hempty
  exact hne (Set.eq_empty_of_subset_empty (hempty ▸ denot_direct_reduct_subset ht' ρ))

end GraphModel
