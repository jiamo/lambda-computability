/-
The divergence half of minimisation.

If the tested function has no zero, the search term `Lambda.mu F` reduces to no
weak head normal form at all — in particular to no Church numeral.

The argument is an infinite descent along the weak head strategy:

* one turn of the search loop begins with a *weak head* step
  (`Lambda.muX_wstep`) and ends back at the next search state
  (`Lambda.muX_loop_step_from`);
* a weak head step strictly decreases the number of weak head steps that remain
  before a weak head normal form is reached, and an arbitrary reduction never
  increases it (`Lambda.whnIn_of_reduces`);
* so a search state can only have a weak head normal form if the descent stops,
  which it never does (`Lambda.not_hasWhnfEval_of_loop`).

Finally, the weak head strategy is normalizing
(`Lambda.hasWhnfEval_of_reduces_whnf`), so a term on which it diverges reduces
to no weak head normal form whatsoever.
-/

import Start.Minimization
import Start.Standardization

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Infinite descent along the weak head strategy
------------------------------------------------------------------------

/-- **Looping terms have no weak head normal form.**  If from every `t k` a weak head
step leads to a term that reduces to `t (k+1)`, then the weak head strategy diverges
on `t 0`. -/
theorem not_hasWhnfEval_of_loop (t : ℕ → Lambda)
    (hloop : ∀ k, ∃ z, wstep (t k) z ∧ Lambda.reduces z (t (k + 1))) :
    ¬ HasWhnfEval (t 0) := by
  have key : ∀ n : ℕ, ∀ s : ℕ → Lambda,
      (∀ k, ∃ z, wstep (s k) z ∧ Lambda.reduces z (s (k + 1))) → ¬ WHNIn n (s 0) := by
    intro n
    induction n with
    | zero =>
        intro s hs hw
        obtain ⟨z, hz, -⟩ := hs 0
        exact (hw z) hz
    | succ n ih =>
        intro s hs hw
        obtain ⟨z, hz, hzred⟩ := hs 0
        rcases hw with hwhnf | ⟨y, hy, hyn⟩
        · exact (hwhnf z) hz
        · have hyz : y = z := wstep_deterministic hy hz
          subst hyz
          have h1 : WHNIn n (s 1) := whnIn_of_reduces hzred hyn
          exact ih (fun k => s (k + 1)) (fun k => hs (k + 1)) h1
  rintro ⟨n, hn⟩
  exact key n t hloop hn

/-- A looping term reduces to no weak head normal form. -/
theorem not_reduces_whnf_of_loop (t : ℕ → Lambda)
    (hloop : ∀ k, ∃ z, wstep (t k) z ∧ Lambda.reduces z (t (k + 1)))
    {u : Lambda} (hu : IsWhnf u) : ¬ Lambda.reduces (t 0) u := by
  intro hred
  exact not_hasWhnfEval_of_loop t hloop (hasWhnfEval_of_reduces_whnf hred hu)

------------------------------------------------------------------------
-- One turn of the search loop
------------------------------------------------------------------------

/-- Unfolding the fixed point of the search loop is a weak head step. -/
theorem muX_wstep (F : Lambda) (hF : Lambda.IsClosed F) (k : ℕ) :
    wstep (Lambda.app (muX F) (Lambda.church k))
      (Lambda.app (Lambda.app (muBody F) (muX F)) (Lambda.church k)) := by
  have h : wstep (Lambda.app (Lambda.W (muBody F)) (Lambda.W (muBody F)))
      (Lambda.app (muBody F) (muX F)) := by
    have := wstep.beta (Lambda.app (muBody F) (Lambda.app (Lambda.var 0) (Lambda.var 0)))
      (Lambda.W (muBody F))
    simpa [Lambda.W, muX, Lambda.subst,
      Lambda.IsClosed_imp_subst_eq (muBody_closed F hF)] using this
  exact wstep.app _ h

/-- The one-turn law of the search loop, starting from the unfolded state. -/
theorem muX_step_from (F : Lambda) (hF : Lambda.IsClosed F) (k : ℕ) :
    Lambda.reduces (Lambda.app (Lambda.app (muBody F) (muX F)) (Lambda.church k))
      (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
        (Lambda.app Lambda.isZero (Lambda.app F (Lambda.church k)))) (Lambda.church k))
        (Lambda.app (muX F) (Lambda.app Lambda.succ (Lambda.church k)))) := by
  rw [muBody_eq F hF]
  have h2 := Lambda.double_beta_reduction
    (Lambda.app
      (Lambda.app (Lambda.app Lambda.ifThenElse
        (Lambda.app Lambda.isZero (Lambda.app F (Lambda.var 0)))) (Lambda.var 0))
      (Lambda.app (Lambda.var 1) (Lambda.app Lambda.succ (Lambda.var 0))))
    (muX F) (Lambda.church k) (muX_closed F hF)
  convert h2 using 1
  simp [Lambda.subst, Lambda.IsClosed_imp_subst_eq hF,
    Lambda.IsClosed_imp_subst_eq (muX_closed F hF),
    Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed,
    Lambda.IsClosed_imp_subst_eq isZero_closed,
    Lambda.IsClosed_imp_subst_eq Lambda.succ_closed]

/-- From the unfolded state at a nonzero test value, the search moves on to the next
index. -/
theorem muX_loop_step_from (F : Lambda) (hF : Lambda.IsClosed F) (f : ℕ → ℕ)
    (hFf : ∀ n, Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church (f n)))
    (k : ℕ) (hk : f k ≠ 0) :
    Lambda.reduces (Lambda.app (Lambda.app (muBody F) (muX F)) (Lambda.church k))
      (Lambda.app (muX F) (Lambda.church (k + 1))) := by
  obtain ⟨j, hj⟩ : ∃ j, f k = j + 1 := ⟨f k - 1, by omega⟩
  refine Lambda.reduces_trans (muX_step_from F hF k) ?_
  have hcond : Lambda.reduces (Lambda.app Lambda.isZero (Lambda.app F (Lambda.church k)))
      Lambda.false := by
    refine Lambda.reduces_trans (Lambda.reduces_app_right (hFf k)) ?_
    rw [hj]
    exact Lambda.isZero_succ j
  refine Lambda.reduces_trans
    (Lambda.reduces_app_left (Lambda.reduces_app_left (Lambda.reduces_app_right hcond))) ?_
  refine Lambda.reduces_trans (Lambda.ifThenElse_false (Lambda.church k)
    (Lambda.app (muX F) (Lambda.app Lambda.succ (Lambda.church k)))) ?_
  exact Lambda.reduces_app_right (Lambda.succ_works k)

------------------------------------------------------------------------
-- Divergence of a witnessless search
------------------------------------------------------------------------

/-- **A witnessless search has no weak head normal form.** -/
theorem muX_not_hasWhnfEval (F : Lambda) (hF : Lambda.IsClosed F) (f : ℕ → ℕ)
    (hFf : ∀ n, Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church (f n)))
    (hno : ∀ n, f n ≠ 0) (k : ℕ) :
    ¬ HasWhnfEval (Lambda.app (muX F) (Lambda.church k)) := by
  have h := not_hasWhnfEval_of_loop (fun j => Lambda.app (muX F) (Lambda.church (k + j))) ?_
  · simpa using h
  · intro j
    refine ⟨Lambda.app (Lambda.app (muBody F) (muX F)) (Lambda.church (k + j)),
      muX_wstep F hF (k + j), ?_⟩
    have := muX_loop_step_from F hF f hFf (k + j) (hno (k + j))
    simpa [Nat.add_assoc] using this

/-- **The divergence half of minimisation.**  If the tested function has no zero, the
search term reduces to no weak head normal form; in particular to no Church numeral. -/
theorem mu_not_reduces_whnf (F : Lambda) (hF : Lambda.IsClosed F) (f : ℕ → ℕ)
    (hFf : ∀ n, Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church (f n)))
    (hno : ∀ n, f n ≠ 0) {u : Lambda} (hu : IsWhnf u) :
    ¬ Lambda.reduces (Lambda.app Lambda.mu F) u := by
  intro hred
  have hstate : Lambda.reduces (Lambda.app Lambda.mu F)
      (Lambda.app (muX F) (Lambda.church 0)) := mu_reduces_muX F hF
  obtain ⟨w, hw1, hw2⟩ := Lambda.confluence_theorem hred hstate
  exact muX_not_hasWhnfEval F hF f hFf hno 0
    (hasWhnfEval_of_reduces_whnf hw2 (isWhnf_of_reduces hu hw1))

/-- If the tested function has no zero, the weak head strategy diverges on the search
term. -/
theorem mu_not_hasWhnfEval (F : Lambda) (hF : Lambda.IsClosed F) (f : ℕ → ℕ)
    (hFf : ∀ n, Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church (f n)))
    (hno : ∀ n, f n ≠ 0) :
    ¬ HasWhnfEval (Lambda.app Lambda.mu F) := by
  intro h
  obtain ⟨u, hu1, hu2⟩ := exists_whnf_of_hasWhnfEval h
  exact mu_not_reduces_whnf F hF f hFf hno hu2 hu1

/-- If the tested function has no zero, the search term reduces to no Church numeral. -/
theorem mu_not_reduces_church (F : Lambda) (hF : Lambda.IsClosed F) (f : ℕ → ℕ)
    (hFf : ∀ n, Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church (f n)))
    (hno : ∀ n, f n ≠ 0) (m : ℕ) :
    ¬ Lambda.reduces (Lambda.app Lambda.mu F) (Lambda.church m) :=
  mu_not_reduces_whnf F hF f hFf hno (isWhnf_church m)

/-- The divergence half of the specification of `Lambda.mu`, in the shape of
`Lambda.MuCorrectness`. -/
def MuDivergence : Prop :=
  ∀ (f : ℕ → ℕ) (F : Lambda),
    Lambda.IsClosed F →
    (∀ n, Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church (f n))) →
    (∀ n, f n ≠ 0) →
    ∀ m, ¬ Lambda.reduces (Lambda.app Lambda.mu F) (Lambda.church m)

/-- **Divergence of minimisation without a witness.** -/
theorem muDivergence : MuDivergence := fun f F hF hFf hno m =>
  mu_not_reduces_church F hF f hFf hno m

end Lambda

end
