/-
Correctness of the lambda minimisation operator `Lambda.mu`.

`Lambda.mu F` searches for the least `n` with `f n = 0`, where `F` realizes `f`.
This file proves the specification `Lambda.MuCorrectness` stated in
`Start/Recursion.lean`: when a witness exists, `mu F` reduces to the Church
numeral of the least one.
-/

import Start.Realizer

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

theorem isZero_closed : Lambda.IsClosed Lambda.isZero := by
  unfold Lambda.IsClosed
  aesop

/-- The body of the minimisation loop with the tested function `F` substituted in. -/
def muBody (F : Lambda) : Lambda := Lambda.subst F 0 Lambda.mu_body

/-- The self-applied fixed point of the minimisation loop. -/
def muX (F : Lambda) : Lambda := Lambda.app (Lambda.W (muBody F)) (Lambda.W (muBody F))

theorem muBody_eq (F : Lambda) (hF : Lambda.IsClosed F) :
    muBody F =
      Lambda.lam (Lambda.lam (Lambda.app
        (Lambda.app (Lambda.app Lambda.ifThenElse
          (Lambda.app Lambda.isZero (Lambda.app F (Lambda.var 0)))) (Lambda.var 0))
        (Lambda.app (Lambda.var 1) (Lambda.app Lambda.succ (Lambda.var 0))))) := by
  simp [muBody, Lambda.mu_body, Lambda.subst, Lambda.lift_closed hF,
    Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed,
    Lambda.IsClosed_imp_subst_eq isZero_closed,
    Lambda.IsClosed_imp_subst_eq Lambda.succ_closed]

theorem muBody_closed (F : Lambda) (hF : Lambda.IsClosed F) : Lambda.IsClosed (muBody F) := by
  rw [muBody_eq F hF]
  intro s x
  simp [Lambda.subst, Lambda.IsClosed_imp_subst_eq hF,
    Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed,
    Lambda.IsClosed_imp_subst_eq isZero_closed,
    Lambda.IsClosed_imp_subst_eq Lambda.succ_closed]

theorem muX_closed (F : Lambda) (hF : Lambda.IsClosed F) : Lambda.IsClosed (muX F) :=
  Lambda.IsClosed_app (Lambda.W_closed _ (muBody_closed F hF))
    (Lambda.W_closed _ (muBody_closed F hF))

theorem mu_reduces_muX (F : Lambda) (hF : Lambda.IsClosed F) :
    Lambda.reduces (Lambda.app Lambda.mu F) (Lambda.app (muX F) (Lambda.church 0)) := by
  have h1 : Lambda.reduces (Lambda.app Lambda.mu F)
      (Lambda.subst F 0
        (Lambda.app (Lambda.app Lambda.fix Lambda.mu_body) (Lambda.church 0))) :=
    Lambda.beta_reduces
  have h2 : Lambda.subst F 0 (Lambda.app (Lambda.app Lambda.fix Lambda.mu_body) (Lambda.church 0))
      = Lambda.app (Lambda.app Lambda.fix (muBody F)) (Lambda.church 0) := by
    simp [Lambda.subst, muBody, Lambda.IsClosed_imp_subst_eq Lambda.fix_closed,
      Lambda.IsClosed_imp_subst_eq (Lambda.church_closed 0)]
  rw [h2] at h1
  exact Lambda.reduces_trans h1
    (Lambda.reduces_app_left (Lambda.fix_reduces_W _ (muBody_closed F hF)))

theorem muX_unfold (F : Lambda) (hF : Lambda.IsClosed F) :
    Lambda.reduces (muX F) (Lambda.app (muBody F) (muX F)) := by
  have h := Lambda.W_reduces (muBody F)
  rwa [Lambda.IsClosed_imp_subst_eq (muBody_closed F hF)] at h

theorem muX_step (F : Lambda) (hF : Lambda.IsClosed F) (k : ℕ) :
    Lambda.reduces (Lambda.app (muX F) (Lambda.church k))
      (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
        (Lambda.app Lambda.isZero (Lambda.app F (Lambda.church k)))) (Lambda.church k))
        (Lambda.app (muX F) (Lambda.app Lambda.succ (Lambda.church k)))) := by
  have h1 : Lambda.reduces (Lambda.app (muX F) (Lambda.church k))
      (Lambda.app (Lambda.app (muBody F) (muX F)) (Lambda.church k)) :=
    Lambda.reduces_app_left (muX_unfold F hF)
  rw [muBody_eq F hF] at h1
  refine Lambda.reduces_trans h1 ?_
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

theorem muX_works (F : Lambda) (hF : Lambda.IsClosed F) (f : ℕ → ℕ)
    (hFf : ∀ n, Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church (f n)))
    (n : ℕ) (hlt : ∀ m < n, f m ≠ 0) (hn : f n = 0) :
    ∀ k, k ≤ n → Lambda.reduces (Lambda.app (muX F) (Lambda.church k)) (Lambda.church n) := by
  have key : ∀ d k, n = k + d →
      Lambda.reduces (Lambda.app (muX F) (Lambda.church k)) (Lambda.church n) := by
    intro d
    induction d with
    | zero =>
        intro k hd
        obtain rfl : k = n := by omega
        refine Lambda.reduces_trans (muX_step F hF k) ?_
        have hcond : Lambda.reduces (Lambda.app Lambda.isZero (Lambda.app F (Lambda.church k)))
            Lambda.true := by
          refine Lambda.reduces_trans (Lambda.reduces_app_right (hFf k)) ?_
          rw [hn]
          exact Lambda.isZero_zero
        refine Lambda.reduces_trans
          (Lambda.reduces_app_left (Lambda.reduces_app_left
            (Lambda.reduces_app_right hcond))) ?_
        simpa using Lambda.ifThenElse_true (Lambda.church k)
          (Lambda.app (muX F) (Lambda.app Lambda.succ (Lambda.church k)))
    | succ d ih =>
        intro k hd
        have hklt : k < n := by omega
        have hfk : f k ≠ 0 := hlt k hklt
        obtain ⟨j, hj⟩ : ∃ j, f k = j + 1 := ⟨f k - 1, by omega⟩
        refine Lambda.reduces_trans (muX_step F hF k) ?_
        have hcond : Lambda.reduces (Lambda.app Lambda.isZero (Lambda.app F (Lambda.church k)))
            Lambda.false := by
          refine Lambda.reduces_trans (Lambda.reduces_app_right (hFf k)) ?_
          rw [hj]
          exact Lambda.isZero_succ j
        refine Lambda.reduces_trans
          (Lambda.reduces_app_left (Lambda.reduces_app_left
            (Lambda.reduces_app_right hcond))) ?_
        refine Lambda.reduces_trans (Lambda.ifThenElse_false (Lambda.church k)
          (Lambda.app (muX F) (Lambda.app Lambda.succ (Lambda.church k)))) ?_
        refine Lambda.reduces_trans (Lambda.reduces_app_right (Lambda.succ_works k)) ?_
        exact ih (k + 1) (by omega)
  intro k hk
  exact key (n - k) k (by omega)

/-- **Correctness of the minimisation combinator.** -/
theorem muCorrectness : Lambda.MuCorrectness := by
  intro f F hF hFf n hlt hn
  exact Lambda.reduces_trans (mu_reduces_muX F hF)
    (muX_works F hF f hFf n hlt hn 0 (Nat.zero_le n))

------------------------------------------------------------------------
-- Behaviour of the search when there is no witness
------------------------------------------------------------------------

/-- One turn of the search loop: at an index where the tested function is nonzero,
the search moves on to the next index. -/
theorem muX_loop_step (F : Lambda) (hF : Lambda.IsClosed F) (f : ℕ → ℕ)
    (hFf : ∀ n, Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church (f n)))
    (k : ℕ) (hk : f k ≠ 0) :
    Lambda.reduces (Lambda.app (muX F) (Lambda.church k))
      (Lambda.app (muX F) (Lambda.church (k + 1))) := by
  obtain ⟨j, hj⟩ : ∃ j, f k = j + 1 := ⟨f k - 1, by omega⟩
  refine Lambda.reduces_trans (muX_step F hF k) ?_
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

/-- Without a witness the search passes through every index. -/
theorem muX_loop (F : Lambda) (hF : Lambda.IsClosed F) (f : ℕ → ℕ)
    (hFf : ∀ n, Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church (f n)))
    (hno : ∀ n, f n ≠ 0) (k : ℕ) :
    Lambda.reduces (Lambda.app (muX F) (Lambda.church 0))
      (Lambda.app (muX F) (Lambda.church k)) := by
  induction k with
  | zero => exact Lambda.reduces.refl _
  | succ k ih =>
      exact Lambda.reduces_trans ih (muX_loop_step F hF f hFf k (hno k))

/-- Without a witness, `mu F` reduces to the search state at every index. -/
theorem mu_reduces_state (F : Lambda) (hF : Lambda.IsClosed F) (f : ℕ → ℕ)
    (hFf : ∀ n, Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church (f n)))
    (hno : ∀ n, f n ≠ 0) (k : ℕ) :
    Lambda.reduces (Lambda.app Lambda.mu F) (Lambda.app (muX F) (Lambda.church k)) :=
  Lambda.reduces_trans (mu_reduces_muX F hF) (muX_loop F hF f hFf hno k)

/-
What is still missing for the divergence half of minimisation.

The theorem below records how far the reduction theory of this development reaches:
if a witnessless search did reduce to a Church numeral, then *every* state of the
search would reduce to that same numeral.  This is exactly the point at which an
equational argument stops working, because "the constant function" satisfies all the
reduction equations of the loop; ruling it out needs a syntactic notion of head
normal form (solvability) together with a standardization theorem, neither of which
is part of this development.
-/

/-- If a witnessless search reduced to a Church numeral, every state of the search
would reduce to that same numeral. -/
theorem muX_state_reduces_of_mu_reduces (F : Lambda) (hF : Lambda.IsClosed F) (f : ℕ → ℕ)
    (hFf : ∀ n, Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church (f n)))
    (hno : ∀ n, f n ≠ 0) {m : ℕ}
    (hm : Lambda.reduces (Lambda.app Lambda.mu F) (Lambda.church m)) (k : ℕ) :
    Lambda.reduces (Lambda.app (muX F) (Lambda.church k)) (Lambda.church m) := by
  obtain ⟨t, ht1, ht2⟩ := Lambda.confluence_theorem hm (mu_reduces_state F hF f hFf hno k)
  rwa [← Lambda.reduces_normal_eq (Lambda.church_normal m) ht1] at ht2

end Lambda

end
