/-
Closing terms, the primitive recursion combinator `Lambda.prec`, and the
minimisation combinator `Lambda.mu`.

Extracted from `Start/Basic.lean` as part of the modular split.
-/

import Start.Pairing


set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

def Lambda.closeAt (k : ℕ) : Lambda → Lambda
  | Lambda.var i => if i < k then Lambda.var i else Lambda.church 0
  | Lambda.app t1 t2 => Lambda.app (Lambda.closeAt k t1) (Lambda.closeAt k t2)
  | Lambda.lam t => Lambda.lam (Lambda.closeAt (k + 1) t)

def Lambda.close (t : Lambda) : Lambda := Lambda.closeAt 0 t

theorem Lambda.closeAt_is_closedAt (t : Lambda) (k : ℕ) :
    Lambda.IsClosedAt (Lambda.closeAt k t) k := by
  induction t generalizing k with
  | var n =>
      by_cases hnk : n < k
      · simpa [Lambda.closeAt, hnk] using Lambda.IsClosedAt_var n k hnk
      · intro s x hx
        simpa [Lambda.closeAt, hnk] using (Lambda.church_closed 0 s x)
  | app t1 t2 ih1 ih2 =>
      simpa [Lambda.closeAt] using Lambda.IsClosedAt_app (ih1 k) (ih2 k)
  | lam t ih =>
      simpa [Lambda.closeAt] using Lambda.IsClosedAt_lam (k := k) (ih (k + 1))

theorem Lambda.close_is_closed (t : Lambda) : Lambda.IsClosed (Lambda.close t) := by
  unfold Lambda.close
  exact (Lambda.IsClosedAt_zero_iff_IsClosed _).mp (Lambda.closeAt_is_closedAt t 0)

theorem Lambda.lift_closeAt_generalized (t : Lambda) (j k : ℕ) :
  Lambda.lift 1 j (Lambda.closeAt (k + j) t) = Lambda.closeAt (k + j + 1) (Lambda.lift 1 j t) := by
  have h_lift_closeAt : ∀ t : Lambda, ∀ k j : ℕ,
      Lambda.lift 1 j (Lambda.closeAt (k + j) t) = Lambda.closeAt (k + j + 1) (Lambda.lift 1 j t) :=
          by
    intro t k j
    induction t generalizing k j with
    | var n =>
        by_cases hnk : n < k + j
        · by_cases hnj : n < j
          · have hlt : n < k + j + 1 := by omega
            simp [Lambda.closeAt, Lambda.lift, hnk, hnj, hlt]
          · have hsucc : n + 1 < k + j + 1 := by omega
            simp [Lambda.closeAt, Lambda.lift, hnk, hnj, hsucc]
        · have hnj : ¬ n < j := by omega
          have hsucc : ¬ n + 1 < k + j + 1 := by omega
          simp [Lambda.closeAt, Lambda.lift, hnk, hnj, hsucc, Lambda.lift_church]
    | app t1 t2 ih1 ih2 =>
        simp [Lambda.closeAt, Lambda.lift, ih1, ih2]
    | lam t ih =>
        simpa [Lambda.closeAt, Lambda.lift, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          ih k (j + 1)
  exact h_lift_closeAt t k j

def Lambda.omega : Lambda :=
  Lambda.app (Lambda.lam (Lambda.app (Lambda.var 0) (Lambda.var 0)))
      (Lambda.lam (Lambda.app (Lambda.var 0) (Lambda.var 0)))

theorem Lambda.step_omega_omega : Lambda.step Lambda.omega Lambda.omega := by
  -- By definition of omega, we have omega = (\x. x x) (\x. x x). Therefore, omega.step omega
  -- follows directly from the definition of step.
  apply Lambda.step.beta

theorem Lambda.omega_reduces_omega : Lambda.reduces Lambda.omega Lambda.omega := by
  -- By definition of `reduces`, we need to show that `omega` reduces to itself through a series of
  -- steps. We can use the fact that `omega` reduces to itself in one step.
  apply Lambda.reduces.refl

theorem Lambda.step_omega_eq (t : Lambda) (h : Lambda.step Lambda.omega t) : t = Lambda.omega := by
  -- Since omega is a fixed point, any step from omega must be omega itself.
  have h_omega_fixed : ∀ t, Lambda.step Lambda.omega t → t = Lambda.omega := by
    -- By definition of omega, we know that omega steps to itself. Therefore, if omega steps to t,
    -- then t must be omega.
    intros t ht
    have h_eq : t = omega := by
      cases ht <;> tauto
    exact h_eq;
  -- Apply the hypothesis `h_omega_fixed` to `h` to conclude that `t = omega`.
  apply h_omega_fixed; assumption

theorem Lambda.closeAt_eq_self_of_closedAt (t : Lambda) (k : ℕ) (h : Lambda.IsClosedAt t k) :
    Lambda.closeAt k t = t := by
  have h_closeAt :
      ∀ (u : Lambda) (m : ℕ),
        (∀ x, x ≥ m → Lambda.subst (Lambda.church 0) x u = u) →
        Lambda.closeAt m u = u := by
    intro u m h0
    revert m h0
    induction u with
    | var n =>
        intro m h0
        by_cases hnk : n < m
        · simp [Lambda.closeAt, hnk]
        · exfalso
          have hnk' : m ≤ n := Nat.le_of_not_lt hnk
          have hbad := h0 n hnk'
          simp [Lambda.subst, Lambda.church] at hbad
    | app t1 t2 ih1 ih2 =>
        intro m h0
        have h1 : ∀ x, x ≥ m → Lambda.subst (Lambda.church 0) x t1 = t1 := by
          intro x hx
          have h_eq := h0 x hx
          unfold Lambda.subst at h_eq
          injection h_eq with h1 h2
        have h2 : ∀ x, x ≥ m → Lambda.subst (Lambda.church 0) x t2 = t2 := by
          intro x hx
          have h_eq := h0 x hx
          unfold Lambda.subst at h_eq
          injection h_eq with h1 h2
        simp [Lambda.closeAt, ih1 m h1, ih2 m h2]
    | lam t ih =>
        intro m h0
        have h_body : ∀ x, x ≥ m + 1 → Lambda.subst (Lambda.church 0) x t = t := by
          intro x hx
          have hx1 : 1 ≤ x := le_trans (Nat.succ_le_succ (Nat.zero_le m)) hx
          have hxm1 : m ≤ x - 1 := by omega
          have h_eq := h0 (x - 1) hxm1
          unfold Lambda.subst at h_eq
          injection h_eq with h_inner
          simpa [Nat.sub_add_cancel hx1, Lambda.lift_church] using h_inner
        simp [Lambda.closeAt, ih (m + 1) h_body]
  exact h_closeAt t k (fun x hx => h (Lambda.church 0) x hx)

theorem Lambda.lift_subst_var (s : Lambda) (n k x y : ℕ) (h : k ≤ x) :
  Lambda.lift n k (Lambda.subst s x (Lambda.var y)) = Lambda.subst (Lambda.lift n k s) (x + n)
      (Lambda.lift n k (Lambda.var y)) := by
  simpa using Lambda.lift_subst (Lambda.var y) s n k x h

theorem Lambda.lift_subst_of_closed (s t : Lambda) (n k x : ℕ) (h : k ≤ x) (hs : Lambda.IsClosed s)
    :
  Lambda.lift n k (Lambda.subst s x t) = Lambda.subst s (x + n) (Lambda.lift n k t) := by
  simpa [Lambda.lift_closed hs n k] using Lambda.lift_subst t s n k x h

theorem Lambda.lift_subst_var_of_closed (s : Lambda) (n k x y : ℕ) (h : k ≤ x) (hs : Lambda.IsClosed
    s) :
  Lambda.lift n k (Lambda.subst s x (Lambda.var y)) = Lambda.subst s (x + n)
      (Lambda.lift n k (Lambda.var y)) := by
  simpa [Lambda.lift_closed hs n k] using Lambda.lift_subst_var s n k x y h

theorem Lambda.lift_lift_zero (s : Lambda) (n k : ℕ) :
  Lambda.lift n (k + 1) (Lambda.lift 1 0 s) = Lambda.lift 1 0 (Lambda.lift n k s) := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Lambda.lift_lift s 1 n 0 k (Nat.zero_le k)).symm



/-
If a term is closed, `closeAt` acts as the identity.
-/
theorem Lambda.closeAt_eq_of_closed (s : Lambda) (x : ℕ) (hs : Lambda.IsClosed s) :
    Lambda.closeAt x s = s := by
  exact Lambda.closeAt_eq_self_of_closedAt s x (fun s2 x2 hx2 => hs s2 x2)

/-
Substitution of a closed term commutes with `closeAt`.
-/
theorem Lambda.subst_closeAt (s t : Lambda) (x : ℕ) (hs : Lambda.IsClosed s) :
  Lambda.closeAt x (Lambda.subst s x t) = Lambda.subst s x (Lambda.closeAt (x + 1) t) := by
  induction t generalizing s x with
  | var y =>
      by_cases hxy : y = x
      · subst hxy
        simp [Lambda.subst, Lambda.closeAt, Lambda.closeAt_eq_of_closed, hs]
      · have hxy' : x ≠ y := by
          intro h
          exact hxy h.symm
        by_cases hgt : y > x
        · have hnotlt : ¬ y < x := by exact not_lt.mpr (Nat.le_of_lt hgt)
          have hnotlt' : ¬ y < x + 1 := by exact not_lt.mpr (Nat.succ_le_of_lt hgt)
          have hy1 : ¬ y - 1 < x := by
            omega
          have hsubstVar : Lambda.subst s x (Lambda.var y) = Lambda.var (y - 1) := by
            unfold Lambda.subst
            by_cases hyx : y = x
            · exact False.elim (hxy hyx)
            · simp [hyx, hgt]
          have hcloseVar : Lambda.closeAt (x + 1) (Lambda.var y) = Lambda.church 0 := by
            simp [Lambda.closeAt, hnotlt']
          have hsubstChurch : s.subst x (Lambda.church 0) = Lambda.church 0 :=
            Lambda.IsClosed_imp_subst_eq (Lambda.church_closed 0) s x
          calc
            Lambda.closeAt x (Lambda.subst s x (Lambda.var y)) = Lambda.church 0 := by
              rw [hsubstVar]
              simp [Lambda.closeAt, hy1]
            _ = Lambda.subst s x (Lambda.closeAt (x + 1) (Lambda.var y)) := by
              rw [hcloseVar, hsubstChurch]
        · have hlt : y < x := lt_of_le_of_ne (le_of_not_gt hgt) hxy
          have hylt : y < x + 1 := Nat.lt_succ_of_lt hlt
          have hnotxy : ¬ x < y := by
            exact not_lt.mpr (Nat.le_of_lt hlt)
          have hsubstVar : Lambda.subst s x (Lambda.var y) = Lambda.var y := by
            unfold Lambda.subst
            by_cases hyx : y = x
            · exact False.elim (hxy hyx)
            · simp [hyx, hgt]
          have hcloseVar : Lambda.closeAt (x + 1) (Lambda.var y) = Lambda.var y := by
            simp [Lambda.closeAt, hylt]
          calc
            Lambda.closeAt x (Lambda.subst s x (Lambda.var y)) = Lambda.var y := by
              rw [hsubstVar]
              simp [Lambda.closeAt, hlt]
            _ = Lambda.subst s x (Lambda.closeAt (x + 1) (Lambda.var y)) := by
              rw [hcloseVar, hsubstVar]
  | app t1 t2 ih1 ih2 =>
      simp [Lambda.subst, Lambda.closeAt, ih1 s x hs, ih2 s x hs]
  | lam t ih =>
      simpa [Lambda.subst, Lambda.closeAt, Nat.add_assoc, Lambda.lift_closed hs 1 0] using ih s
          (x + 1) hs

/-
If a term is closed at `k`, it is closed at any `k' >= k`.
-/
theorem Lambda.IsClosedAt_mono {t : Lambda} {k k' : ℕ} (h : k ≤ k') (ht : Lambda.IsClosedAt t k) :
    Lambda.IsClosedAt t k' := by
  exact fun s x hx => ht s x ( le_trans h hx ) ;











/-
Definition of the primitive recursion combinator `prec`.
-/
def Lambda.prec : Lambda :=
  Lambda.lam (Lambda.lam (
    Lambda.app Lambda.fix
      (Lambda.lam (Lambda.lam (
        Lambda.app
            (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app Lambda.isZero (Lambda.var 0)))
          (Lambda.var 3))
          (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.app Lambda.pred (Lambda.var 0)))
                      (Lambda.app (Lambda.var 1) (Lambda.app Lambda.pred (Lambda.var 0))))
      )))
  ))

/-
Definition of the step function for primitive recursion.
-/
def Lambda.prec_step (v s : Lambda) : Lambda :=
  Lambda.lam (Lambda.lam (
    Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app Lambda.isZero (Lambda.var 0)))
      (Lambda.lift 2 0 v))
      (Lambda.app (Lambda.app (Lambda.lift 2 0 s) (Lambda.app Lambda.pred (Lambda.var 0)))
                  (Lambda.app (Lambda.var 1) (Lambda.app Lambda.pred (Lambda.var 0))))
  ))

/-
Definition of the body of the primitive recursion combinator, with correct lifting.
-/
def Lambda.prec_body (v s : Lambda) : Lambda :=
  Lambda.lam (Lambda.lam (
    Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app Lambda.isZero (Lambda.var 0)))
      (Lambda.lift 3 0 v))
      (Lambda.app (Lambda.app (Lambda.lift 2 0 s) (Lambda.app Lambda.pred (Lambda.var 0)))
                  (Lambda.app (Lambda.var 1) (Lambda.app Lambda.pred (Lambda.var 0))))
  ))

/-
Lifting by m then n is the same as lifting by n+m.
-/
theorem Lambda.lift_add_rev (t : Lambda) (n m k : ℕ) :
    Lambda.lift n k (Lambda.lift m k t) = Lambda.lift (n + m) k t := by
  simpa using (Lambda.lift_add n m k t).symm


/-
Correct definition of the body of the primitive recursion combinator.
-/
def Lambda.prec_body_correct (v s : Lambda) : Lambda :=
  Lambda.lam (Lambda.lam (
    Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app Lambda.isZero (Lambda.var 0)))
      (Lambda.lift 2 0 v))
      (Lambda.app (Lambda.app (Lambda.lift 2 0 s) (Lambda.app Lambda.pred (Lambda.var 0)))
                  (Lambda.app (Lambda.var 1) (Lambda.app Lambda.pred (Lambda.var 0))))
  ))


/-
Definition of the primitive recursion term using the correct body.
-/
def Lambda.prec_term (v s : Lambda) : Lambda :=
  Lambda.app Lambda.fix (Lambda.prec_body_correct v s)

/-
The body of the primitive recursion term is closed if its arguments are closed.
-/
theorem Lambda.prec_body_correct_closed (v s : Lambda) (hv : Lambda.IsClosed v) (hs :
    Lambda.IsClosed s) :
  Lambda.IsClosed (Lambda.prec_body_correct v s) := by
  have h_ifThenElse_closed : Lambda.IsClosedAt Lambda.ifThenElse 2 := by
    exact Lambda.IsClosedAt_mono (Nat.zero_le 2)
        ((Lambda.IsClosedAt_zero_iff_IsClosed _).mpr Lambda.ifThenElse_closed)
  have h_isZero_closed : Lambda.IsClosedAt Lambda.isZero 2 := by
    have h_isZero_is_closed : Lambda.IsClosed Lambda.isZero := by
      intro s2 x2
      simp [Lambda.isZero, Lambda.subst, Lambda.subst_church, Lambda.true, Lambda.K, Lambda.false]
    exact Lambda.IsClosedAt_mono (Nat.zero_le 2)
        ((Lambda.IsClosedAt_zero_iff_IsClosed _).mpr h_isZero_is_closed)
  have h_pred_closed : Lambda.IsClosedAt Lambda.pred 2 := by
    exact Lambda.IsClosedAt_mono (Nat.zero_le 2)
        ((Lambda.IsClosedAt_zero_iff_IsClosed _).mpr Lambda.pred_closed)
  have h_lift_v_closed : Lambda.IsClosedAt (Lambda.lift 2 0 v) 2 := by
    simpa [Lambda.lift_closed hv 2 0] using
      (Lambda.IsClosedAt_mono (Nat.zero_le 2) ((Lambda.IsClosedAt_zero_iff_IsClosed v).mpr hv))
  have h_lift_s_closed : Lambda.IsClosedAt (Lambda.lift 2 0 s) 2 := by
    simpa [Lambda.lift_closed hs 2 0] using
      (Lambda.IsClosedAt_mono (Nat.zero_le 2) ((Lambda.IsClosedAt_zero_iff_IsClosed s).mpr hs))
  have h_var0 : Lambda.IsClosedAt (Lambda.var 0) 2 := by
    exact Lambda.IsClosedAt_var 0 2 (by decide)
  have h_var1 : Lambda.IsClosedAt (Lambda.var 1) 2 := by
    exact Lambda.IsClosedAt_var 1 2 (by decide)
  have h_isZero_app : Lambda.IsClosedAt (Lambda.app Lambda.isZero (Lambda.var 0)) 2 := by
    exact Lambda.IsClosedAt_app h_isZero_closed h_var0
  have h_pred_var0 : Lambda.IsClosedAt (Lambda.app Lambda.pred (Lambda.var 0)) 2 := by
    exact Lambda.IsClosedAt_app h_pred_closed h_var0
  have h_left :
      Lambda.IsClosedAt
        (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app Lambda.isZero (Lambda.var 0)))
            (Lambda.lift 2 0 v))
        2 := by
    exact Lambda.IsClosedAt_app (Lambda.IsClosedAt_app h_ifThenElse_closed h_isZero_app)
        h_lift_v_closed
  have h_right :
      Lambda.IsClosedAt
        (Lambda.app (Lambda.app (Lambda.lift 2 0 s) (Lambda.app Lambda.pred (Lambda.var 0)))
          (Lambda.app (Lambda.var 1) (Lambda.app Lambda.pred (Lambda.var 0))))
        2 := by
    exact Lambda.IsClosedAt_app
      (Lambda.IsClosedAt_app h_lift_s_closed h_pred_var0)
      (Lambda.IsClosedAt_app h_var1 h_pred_var0)
  have h_body :
      Lambda.IsClosedAt
        (Lambda.app
          (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app Lambda.isZero (Lambda.var 0)))
              (Lambda.lift 2 0 v))
          (Lambda.app (Lambda.app (Lambda.lift 2 0 s) (Lambda.app Lambda.pred (Lambda.var 0)))
            (Lambda.app (Lambda.var 1) (Lambda.app Lambda.pred (Lambda.var 0)))))
        2 := by
    exact Lambda.IsClosedAt_app h_left h_right
  apply (Lambda.IsClosedAt_zero_iff_IsClosed _).mp
  simpa [Lambda.prec_body_correct] using
    (Lambda.IsClosedAt_lam (k := 0) (Lambda.IsClosedAt_lam (k := 1) h_body))

/-
The primitive recursion term is closed if its arguments are closed.
-/
theorem Lambda.prec_term_closed (v s : Lambda) (hv : Lambda.IsClosed v) (hs : Lambda.IsClosed s) :
  Lambda.IsClosed (Lambda.prec_term v s) := by
  convert Lambda.IsClosed_app _ _ using 1
  · exact Lambda.fix_closed
  · exact Lambda.prec_body_correct_closed v s hv hs

/-
Double beta reduction lemma.
-/
theorem Lambda.double_beta_reduction (t a b : Lambda) (ha : Lambda.IsClosed a) :
  Lambda.reduces (Lambda.app (Lambda.app (Lambda.lam (Lambda.lam t)) a) b)
    (Lambda.subst b 0 (Lambda.subst a 1 t)) := by
  have step1 : Lambda.reduces (Lambda.app (Lambda.lam (Lambda.lam t)) a)
      (Lambda.lam (Lambda.subst a 1 t)) := by
    refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
    convert Lambda.reduces.refl _ using 1
    simp [Lambda.subst, Lambda.lift_closed ha 1 0]
  have step2 :
      Lambda.reduces (Lambda.app (Lambda.app (Lambda.lam (Lambda.lam t)) a) b)
          (Lambda.app (Lambda.lam (Lambda.subst a 1 t)) b) := by
    exact Lambda.reduces_app_left step1
  have step3 : Lambda.reduces (Lambda.app (Lambda.lam (Lambda.subst a 1 t)) b)
      (Lambda.subst b 0 (Lambda.subst a 1 t)) := by
    exact Lambda.beta_reduces
  exact Lambda.reduces_trans step2 step3

/-
Definition of Q (the unfolding of the fixed point) and proof that prec_term reduces to Q.
-/
def Lambda.Q (v s : Lambda) : Lambda :=
  Lambda.app (Lambda.W (Lambda.prec_body_correct v s)) (Lambda.W (Lambda.prec_body_correct v s))

theorem Lambda.prec_term_reduces_to_Q (v s : Lambda) (hv : Lambda.IsClosed v) (hs : Lambda.IsClosed
    s) :
  Lambda.reduces (Lambda.prec_term v s) (Lambda.Q v s) := by
  unfold Lambda.prec_term Lambda.Q
  exact Lambda.fix_reduces_W _ (Lambda.prec_body_correct_closed v s hv hs)

/-
Q reduces to the body applied to Q.
-/
theorem Lambda.Q_reduces (v s : Lambda) (hv : Lambda.IsClosed v) (hs : Lambda.IsClosed s) :
  Lambda.reduces (Lambda.Q v s) (Lambda.app (Lambda.prec_body_correct v s) (Lambda.Q v s)) := by
  have h_subst : Lambda.subst (Lambda.W (Lambda.prec_body_correct v s)) 0
      (Lambda.prec_body_correct v s) = Lambda.prec_body_correct v s := by
    have h_subst : Lambda.IsClosed (Lambda.prec_body_correct v s) := by
      exact Lambda.prec_body_correct_closed v s hv hs
    exact Lambda.IsClosed_imp_subst_eq h_subst _ _
  have := @Lambda.W_reduces (Lambda.prec_body_correct v s)
  aesop

/-
Definition of the inner body of the primitive recursion combinator and equality with the correct
body.
-/
def Lambda.prec_body_inner (v s : Lambda) : Lambda :=
    Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app Lambda.isZero (Lambda.var 0)))
      (Lambda.lift 2 0 v))
      (Lambda.app (Lambda.app (Lambda.lift 2 0 s) (Lambda.app Lambda.pred (Lambda.var 0)))
                  (Lambda.app (Lambda.var 1) (Lambda.app Lambda.pred (Lambda.var 0))))

theorem Lambda.prec_body_correct_eq (v s : Lambda) :
  Lambda.prec_body_correct v s = Lambda.lam (Lambda.lam (Lambda.prec_body_inner v s)) := by
    rfl

/-
The result of substituting into the inner body of the primitive recursion combinator.
-/
theorem Lambda.prec_body_inner_subst_eq (v s f : Lambda) (hv : Lambda.IsClosed v) (hs :
    Lambda.IsClosed s) :
  Lambda.subst (Lambda.church 0) 0 (Lambda.subst f 1 (Lambda.prec_body_inner v s)) =
  Lambda.app
      (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app Lambda.isZero (Lambda.church 0))) v)
    (Lambda.app (Lambda.app s (Lambda.app Lambda.pred (Lambda.church 0)))
      (Lambda.app (Lambda.subst (Lambda.church 0) 0 f) (Lambda.app Lambda.pred (Lambda.church 0))))
          := by
  have h_isZero_closed : Lambda.IsClosed Lambda.isZero := by
    intro s2 x2
    simp [Lambda.isZero, Lambda.subst, Lambda.subst_church, Lambda.true, Lambda.K, Lambda.false]
  have h_if_inner : f.subst 1 Lambda.ifThenElse = Lambda.ifThenElse :=
    Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed f 1
  have h_isZero_inner : f.subst 1 Lambda.isZero = Lambda.isZero :=
    Lambda.IsClosed_imp_subst_eq h_isZero_closed f 1
  have h_pred_inner : f.subst 1 Lambda.pred = Lambda.pred :=
    Lambda.IsClosed_imp_subst_eq Lambda.pred_closed f 1
  have h_v_inner : f.subst 1 v = v :=
    Lambda.IsClosed_imp_subst_eq hv f 1
  have h_s_inner : f.subst 1 s = s :=
    Lambda.IsClosed_imp_subst_eq hs f 1
  have h_v_outer : (Lambda.church 0).subst 0 (f.subst 1 v) = v := by
    simpa [h_v_inner] using (Lambda.IsClosed_imp_subst_eq hv (Lambda.church 0) 0)
  have h_s_outer : (Lambda.church 0).subst 0 (f.subst 1 s) = s := by
    simpa [h_s_inner] using (Lambda.IsClosed_imp_subst_eq hs (Lambda.church 0) 0)
  simp [Lambda.prec_body_inner, Lambda.subst, Lambda.lift_closed hv 2 0, Lambda.lift_closed hs 2 0,
    h_v_outer, h_s_outer]
  constructor
  · constructor
    · simpa [h_if_inner] using
        (Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed (Lambda.church 0) 0)
    · simpa [h_isZero_inner] using
        (Lambda.IsClosed_imp_subst_eq h_isZero_closed (Lambda.church 0) 0)
  · simpa [h_pred_inner] using (Lambda.IsClosed_imp_subst_eq Lambda.pred_closed (Lambda.church 0) 0)

/-
The substituted inner body of the primitive recursion combinator reduces to v.
-/
theorem Lambda.prec_body_inner_subst_reduces (v s f : Lambda) (hv : Lambda.IsClosed v) (hs :
    Lambda.IsClosed s) :
  Lambda.reduces (Lambda.subst (Lambda.church 0) 0 (Lambda.subst f 1 (Lambda.prec_body_inner v s)))
      v := by
  rw [Lambda.prec_body_inner_subst_eq v s f hv hs]
  have h_ifThenElse_true :
      Lambda.reduces
        (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse Lambda.true) v)
          (Lambda.app (Lambda.app s (Lambda.app Lambda.pred (Lambda.church 0)))
            (Lambda.app (Lambda.subst (Lambda.church 0) 0 f) (Lambda.app Lambda.pred (Lambda.church
                0)))))
        v := by
    exact Lambda.ifThenElse_true v _
  refine Lambda.reduces_trans ?_ h_ifThenElse_true
  apply_rules [Lambda.reduces_app_left, Lambda.reduces_app_right]
  exact Lambda.isZero_zero

/-
Auxiliary lemma: the expanded inner body reduces to v.
-/
theorem Lambda.prec_body_inner_subst_reduces_aux (v s f : Lambda) :
  Lambda.reduces (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app Lambda.isZero
      (Lambda.church 0))) v)
    (Lambda.app (Lambda.app s (Lambda.app Lambda.pred (Lambda.church 0)))
      (Lambda.app (Lambda.subst (Lambda.church 0) 0 f) (Lambda.app Lambda.pred (Lambda.church 0)))))
          v := by
  have h_ifThenElse_true :
      Lambda.reduces
        (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse Lambda.true) v)
          (Lambda.app (Lambda.app s (Lambda.app Lambda.pred (Lambda.church 0)))
            (Lambda.app (Lambda.subst (Lambda.church 0) 0 f) (Lambda.app Lambda.pred (Lambda.church
                0)))))
        v := by
    exact Lambda.ifThenElse_true v _
  refine Lambda.reduces_trans ?_ h_ifThenElse_true
  apply_rules [Lambda.reduces_app_left, Lambda.reduces_app_right]
  exact Lambda.isZero_zero

/-
The primitive recursion term applied to 0 reduces to v.
-/
theorem Lambda.prec_term_reduces_zero (v s : Lambda) (hv : Lambda.IsClosed v) (hs : Lambda.IsClosed
    s) :
  Lambda.reduces (Lambda.app (Lambda.prec_term v s) (Lambda.church 0)) v := by
  have h_subst :
      Lambda.reduces
        (Lambda.app (Lambda.app (Lambda.lam (Lambda.lam (Lambda.prec_body_inner v s))) (Lambda.Q v
            s)) (Lambda.church 0))
        (Lambda.subst (Lambda.church 0) 0 (Lambda.subst (Lambda.Q v s) 1 (Lambda.prec_body_inner v
            s))) := by
    exact Lambda.double_beta_reduction (Lambda.prec_body_inner v s) (Lambda.Q v s) (Lambda.church 0)
        <|
      by
        unfold Lambda.Q
        have hQ_closed : Lambda.IsClosed (Lambda.prec_body_correct v s) := by
          exact Lambda.prec_body_correct_closed v s hv hs
        exact Lambda.IsClosed_app (Lambda.W_closed _ hQ_closed) (Lambda.W_closed _ hQ_closed)
  convert Lambda.reduces_trans _ (Lambda.reduces_trans _ (Lambda.reduces_trans h_subst _)) using 1
  · convert Lambda.reduces_app_left (Lambda.prec_term_reduces_to_Q v s hv hs) using 1
  · convert Lambda.reduces_app_left (Lambda.Q_reduces v s hv hs) using 1
  · convert Lambda.prec_body_inner_subst_reduces v s (Lambda.Q v s) hv hs using 1

/-
The substituted inner body of the primitive recursion combinator reduces to the recursive step when
the argument is n+1.
-/
theorem Lambda.prec_body_inner_subst_succ_reduces (v s f : Lambda) (n : ℕ) (hv : Lambda.IsClosed v)
    (hs : Lambda.IsClosed s) (hf : Lambda.IsClosed f) :
  Lambda.reduces
      (Lambda.subst (Lambda.church (n + 1)) 0 (Lambda.subst f 1 (Lambda.prec_body_inner v s)))
    (Lambda.app (Lambda.app s (Lambda.church n)) (Lambda.app f (Lambda.church n))) := by
  have h_subst :
      Lambda.subst (Lambda.church (n + 1)) 0 (Lambda.subst f 1 (Lambda.prec_body_inner v s)) =
        Lambda.app
          (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app Lambda.isZero (Lambda.church (n +
              1)))) v)
          (Lambda.app (Lambda.app s (Lambda.app Lambda.pred (Lambda.church (n + 1))))
            (Lambda.app f (Lambda.app Lambda.pred (Lambda.church (n + 1))))) := by
    have h_isZero_closed : Lambda.IsClosed Lambda.isZero := by
      intro s2 x2
      simp [Lambda.isZero, Lambda.subst, Lambda.subst_church, Lambda.true, Lambda.K, Lambda.false]
    have h_if_inner : f.subst 1 Lambda.ifThenElse = Lambda.ifThenElse :=
      Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed f 1
    have h_isZero_inner : f.subst 1 Lambda.isZero = Lambda.isZero :=
      Lambda.IsClosed_imp_subst_eq h_isZero_closed f 1
    have h_pred_inner : f.subst 1 Lambda.pred = Lambda.pred :=
      Lambda.IsClosed_imp_subst_eq Lambda.pred_closed f 1
    have h_v_inner : f.subst 1 v = v :=
      Lambda.IsClosed_imp_subst_eq hv f 1
    have h_s_inner : f.subst 1 s = s :=
      Lambda.IsClosed_imp_subst_eq hs f 1
    have h_v_outer : (Lambda.church (n + 1)).subst 0 (f.subst 1 v) = v := by
      simpa [h_v_inner] using (Lambda.IsClosed_imp_subst_eq hv (Lambda.church (n + 1)) 0)
    have h_s_outer : (Lambda.church (n + 1)).subst 0 (f.subst 1 s) = s := by
      simpa [h_s_inner] using (Lambda.IsClosed_imp_subst_eq hs (Lambda.church (n + 1)) 0)
    have h_f_outer : (Lambda.church (n + 1)).subst 0 f = f :=
      Lambda.IsClosed_imp_subst_eq hf (Lambda.church (n + 1)) 0
    simp [Lambda.prec_body_inner, Lambda.subst, Lambda.lift_closed hv 2 0, Lambda.lift_closed hs 2
        0,
      h_v_outer, h_s_outer, h_f_outer]
    constructor
    · constructor
      · simpa [h_if_inner] using
          (Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed (Lambda.church (n + 1)) 0)
      · simpa [h_isZero_inner] using
          (Lambda.IsClosed_imp_subst_eq h_isZero_closed (Lambda.church (n + 1)) 0)
    · simpa [h_pred_inner] using
        (Lambda.IsClosed_imp_subst_eq Lambda.pred_closed (Lambda.church (n + 1)) 0)
  have h_reduces :
      Lambda.reduces
        (Lambda.app
          (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app Lambda.isZero (Lambda.church (n +
              1)))) v)
          (Lambda.app (Lambda.app s (Lambda.app Lambda.pred (Lambda.church (n + 1))))
            (Lambda.app f (Lambda.app Lambda.pred (Lambda.church (n + 1)))))
        )
        (Lambda.app (Lambda.app s (Lambda.app Lambda.pred (Lambda.church (n + 1))))
          (Lambda.app f (Lambda.app Lambda.pred (Lambda.church (n + 1))))) := by
    have h_reduces :
        Lambda.reduces
          (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse Lambda.false) v)
            (Lambda.app (Lambda.app s (Lambda.app Lambda.pred (Lambda.church (n + 1))))
              (Lambda.app f (Lambda.app Lambda.pred (Lambda.church (n + 1)))))
          )
          (Lambda.app (Lambda.app s (Lambda.app Lambda.pred (Lambda.church (n + 1))))
            (Lambda.app f (Lambda.app Lambda.pred (Lambda.church (n + 1))))) := by
      exact Lambda.ifThenElse_false v _
    convert Lambda.reduces_trans _ h_reduces using 1
    apply_rules [Lambda.reduces_app_left, Lambda.reduces_app_right]
    exact Lambda.isZero_succ n
  have h_pred : Lambda.reduces (Lambda.app Lambda.pred (Lambda.church (n + 1))) (Lambda.church n) :=
      by
    convert Lambda.pred_works (n + 1) using 1
  have h_reduces_subst :
      Lambda.reduces
        (Lambda.app (Lambda.app s (Lambda.app Lambda.pred (Lambda.church (n + 1))))
          (Lambda.app f (Lambda.app Lambda.pred (Lambda.church (n + 1)))))
        (Lambda.app (Lambda.app s (Lambda.church n)) (Lambda.app f (Lambda.app Lambda.pred
            (Lambda.church (n + 1))))) := by
    exact Lambda.reduces_app_left (Lambda.reduces_app_right h_pred)
  have h_reduces_subst' :
      Lambda.reduces
        (Lambda.app (Lambda.app s (Lambda.church n)) (Lambda.app f (Lambda.app Lambda.pred
            (Lambda.church (n + 1)))))
        (Lambda.app (Lambda.app s (Lambda.church n)) (Lambda.app f (Lambda.church n))) := by
    exact Lambda.reduces_app_right (Lambda.reduces_app_right h_pred)
  exact h_subst.symm ▸ Lambda.reduces_trans h_reduces
      (Lambda.reduces_trans h_reduces_subst h_reduces_subst')

/-
The result of substituting into the inner body of the primitive recursion combinator with successor.
-/
theorem Lambda.prec_body_inner_subst_succ_eq (v s f : Lambda) (n : ℕ) (hv : Lambda.IsClosed v) (hs :
    Lambda.IsClosed s) (hf : Lambda.IsClosed f) :
  Lambda.subst (Lambda.church (n + 1)) 0 (Lambda.subst f 1 (Lambda.prec_body_inner v s)) =
  Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app Lambda.isZero (Lambda.church (n +
      1)))) v)
    (Lambda.app (Lambda.app s (Lambda.app Lambda.pred (Lambda.church (n + 1))))
      (Lambda.app f (Lambda.app Lambda.pred (Lambda.church (n + 1))))) := by
  have h_isZero_closed : Lambda.IsClosed Lambda.isZero := by
    intro s2 x2
    simp [Lambda.isZero, Lambda.subst, Lambda.subst_church, Lambda.true, Lambda.K, Lambda.false]
  have h_if_inner : f.subst 1 Lambda.ifThenElse = Lambda.ifThenElse :=
    Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed f 1
  have h_isZero_inner : f.subst 1 Lambda.isZero = Lambda.isZero :=
    Lambda.IsClosed_imp_subst_eq h_isZero_closed f 1
  have h_pred_inner : f.subst 1 Lambda.pred = Lambda.pred :=
    Lambda.IsClosed_imp_subst_eq Lambda.pred_closed f 1
  have h_v_inner : f.subst 1 v = v :=
    Lambda.IsClosed_imp_subst_eq hv f 1
  have h_s_inner : f.subst 1 s = s :=
    Lambda.IsClosed_imp_subst_eq hs f 1
  have h_v_outer : (Lambda.church (n + 1)).subst 0 (f.subst 1 v) = v := by
    simpa [h_v_inner] using (Lambda.IsClosed_imp_subst_eq hv (Lambda.church (n + 1)) 0)
  have h_s_outer : (Lambda.church (n + 1)).subst 0 (f.subst 1 s) = s := by
    simpa [h_s_inner] using (Lambda.IsClosed_imp_subst_eq hs (Lambda.church (n + 1)) 0)
  have h_f_outer : (Lambda.church (n + 1)).subst 0 f = f :=
    Lambda.IsClosed_imp_subst_eq hf (Lambda.church (n + 1)) 0
  simp [Lambda.prec_body_inner, Lambda.subst, Lambda.lift_closed hv 2 0, Lambda.lift_closed hs 2 0,
    h_v_outer, h_s_outer, h_f_outer]
  constructor
  · constructor
    · simpa [h_if_inner] using
        (Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed (Lambda.church (n + 1)) 0)
    · simpa [h_isZero_inner] using
        (Lambda.IsClosed_imp_subst_eq h_isZero_closed (Lambda.church (n + 1)) 0)
  · simpa [h_pred_inner] using
      (Lambda.IsClosed_imp_subst_eq Lambda.pred_closed (Lambda.church (n + 1)) 0)

/-
The primitive recursion term applied to n+1 reduces to the recursive step applied to Q.
-/
theorem Lambda.prec_term_reduces_succ_aux (v s : Lambda) (n : ℕ) (hv : Lambda.IsClosed v) (hs :
    Lambda.IsClosed s) :
  Lambda.reduces (Lambda.app (Lambda.prec_term v s) (Lambda.church (n + 1)))
    (Lambda.app (Lambda.app s (Lambda.church n)) (Lambda.app (Lambda.Q v s) (Lambda.church n))) :=
        by
  have hQ :
      Lambda.reduces
        (Lambda.app (Lambda.prec_term v s) (Lambda.church (n + 1)))
        (Lambda.app (Lambda.app (Lambda.prec_body_correct v s) (Lambda.Q v s)) (Lambda.church (n +
            1))) := by
    have hQ :
        Lambda.reduces
          (Lambda.app (Lambda.prec_term v s) (Lambda.church (n + 1)))
          (Lambda.app (Lambda.Q v s) (Lambda.church (n + 1))) := by
      apply_rules [Lambda.reduces_app_left]
      exact Lambda.prec_term_reduces_to_Q v s hv hs
    have hQ : Lambda.reduces (Lambda.Q v s)
        (Lambda.app (Lambda.prec_body_correct v s) (Lambda.Q v s)) := by
      exact Lambda.Q_reduces v s hv hs
    exact Lambda.reduces_trans ‹_› (Lambda.reduces_app_left hQ)
  have hQ' :
      Lambda.reduces
        (Lambda.subst (Lambda.church (n + 1)) 0 (Lambda.subst (Lambda.Q v s) 1
            (Lambda.prec_body_inner v s)))
        (Lambda.app (Lambda.app s (Lambda.church n)) (Lambda.app (Lambda.Q v s) (Lambda.church n)))
            := by
    convert Lambda.prec_body_inner_subst_succ_reduces v s (Lambda.Q v s) n hv hs _ using 1
    unfold Lambda.Q
    have hQ_closed : Lambda.IsClosed (Lambda.prec_body_correct v s) := by
      exact Lambda.prec_body_correct_closed v s hv hs
    have hW_closed : ∀ t : Lambda, Lambda.IsClosed t → Lambda.IsClosed (Lambda.W t) := by
      exact fun t ht => Lambda.W_closed t ht
    exact Lambda.IsClosed_app (hW_closed _ hQ_closed) (hW_closed _ hQ_closed)
  refine Lambda.reduces_trans hQ ?_
  convert Lambda.reduces_trans _ hQ' using 1
  convert Lambda.double_beta_reduction _ _ _ ?_ using 1
  unfold Lambda.Q
  have hQ_closed : Lambda.IsClosed (Lambda.prec_body_correct v s) := by
    exact Lambda.prec_body_correct_closed v s hv hs
  exact Lambda.IsClosed_app (Lambda.W_closed _ hQ_closed) (Lambda.W_closed _ hQ_closed)

/-
The primitive recursion term correctly computes the primitive recursion of a function.
-/
theorem Lambda.prec_works (v : ℕ) (s : Lambda) (f : ℕ → ℕ → ℕ) (n : ℕ)
  (hs_closed : Lambda.IsClosed s)
  (hs : ∀ n r, Lambda.reduces (Lambda.app (Lambda.app s (Lambda.church n)) (Lambda.church r))
      (Lambda.church (f n r))) :
  Lambda.reduces (Lambda.app (Lambda.prec_term (Lambda.church v) s) (Lambda.church n))
      (Lambda.church (Nat.rec v f n)) := by
  induction n generalizing v s f with
  | zero =>
      convert Lambda.prec_term_reduces_zero _ _ _ _ using 1
      · exact Lambda.church_closed v
      · assumption
  | succ n ih =>
      have h_Q_n : Lambda.reduces (Lambda.app (Lambda.Q (Lambda.church v) s) (Lambda.church n))
          (Lambda.church (Nat.rec v f n)) := by
        have h_Q_n :
            Lambda.reduces
              (Lambda.app (Lambda.prec_term (Lambda.church v) s) (Lambda.church n))
              (Lambda.app (Lambda.Q (Lambda.church v) s) (Lambda.church n)) := by
          apply_rules [Lambda.reduces_app_left]
          exact Lambda.prec_term_reduces_to_Q (Lambda.church v) s (Lambda.church_closed v) hs_closed
        have := ih v s f hs_closed hs
        have := Lambda.confluence_theorem this h_Q_n
        obtain ⟨t3, ht3₁, ht3₂⟩ := this
        have := Lambda.church_normal (Nat.rec v f n)
        have := Lambda.reduces_normal_eq this ht3₁
        aesop
      have h_prec_succ :
        Lambda.reduces
          (Lambda.app (Lambda.prec_term (Lambda.church v) s) (Lambda.church (n + 1)))
          (Lambda.app (Lambda.app s (Lambda.church n)) (Lambda.app (Lambda.Q (Lambda.church v) s)
              (Lambda.church n))) := by
        apply_rules [Lambda.prec_term_reduces_succ_aux]
        exact Lambda.church_closed v
      have h_s_n_Q_n :
        Lambda.reduces
          (Lambda.app (Lambda.app s (Lambda.church n)) (Lambda.app (Lambda.Q (Lambda.church v) s)
              (Lambda.church n)))
          (Lambda.church (f n (Nat.rec v f n))) := by
        have := hs n (Nat.rec v f n)
        exact reduces_trans (reduces_app_right h_Q_n) this
      exact Lambda.reduces_trans h_prec_succ h_s_n_Q_n |> fun h => by simpa [Nat.rec] using h

/-
Substitution of a closed term commutes with `closeAt`.
-/
theorem Lambda.closeAt_subst_closed (s t : Lambda) (x : ℕ) (hs : Lambda.IsClosed s) :
  Lambda.closeAt x (Lambda.subst s x t) = Lambda.subst s x (Lambda.closeAt (x + 1) t) := by
    convert @Lambda.subst_closeAt s t x hs using 1

/-
Minimization (mu operator) using the Y combinator.
mu_body = λ r n. ifThenElse (isZero (f n)) n (r (succ n))
where f is a free variable (var 2).
-/
def Lambda.mu_body : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app
      Lambda.isZero (Lambda.app (Lambda.var 2) (Lambda.var 0)))) (Lambda.var 0)) (Lambda.app
      (Lambda.var 1) (Lambda.app Lambda.succ (Lambda.var 0)))))

/-- mu f = fix (mu_body f) 0 -/
def Lambda.mu : Lambda :=
  Lambda.lam (Lambda.app (Lambda.app Lambda.fix Lambda.mu_body) (Lambda.church 0))

/--
Target specification for minimization.

The file defines the combinator `Lambda.mu`, but the surrounding development does not yet
derive this correctness statement. Keeping the specification explicit is more honest than
postulating a global theorem or hiding the gap behind an axiom.
-/
def Lambda.MuCorrectness : Prop :=
  ∀ (f : ℕ → ℕ) (F : Lambda),
    Lambda.IsClosed F →
    (∀ n, Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church (f n))) →
    ∀ n, (∀ m < n, f m ≠ 0) → f n = 0 →
      Lambda.reduces (Lambda.app Lambda.mu F) (Lambda.church n)

/-
What is actually established in this file is the direction
`LambdaComputable -> Nat.Partrec`, together with concrete Lambda realizers for a number of
basic operators and a primitive-recursion term over Church numerals.

A full theorem `Nat.Partrec f -> LambdaComputable f` still needs two missing ingredients:
1. a general compiler for the `Nat.Partrec.prec`/`Nat.Partrec.Code.prec` constructor on
   paired inputs, not only the specialized `Lambda.prec_works` theorem proved above;
2. a proof of `Lambda.MuCorrectness`, which would cover minimization / `rfind`.
-/

-- #print Nat.Partrec

-- #print Nat.Partrec.Code

-- #print Nat.Partrec




/-
Lifting commutes with substitution for closed s.
-/
theorem Lambda.lift_subst_closed (s t : Lambda) (n k x : ℕ) (h : k ≤ x) (hs : Lambda.IsClosed s) :
  Lambda.lift n k (Lambda.subst s x t) = Lambda.subst (Lambda.lift n k s) (x + n)
      (Lambda.lift n k t) := by
    convert Lambda.lift_subst_of_closed s t n k x h hs using 1;
    -- Since $s$ is closed, $lift n k s = s$ by definition of lift and the fact that $s$'s variables
    -- do not depend on $k$ or $n$.
    have h_lift_closed : s.IsClosed → lift n k s = s := by
      exact fun h => Lambda.lift_closed h n k;
    rw [ h_lift_closed hs ]









/-
Substitution of a closed term commutes with closure.
-/
theorem Lambda.subst_close_of_closed (s t : Lambda) (hs : Lambda.IsClosed s) :
  Lambda.close (Lambda.subst s 0 t) = Lambda.subst s 0 (Lambda.closeAt 1 t) := by
    convert Lambda.closeAt_subst_closed s t 0 _ using 1 ; aesop;

def t_counter : Lambda := Lambda.app (Lambda.lam (Lambda.lam (Lambda.var 1))) (Lambda.var 0)
-- #eval
-- #eval (Lambda.var 0) 0 (Lambda.lam (Lambda.var 1)))

end
