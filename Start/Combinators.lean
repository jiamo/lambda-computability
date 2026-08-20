/-
Booleans, conditionals, pairs, predecessor, subtraction and comparison
combinators, together with the closed-term API (`Lambda.IsClosed`).

Extracted from `Start/Basic.lean` as part of the modular split.
-/

import Start.Arithmetic


set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Definitions of boolean logic, predecessor, subtraction, comparison, and pairing on Church numerals.
-/
def Lambda.true : Lambda := Lambda.K
def Lambda.false : Lambda := Lambda.church 0

def Lambda.isZero : Lambda :=
  Lambda.lam (Lambda.app (Lambda.app (Lambda.var 0) (Lambda.lam Lambda.false)) Lambda.true)

def Lambda.pred : Lambda :=
  Lambda.lam (Lambda.app Lambda.fst (Lambda.app (Lambda.app (Lambda.var 0) (Lambda.lam (Lambda.app
      (Lambda.app Lambda.pair (Lambda.app Lambda.snd (Lambda.var 0))) (Lambda.app Lambda.succ
      (Lambda.app Lambda.snd (Lambda.var 0)))))) (Lambda.app (Lambda.app Lambda.pair (Lambda.church
      0)) (Lambda.church 0))))

def Lambda.sub : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 0) Lambda.pred) (Lambda.var 1)))

def Lambda.leq : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.app Lambda.isZero (Lambda.app (Lambda.app Lambda.sub (Lambda.var
      1)) (Lambda.var 0))))

def Lambda.and : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 1) (Lambda.var 0)) Lambda.false))

def Lambda.not : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.var 0))
      (Lambda.var 1))))

def Lambda.lt : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.app Lambda.not (Lambda.app (Lambda.app Lambda.leq (Lambda.var 0))
      (Lambda.var 1))))

def Lambda.ifThenElse : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.var 1))
      (Lambda.var 0))))

def Lambda.natPair : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app
      (Lambda.app Lambda.lt (Lambda.var 1)) (Lambda.var 0))) (Lambda.app (Lambda.app Lambda.add
      (Lambda.app (Lambda.app Lambda.mult (Lambda.var 0)) (Lambda.var 0))) (Lambda.var 1)))
      (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app
      Lambda.mult (Lambda.var 1)) (Lambda.var 1))) (Lambda.var 1))) (Lambda.var 0))))

/-
The unpairing combinators are *not* defined here: the real implementations are
`Lambda.unpairLeft_impl` and `Lambda.unpairRight_impl` in `Start/Pairing.lean`,
together with their correctness theorems `Lambda.unpairLeft_works` and
`Lambda.unpairRight_works`.  The former placeholder definitions
`Lambda.unpairLeft := Lambda.church 0` and `Lambda.unpairRight := Lambda.church 0`
were unused dead code and are kept only in this comment for reference.
-/



/-
Substitution into a Church numeral (which is a closed term) is the identity.
-/
theorem Lambda.subst_church (s : Lambda) (k : ℕ) (n : ℕ) :
    Lambda.subst s k (Lambda.church n) = Lambda.church n := by
  rw [Lambda.church_eq_iterate]
  have h0neq : 0 ≠ k + 2 := by omega
  have h1neq : 1 ≠ k + 2 := by omega
  have h0gt : ¬ 0 > k + 2 := by omega
  have h1gt : ¬ 1 > k + 2 := by omega
  simp [Lambda.subst, Lambda.subst_iterate, h0gt, h1gt]

/-
`Lambda.mult_aux n m` reduces to `Lambda.church (n * m)`.
-/
def Lambda.mult_aux (n m : ℕ) :=
  Lambda.lam
      (Lambda.lam (Lambda.iterate (Lambda.app (Lambda.church m) (Lambda.var 1)) (Lambda.var 0) n))

theorem Lambda.mult_aux_reduces_church (n m : ℕ) :
  Lambda.reduces (Lambda.mult_aux n m) (Lambda.church (n * m)) := by
    -- Apply the hypothesis `h_subst` to the term `Lambda.app (Lambda.var 3) (Lambda.var 1)`.
    have h_apply : Lambda.reduces
        (Lambda.iterate (Lambda.app (Lambda.church m) (Lambda.var 1)) (Lambda.var 0) n)
        (Lambda.iterate (Lambda.var 1) (Lambda.var 0) (n * m)) := by
      exact Lambda.iterate_mul_term n m
    apply_rules [ Lambda.reduces_lam ]

/-
`Lambda.mult (church n) (church m)` reduces to `Lambda.mult_step1 n m`.
-/
def Lambda.mult_step1 (n m : ℕ) :=
  Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.church n) (Lambda.app (Lambda.church m)
      (Lambda.var 1))) (Lambda.var 0)))

theorem Lambda.mult_reduces_to_step1 (n m : ℕ) :
  Lambda.reduces (Lambda.app (Lambda.app Lambda.mult (Lambda.church n)) (Lambda.church m))
      (Lambda.mult_step1 n m) := by
  refine Lambda.reduces.step _ _ _ (.app_left _ _ _ (.beta _ _)) ?_
  refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
  convert Lambda.reduces.refl (Lambda.mult_step1 n m) using 1
  simp [Lambda.mult_step1, Lambda.subst, Lambda.subst_church, Lambda.lift_church]


/-
`mult_step1` reduces to `mult_aux`.
-/
theorem Lambda.mult_step1_reduces_to_mult_aux (n m : ℕ) :
    Lambda.reduces (Lambda.mult_step1 n m) (Lambda.mult_aux n m) := by
  have h_apply :
      Lambda.reduces
        (Lambda.app (Lambda.app (Lambda.church n) (Lambda.app (Lambda.church m) (Lambda.var 1)))
            (Lambda.var 0))
        (Lambda.iterate (Lambda.app (Lambda.church m) (Lambda.var 1)) (Lambda.var 0) n) := by
    exact Lambda.church_reduces_iterate n (Lambda.app (Lambda.church m) (Lambda.var 1))
        (Lambda.var 0)
  apply_rules [Lambda.reduces_lam]

/-
Multiplication works on Church numerals.
-/
theorem Lambda.mult_works (n m : ℕ) :
    Lambda.reduces (Lambda.app (Lambda.app Lambda.mult (Lambda.church n)) (Lambda.church m))
        (Lambda.church (n * m)) := by
  -- By transitivity, we can chain these reductions together.
  exact Lambda.reduces_trans (Lambda.mult_reduces_to_step1 n m)
    (Lambda.reduces_trans (Lambda.mult_step1_reduces_to_mult_aux n m)
      (Lambda.mult_aux_reduces_church n m))

/-
`isZero` applied to `church 0` reduces to `true`.
-/
theorem Lambda.isZero_zero :
    Lambda.reduces (Lambda.app Lambda.isZero (Lambda.church 0)) Lambda.true := by
  constructor;
  constructor;
  -- By definition of `church`, we know that `church 0` is the identity function.
  have h_church0 : Lambda.church 0 = Lambda.lam (Lambda.lam (Lambda.var 0)) := by
    rfl;
  -- The identity function applied to any argument is just the argument itself.
  simp [h_church0, Lambda.subst];
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor

/-
`isZero` applied to `church (n+1)` reduces to `false`.
-/
theorem Lambda.isZero_succ (n : ℕ) :
    Lambda.reduces (Lambda.app Lambda.isZero (Lambda.church (n + 1))) Lambda.false := by
  cases n with
  | zero =>
      repeat constructor
  | succ n =>
      rw [Lambda.church]
      have h_iter :
          List.foldl (fun t x => (Lambda.var 1).app t) (Lambda.var 0) (List.range (n + 2)) =
            (Lambda.var 1).app
                (List.foldl (fun t x => (Lambda.var 1).app t) (Lambda.var 0) (List.range (n + 1)))
                := by
        simp +decide [List.range_succ]
      rw [h_iter]
      repeat constructor



/-
Definition of the result of reducing `pair t1 t2`.
-/
def Lambda.pair_res (t1 t2 : Lambda) : Lambda :=
  Lambda.lam
    (Lambda.app
      (Lambda.app (Lambda.var 0) (Lambda.lift 1 0 t1))
      (Lambda.lift 1 0 t2))

/-
Reduction of `pair t1 t2` to `pair_res t1 t2`.
-/
theorem Lambda.pair_reduces (t1 t2 : Lambda) :
  Lambda.reduces (Lambda.app (Lambda.app Lambda.pair t1) t2) (Lambda.pair_res t1 t2) := by
  refine Lambda.reduces.step _ _ _ (.app_left _ _ _ (.beta _ _)) ?_
  refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
  convert Lambda.reduces.refl (Lambda.pair_res t1 t2) using 1
  rw [Lambda.pair_res]
  have hsubst :
      Lambda.subst (Lambda.lift 1 0 t2) 1 (Lambda.lift 1 0 (Lambda.lift 1 0 t1)) =
        Lambda.lift 1 0 t1 := by
    rw [Lambda.lift_lift t1 1 1 0 0 (Nat.le_refl 0)]
    simpa using (Lambda.subst_lift (Lambda.lift 1 0 t1) (Lambda.lift 1 0 t2) 1)
  simp [Lambda.subst, hsubst]

/-
`fst p` reduces to `p K`.
-/
theorem Lambda.fst_app_reduces (p : Lambda) :
  Lambda.reduces (Lambda.app Lambda.fst p) (Lambda.app p Lambda.K) := by
    exact .step _ _ _ ( .beta _ _ ) ( .refl _ )

/-
Definition of closed terms: substitution has no effect.
-/
def Lambda.IsClosed (t : Lambda) : Prop := ∀ s x, Lambda.subst s x t = t

/-
Variables are not closed terms.
-/
theorem Lambda.IsClosed_var (n : ℕ) : ¬ Lambda.IsClosed (Lambda.var n) := by
  -- By definition of closed, if a term is closed, then substituting any term for any variable in it
  -- doesn't change it. For a variable term (var n), substituting any term for n would result in a
  -- different term. Therefore, var n cannot be closed.
  intro h
  have hn := h (Lambda.var (n + 1)) n
  simp [Lambda.subst] at hn

/-
Checking Nat.pair definition and LambdaComputable.succ status.
-/

/-
`pred 0` reduces to `0`.
-/
theorem Lambda.pred_zero :
    Lambda.reduces (Lambda.app Lambda.pred (Lambda.church 0)) (Lambda.church 0) := by
  -- By definition of `pred`, we have `pred.app (church 0) = app (fst) (app (app (church 0) (app
  -- (app pair (app snd (var 0))) (app succ (app snd (var 0))))) (app (app pair (church 0)) (church
  -- 0)))`.
  simp only [Lambda.pred, Lambda.fst, Lambda.pair]
  repeat' constructor

/-
Helper definitions for predecessor: step function and initial value.
-/
def Lambda.pred_step : Lambda :=
  Lambda.lam (Lambda.app (Lambda.app Lambda.pair (Lambda.app Lambda.snd (Lambda.var 0))) (Lambda.app
      Lambda.succ (Lambda.app Lambda.snd (Lambda.var 0))))

def Lambda.pred_init : Lambda :=
  Lambda.app (Lambda.app Lambda.pair (Lambda.church 0)) (Lambda.church 0)

/-
Definition of IsClosedAt: t has no free variables >= k.
-/
def Lambda.IsClosedAt (t : Lambda) (k : ℕ) : Prop := ∀ s x, x ≥ k → Lambda.subst s x t = t

/-
Application of closed terms is closed.
-/
theorem Lambda.IsClosed_app {t1 t2 : Lambda} (h1 : Lambda.IsClosed t1) (h2 : Lambda.IsClosed t2) :
    Lambda.IsClosed (Lambda.app t1 t2) := by
  unfold Lambda.IsClosed at *;
  unfold Lambda.subst; aesop;

/-
Lambda abstraction of a closed term is closed.
-/
theorem Lambda.IsClosed_lam {t : Lambda} (h : Lambda.IsClosed t) :
    Lambda.IsClosed (Lambda.lam t) := by
  intro s x;
  -- By definition of substitution, we have:
  unfold Lambda.subst;
  -- By definition of substitution, if $t$ is closed, then substituting any term for a variable in
  -- $t$ does not change $t$.
  have h_subst : ∀ s x, Lambda.subst s x t = t := by
    exact h;
  rw [ h_subst ]

/-
A variable `n` is closed at `k` if `n < k`.
-/
theorem Lambda.IsClosedAt_var (n k : ℕ) (h : n < k) : Lambda.IsClosedAt (Lambda.var n) k := by
  intro s x hx
  have hne : n ≠ x := by omega
  have hngt : ¬ n > x := by omega
  simp [Lambda.subst, hne, hngt]

/-
Application of terms closed at k is closed at k.
-/
theorem Lambda.IsClosedAt_app {t1 t2 : Lambda} {k : ℕ} (h1 : Lambda.IsClosedAt t1 k) (h2 :
    Lambda.IsClosedAt t2 k) : Lambda.IsClosedAt (Lambda.app t1 t2) k := by
  intro s x hx;
  unfold Lambda.subst;
  rw [h1 s x hx, h2 s x hx]

/-
Lambda abstraction of a term closed at k+1 is closed at k.
-/
theorem Lambda.IsClosedAt_lam {t : Lambda} {k : ℕ} (h : Lambda.IsClosedAt t (k + 1)) :
    Lambda.IsClosedAt (Lambda.lam t) k := by
  intro s x hx
  simp only [Lambda.subst, Lambda.lam.injEq]
  exact h (Lambda.lift 1 0 s) (x + 1) (by omega)

/-
IsClosedAt t 0 is equivalent to IsClosed t.
-/
theorem Lambda.IsClosedAt_zero_iff_IsClosed (t : Lambda) :
    Lambda.IsClosedAt t 0 ↔ Lambda.IsClosed t := by
  constructor
  · exact fun a s x => a s x (Nat.zero_le _)
  · exact fun a s x _ => a s x

theorem Lambda.IsClosed_imp_subst_eq {t : Lambda} (h : Lambda.IsClosed t) (s : Lambda) (x : ℕ) :
  Lambda.subst s x t = t := by
  exact h s x

theorem Lambda.lift_closed {t : Lambda} (h : Lambda.IsClosed t) (n k : ℕ) :
    Lambda.lift n k t = t := by
  have h_lift_closed :
      ∀ (t : Lambda) (d n k : ℕ),
        (∀ s x, x ≥ k → Lambda.subst (Lambda.lift d 0 s) x t = t) →
        Lambda.lift n k t = t := by
    intro t
    induction t with
    | var i =>
        intro d n k ht
        by_cases hik : i < k
        · simp [Lambda.lift, hik]
        · exfalso
          have hki : k ≤ i := Nat.le_of_not_lt hik
          have hbad := ht (Lambda.var (i + 1)) i hki
          simp [Lambda.subst, Lambda.lift] at hbad
          omega
    | app t1 t2 ih1 ih2 =>
        intro d n k ht
        have ht1 : ∀ s x, x ≥ k → Lambda.subst (Lambda.lift d 0 s) x t1 = t1 := by
          intro s x hx
          have h_eq := ht s x hx
          unfold Lambda.subst at h_eq
          injection h_eq with h1 h2
        have ht2 : ∀ s x, x ≥ k → Lambda.subst (Lambda.lift d 0 s) x t2 = t2 := by
          intro s x hx
          have h_eq := ht s x hx
          unfold Lambda.subst at h_eq
          injection h_eq with h1 h2
        have h1 : Lambda.lift n k t1 = t1 := ih1 d n k ht1
        have h2 : Lambda.lift n k t2 = t2 := ih2 d n k ht2
        simp [Lambda.lift, h1, h2]
    | lam t ih =>
        intro d n k ht
        have ht' : ∀ s x, x ≥ k + 1 → Lambda.subst (Lambda.lift (d + 1) 0 s) x t = t := by
          intro s x hx
          have hx1 : 1 ≤ x := le_trans (Nat.succ_le_succ (Nat.zero_le k)) hx
          have hxm1 : k ≤ x - 1 := by
            omega
          have h_eq := ht s (x - 1) hxm1
          unfold Lambda.subst at h_eq
          injection h_eq with h_inner
          rw [← Lambda.lift_add 1 d 0 s] at h_inner
          simpa [Nat.sub_add_cancel hx1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              h_inner
        have h_body : Lambda.lift n (k + 1) t = t := ih (d + 1) n (k + 1) ht'
        simpa [Lambda.lift] using congrArg Lambda.lam h_body
  exact h_lift_closed t 0 n k (fun s x _ => by simpa [Lambda.lift_zero] using h s x)

/-
Simplification of `pair_res` when the residual substitution and lift are trivial.
-/
theorem Lambda.pair_res_closed_eq (t1 t2 : Lambda)
  (h_lift1 : Lambda.lift 1 0 t1 = t1)
  (h_lift2 : Lambda.lift 1 0 t2 = t2) :
  Lambda.pair_res t1 t2 = Lambda.lam (Lambda.app (Lambda.app (Lambda.var 0) t1) t2) := by
  simp [Lambda.pair_res, h_lift1, h_lift2]


/-
`snd p` reduces to `p (\x y. y)`.
-/
theorem Lambda.snd_app_reduces (p : Lambda) :
  Lambda.reduces (Lambda.app Lambda.snd p) (Lambda.app p (Lambda.lam (Lambda.lam (Lambda.var 0))))
      := by
    constructor;
    constructor;
    constructor


/-
Check definitions of Nat.unpair and Nat.sqrt
-/

/-
Church numerals are closed terms.
-/
theorem Lambda.church_closed (n : ℕ) : Lambda.IsClosed (Lambda.church n) := by
  -- By definition of church numerals, they are closed terms, so for any s and x, `Lambda.subst s x
  -- (Lambda.church n) = Lambda.church n`.
  have h_closed : ∀ s x, Lambda.subst s x (Lambda.church n) = Lambda.church n := by
    intros s x; exact Lambda.subst_church s x n
  exact h_closed

/-
`pair_res (church n) (church m)` simplifies to `\z. z (church n) (church m)`.
-/
theorem Lambda.pair_res_church (n m : ℕ) :
  Lambda.pair_res (Lambda.church n) (Lambda.church m) = Lambda.lam
      (Lambda.app (Lambda.app (Lambda.var 0) (Lambda.church n)) (Lambda.church m)) := by
  apply Lambda.pair_res_closed_eq
  · exact Lambda.lift_church 1 0 n
  · exact Lambda.lift_church 1 0 m

/-
`fst (pair (church n) (church m))` reduces to `church n`.
-/
theorem Lambda.fst_pair_church (n m : ℕ) :
  Lambda.reduces (Lambda.app Lambda.fst (Lambda.app (Lambda.app Lambda.pair (Lambda.church n))
      (Lambda.church m))) (Lambda.church n) := by
  have h_fst_pair_reduces_aux :
      Lambda.reduces (Lambda.app Lambda.fst (Lambda.pair_res (Lambda.church n) (Lambda.church m)))
          (Lambda.church n) := by
    have h1 :
        Lambda.reduces (Lambda.app Lambda.fst (Lambda.pair_res (Lambda.church n) (Lambda.church m)))
          (Lambda.app (Lambda.pair_res (Lambda.church n) (Lambda.church m)) Lambda.K) := by
      exact Lambda.fst_app_reduces _
    have h2 :
        Lambda.reduces (Lambda.app (Lambda.pair_res (Lambda.church n) (Lambda.church m)) Lambda.K)
          (Lambda.app (Lambda.app Lambda.K (Lambda.church n)) (Lambda.church m)) := by
      rw [Lambda.pair_res_church]
      refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
      convert Lambda.reduces.refl
          (Lambda.app (Lambda.app Lambda.K (Lambda.church n)) (Lambda.church m)) using 1
      simp [Lambda.subst, Lambda.subst_church]
    have h3 :
        Lambda.reduces (Lambda.app (Lambda.app Lambda.K (Lambda.church n)) (Lambda.church m))
            (Lambda.church n) := by
      refine Lambda.reduces.step _ _ _ (.app_left _ _ _ (.beta _ _)) ?_
      refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
      convert Lambda.reduces.refl (Lambda.church n) using 1
      simp [Lambda.subst, Lambda.subst_church, Lambda.lift_church]
    exact Lambda.reduces_trans h1 (Lambda.reduces_trans h2 h3)
  have h_fst_pair :
      Lambda.reduces (Lambda.app Lambda.fst (Lambda.app (Lambda.app Lambda.pair (Lambda.church n))
          (Lambda.church m)))
        (Lambda.app Lambda.fst (Lambda.pair_res (Lambda.church n) (Lambda.church m))) := by
    exact Lambda.reduces_app_right (Lambda.pair_reduces _ _)
  exact Lambda.reduces_trans h_fst_pair h_fst_pair_reduces_aux

/-
`snd (pair (church n) (church m))` reduces to `church m`.
-/
theorem Lambda.snd_pair_church (n m : ℕ) :
  Lambda.reduces (Lambda.app Lambda.snd (Lambda.app (Lambda.app Lambda.pair (Lambda.church n))
      (Lambda.church m))) (Lambda.church m) := by
    -- By Lemma 25, `snd (pair_res (church n) (church m))` reduces to `church m`.
    have h_snd_pair_res : Lambda.reduces
        (Lambda.app Lambda.snd (Lambda.pair_res (Lambda.church n) (Lambda.church m)))
        (Lambda.church m) := by
      rw [ Lambda.pair_res_church ];
      -- Using the identity `snd (\f x. f x y) -> y`, we get: `snd (\z. z (church n) (church m)) ->
      -- (\z. z (church n) (church m)) (\x y. y)`.
      have h_snd : Lambda.reduces (Lambda.app Lambda.snd (Lambda.lam (Lambda.app (Lambda.app
          (Lambda.var 0) (Lambda.church n)) (Lambda.church m)))) (Lambda.app (Lambda.lam (Lambda.app
          (Lambda.app (Lambda.var 0) (Lambda.church n)) (Lambda.church m))) (Lambda.lam (Lambda.lam
          (Lambda.var 0)))) := by
        exact Lambda.snd_app_reduces _
      -- Applying the reduction step to the lambda term, we get:
      have h_beta : Lambda.reduces (Lambda.app (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 0)
          (Lambda.church n)) (Lambda.church m))) (Lambda.lam (Lambda.lam (Lambda.var 0))))
          (Lambda.app (Lambda.lam (Lambda.var 0)) (Lambda.church m)) := by
        constructor;
        constructor;
        constructor;
        constructor;
        constructor;
        -- Since substitution of a closed term doesn't change it, we have:
        have h_subst_closed : ∀ t : Lambda, Lambda.IsClosed t → ∀ s x, Lambda.subst s x t = t := by
          intro t ht; exact ht
        convert Lambda.reduces.refl _ using 1;
        congr;
        exact Eq.symm ( h_subst_closed _ ( Lambda.church_closed _ ) _ _ );
      -- Applying the reduction step to the lambda term, we get the final result.
      have h_final : Lambda.reduces (Lambda.app (Lambda.lam (Lambda.var 0)) (Lambda.church m))
          (Lambda.church m) := by
        constructor;
        constructor;
        simp [Lambda.subst]; constructor
      exact Lambda.reduces_trans h_snd ( Lambda.reduces_trans h_beta h_final );
    exact Lambda.reduces_trans (Lambda.reduces_app_right (Lambda.pair_reduces _ _)) h_snd_pair_res

/-
Check if `Lambda.reduces_trans`, `Lambda.fst_pair_church`, and `Lambda.pair_res_church` are
available.
-/

/-
`pred_step` applied to `pair n m` reduces to `pair m (m+1)`.
-/
theorem Lambda.pred_step_reduces (n m : ℕ) :
  Lambda.reduces (Lambda.app Lambda.pred_step (Lambda.app (Lambda.app Lambda.pair (Lambda.church n))
      (Lambda.church m)))
                 (Lambda.app (Lambda.app Lambda.pair (Lambda.church m)) (Lambda.church (m + 1))) :=
                     by
  have h_pred_step_def :
      Lambda.reduces
        (Lambda.app Lambda.pred_step (Lambda.app (Lambda.app Lambda.pair (Lambda.church n))
            (Lambda.church m)))
        (Lambda.app
          (Lambda.app Lambda.pair (Lambda.app Lambda.snd (Lambda.app (Lambda.app Lambda.pair
              (Lambda.church n)) (Lambda.church m))))
          (Lambda.app Lambda.succ (Lambda.app Lambda.snd (Lambda.app (Lambda.app Lambda.pair
              (Lambda.church n)) (Lambda.church m))))) := by
    constructor
    constructor
    constructor
  have h_snd : Lambda.reduces (Lambda.app Lambda.snd (Lambda.app (Lambda.app Lambda.pair
      (Lambda.church n)) (Lambda.church m))) (Lambda.church m) := by
    apply Lambda.snd_pair_church
  have h_succ : Lambda.reduces (Lambda.app Lambda.succ (Lambda.church m)) (Lambda.church (m + 1)) :=
      by
    apply Lambda.succ_works
  have h_pair :
      Lambda.reduces
        (Lambda.app
          (Lambda.app Lambda.pair (Lambda.app Lambda.snd (Lambda.app (Lambda.app Lambda.pair
              (Lambda.church n)) (Lambda.church m))))
          (Lambda.app Lambda.succ (Lambda.app Lambda.snd (Lambda.app (Lambda.app Lambda.pair
              (Lambda.church n)) (Lambda.church m)))))
        (Lambda.app (Lambda.app Lambda.pair (Lambda.church m)) (Lambda.app Lambda.succ
            (Lambda.church m))) := by
    exact
      Lambda.reduces_trans
        (Lambda.reduces_app_left (Lambda.reduces_app_right h_snd))
        (Lambda.reduces_app_right (Lambda.reduces_app_right h_snd))
  have h_final :
      Lambda.reduces (Lambda.app (Lambda.app Lambda.pair (Lambda.church m)) (Lambda.app Lambda.succ
          (Lambda.church m)))
        (Lambda.app (Lambda.app Lambda.pair (Lambda.church m)) (Lambda.church (m + 1))) := by
    exact Lambda.reduces_app_right h_succ
  exact Lambda.reduces_trans h_pred_step_def (Lambda.reduces_trans h_pair h_final)

/-
Check availability of definitions and lemmas.
-/

/-
Iterating `pred_step` `n` times on `pred_init` reduces to `pair (n-1) n`.
-/
theorem Lambda.iterate_pred_step (n : ℕ) :
    Lambda.reduces (Lambda.iterate Lambda.pred_step Lambda.pred_init n)
        (Lambda.app (Lambda.app Lambda.pair (Lambda.church (n - 1))) (Lambda.church n)) := by
  induction n with
  | zero =>
      simp [Lambda.iterate, Lambda.pred_init]
      constructor
  | succ n ih =>
      have h_step :
          Lambda.reduces
            (Lambda.app Lambda.pred_step (Lambda.app (Lambda.app Lambda.pair (Lambda.church (n -
                1))) (Lambda.church n)))
            (Lambda.app (Lambda.app Lambda.pair (Lambda.church n)) (Lambda.church (n + 1))) := by
        convert Lambda.pred_step_reduces (n - 1) n using 1
      simpa [Lambda.iterate_succ] using
        (Lambda.reduces_trans (Lambda.reduces_app_right ih) h_step)

/-
`pred (church n)` reduces to `church (n-1)`.
-/
theorem Lambda.pred_works (n : ℕ) :
    Lambda.reduces (Lambda.app Lambda.pred (Lambda.church n)) (Lambda.church (n - 1)) := by
  have h_def : Lambda.reduces (Lambda.app Lambda.pred (Lambda.church n))
      (Lambda.app Lambda.fst (Lambda.iterate Lambda.pred_step Lambda.pred_init n)) := by
    have h_def : Lambda.reduces (Lambda.app Lambda.pred (Lambda.church n)) (Lambda.app Lambda.fst
        (Lambda.app (Lambda.app (Lambda.church n) Lambda.pred_step) Lambda.pred_init)) := by
      have h_def : Lambda.pred = Lambda.lam (Lambda.app Lambda.fst (Lambda.app (Lambda.app
          (Lambda.var 0) Lambda.pred_step) Lambda.pred_init)) := rfl
      rw [h_def];
      constructor;
      constructor;
      simp [Lambda.subst, Lambda.fst, Lambda.pred_step, Lambda.pred_init, Lambda.pair, Lambda.succ,
          Lambda.snd, Lambda.church]; constructor
    have h_def : Lambda.reduces
        (Lambda.app (Lambda.app (Lambda.church n) Lambda.pred_step) Lambda.pred_init)
        (Lambda.iterate Lambda.pred_step Lambda.pred_init n) := by
      apply_rules [ Lambda.church_reduces_iterate ];
    have h_trans : ∀ {t1 t2 t3 : Lambda}, Lambda.reduces t1 t2 → Lambda.reduces t2 t3 →
        Lambda.reduces t1 t3 := by
      intros t1 t2 t3 h1 h2; exact Lambda.reduces_trans h1 h2
    exact h_trans ‹_› (Lambda.reduces_app_right h_def)
  -- By definition of `fst`, we know that `fst (pair (church (n - 1)) (church n))` reduces to
  -- `church (n - 1)`.
  have h_fst : Lambda.reduces (Lambda.app Lambda.fst (Lambda.app (Lambda.app Lambda.pair
      (Lambda.church (n - 1))) (Lambda.church n))) (Lambda.church (n - 1)) := by
    apply_rules [ Lambda.fst_pair_church ];
  have h_iter : Lambda.reduces (Lambda.iterate Lambda.pred_step Lambda.pred_init n)
      (Lambda.app (Lambda.app Lambda.pair (Lambda.church (n - 1))) (Lambda.church n)) := by
    convert Lambda.iterate_pred_step n using 1;
  have h_trans : Lambda.reduces (Lambda.app Lambda.fst (Lambda.iterate Lambda.pred_step
      Lambda.pred_init n)) (Lambda.app Lambda.fst (Lambda.app (Lambda.app Lambda.pair (Lambda.church
      (n - 1))) (Lambda.church n))) := by
    exact Lambda.reduces_app_right h_iter
  exact Lambda.reduces_trans h_def ( Lambda.reduces_trans h_trans h_fst )

/-
`pred` is a closed term.
-/
theorem Lambda.pred_closed : Lambda.IsClosed Lambda.pred := by
  unfold Lambda.pred Lambda.fst Lambda.snd Lambda.pair Lambda.succ; intros s x; aesop;

/-
Iterating `pred` `m` times on `church n` yields `church (n-m)`.
-/
theorem Lambda.iterate_pred_works (n m : ℕ) :
    Lambda.reduces (Lambda.iterate Lambda.pred (Lambda.church n) m) (Lambda.church (n - m)) := by
  induction m generalizing n with
  | zero =>
      simp [Lambda.iterate]
      constructor
  | succ m ih =>
      have h_ind :
          Lambda.reduces (Lambda.iterate Lambda.pred (Lambda.church n) m) (Lambda.church (n - m)) :=
              by
        exact ih n
      have h_pred : Lambda.reduces (Lambda.app Lambda.pred (Lambda.church (n - m)))
          (Lambda.church ((n - m) - 1)) := by
        exact Lambda.pred_works (n - m)
      have h_eq : n - m - 1 = n - (m + 1) := by omega
      simpa [Lambda.iterate_succ, h_eq] using
        (Lambda.reduces_trans (Lambda.reduces_app_right h_ind) h_pred)

/-
`sub (church n) (church m)` reduces to `church (n - m)`.
-/
theorem Lambda.sub_works (n m : ℕ) :
    Lambda.reduces (Lambda.app (Lambda.app Lambda.sub (Lambda.church n)) (Lambda.church m))
        (Lambda.church (n - m)) := by
  have h_pred_subst1 : Lambda.subst (Lambda.church n) 1 Lambda.pred = Lambda.pred := by
    exact Lambda.pred_closed _ _
  have h_def1 :
      Lambda.reduces (Lambda.app Lambda.sub (Lambda.church n))
        (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 0) Lambda.pred) (Lambda.church n))) := by
    unfold Lambda.sub
    refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
    convert Lambda.reduces.refl _ using 1
    simp [Lambda.subst, Lambda.lift_church, h_pred_subst1]
  have h_pred_subst0 : Lambda.subst (Lambda.church m) 0 Lambda.pred = Lambda.pred := by
    exact Lambda.pred_closed _ _
  have h_def2 :
      Lambda.reduces
        (Lambda.app (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 0) Lambda.pred) (Lambda.church
            n))) (Lambda.church m))
        (Lambda.app (Lambda.app (Lambda.church m) Lambda.pred) (Lambda.church n)) := by
    refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
    convert Lambda.reduces.refl _ using 1
    simp [Lambda.subst, Lambda.subst_church_aux, h_pred_subst0]
  have h_iter :
      Lambda.reduces (Lambda.app (Lambda.app (Lambda.church m) Lambda.pred) (Lambda.church n))
        (Lambda.iterate (Lambda.subst (Lambda.church n) 0 Lambda.pred) (Lambda.church n) m) := by
    exact Lambda.church_reduces_iterate m Lambda.pred (Lambda.church n)
  have h_pred_subst : Lambda.subst (Lambda.church n) 0 Lambda.pred = Lambda.pred := by
    exact Lambda.pred_closed _ _
  have h_iter' :
      Lambda.reduces
          (Lambda.iterate (Lambda.subst (Lambda.church n) 0 Lambda.pred) (Lambda.church n) m)
        (Lambda.iterate Lambda.pred (Lambda.church n) m) := by
    simpa [h_pred_subst] using
      (Lambda.reduces.refl (Lambda.iterate (Lambda.subst (Lambda.church n) 0 Lambda.pred)
          (Lambda.church n) m))
  exact
    Lambda.reduces_trans (Lambda.reduces_app_left h_def1)
      (Lambda.reduces_trans h_def2
        (Lambda.reduces_trans h_iter
          (Lambda.reduces_trans h_iter' (Lambda.iterate_pred_works n m))))

/-
Check status of remaining theorems.
-/

/-
`false x y` reduces to `y`.
-/
theorem Lambda.false_works (x y : Lambda) :
    Lambda.reduces (Lambda.app (Lambda.app Lambda.false x) y) y := by
  -- By definition of `false`, we have `false = \f x. x`.
  have h_false : Lambda.false = Lambda.lam (Lambda.lam (Lambda.var 0)) := by
    rfl;
  -- By definition of `beta`, we have `Lambda.app (Lambda.app (Lambda.lam (Lambda.lam (Lambda.var
  -- 0))) x) y` reduces to `Lambda.app (Lambda.lam (Lambda.var 0)) y`.
  have h_beta : Lambda.reduces
      (Lambda.app (Lambda.app (Lambda.lam (Lambda.lam (Lambda.var 0))) x) y)
      (Lambda.app (Lambda.lam (Lambda.var 0)) y) := by
    exact .step _ _ _ ( by tauto ) ( .refl _ );
  -- Rewriting with the definition of `false`, the claim is the composite of the two beta steps.
  rw [h_false]
  exact Lambda.reduces_trans h_beta (.step _ _ _ (.beta _ _) (.refl _))

/-
`true x y` reduces to `x` for closed `x`.
-/
theorem Lambda.true_works (x y : Lambda) :
    Lambda.reduces (Lambda.app (Lambda.app Lambda.true x) y) x := by
  refine Lambda.reduces.step _ _ _ (.app_left _ _ _ (.beta _ _)) ?_
  refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
  simp only [Lambda.subst, ↓reduceIte]
  rw [Lambda.subst_lift x y 0]
  exact Lambda.reduces.refl x

/-
`ifThenElse true a b` reduces to `a` for closed `a`.
-/
theorem Lambda.ifThenElse_true (a b : Lambda) :
    Lambda.reduces (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse Lambda.true) a) b) a := by
  have h_true : Lambda.reduces (Lambda.app (Lambda.app Lambda.true a) b) a := by
    exact Lambda.true_works a b
  have h_ifThenElse_true : Lambda.reduces (Lambda.app Lambda.ifThenElse Lambda.true) Lambda.true :=
      by
    constructor
    all_goals constructor
    constructor
    constructor
    constructor
    constructor
    constructor
    constructor
    constructor
    constructor
    constructor
  have h_ifThenElse_step1 :
      Lambda.reduces (Lambda.app (Lambda.app Lambda.ifThenElse Lambda.true) a)
          (Lambda.app Lambda.true a) := by
    exact Lambda.reduces_app_left h_ifThenElse_true
  have h_ifThenElse_step2 :
      Lambda.reduces (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse Lambda.true) a) b)
          (Lambda.app (Lambda.app Lambda.true a) b) := by
    exact Lambda.reduces_app_left h_ifThenElse_step1
  exact Lambda.reduces_trans h_ifThenElse_step2 h_true

/-
`ifThenElse false a b` reduces to `b`.
-/
theorem Lambda.ifThenElse_false (a b : Lambda) :
    Lambda.reduces (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse Lambda.false) a) b) b := by
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  norm_num +zetaDelta at *;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor

/-
`not false` reduces to `true`.
-/
theorem Lambda.not_false : Lambda.reduces (Lambda.app Lambda.not Lambda.false) Lambda.true := by
  unfold Lambda.not Lambda.false; constructor;
  all_goals norm_num [church];
  constructor;
  -- After substituting, the term simplifies to `(\a b. b)`, which is the definition of `false`.
  simp [Lambda.subst];
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor

/-
`and true true` reduces to `true`.
-/
theorem Lambda.and_true_true :
    Lambda.reduces (Lambda.app (Lambda.app Lambda.and Lambda.true) Lambda.true) Lambda.true := by
  -- By definition of `and`, we have `and true true` simplifies to `true`.
  simp [and];
  -- By definition of `True`, we have `True = K`.
  have h_true : Lambda.true = Lambda.K := by
    rfl;
  -- By definition of `K`, we have `K x y = x`.
  simp [h_true, Lambda.K];
  repeat constructor;

/-
`and true false` reduces to `false`.
-/
theorem Lambda.and_true_false :
    Lambda.reduces (Lambda.app (Lambda.app Lambda.and Lambda.true) Lambda.false) Lambda.false := by
  -- By definition of `and`, we have `and true false = true false false`.
  simp [Lambda.and];
  -- By definition of `Lambda.false`, we have `Lambda.false = \x y. y`.
  have h_false : Lambda.false = Lambda.lam (Lambda.lam (Lambda.var 0)) := by
    rfl;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor

/-
`and false true` reduces to `false`.
-/
theorem Lambda.and_false_true :
    Lambda.reduces (Lambda.app (Lambda.app Lambda.and Lambda.false) Lambda.true) Lambda.false := by
  repeat' constructor;

/-
`and false false` reduces to `false`.
-/
theorem Lambda.and_false_false :
    Lambda.reduces (Lambda.app (Lambda.app Lambda.and Lambda.false) Lambda.false) Lambda.false := by
  -- By definition of `and`, we have `and false false` reduces to `false`.
  have h_and_false_false : Lambda.reduces
      (Lambda.app (Lambda.app Lambda.and Lambda.false) Lambda.false)
      (Lambda.app (Lambda.app Lambda.false Lambda.false) Lambda.false) := by
    constructor;
    constructor;
    constructor;
    constructor;
    constructor;
    constructor
  generalize_proofs at *;
  -- By definition of `false`, we have `false false false` reduces to `false`.
  have h_false_false_false : Lambda.reduces
      (Lambda.app (Lambda.app Lambda.false Lambda.false) Lambda.false) Lambda.false := by
    exact Lambda.false_works Lambda.false Lambda.false
  exact Lambda.reduces_trans h_and_false_false h_false_false_false


/-
`leq` correctly computes the less-than-or-equal relation on Church numerals.
-/
theorem Lambda.leq_works (n m : ℕ) :
  Lambda.reduces (Lambda.app (Lambda.app Lambda.leq (Lambda.church n)) (Lambda.church m))
    (if n ≤ m then Lambda.true else Lambda.false) := by
  have h_isZero_closed : Lambda.IsClosed Lambda.isZero := by
    unfold Lambda.IsClosed
    aesop
  have h_sub_closed : Lambda.IsClosed Lambda.sub := by
    unfold Lambda.IsClosed
    aesop
  have h_isZero_subst1 : Lambda.subst (Lambda.church n) 1 Lambda.isZero = Lambda.isZero := by
    exact h_isZero_closed _ _
  have h_sub_subst1 : Lambda.subst (Lambda.church n) 1 Lambda.sub = Lambda.sub := by
    exact h_sub_closed _ _
  have h1 :
      Lambda.reduces (Lambda.app Lambda.leq (Lambda.church n))
        (Lambda.lam (Lambda.app Lambda.isZero (Lambda.app (Lambda.app Lambda.sub (Lambda.church n))
            (Lambda.var 0)))) := by
    unfold Lambda.leq
    refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
    convert Lambda.reduces.refl _ using 1
    simp [Lambda.subst, Lambda.lift_church, h_isZero_subst1, h_sub_subst1]
  have h_isZero_subst0 : Lambda.subst (Lambda.church m) 0 Lambda.isZero = Lambda.isZero := by
    exact h_isZero_closed _ _
  have h_sub_subst0 : Lambda.subst (Lambda.church m) 0 Lambda.sub = Lambda.sub := by
    exact h_sub_closed _ _
  have h_leq_def :
      Lambda.reduces (Lambda.app (Lambda.app Lambda.leq (Lambda.church n)) (Lambda.church m))
        (Lambda.app Lambda.isZero (Lambda.app (Lambda.app Lambda.sub (Lambda.church n))
            (Lambda.church m))) := by
    refine Lambda.reduces_trans (Lambda.reduces_app_left h1) ?_
    refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
    convert Lambda.reduces.refl _ using 1
    simp [Lambda.subst, Lambda.subst_church_aux, h_isZero_subst0, h_sub_subst0]
  have h_sub :
      Lambda.reduces (Lambda.app (Lambda.app Lambda.sub (Lambda.church n)) (Lambda.church m))
        (Lambda.church (n - m)) := by
    exact Lambda.sub_works n m
  have h_isZero_def :
      Lambda.reduces (Lambda.app Lambda.isZero (Lambda.church (n - m)))
        (if n - m = 0 then Lambda.true else Lambda.false) := by
    cases h : n - m with
    | zero =>
        simpa [h] using Lambda.isZero_zero
    | succ k =>
        simpa [h] using Lambda.isZero_succ k
  have h_isZero :
      Lambda.reduces (Lambda.app Lambda.isZero (Lambda.app (Lambda.app Lambda.sub (Lambda.church n))
          (Lambda.church m)))
        (if n - m = 0 then Lambda.true else Lambda.false) := by
    exact Lambda.reduces_trans (Lambda.reduces_app_right h_sub) h_isZero_def
  have h_final :
      Lambda.reduces (Lambda.app (Lambda.app Lambda.leq (Lambda.church n)) (Lambda.church m))
        (if n - m = 0 then Lambda.true else Lambda.false) := by
    exact Lambda.reduces_trans h_leq_def h_isZero
  simpa [Nat.sub_eq_zero_iff_le] using h_final

/-
Check the definition of Nat.pair to see if it matches Szudzik's pairing function.
-/

/-
Definition of logical OR in Lambda calculus.
-/
def Lambda.or : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 1) Lambda.true) (Lambda.var 0)))

/-
`or true true` reduces to `true`.
-/
theorem Lambda.or_true_true :
    Lambda.reduces (Lambda.app (Lambda.app Lambda.or Lambda.true) Lambda.true) Lambda.true := by
  -- Applying the definition of `or` to `true` and `true` gives `true`.
  have h_or_true_true : Lambda.reduces (Lambda.app (Lambda.app Lambda.or Lambda.true) Lambda.true)
      Lambda.true := by
    have h_def : Lambda.or = Lambda.lam
        (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 1) Lambda.true) (Lambda.var 0))) := by
      rfl
    rw [h_def]
    -- By definition of `true`, we have `true = Lambda.lam (Lambda.lam (Lambda.var 1))`.
    have h_true : Lambda.true = Lambda.lam (Lambda.lam (Lambda.var 1)) := by
      rfl
    rw [h_true];
    apply_rules [ Lambda.reduces_trans, Lambda.reduces.refl, Lambda.reduces.step ];
    all_goals repeat' constructor;
  exact h_or_true_true

/-
`or true false` reduces to `true`.
-/
theorem Lambda.or_true_false :
    Lambda.reduces (Lambda.app (Lambda.app Lambda.or Lambda.true) Lambda.false) Lambda.true := by
  have h_or_true_false : Lambda.reduces (Lambda.app (Lambda.app (Lambda.lam (Lambda.lam (Lambda.app
      (Lambda.app (Lambda.var 1) Lambda.true) (Lambda.var 0)))) Lambda.true) Lambda.false)
      (Lambda.app (Lambda.app Lambda.true Lambda.true) Lambda.false) := by
    constructor;
    constructor;
    constructor;
    constructor;
    constructor;
    constructor;
  have h_true_true : Lambda.reduces (Lambda.app (Lambda.app Lambda.true Lambda.true) Lambda.false)
      Lambda.true := by
    exact Lambda.true_works _ _
  exact Lambda.reduces_trans h_or_true_false h_true_true

/-
`or false true` reduces to `true`.
-/
theorem Lambda.or_false_true :
    Lambda.reduces (Lambda.app (Lambda.app Lambda.or Lambda.false) Lambda.true) Lambda.true := by
  constructor;
  all_goals constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor

/-
`or false false` reduces to `false`.
-/
theorem Lambda.or_false_false :
    Lambda.reduces (Lambda.app (Lambda.app Lambda.or Lambda.false) Lambda.false) Lambda.false := by
  repeat' constructor;

/-
Checking if definitions exist.
-/

/-
Alternative definition of `not` that avoids the substitution bug.
-/
def Lambda.not' : Lambda :=
  Lambda.lam (Lambda.app (Lambda.app (Lambda.var 0) Lambda.false) Lambda.true)

theorem Lambda.not'_true : Lambda.reduces (Lambda.app Lambda.not' Lambda.true) Lambda.false := by
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor

/-
`not' false` reduces to `true`.
-/
theorem Lambda.not'_false : Lambda.reduces (Lambda.app Lambda.not' Lambda.false) Lambda.true := by
  -- By definition of `not'`, we know that `not' false` reduces to `true`.
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor;
  constructor

/-
Checking if `Lambda.not'_true` is already defined.
-/

/-
Checking substitution behavior.
-/
-- #eval Lambda.subst (Lambda.var 0) 0 (Lambda.lam (Lambda.var 1))

/-
`not true` reduces to `false`.
-/
theorem Lambda.not_true_reduces_false :
    Lambda.reduces (Lambda.app Lambda.not Lambda.true) Lambda.false := by
  have h_top :
      Lambda.reduces (Lambda.app Lambda.not Lambda.true)
        (Lambda.lam (Lambda.lam (Lambda.app (Lambda.app Lambda.true (Lambda.var 0)) (Lambda.var
            1)))) := by
    unfold Lambda.not
    simpa [Lambda.subst, Lambda.true, Lambda.K] using
        (Lambda.beta_reduces : Lambda.reduces (Lambda.app Lambda.not Lambda.true) _)
  have h_inner1 : Lambda.reduces (Lambda.app Lambda.true (Lambda.var 0)) (Lambda.lam (Lambda.var 1))
      := by
    unfold Lambda.true Lambda.K
    simpa [Lambda.subst, Lambda.lift] using
      (Lambda.beta_reduces : Lambda.reduces (Lambda.app Lambda.true (Lambda.var 0)) _)
  have h_inner2 :
      Lambda.reduces (Lambda.app (Lambda.app Lambda.true (Lambda.var 0)) (Lambda.var 1))
        (Lambda.app (Lambda.lam (Lambda.var 1)) (Lambda.var 1)) := by
    exact Lambda.reduces_app_left h_inner1
  have h_inner3 : Lambda.reduces (Lambda.app (Lambda.lam (Lambda.var 1)) (Lambda.var 1))
      (Lambda.var 0) := by
    simpa [Lambda.subst, Lambda.lift] using
      (Lambda.beta_reduces : Lambda.reduces (Lambda.app (Lambda.lam (Lambda.var 1)) (Lambda.var 1))
          _)
  have h_inner :
      Lambda.reduces (Lambda.app (Lambda.app Lambda.true (Lambda.var 0)) (Lambda.var 1))
          (Lambda.var 0) := by
    exact Lambda.reduces_trans h_inner2 h_inner3
  have h_lam :
      Lambda.reduces
        (Lambda.lam (Lambda.lam (Lambda.app (Lambda.app Lambda.true (Lambda.var 0)) (Lambda.var
            1))))
        (Lambda.lam (Lambda.lam (Lambda.var 0))) := by
    exact Lambda.reduces_lam (Lambda.reduces_lam h_inner)
  simpa [Lambda.false, Lambda.church] using Lambda.reduces_trans h_top h_lam

/-
Checking if `and` theorems are already declared.
-/

/-
Alternative definition of `lt` using `not'`.
-/
def Lambda.lt' : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.app Lambda.not' (Lambda.app (Lambda.app Lambda.leq (Lambda.var 0))
      (Lambda.var 1))))

/-
`lt'` correctly computes the less-than relation.
-/
theorem Lambda.lt'_works (n m : ℕ) :
  Lambda.reduces (Lambda.app (Lambda.app Lambda.lt' (Lambda.church n)) (Lambda.church m))
    (if n < m then Lambda.true else Lambda.false) := by
  have h_not_closed : Lambda.IsClosed Lambda.not' := by
    unfold Lambda.IsClosed
    aesop
  have h_leq_closed : Lambda.IsClosed Lambda.leq := by
    unfold Lambda.IsClosed
    aesop
  have h_not_subst1 : Lambda.subst (Lambda.church n) 1 Lambda.not' = Lambda.not' := by
    exact h_not_closed _ _
  have h_leq_subst1 : Lambda.subst (Lambda.church n) 1 Lambda.leq = Lambda.leq := by
    exact h_leq_closed _ _
  have h1 :
      Lambda.reduces (Lambda.app Lambda.lt' (Lambda.church n))
        (Lambda.lam (Lambda.app Lambda.not' (Lambda.app (Lambda.app Lambda.leq (Lambda.var 0))
            (Lambda.church n)))) := by
    unfold Lambda.lt'
    refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
    convert Lambda.reduces.refl _ using 1
    simp [Lambda.subst, Lambda.lift_church, h_not_subst1, h_leq_subst1]
  have h_not_subst0 : Lambda.subst (Lambda.church m) 0 Lambda.not' = Lambda.not' := by
    exact h_not_closed _ _
  have h_leq_subst0 : Lambda.subst (Lambda.church m) 0 Lambda.leq = Lambda.leq := by
    exact h_leq_closed _ _
  have h_lt_def :
      Lambda.reduces (Lambda.app (Lambda.app Lambda.lt' (Lambda.church n)) (Lambda.church m))
        (Lambda.app Lambda.not' (Lambda.app (Lambda.app Lambda.leq (Lambda.church m)) (Lambda.church
            n))) := by
    refine Lambda.reduces_trans (Lambda.reduces_app_left h1) ?_
    refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
    convert Lambda.reduces.refl _ using 1
    simp [Lambda.subst, Lambda.subst_church_aux, h_not_subst0, h_leq_subst0]
  have h_leq : Lambda.reduces
      (Lambda.app (Lambda.app Lambda.leq (Lambda.church m)) (Lambda.church n))
      (if m ≤ n then Lambda.true else Lambda.false) := by
    exact Lambda.leq_works m n
  have h_not : Lambda.reduces (Lambda.app Lambda.not' Lambda.true) Lambda.false ∧ Lambda.reduces
      (Lambda.app Lambda.not' Lambda.false) Lambda.true := by
    exact ⟨Lambda.not'_true, Lambda.not'_false⟩
  have h_trans :
      Lambda.reduces (Lambda.app Lambda.not' (Lambda.app (Lambda.app Lambda.leq (Lambda.church m))
          (Lambda.church n)))
        (Lambda.app Lambda.not' (if m ≤ n then Lambda.true else Lambda.false)) := by
    exact Lambda.reduces_app_right h_leq
  by_cases hmn : m ≤ n
  · have h_false :
        Lambda.reduces (Lambda.app (Lambda.app Lambda.lt' (Lambda.church n)) (Lambda.church m))
            Lambda.false := by
      have h_not_false :
          Lambda.reduces (Lambda.app Lambda.not' (if m ≤ n then Lambda.true else Lambda.false))
              Lambda.false := by
        simpa [hmn] using h_not.1
      exact Lambda.reduces_trans h_lt_def (Lambda.reduces_trans h_trans h_not_false)
    simpa [hmn, not_lt_of_ge hmn] using h_false
  · have h_true :
        Lambda.reduces (Lambda.app (Lambda.app Lambda.lt' (Lambda.church n)) (Lambda.church m))
            Lambda.true := by
      have h_not_true :
          Lambda.reduces (Lambda.app Lambda.not' (if m ≤ n then Lambda.true else Lambda.false))
              Lambda.true := by
        simpa [hmn] using h_not.2
      exact Lambda.reduces_trans h_lt_def (Lambda.reduces_trans h_trans h_not_true)
    have hlt : n < m := Nat.lt_of_not_ge hmn
    simpa [hmn, hlt] using h_true

/-
Alternative definition of `natPair` using `lt'`.
-/
def Lambda.natPair' : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app
      (Lambda.app Lambda.lt' (Lambda.var 1)) (Lambda.var 0))) (Lambda.app (Lambda.app Lambda.add
      (Lambda.app (Lambda.app Lambda.mult (Lambda.var 0)) (Lambda.var 0))) (Lambda.var 1)))
      (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app
      Lambda.mult (Lambda.var 1)) (Lambda.var 1))) (Lambda.var 1))) (Lambda.var 0))))

/-
Checking if add_works and mult_works are available.
-/

/-
`natPair' n m` reduces to the if-then-else expression.
-/
theorem Lambda.natPair'_reduces_if (n m : ℕ) :
  Lambda.reduces (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n)) (Lambda.church m))
    (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app (Lambda.app Lambda.lt'
        (Lambda.church n)) (Lambda.church m)))
      (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app Lambda.mult (Lambda.church m))
          (Lambda.church m))) (Lambda.church n)))
      (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app
          Lambda.mult (Lambda.church n)) (Lambda.church n))) (Lambda.church n))) (Lambda.church m)))
          := by
  have h_lt_closed : Lambda.IsClosed Lambda.lt' := by
    unfold Lambda.IsClosed
    aesop
  have h_add_closed : Lambda.IsClosed Lambda.add := by
    unfold Lambda.IsClosed
    aesop
  have h_mult_closed : Lambda.IsClosed Lambda.mult := by
    unfold Lambda.IsClosed
    aesop
  have h_ifThenElse_closed : Lambda.IsClosed Lambda.ifThenElse := by
    unfold Lambda.IsClosed
    aesop
  have h_ifThenElse_subst1 : Lambda.subst (Lambda.church n) 1 Lambda.ifThenElse = Lambda.ifThenElse
      := by
    exact h_ifThenElse_closed _ _
  have h_lt_subst1 : Lambda.subst (Lambda.church n) 1 Lambda.lt' = Lambda.lt' := by
    exact h_lt_closed _ _
  have h_add_subst1 : Lambda.subst (Lambda.church n) 1 Lambda.add = Lambda.add := by
    exact h_add_closed _ _
  have h_mult_subst1 : Lambda.subst (Lambda.church n) 1 Lambda.mult = Lambda.mult := by
    exact h_mult_closed _ _
  have h1 :
      Lambda.reduces (Lambda.app Lambda.natPair' (Lambda.church n))
        (Lambda.lam
          (Lambda.app
            (Lambda.app
              (Lambda.app Lambda.ifThenElse (Lambda.app (Lambda.app Lambda.lt' (Lambda.church n))
                  (Lambda.var 0)))
              (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app Lambda.mult (Lambda.var 0))
                  (Lambda.var 0))) (Lambda.church n)))
            (Lambda.app
              (Lambda.app Lambda.add
                (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app Lambda.mult
                    (Lambda.church n)) (Lambda.church n))) (Lambda.church n)))
              (Lambda.var 0)))) := by
    unfold Lambda.natPair'
    refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
    convert Lambda.reduces.refl _ using 1
    simp [Lambda.subst, Lambda.lift_church, h_ifThenElse_subst1, h_lt_subst1, h_add_subst1,
        h_mult_subst1]
  have h_ifThenElse_subst0 : Lambda.subst (Lambda.church m) 0 Lambda.ifThenElse = Lambda.ifThenElse
      := by
    exact h_ifThenElse_closed _ _
  have h_lt_subst0 : Lambda.subst (Lambda.church m) 0 Lambda.lt' = Lambda.lt' := by
    exact h_lt_closed _ _
  have h_add_subst0 : Lambda.subst (Lambda.church m) 0 Lambda.add = Lambda.add := by
    exact h_add_closed _ _
  have h_mult_subst0 : Lambda.subst (Lambda.church m) 0 Lambda.mult = Lambda.mult := by
    exact h_mult_closed _ _
  refine Lambda.reduces_trans (Lambda.reduces_app_left h1) ?_
  refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
  convert Lambda.reduces.refl _ using 1
  simp [Lambda.subst, Lambda.subst_church_aux, h_ifThenElse_subst0, h_lt_subst0, h_add_subst0,
      h_mult_subst0]

/-
Helper lemma for the first branch of `natPair'`.
-/
theorem Lambda.natPair'_branch1 (n m : ℕ) :
  Lambda.reduces (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app Lambda.mult
      (Lambda.church m)) (Lambda.church m))) (Lambda.church n)) (Lambda.church (m * m + n)) := by
    -- Apply the transitivity of reduction.
    exact Lambda.reduces_trans
      (Lambda.reduces_app_left (Lambda.reduces_app_right (Lambda.mult_works m m)))
      (Lambda.add_works (m * m) n)

/-
Helper lemma for the second branch of `natPair'`.
-/
theorem Lambda.natPair'_branch2 (n m : ℕ) :
  Lambda.reduces (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app Lambda.add (Lambda.app
      (Lambda.app Lambda.mult (Lambda.church n)) (Lambda.church n))) (Lambda.church n)))
      (Lambda.church m)) (Lambda.church (n * n + n + m)) := by
  have h_mult_add :
      Lambda.reduces
        (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app Lambda.mult (Lambda.church n))
            (Lambda.church n))) (Lambda.church n))
        (Lambda.church (n * n + n)) := by
    exact Lambda.reduces_trans
        (Lambda.reduces_app_left (Lambda.reduces_app_right (Lambda.mult_works n n)))
        (Lambda.add_works (n * n) n)
  have h_add :
      Lambda.reduces
          (Lambda.app (Lambda.app Lambda.add (Lambda.church (n * n + n))) (Lambda.church m))
        (Lambda.church ((n * n + n) + m)) := by
    exact Lambda.add_works (n * n + n) m
  have h_trans :
      Lambda.reduces
        (Lambda.app
          (Lambda.app Lambda.add
            (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app Lambda.mult (Lambda.church
                n)) (Lambda.church n))) (Lambda.church n)))
          (Lambda.church m))
        (Lambda.app (Lambda.app Lambda.add (Lambda.church (n * n + n))) (Lambda.church m)) := by
    exact Lambda.reduces_app_left (Lambda.reduces_app_right h_mult_add)
  exact Lambda.reduces_trans h_trans h_add

/-
Checking availability of congruence lemmas.
-/
-- #check Lambda.reduces_app_left
-- #check Lambda.reduces_app_right

/-
`Lambda.natPair'` correctly computes the pairing function on Church numerals.
-/
theorem Lambda.natPair'_works (n m : ℕ) :
  Lambda.reduces (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n)) (Lambda.church m))
      (Lambda.church (Nat.pair n m)) := by
    -- Use `Lambda.natPair'_reduces_if` to reduce the term to the `ifThenElse` expression.
    have h1 : Lambda.reduces
        (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n)) (Lambda.church m))
              (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app (Lambda.app
                  Lambda.lt' (Lambda.church n)) (Lambda.church m)))
                (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app Lambda.mult
                    (Lambda.church m)) (Lambda.church m))) (Lambda.church n)))
                (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app Lambda.add (Lambda.app
                    (Lambda.app Lambda.mult (Lambda.church n)) (Lambda.church n))) (Lambda.church
                    n))) (Lambda.church m))) := by
                  exact Lambda.natPair'_reduces_if n m;
    have h2 : Lambda.reduces
        (Lambda.app (Lambda.app Lambda.lt' (Lambda.church n)) (Lambda.church m))
        (if n < m then Lambda.true else Lambda.false) := by
      exact Lambda.lt'_works n m;
    have h3 : Lambda.reduces (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (if n < m then
        Lambda.true else Lambda.false)) (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app
        Lambda.mult (Lambda.church m)) (Lambda.church m))) (Lambda.church n))) (Lambda.app
        (Lambda.app Lambda.add (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app
        Lambda.mult (Lambda.church n)) (Lambda.church n))) (Lambda.church n))) (Lambda.church m)))
        (if n < m then Lambda.church (m * m + n) else Lambda.church (n * n + n + m)) := by
      split_ifs
      · simp_all +decide only [↓reduceIte]
        convert Lambda.reduces_trans (Lambda.ifThenElse_true _ _) (Lambda.natPair'_branch1 _ _)
          using 1
      · simp_all +decide only [↓reduceIte, not_lt]
        convert Lambda.reduces_trans _ (Lambda.natPair'_branch2 n m) using 1
        convert Lambda.ifThenElse_false _ _ using 1
    have h4 : Lambda.reduces (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app
        (Lambda.app Lambda.lt' (Lambda.church n)) (Lambda.church m)))
                  (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app Lambda.mult
                      (Lambda.church m)) (Lambda.church m))) (Lambda.church n)))
                  (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app Lambda.add (Lambda.app
                      (Lambda.app Lambda.mult (Lambda.church n)) (Lambda.church n))) (Lambda.church
                      n))) (Lambda.church m)))
                  (if n < m then Lambda.church (m * m + n) else Lambda.church (n * n + n + m)) := by
                    have h4 : Lambda.reduces (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
                        (Lambda.app (Lambda.app Lambda.lt' (Lambda.church n)) (Lambda.church m)))
                                  (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app
                                      Lambda.mult (Lambda.church m)) (Lambda.church m)))
                                      (Lambda.church n)))
                                  (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app
                                      Lambda.add (Lambda.app (Lambda.app Lambda.mult (Lambda.church
                                      n)) (Lambda.church n))) (Lambda.church n))) (Lambda.church
                                      m)))
                                (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (if n < m then
                                    Lambda.true else Lambda.false))
                                  (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app
                                      Lambda.mult (Lambda.church m)) (Lambda.church m)))
                                      (Lambda.church n)))
                                  (Lambda.app (Lambda.app Lambda.add (Lambda.app (Lambda.app
                                      Lambda.add (Lambda.app (Lambda.app Lambda.mult (Lambda.church
                                      n)) (Lambda.church n))) (Lambda.church n))) (Lambda.church
                                      m))) := by
                                    apply_rules
                                        [ Lambda.reduces_app_left, Lambda.reduces_app_right ];
                    exact Lambda.reduces_trans h4 h3;
    -- By transitivity of reduction, we can conclude that the original term reduces to the church
    -- numeral of the pairing function's result.
    have h_final : Lambda.reduces
        (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n)) (Lambda.church m))
        (if n < m then Lambda.church (m * m + n) else Lambda.church (n * n + n + m)) := by
      exact Lambda.reduces_trans h1 h4;
    unfold Nat.pair; aesop;

/-
Case `n < m` for `natPair'`.
-/
theorem Lambda.natPair'_case_lt (n m : ℕ) (h : n < m) :
    Lambda.reduces (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n)) (Lambda.church m))
      (Lambda.church (m * m + n)) := by
    -- `natPair'` computes `Nat.pair`, which in the case `n < m` is `m * m + n`.
    have hpair : Nat.pair n m = m * m + n := by
      unfold Nat.pair; simp [h]
    have := Lambda.natPair'_works n m
    rwa [hpair] at this

/-
Case `n >= m` for `natPair'`.
-/
theorem Lambda.natPair'_case_ge (n m : ℕ) (h : ¬ n < m) :
    Lambda.reduces (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n)) (Lambda.church m))
      (Lambda.church (n * n + n + m)) := by
    -- `natPair'` computes `Nat.pair`, which in the case `m ≤ n` is `n * n + n + m`.
    have hpair : Nat.pair n m = n * n + n + m := by
      unfold Nat.pair; simp [h]
    have := Lambda.natPair'_works n m
    rwa [hpair] at this

end
