/-
A fixed-point combinator based recursion scheme and the lambda term computing
integer square roots.

Extracted from `Start/Basic.lean` as part of the modular split.
-/

import Start.Combinators


set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Definition of integer square root in Lambda calculus.
-/
def Lambda.sqrt_iter : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam (
    Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
      (Lambda.app (Lambda.app Lambda.lt (Lambda.app (Lambda.app Lambda.mult (Lambda.app Lambda.succ
          (Lambda.var 0))) (Lambda.app Lambda.succ (Lambda.var 0)))) (Lambda.var 1)))
      (Lambda.var 0))
      (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.var 1)) (Lambda.app Lambda.succ (Lambda.var
          0)))
  )))

def Lambda.sqrt : Lambda :=
  Lambda.lam (Lambda.app (Lambda.app (Lambda.app Lambda.fix Lambda.sqrt_iter) (Lambda.var 0))
      (Lambda.church 0))


/-
Corrected definition of sqrt_iter and sqrt using lt' instead of lt.
-/
def Lambda.sqrt_iter' : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam (
    Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
      (Lambda.app (Lambda.app Lambda.lt' (Lambda.app (Lambda.app Lambda.mult (Lambda.app Lambda.succ
          (Lambda.var 0))) (Lambda.app Lambda.succ (Lambda.var 0)))) (Lambda.var 1)))
      (Lambda.var 0))
      (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.var 1)) (Lambda.app Lambda.succ (Lambda.var
          0)))
  )))

def Lambda.sqrt' : Lambda :=
  Lambda.lam (Lambda.app (Lambda.app (Lambda.app Lambda.fix Lambda.sqrt_iter') (Lambda.var 0))
      (Lambda.church 0))

/-
Corrected definition of sqrt_iter and sqrt with the correct condition logic (n < (k+1)^2).
-/
def Lambda.sqrt_iter_correct : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam (
    Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
      (Lambda.app (Lambda.app Lambda.lt' (Lambda.var 1)) (Lambda.app (Lambda.app Lambda.mult
          (Lambda.app Lambda.succ (Lambda.var 0))) (Lambda.app Lambda.succ (Lambda.var 0)))))
      (Lambda.var 0))
      (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.var 1)) (Lambda.app Lambda.succ (Lambda.var
          0)))
  )))

def Lambda.sqrt_correct : Lambda :=
  Lambda.lam (Lambda.app (Lambda.app (Lambda.app Lambda.fix Lambda.sqrt_iter_correct) (Lambda.var
      0)) (Lambda.church 0))

/-
Corrected definition of sqrt_iter and sqrt using lt' and correct argument order for the condition n
< (k+1)^2.
-/
def Lambda.sqrt_iter_v2 : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam (
    Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
      (Lambda.app (Lambda.app Lambda.lt' (Lambda.var 1)) (Lambda.app (Lambda.app Lambda.mult
          (Lambda.app Lambda.succ (Lambda.var 0))) (Lambda.app Lambda.succ (Lambda.var 0)))))
      (Lambda.var 0))
      (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.var 1)) (Lambda.app Lambda.succ (Lambda.var
          0)))
  )))

def Lambda.sqrt_v2 : Lambda :=
  Lambda.lam (Lambda.app (Lambda.app (Lambda.app Lambda.fix Lambda.sqrt_iter_v2) (Lambda.var 0))
      (Lambda.church 0))

/-
Define W f = \x. f (x x) and prove fix f reduces to W f (W f).
-/
def Lambda.W (f : Lambda) : Lambda :=
  Lambda.lam (Lambda.app f (Lambda.app (Lambda.var 0) (Lambda.var 0)))

theorem Lambda.fix_reduces_W (f : Lambda) :
  Lambda.IsClosed f →
  Lambda.reduces (Lambda.app Lambda.fix f) (Lambda.app (Lambda.W f) (Lambda.W f)) := by
  intro hf
  refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
  convert Lambda.reduces.refl (Lambda.app (Lambda.W f) (Lambda.W f)) using 1
  simp [Lambda.W, Lambda.subst, Lambda.lift_closed hf 1 0]

/-
W f (W f) reduces to (subst (W f) 0 f) (W f (W f)).
Recall W f = \x. f (x x).
So (W f) (W f) -> (\x. f (x x)) (W f) -> (f (x x))[x := W f]
= f[x := W f] (W f (W f)) (assuming x is 0 in f, and we need to be careful about indices).
Actually, W f = lam (app f (app (var 0) (var 0))).
So (W f) (W f) reduces to (app f (app (var 0) (var 0))) [0 := W f].
= app (subst (W f) 0 f) (app (subst (W f) 0 (var 0)) (subst (W f) 0 (var 0)))
= app (subst (W f) 0 f) (app (W f) (W f)).
This seems correct.
-/
theorem Lambda.W_reduces (f : Lambda) :
  Lambda.reduces (Lambda.app (Lambda.W f) (Lambda.W f))
      (Lambda.app (Lambda.subst (Lambda.W f) 0 f) (Lambda.app (Lambda.W f) (Lambda.W f))) := by
  refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
  simpa [Lambda.W, Lambda.subst] using
    (Lambda.reduces.refl (Lambda.app (Lambda.subst (Lambda.W f) 0 f) (Lambda.app (Lambda.W f)
        (Lambda.W f))))

/-
Property of the Y combinator: fix f reduces to some x, and x reduces to f x, assuming f is
well-behaved.
-/
theorem Lambda.fix_prop (f : Lambda) (hf : Lambda.IsClosed f) :
  ∃ x, Lambda.reduces (Lambda.app Lambda.fix f) x ∧ Lambda.reduces x (Lambda.app f x) := by
    use Lambda.app (Lambda.W f) (Lambda.W f);
    exact ⟨Lambda.fix_reduces_W f hf, by
      simpa [Lambda.IsClosed_imp_subst_eq hf (Lambda.W f) 0] using Lambda.W_reduces f⟩

/-
Prove that the successor function is a closed term.
-/
theorem Lambda.succ_closed : Lambda.IsClosed Lambda.succ := by
  unfold Lambda.IsClosed; aesop;

/-
Prove that the multiplication function is a closed term.
-/
theorem Lambda.mult_closed : Lambda.IsClosed Lambda.mult := by
  intro s x; aesop;

/-
Prove that the less-than function is a closed term.
-/
theorem Lambda.lt'_closed : Lambda.IsClosed Lambda.lt' := by
  unfold Lambda.IsClosed; aesop;

/-
Prove that ifThenElse is a closed term.
-/
theorem Lambda.ifThenElse_closed : Lambda.IsClosed Lambda.ifThenElse := by
  unfold Lambda.IsClosed at *; aesop;

/-
The term sqrt_iter_v2 is closed (has no free variables).
-/
set_option maxHeartbeats 1000000 in
-- The simp normal form of `sqrt_iter_v2` is large, so this closedness check needs
-- more heartbeats than the default budget.
theorem Lambda.sqrt_iter_v2_closed : Lambda.IsClosed Lambda.sqrt_iter_v2 := by
  intro s x
  simp only [sqrt_iter_v2, subst, Nat.right_eq_add, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero,
    and_false, ↓reduceIte, gt_iff_lt, add_lt_iff_neg_right, not_lt_zero, one_ne_zero,
    Nat.add_one_sub_one, lam.injEq, app.injEq, and_true, and_self_right, ite_eq_right_iff,
    var.injEq, OfNat.one_ne_ofNat, imp_false, not_lt, le_add_iff_nonneg_left, zero_le, and_self,
    true_and]
  exact ⟨⟨Lambda.ifThenElse_closed s _, Lambda.lt'_closed s _, Lambda.mult_closed s _,
      Lambda.succ_closed s _⟩, Lambda.succ_closed s _⟩

/-
Substitution into sqrt_iter_v2 is identity because it is closed.
-/
theorem Lambda.subst_sqrt_iter_v2_eq (s : Lambda) (x : ℕ) :
  Lambda.subst s x Lambda.sqrt_iter_v2 = Lambda.sqrt_iter_v2 := by
    -- Apply the fact that substitution into a closed term is the identity.
    apply Lambda.IsClosed_imp_subst_eq; exact Lambda.sqrt_iter_v2_closed

/-
Prove the fixpoint property for sqrt_iter_v2 and define REC_v2.
-/
theorem Lambda.sqrt_iter_v2_fix_prop :
  ∃ x, Lambda.reduces (Lambda.app Lambda.fix Lambda.sqrt_iter_v2) x ∧ Lambda.reduces x
      (Lambda.app Lambda.sqrt_iter_v2 x) := by
  apply Lambda.fix_prop
  exact Lambda.sqrt_iter_v2_closed

def Lambda.REC_v2 : Lambda := Lambda.app Lambda.fix Lambda.sqrt_iter_v2

/-
Define the fixed point term explicitly and prove it reduces to the function applied to itself.
-/
def Lambda.REC_v2_fixed : Lambda :=
  Lambda.app (Lambda.W Lambda.sqrt_iter_v2) (Lambda.W Lambda.sqrt_iter_v2)

theorem Lambda.REC_v2_reduces_to_fixed :
  Lambda.reduces Lambda.REC_v2 Lambda.REC_v2_fixed := by
  unfold Lambda.REC_v2
  exact Lambda.fix_reduces_W _ Lambda.sqrt_iter_v2_closed

theorem Lambda.REC_v2_fixed_reduces_step :
  Lambda.reduces Lambda.REC_v2_fixed (Lambda.app Lambda.sqrt_iter_v2 Lambda.REC_v2_fixed) := by
  have h := Lambda.W_reduces Lambda.sqrt_iter_v2
  rw [Lambda.subst_sqrt_iter_v2_eq] at h
  exact h

/-
Helper definition for the body of the square root iterator.
-/
def Lambda.sqrt_iter_v2_body (f n k : Lambda) : Lambda :=
  Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
    (Lambda.app (Lambda.app Lambda.lt' n) (Lambda.app (Lambda.app Lambda.mult (Lambda.app
        Lambda.succ k)) (Lambda.app Lambda.succ k))))
    k)
    (Lambda.app (Lambda.app f n) (Lambda.app Lambda.succ k))

/-
Unfold sqrt_iter_v2 to show it equals the lambda abstraction of its body.
-/
theorem Lambda.sqrt_iter_v2_eq_lam :
  Lambda.sqrt_iter_v2 = Lambda.lam (Lambda.lam (Lambda.lam (Lambda.sqrt_iter_v2_body (Lambda.var 2)
      (Lambda.var 1) (Lambda.var 0)))) := by
  rfl

/-
Reduction lemma for three consecutive beta reductions.
-/
theorem Lambda.triple_beta_reduction (t a b c : Lambda) (ha : Lambda.IsClosed a) (hb :
    Lambda.IsClosed b) :
  Lambda.reduces
    (Lambda.app (Lambda.app (Lambda.app (Lambda.lam (Lambda.lam (Lambda.lam t))) a) b) c)
    (Lambda.subst c 0 (Lambda.subst b 1 (Lambda.subst a 2 t))) := by
  have step1 :
      Lambda.reduces (Lambda.app (Lambda.lam (Lambda.lam (Lambda.lam t))) a)
        (Lambda.lam (Lambda.lam (Lambda.subst a 2 t))) := by
    refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
    convert Lambda.reduces.refl _ using 1
    simp [Lambda.subst, Lambda.lift_closed ha 1 0]
  have step2 :
      Lambda.reduces
        (Lambda.app (Lambda.app (Lambda.lam (Lambda.lam (Lambda.lam t))) a) b)
        (Lambda.app (Lambda.lam (Lambda.lam (Lambda.subst a 2 t))) b) := by
    apply Lambda.reduces_app_left
    exact step1
  have step3 :
      Lambda.reduces (Lambda.app (Lambda.lam (Lambda.lam (Lambda.subst a 2 t))) b)
        (Lambda.lam (Lambda.subst b 1 (Lambda.subst a 2 t))) := by
    refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
    convert Lambda.reduces.refl _ using 1
    simp [Lambda.subst, Lambda.lift_closed hb 1 0]
  have step4 :
      Lambda.reduces
        (Lambda.app (Lambda.app (Lambda.lam (Lambda.lam (Lambda.lam t))) a) b)
        (Lambda.lam (Lambda.subst b 1 (Lambda.subst a 2 t))) := by
    apply Lambda.reduces_trans step2 step3
  have step5 :
      Lambda.reduces
        (Lambda.app (Lambda.app (Lambda.app (Lambda.lam (Lambda.lam (Lambda.lam t))) a) b) c)
        (Lambda.app (Lambda.lam (Lambda.subst b 1 (Lambda.subst a 2 t))) c) := by
    apply Lambda.reduces_app_left
    exact step4
  have step6 :
      Lambda.reduces (Lambda.app (Lambda.lam (Lambda.subst b 1 (Lambda.subst a 2 t))) c)
        (Lambda.subst c 0 (Lambda.subst b 1 (Lambda.subst a 2 t))) := by
    apply Lambda.beta_reduces
  apply Lambda.reduces_trans step5 step6

/-
Prove that fix and REC_v2 are closed.
-/
theorem Lambda.fix_closed : Lambda.IsClosed Lambda.fix := by
  unfold Lambda.IsClosed; aesop;

theorem Lambda.REC_v2_closed : Lambda.IsClosed Lambda.REC_v2 := by
  exact Lambda.IsClosed_app Lambda.fix_closed Lambda.sqrt_iter_v2_closed

/-
Substitution lemma for the body of sqrt_iter_v2, assuming arguments are closed.
-/
theorem Lambda.subst_sqrt_iter_v2_body_eq_of_closed (f n k : Lambda)
  (hf : Lambda.IsClosed f) (hn : Lambda.IsClosed n) :
  Lambda.subst k 0 (Lambda.subst n 1 (Lambda.subst f 2 (Lambda.sqrt_iter_v2_body (Lambda.var 2)
      (Lambda.var 1) (Lambda.var 0)))) =
  Lambda.sqrt_iter_v2_body f n k := by
  unfold Lambda.sqrt_iter_v2_body
  simp only [Lambda.subst]
  rw [Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed]
  rw [Lambda.IsClosed_imp_subst_eq Lambda.lt'_closed]
  rw [Lambda.IsClosed_imp_subst_eq Lambda.mult_closed]
  rw [Lambda.IsClosed_imp_subst_eq Lambda.succ_closed]
  rw [Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed]
  rw [Lambda.IsClosed_imp_subst_eq Lambda.lt'_closed]
  rw [Lambda.IsClosed_imp_subst_eq Lambda.mult_closed]
  rw [Lambda.IsClosed_imp_subst_eq Lambda.succ_closed]
  rw [Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed]
  rw [Lambda.IsClosed_imp_subst_eq Lambda.lt'_closed]
  rw [Lambda.IsClosed_imp_subst_eq Lambda.mult_closed]
  rw [Lambda.IsClosed_imp_subst_eq Lambda.succ_closed]
  simp only [OfNat.one_ne_ofNat, ↓reduceIte, gt_iff_lt, Nat.not_ofNat_lt_one, subst,
    OfNat.zero_ne_ofNat, not_lt_zero, zero_ne_one, app.injEq, true_and, and_true]
  -- Now we need to handle the substitutions into f, n, k
  -- subst f 2 (var 2) = f
  -- subst n 1 (subst f 2 (var 2)) = subst n 1 f = f (since f is closed)
  -- subst k 0 (subst n 1 (subst f 2 (var 2))) = subst k 0 f = f (since f is closed)
  -- Similarly for n and k
  rw [Lambda.IsClosed_imp_subst_eq hf]
  rw [Lambda.IsClosed_imp_subst_eq hf]
  rw [Lambda.IsClosed_imp_subst_eq hn]
  simp 

/-
Reduction lemma for sqrt_iter_v2 applied to closed arguments.
-/
theorem Lambda.sqrt_iter_v2_app_reduces_closed (f n k : Lambda)
  (hf : Lambda.IsClosed f) (hn : Lambda.IsClosed n) :
  Lambda.reduces
    (Lambda.app (Lambda.app (Lambda.app Lambda.sqrt_iter_v2 f) n) k)
    (Lambda.sqrt_iter_v2_body f n k) := by
  rw [Lambda.sqrt_iter_v2_eq_lam]
  have reduction := Lambda.triple_beta_reduction
      (Lambda.sqrt_iter_v2_body (Lambda.var 2) (Lambda.var 1) (Lambda.var 0)) f n k hf hn
  have subst_eq := Lambda.subst_sqrt_iter_v2_body_eq_of_closed f n k hf hn
  rw [subst_eq] at reduction
  exact reduction

/-
Prove that REC_v2_fixed is closed.
-/
theorem Lambda.W_closed (f : Lambda) (hf : Lambda.IsClosed f) : Lambda.IsClosed (Lambda.W f) := by
  intro s x
  unfold Lambda.W
  simp only [subst, Nat.right_eq_add, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    gt_iff_lt, not_lt_zero, lam.injEq, app.injEq, and_true]
  rw [Lambda.IsClosed_imp_subst_eq hf]

theorem Lambda.REC_v2_fixed_closed : Lambda.IsClosed Lambda.REC_v2_fixed := by
  unfold Lambda.REC_v2_fixed
  exact Lambda.IsClosed_app (Lambda.W_closed _ Lambda.sqrt_iter_v2_closed)
    (Lambda.W_closed _ Lambda.sqrt_iter_v2_closed)

/-
REC_v2_fixed applied to n and k reduces to the body of the iterator.
-/
theorem Lambda.REC_v2_fixed_app_reduces (n k : ℕ) :
  Lambda.reduces
    (Lambda.app (Lambda.app Lambda.REC_v2_fixed (Lambda.church n)) (Lambda.church k))
    (Lambda.sqrt_iter_v2_body Lambda.REC_v2_fixed (Lambda.church n) (Lambda.church k)) := by
  have step1 : Lambda.reduces
      (Lambda.app (Lambda.app Lambda.REC_v2_fixed (Lambda.church n)) (Lambda.church k))
                              (Lambda.app (Lambda.app (Lambda.app Lambda.sqrt_iter_v2
                                  Lambda.REC_v2_fixed) (Lambda.church n)) (Lambda.church k)) := by
    apply Lambda.reduces_app_left
    apply Lambda.reduces_app_left
    apply Lambda.REC_v2_fixed_reduces_step
  have step2 : Lambda.reduces (Lambda.app (Lambda.app (Lambda.app Lambda.sqrt_iter_v2
      Lambda.REC_v2_fixed) (Lambda.church n)) (Lambda.church k))
                              (Lambda.sqrt_iter_v2_body Lambda.REC_v2_fixed (Lambda.church n)
                                  (Lambda.church k)) := by
    exact Lambda.sqrt_iter_v2_app_reduces_closed _ _ _ Lambda.REC_v2_fixed_closed
      (Lambda.church_closed n)
  apply Lambda.reduces_trans step1 step2

/-
Define Nat.sqrt_aux and its unfolding lemma.
-/
def Nat.sqrt_aux (n k : ℕ) : ℕ :=
  if h : n < (k + 1) * (k + 1) then k
  else Nat.sqrt_aux n (k + 1)
termination_by n - k
decreasing_by all_goals
grind

theorem Nat.sqrt_aux_eq (n k : ℕ) :
  Nat.sqrt_aux n k = if n < (k + 1) * (k + 1) then k else Nat.sqrt_aux n (k + 1) := by
  rw [Nat.sqrt_aux]
  rfl

/-
Check properties of Nat.sqrt and prove correctness of Nat.sqrt_aux.
-/

theorem Nat.sqrt_aux_correct (n k : ℕ) (h : k * k ≤ n) : Nat.sqrt_aux n k = Nat.sqrt n := by
  let m := Nat.sqrt n
  have hk : k ≤ m := by
    simpa [m] using (Nat.le_sqrt.2 h)
  have hmain : ∀ k ≤ m, Nat.sqrt_aux n k = m := by
    intro k hk
    generalize hd : m - k = d
    induction d generalizing k with
    | zero =>
        have hk_eq : k = m := by omega
        subst hk_eq
        rw [Nat.sqrt_aux_eq]
        have hlt : n < (m + 1) * (m + 1) := by
          simpa [m] using Nat.lt_succ_sqrt n
        simp [hlt]
    | succ d ih =>
        have hk1 : k + 1 ≤ m := by omega
        have hnot : ¬ n < (k + 1) * (k + 1) := by
          exact not_lt.mpr ((Nat.le_sqrt).1 hk1)
        rw [Nat.sqrt_aux_eq, if_neg hnot]
        apply ih (k + 1) hk1
        omega
  simpa [m] using hmain k hk

/-
Define Nat.sqrt_aux' and its unfolding lemma.
-/
def Nat.sqrt_aux' (n k : ℕ) : ℕ :=
  if h : n < (k + 1) * (k + 1) then k
  else Nat.sqrt_aux' n (k + 1)
termination_by n - k
decreasing_by
  have h' : (k + 1) * (k + 1) ≤ n := Nat.le_of_not_lt h
  have : k + 1 ≤ n := Nat.le_trans (Nat.le_mul_self (k + 1)) h'
  apply Nat.sub_succ_lt_self
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self k) this

theorem Nat.sqrt_aux'_eq (n k : ℕ) :
  Nat.sqrt_aux' n k = if n < (k + 1) * (k + 1) then k else Nat.sqrt_aux' n (k + 1) := by
  rw [Nat.sqrt_aux']
  rfl

/-
Define a helper function for integer square root and its unfolding lemma.
-/
def Nat.sqrt_aux_v3 (n k : ℕ) : ℕ :=
  if h : n < (k + 1) * (k + 1) then k
  else Nat.sqrt_aux_v3 n (k + 1)
termination_by n - k
decreasing_by all_goals
-- Since $n \geq (k + 1)^2$, we have $n \geq k + 1$.
have h_n_ge_k1 : n ≥ k + 1 := by
  nlinarith;
omega

theorem Nat.sqrt_aux_v3_eq (n k : ℕ) :
  Nat.sqrt_aux_v3 n k = if n < (k + 1) * (k + 1) then k else Nat.sqrt_aux_v3 n (k + 1) := by
  rw [Nat.sqrt_aux_v3]
  rfl

/-
Correctness of Nat.sqrt_aux_v3.
-/
theorem Nat.sqrt_aux_v3_correct (n k : ℕ) (h : k * k ≤ n) : Nat.sqrt_aux_v3 n k = Nat.sqrt n := by
  let m := Nat.sqrt n
  have hk : k ≤ m := by
    simpa [m] using (Nat.le_sqrt.2 h)
  have hmain : ∀ k ≤ m, Nat.sqrt_aux_v3 n k = m := by
    intro k hk
    generalize hd : m - k = d
    induction d generalizing k with
    | zero =>
        have hk_eq : k = m := by omega
        subst hk_eq
        rw [Nat.sqrt_aux_v3_eq]
        have hlt : n < (m + 1) * (m + 1) := by
          simpa [m] using Nat.lt_succ_sqrt n
        simp [hlt]
    | succ d ih =>
        have hk1 : k + 1 ≤ m := by omega
        have hnot : ¬ n < (k + 1) * (k + 1) := by
          exact not_lt.mpr ((Nat.le_sqrt).1 hk1)
        rw [Nat.sqrt_aux_v3_eq, if_neg hnot]
        apply ih (k + 1) hk1
        omega
  simpa [m] using hmain k hk

/-
Check for existence of Nat.sqrt lemmas.
-/


theorem Lambda.succ_sq_reduces (k : ℕ) :
  Lambda.reduces
    (Lambda.app (Lambda.app Lambda.mult (Lambda.app Lambda.succ (Lambda.church k))) (Lambda.app
        Lambda.succ (Lambda.church k)))
    (Lambda.church ((k + 1) * (k + 1))) := by
      refine Lambda.reduces_trans
        (t2 := Lambda.app (Lambda.app Lambda.mult (Lambda.church (k + 1))) (Lambda.church (k + 1)))
        ?_ ?_
      · -- Apply the reduce_app_left lemma to show that the left argument reduces, then use
        -- reduce_app_right for the right argument.
        have h_reduces_left : Lambda.reduces
            (Lambda.app Lambda.mult (Lambda.app Lambda.succ (Lambda.church k)))
            (Lambda.app Lambda.mult (Lambda.church (k + 1))) := by
          apply_rules [ Lambda.reduces_app_left, Lambda.reduces_app_right ];
          exact Lambda.succ_works k;
        exact Lambda.reduces_trans ( Lambda.reduces_app_left h_reduces_left )
            ( Lambda.reduces_app_right ( Lambda.succ_works k ) );
      · exact Lambda.mult_works (k + 1) (k + 1)

theorem Lambda.sqrt_iter_v2_condition_reduces (n k : ℕ) :
  Lambda.reduces
    (Lambda.app (Lambda.app Lambda.lt' (Lambda.church n))
      (Lambda.app (Lambda.app Lambda.mult (Lambda.app Lambda.succ (Lambda.church k))) (Lambda.app
          Lambda.succ (Lambda.church k))))
    (if n < (k + 1) * (k + 1) then Lambda.true else Lambda.false) := by
      by_contra h;
      -- Use `reduces_app_right` to apply the reduction of the second argument of `lt'`.
      have h_reduces_lt' : Lambda.reduces
          (Lambda.app (Lambda.app Lambda.lt' (Lambda.church n)) (Lambda.church ((k + 1) * (k + 1))))
          (if n < (k + 1) * (k + 1) then Lambda.true else Lambda.false) := by
        exact Lambda.lt'_works n ((k + 1) * (k + 1));
      -- Use `reduces_app_right` to apply the reduction of the second argument of `lt'` to the
      -- entire expression.
      have h_reduces_app_right : Lambda.reduces (Lambda.app (Lambda.app Lambda.lt' (Lambda.church
          n)) (Lambda.app (Lambda.app Lambda.mult (Lambda.app Lambda.succ (Lambda.church k)))
          (Lambda.app Lambda.succ (Lambda.church k)))) (Lambda.app (Lambda.app Lambda.lt'
          (Lambda.church n)) (Lambda.church ((k + 1) * (k + 1)))) := by
        apply_rules [ Lambda.reduces_app_right ];
        exact Lambda.succ_sq_reduces k;
      exact h ( h_reduces_app_right |> Lambda.reduces_trans <| h_reduces_lt' )

theorem Lambda.sqrt_iter_v2_body_reduces_true (f : Lambda) (n k : ℕ) (h : n < (k + 1) * (k + 1)) :
  Lambda.reduces
    (Lambda.sqrt_iter_v2_body f (Lambda.church n) (Lambda.church k))
    (Lambda.church k) := by
      convert Lambda.reduces_trans _ (Lambda.ifThenElse_true _ _) using 1
      rotate_left
      · exact Lambda.app (Lambda.app f (Lambda.church n))
          (Lambda.app Lambda.succ (Lambda.church k))
      · apply_rules [ Lambda.reduces_app_right, Lambda.reduces_app_left ];
        convert Lambda.sqrt_iter_v2_condition_reduces n k using 1;
        aesop

theorem Lambda.sqrt_iter_v2_body_reduces_false (f : Lambda) (n k : ℕ) (h : ¬ n < (k + 1) * (k + 1))
    :
  Lambda.reduces
    (Lambda.sqrt_iter_v2_body f (Lambda.church n) (Lambda.church k))
    (Lambda.app (Lambda.app f (Lambda.church n)) (Lambda.church (k + 1))) := by
      have h_cond : Lambda.reduces (Lambda.app (Lambda.app Lambda.lt' (Lambda.church n)) (Lambda.app
          (Lambda.app Lambda.mult (Lambda.app Lambda.succ (Lambda.church k))) (Lambda.app
          Lambda.succ (Lambda.church k)))) Lambda.false := by
        convert Lambda.sqrt_iter_v2_condition_reduces n k using 1;
        aesop;
      have h_if_false : Lambda.reduces (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
          Lambda.false) (Lambda.church k)) (Lambda.app (Lambda.app f (Lambda.church n)) (Lambda.app
          Lambda.succ (Lambda.church k)))) (Lambda.app (Lambda.app f (Lambda.church n)) (Lambda.app
          Lambda.succ (Lambda.church k))) := by
        exact Lambda.ifThenElse_false _ _;
      have h_succ : Lambda.reduces (Lambda.app Lambda.succ (Lambda.church k))
          (Lambda.church (k + 1)) := by
        apply_rules [ Lambda.succ_works ];
      have h_combined : Lambda.reduces (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
          (Lambda.app (Lambda.app Lambda.lt' (Lambda.church n)) (Lambda.app (Lambda.app Lambda.mult
          (Lambda.app Lambda.succ (Lambda.church k))) (Lambda.app Lambda.succ (Lambda.church k)))))
          (Lambda.church k)) (Lambda.app (Lambda.app f (Lambda.church n)) (Lambda.app Lambda.succ
          (Lambda.church k)))) (Lambda.app (Lambda.app f (Lambda.church n)) (Lambda.app Lambda.succ
          (Lambda.church k))) := by
        have h_combined : Lambda.reduces (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
            (Lambda.app (Lambda.app Lambda.lt' (Lambda.church n)) (Lambda.app (Lambda.app
            Lambda.mult (Lambda.app Lambda.succ (Lambda.church k))) (Lambda.app Lambda.succ
            (Lambda.church k))))) (Lambda.church k)) (Lambda.app (Lambda.app f (Lambda.church n))
            (Lambda.app Lambda.succ (Lambda.church k)))) (Lambda.app (Lambda.app (Lambda.app
            Lambda.ifThenElse Lambda.false) (Lambda.church k)) (Lambda.app (Lambda.app f
            (Lambda.church n)) (Lambda.app Lambda.succ (Lambda.church k)))) := by
          apply_rules [ Lambda.reduces_app_left, Lambda.reduces_app_right ];
        exact Lambda.reduces_trans h_combined h_if_false;
      exact Lambda.reduces_trans h_combined ( Lambda.reduces_app_right h_succ )

theorem Lambda.REC_v2_fixed_works (n k : ℕ) :
  Lambda.reduces (Lambda.app (Lambda.app Lambda.REC_v2_fixed (Lambda.church n)) (Lambda.church k))
      (Lambda.church (Nat.sqrt_aux_v3 n k)) := by
  generalize hd : n - k = d
  induction d generalizing n k with
  | zero =>
      have h_case : n < (k + 1) * (k + 1) := by
        have hk : n ≤ k := Nat.sub_eq_zero_iff_le.mp hd
        have hk1 : n < k + 1 := Nat.lt_succ_of_le hk
        have hsq : k + 1 ≤ (k + 1) * (k + 1) := by
          simp
        exact lt_of_lt_of_le hk1 hsq
      rw [Nat.sqrt_aux_v3_eq, if_pos h_case]
      exact Lambda.reduces_trans (Lambda.REC_v2_fixed_app_reduces n k)
          (Lambda.sqrt_iter_v2_body_reduces_true _ _ _ h_case)
  | succ d ih =>
      by_cases h_case : n < (k + 1) * (k + 1)
      · rw [Nat.sqrt_aux_v3_eq, if_pos h_case]
        exact Lambda.reduces_trans (Lambda.REC_v2_fixed_app_reduces n k)
            (Lambda.sqrt_iter_v2_body_reduces_true _ _ _ h_case)
      · have hk1 : k + 1 ≤ n := by
          nlinarith [Nat.le_of_not_lt h_case]
        have hd' : n - (k + 1) = d := by
          omega
        have h_step :
            Lambda.reduces
              (Lambda.app (Lambda.app Lambda.REC_v2_fixed (Lambda.church n)) (Lambda.church k))
              (Lambda.app (Lambda.app Lambda.REC_v2_fixed (Lambda.church n)) (Lambda.church (k +
                  1))) := by
          have h_inner :
              Lambda.reduces
                (Lambda.sqrt_iter_v2_body Lambda.REC_v2_fixed (Lambda.church n) (Lambda.church k))
                (Lambda.app (Lambda.app Lambda.REC_v2_fixed (Lambda.church n)) (Lambda.church (k +
                    1))) := by
            exact Lambda.sqrt_iter_v2_body_reduces_false _ _ _ h_case
          exact Lambda.reduces_trans (Lambda.REC_v2_fixed_app_reduces n k) h_inner
        have h_rec :
            Lambda.reduces
              (Lambda.app (Lambda.app Lambda.REC_v2_fixed (Lambda.church n)) (Lambda.church (k +
                  1)))
              (Lambda.church (Nat.sqrt_aux_v3 n (k + 1))) := by
          exact ih n (k + 1) hd'
        rw [Nat.sqrt_aux_v3_eq, if_neg h_case]
        exact Lambda.reduces_trans h_step h_rec

theorem Lambda.sqrt_iter_v2_works (n k : ℕ) :
  Lambda.reduces (Lambda.app (Lambda.app Lambda.REC_v2 (Lambda.church n)) (Lambda.church k))
      (Lambda.church (Nat.sqrt_aux_v3 n k)) := by
    -- Apply the transitive property of reductions.
    apply Lambda.reduces_trans
        (Lambda.reduces_app_left (Lambda.reduces_app_left Lambda.REC_v2_reduces_to_fixed))
        (Lambda.REC_v2_fixed_works n k)


theorem Lambda.sqrt_v2_reduces_app (n : ℕ) :
  Lambda.reduces (Lambda.app Lambda.sqrt_v2 (Lambda.church n))
    (Lambda.app (Lambda.app Lambda.REC_v2 (Lambda.church n)) (Lambda.church 0)) := by
      convert Lambda.beta_reduces using 1

theorem Lambda.sqrt_v2_works (n : ℕ) :
    Lambda.reduces (Lambda.app Lambda.sqrt_v2 (Lambda.church n)) (Lambda.church (Nat.sqrt n)) := by
  -- By combining the previous theorems, we can conclude the proof.
  have h_combined : Lambda.reduces (Lambda.app Lambda.sqrt_v2 (Lambda.church n))
      (Lambda.church (Nat.sqrt_aux_v3 n 0)) := by
    exact Lambda.reduces_trans (Lambda.sqrt_v2_reduces_app n) (Lambda.sqrt_iter_v2_works n 0)
  rwa [ show Nat.sqrt_aux_v3 n 0 = Nat.sqrt n from Nat.sqrt_aux_v3_correct n 0 ( Nat.zero_le _ ) ]
      at h_combined


theorem Lambda.unique_church_reduct {t : Lambda} {n m : ℕ}
  (h1 : Lambda.reduces t (Lambda.church n)) (h2 : Lambda.reduces t (Lambda.church m)) : n = m := by
    obtain ⟨ t3, ht3 ⟩ := Lambda.confluence_theorem h1 h2;
    -- Since `church n` and `church m` are normal forms, and they both reduce to `t3`, they must be
    -- equal to `t3`.
    have h_church_eq_t3 : Lambda.church n = t3 ∧ Lambda.church m = t3 := by
      exact ⟨ Lambda.reduces_normal_eq ( Lambda.church_normal n ) ht3.1, Lambda.reduces_normal_eq (
          Lambda.church_normal m ) ht3.2 ⟩;
    exact Lambda.church_injective (h_church_eq_t3.1.trans h_church_eq_t3.2.symm)

theorem Lambda.sqrt_v2_reverse (n m : ℕ) :
  Lambda.reduces (Lambda.app Lambda.sqrt_v2 (Lambda.church n)) (Lambda.church m) → Nat.sqrt n = m :=
      by
    have := @Lambda.unique_church_reduct;
    exact fun h => this ( Lambda.sqrt_v2_works n ) h

theorem LambdaComputable.sqrt :
    LambdaComputable (fun n => Part.some (Nat.sqrt n)) := by
  refine ⟨Lambda.sqrt_v2, fun n m => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact Part.some_inj.mp h ▸ Lambda.sqrt_v2_works n
  · exact congrArg Part.some (Lambda.unique_church_reduct (Lambda.sqrt_v2_works n) h)

end
