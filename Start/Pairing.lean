/-
Lambda terms for Cauchy pairing/unpairing, two-argument lambda computability,
and composition combinators.

Extracted from `Start/Basic.lean` as part of the modular split.
-/

import Start.Sqrt


set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Definitions of unpairing functions in Lambda calculus.
-/
def Lambda.unpairLeft_impl : Lambda :=
  Lambda.lam (
    let z := Lambda.var 0
    let s := Lambda.app Lambda.sqrt_v2 z
    let s2 := Lambda.app (Lambda.app Lambda.mult s) s
    let r := Lambda.app (Lambda.app Lambda.sub z) s2
    Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app (Lambda.app Lambda.lt' r) s))
      r)
      s
  )

def Lambda.unpairRight_impl : Lambda :=
  Lambda.lam (
    let z := Lambda.var 0
    let s := Lambda.app Lambda.sqrt_v2 z
    let s2 := Lambda.app (Lambda.app Lambda.mult s) s
    let r := Lambda.app (Lambda.app Lambda.sub z) s2
    Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app (Lambda.app Lambda.lt' r) s))
      s)
      (Lambda.app (Lambda.app Lambda.sub r) s)
  )

/-
Intermediate terms for unpairLeft reduction.
-/
def Lambda.unpairLeft_subst (n : ℕ) : Lambda :=
  let z := Lambda.church n
  let s := Lambda.app Lambda.sqrt_v2 z
  let s2 := Lambda.app (Lambda.app Lambda.mult s) s
  let r := Lambda.app (Lambda.app Lambda.sub z) s2
  Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app (Lambda.app Lambda.lt' r) s))
    r)
    s

def Lambda.unpairLeft_s_evaluated (n : ℕ) : Lambda :=
  let z := Lambda.church n
  let s := Lambda.church (Nat.sqrt n)
  let s2 := Lambda.app (Lambda.app Lambda.mult s) s
  let r := Lambda.app (Lambda.app Lambda.sub z) s2
  Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app (Lambda.app Lambda.lt' r) s))
    r)
    s

def Lambda.unpairLeft_r_evaluated (n : ℕ) : Lambda :=
  let s_val := Nat.sqrt n
  let r_val := n - s_val * s_val
  let s := Lambda.church s_val
  let r := Lambda.church r_val
  Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app (Lambda.app Lambda.lt' r) s))
    r)
    s

/-
Step 1 of unpairLeft reduction: beta reduction.
-/
theorem Lambda.unpairLeft_step1 (n : ℕ) :
  Lambda.reduces (Lambda.app Lambda.unpairLeft_impl (Lambda.church n)) (Lambda.unpairLeft_subst n)
      := by
    constructor;
    constructor;
    constructor

/-
Step 2 of unpairLeft reduction: evaluate sqrt.
-/
theorem Lambda.unpairLeft_step2 (n : ℕ) :
  Lambda.reduces (Lambda.unpairLeft_subst n) (Lambda.unpairLeft_s_evaluated n) := by
    -- `sqrt_v2 n` reduces to `church (Nat.sqrt n)`; the rest is congruence.
    have hs : Lambda.reduces (Lambda.app Lambda.sqrt_v2 (Lambda.church n))
        (Lambda.church (Nat.sqrt n)) := Lambda.sqrt_v2_works n
    have hr : Lambda.reduces
        (Lambda.app (Lambda.app Lambda.sub (Lambda.church n))
          (Lambda.app (Lambda.app Lambda.mult (Lambda.app Lambda.sqrt_v2 (Lambda.church n)))
            (Lambda.app Lambda.sqrt_v2 (Lambda.church n))))
        (Lambda.app (Lambda.app Lambda.sub (Lambda.church n))
          (Lambda.app (Lambda.app Lambda.mult (Lambda.church (Nat.sqrt n)))
            (Lambda.church (Nat.sqrt n)))) :=
      Lambda.reduces_app_right (Lambda.reduces_app (Lambda.reduces_app_right hs) hs)
    unfold Lambda.unpairLeft_subst Lambda.unpairLeft_s_evaluated
    exact Lambda.reduces_app
      (Lambda.reduces_app
        (Lambda.reduces_app_right (Lambda.reduces_app (Lambda.reduces_app_right hr) hs)) hr) hs

/-
Step 3 of unpairLeft reduction: evaluate multiplication and subtraction.
-/
theorem Lambda.unpairLeft_step3 (n : ℕ) :
  Lambda.reduces (Lambda.unpairLeft_s_evaluated n) (Lambda.unpairLeft_r_evaluated n) := by
    -- `mult` and `sub` evaluate the remainder `r`; the rest is congruence.
    have hr : Lambda.reduces
        (Lambda.app (Lambda.app Lambda.sub (Lambda.church n))
          (Lambda.app (Lambda.app Lambda.mult (Lambda.church (Nat.sqrt n)))
            (Lambda.church (Nat.sqrt n))))
        (Lambda.church (n - Nat.sqrt n * Nat.sqrt n)) :=
      Lambda.reduces_trans (Lambda.reduces_app_right (Lambda.mult_works _ _))
        (Lambda.sub_works _ _)
    unfold Lambda.unpairLeft_s_evaluated Lambda.unpairLeft_r_evaluated
    exact Lambda.reduces_app_left
      (Lambda.reduces_app (Lambda.reduces_app_right (Lambda.reduces_app_left
        (Lambda.reduces_app_right hr))) hr)

/-
A conditional guarded by `lt'` on two Church numerals reduces to the corresponding branch.
-/
theorem Lambda.ite_lt'_church (p q : ℕ) (x y : Lambda) :
    Lambda.reduces
      (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
        (Lambda.app (Lambda.app Lambda.lt' (Lambda.church p)) (Lambda.church q))) x) y)
      (if p < q then x else y) := by
  have hc := Lambda.lt'_works p q
  by_cases h : p < q
  · rw [if_pos h] at hc ⊢
    exact Lambda.reduces_trans
      (Lambda.reduces_app_left (Lambda.reduces_app_left (Lambda.reduces_app_right hc)))
      (Lambda.ifThenElse_true x y)
  · rw [if_neg h] at hc ⊢
    exact Lambda.reduces_trans
      (Lambda.reduces_app_left (Lambda.reduces_app_left (Lambda.reduces_app_right hc)))
      (Lambda.ifThenElse_false x y)

/-
Step 4 of unpairLeft reduction: evaluate if-then-else.
-/
theorem Lambda.unpairLeft_step4 (n : ℕ) :
  Lambda.reduces (Lambda.unpairLeft_r_evaluated n) (Lambda.church n.unpair.1) := by
    -- `n.unpair.1` is the `if`-expression selected by the guard `r < s`.
    have hu : n.unpair.1 =
        if n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n then n - Nat.sqrt n * Nat.sqrt n
        else Nat.sqrt n := by
      unfold Nat.unpair
      dsimp only
      split_ifs <;> rfl
    have h := Lambda.ite_lt'_church (n - Nat.sqrt n * Nat.sqrt n) (Nat.sqrt n)
      (Lambda.church (n - Nat.sqrt n * Nat.sqrt n)) (Lambda.church (Nat.sqrt n))
    unfold Lambda.unpairLeft_r_evaluated
    rw [hu]
    split_ifs at h ⊢ with hc
    · exact h
    · exact h

/-
Correctness of unpairLeft.
-/
theorem Lambda.unpairLeft_works (n : ℕ) :
  Lambda.reduces (Lambda.app Lambda.unpairLeft_impl (Lambda.church n)) (Lambda.church n.unpair.1) :=
      by
    exact Lambda.reduces_trans ( Lambda.unpairLeft_step1 n ) ( Lambda.reduces_trans (
        Lambda.unpairLeft_step2 _ ) ( Lambda.reduces_trans ( Lambda.unpairLeft_step3 _ ) (
        Lambda.unpairLeft_step4 _ ) ) )

/-
Intermediate terms for unpairRight reduction.
-/
def Lambda.unpairRight_subst (n : ℕ) : Lambda :=
  let z := Lambda.church n
  let s := Lambda.app Lambda.sqrt_v2 z
  let s2 := Lambda.app (Lambda.app Lambda.mult s) s
  let r := Lambda.app (Lambda.app Lambda.sub z) s2
  Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app (Lambda.app Lambda.lt' r) s))
    s)
    (Lambda.app (Lambda.app Lambda.sub r) s)

def Lambda.unpairRight_s_evaluated (n : ℕ) : Lambda :=
  let z := Lambda.church n
  let s := Lambda.church (Nat.sqrt n)
  let s2 := Lambda.app (Lambda.app Lambda.mult s) s
  let r := Lambda.app (Lambda.app Lambda.sub z) s2
  Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app (Lambda.app Lambda.lt' r) s))
    s)
    (Lambda.app (Lambda.app Lambda.sub r) s)

def Lambda.unpairRight_r_evaluated (n : ℕ) : Lambda :=
  let s_val := Nat.sqrt n
  let r_val := n - s_val * s_val
  let s := Lambda.church s_val
  let r := Lambda.church r_val
  Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse (Lambda.app (Lambda.app Lambda.lt' r) s))
    s)
    (Lambda.app (Lambda.app Lambda.sub r) s)

/-
Step 1 of unpairRight reduction: beta reduction.
-/
theorem Lambda.unpairRight_step1 (n : ℕ) :
  Lambda.reduces (Lambda.app Lambda.unpairRight_impl (Lambda.church n)) (Lambda.unpairRight_subst n)
      := by
    constructor;
    constructor;
    constructor

/-
Step 2 of unpairRight reduction: evaluate sqrt.
-/
theorem Lambda.unpairRight_step2 (n : ℕ) :
  Lambda.reduces (Lambda.unpairRight_subst n) (Lambda.unpairRight_s_evaluated n) := by
    have h_sqrt : Lambda.reduces (Lambda.app Lambda.sqrt_v2 (Lambda.church n))
        (Lambda.church (Nat.sqrt n)) := by
      exact Lambda.sqrt_v2_works n;
    -- Apply the reduction step to the application of sub to r and s.
    have h_sub : Lambda.reduces (Lambda.app (Lambda.app Lambda.sub (Lambda.app (Lambda.app
        Lambda.sub (Lambda.church n)) (Lambda.app (Lambda.app Lambda.mult (Lambda.app Lambda.sqrt_v2
        (Lambda.church n))) (Lambda.app Lambda.sqrt_v2 (Lambda.church n))))) (Lambda.app
        Lambda.sqrt_v2 (Lambda.church n))) (Lambda.app (Lambda.app Lambda.sub (Lambda.app
        (Lambda.app Lambda.sub (Lambda.church n)) (Lambda.app (Lambda.app Lambda.mult (Lambda.church
        (Nat.sqrt n))) (Lambda.church (Nat.sqrt n))))) (Lambda.church (Nat.sqrt n))) := by
      -- Pure congruence: rewrite each occurrence of `sqrt_v2 n` by `church (Nat.sqrt n)`.
      exact Lambda.reduces_app
        (Lambda.reduces_app_right
          (Lambda.reduces_app_right
            (Lambda.reduces_app (Lambda.reduces_app_right h_sqrt) h_sqrt)))
        h_sqrt
    apply_rules [ Lambda.reduces_app_right, Lambda.reduces_app_left, Lambda.reduces_trans ]

/-
Step 3 of unpairRight reduction: evaluate multiplication and subtraction.
-/
theorem Lambda.unpairRight_step3 (n : ℕ) :
  Lambda.reduces (Lambda.unpairRight_s_evaluated n) (Lambda.unpairRight_r_evaluated n) := by
    -- `mult` and `sub` evaluate the remainder `r`; the rest is congruence.
    have hr : Lambda.reduces
        (Lambda.app (Lambda.app Lambda.sub (Lambda.church n))
          (Lambda.app (Lambda.app Lambda.mult (Lambda.church (Nat.sqrt n)))
            (Lambda.church (Nat.sqrt n))))
        (Lambda.church (n - Nat.sqrt n * Nat.sqrt n)) :=
      Lambda.reduces_trans (Lambda.reduces_app_right (Lambda.mult_works _ _))
        (Lambda.sub_works _ _)
    unfold Lambda.unpairRight_s_evaluated Lambda.unpairRight_r_evaluated
    exact Lambda.reduces_app
      (Lambda.reduces_app_left (Lambda.reduces_app_right
        (Lambda.reduces_app_left (Lambda.reduces_app_right hr))))
      (Lambda.reduces_app_left (Lambda.reduces_app_right hr))

/-
Step 4 of unpairRight reduction: evaluate if-then-else.
-/
theorem Lambda.unpairRight_step4 (n : ℕ) :
  Lambda.reduces (Lambda.unpairRight_r_evaluated n) (Lambda.church n.unpair.2) := by
    -- `n.unpair.2` is the `if`-expression selected by the guard `r < s`.
    have hu : n.unpair.2 =
        if n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n then Nat.sqrt n
        else n - Nat.sqrt n * Nat.sqrt n - Nat.sqrt n := by
      unfold Nat.unpair
      dsimp only
      split_ifs <;> rfl
    have h := Lambda.ite_lt'_church (n - Nat.sqrt n * Nat.sqrt n) (Nat.sqrt n)
      (Lambda.church (Nat.sqrt n))
      (Lambda.app (Lambda.app Lambda.sub (Lambda.church (n - Nat.sqrt n * Nat.sqrt n)))
        (Lambda.church (Nat.sqrt n)))
    unfold Lambda.unpairRight_r_evaluated
    rw [hu]
    split_ifs at h ⊢ with hc
    · exact h
    · exact Lambda.reduces_trans h (Lambda.sub_works _ _)

/-
Correctness of unpairRight.
-/
theorem Lambda.unpairRight_works (n : ℕ) :
  Lambda.reduces (Lambda.app Lambda.unpairRight_impl (Lambda.church n)) (Lambda.church n.unpair.2)
      := by
    exact Lambda.reduces_trans ( Lambda.unpairRight_step1 n ) ( Lambda.reduces_trans (
        Lambda.unpairRight_step2 n ) ( Lambda.reduces_trans ( Lambda.unpairRight_step3 n ) (
        Lambda.unpairRight_step4 n ) ) )

/-
Definition of Lambda computability for binary functions.
-/
def LambdaComputable2 (f : ℕ → ℕ →. ℕ) : Prop :=
  ∃ F : Lambda, ∀ n m k, f n m = Part.some k ↔ Lambda.reduces
      (Lambda.app (Lambda.app F (Lambda.church n)) (Lambda.church m)) (Lambda.church k)

/-
Pairing is Lambda computable.
-/
theorem LambdaComputable2.pair :
  LambdaComputable2 (fun n m => Part.some (Nat.pair n m)) := by
    refine ⟨Lambda.natPair', fun n m k => ⟨fun h => ?_, fun h => ?_⟩⟩
    · exact Part.some_inj.mp h ▸ Lambda.natPair'_works n m
    · exact congrArg Part.some (Lambda.unique_church_reduct (Lambda.natPair'_works n m) h)

/-
Left unpairing is Lambda computable.
-/
theorem LambdaComputable.unpairLeft :
  LambdaComputable (fun n => Part.some n.unpair.1) := by
    refine ⟨Lambda.unpairLeft_impl, fun n m => ⟨fun h => ?_, fun h => ?_⟩⟩
    · exact Part.some_inj.mp h ▸ Lambda.unpairLeft_works n
    · exact congrArg Part.some (Lambda.unique_church_reduct (Lambda.unpairLeft_works n) h)

/-
Right unpairing is Lambda computable.
-/
theorem LambdaComputable.unpairRight :
  LambdaComputable (fun n => Part.some n.unpair.2) := by
    refine ⟨Lambda.unpairRight_impl, fun n m => ⟨fun h => ?_, fun h => ?_⟩⟩
    · exact Part.some_inj.mp h ▸ Lambda.unpairRight_works n
    · exact congrArg Part.some (Lambda.unique_church_reduct (Lambda.unpairRight_works n) h)

/-
Checking if LambdaComputable.comp is already defined.
-/

/-
Definition of the sequencing combinator.
-/
def Lambda.seq_comb : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 1) (Lambda.lam (Lambda.var 1)))
      (Lambda.var 0)))

def Lambda.seq (t1 t2 : Lambda) : Lambda := Lambda.app (Lambda.app Lambda.seq_comb t1) t2

/-
The B combinator (composition) reduces correctly for closed terms.
-/
def Lambda.B : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam (Lambda.app (Lambda.var 2) (Lambda.app (Lambda.var 1)
      (Lambda.var 0)))))

theorem Lambda.B_reduces (f g x : Lambda) (hf : Lambda.IsClosed f) (hg : Lambda.IsClosed g) :
  Lambda.reduces (Lambda.app (Lambda.app (Lambda.app Lambda.B f) g) x)
      (Lambda.app f (Lambda.app g x)) := by
    have h_subst : Lambda.subst x 0 (Lambda.subst g 1 (Lambda.subst f 2 (Lambda.app (Lambda.var 2)
        (Lambda.app (Lambda.var 1) (Lambda.var 0))))) = Lambda.app f (Lambda.app g x) := by
      simp +decide [ Lambda.subst ];
      unfold Lambda.IsClosed at hf hg; aesop;
    have h := Lambda.triple_beta_reduction
      (Lambda.app (Lambda.var 2) (Lambda.app (Lambda.var 1) (Lambda.var 0))) f g x hf hg
    rw [h_subst] at h
    exact h

/-
Checking if Lambda.B is defined.
-/

/-
Checking if Lambda.B_reduces is defined.
-/

/-
Checking if Lambda.triple_beta_reduction is available.
-/

/-
Addition is Lambda computable.
-/
theorem LambdaComputable2.add :
  LambdaComputable2 (fun n m => Part.some (n + m)) := by
    refine ⟨Lambda.add, fun n m k => ⟨fun h => ?_, fun h => ?_⟩⟩
    · exact Part.some_inj.mp h ▸ Lambda.add_works n m
    · exact congrArg Part.some (Lambda.unique_church_reduct (Lambda.add_works n m) h)

/-
Checking for existence of reduction lemmas for pred, sub, mult.
-/


/-
Multiplication is Lambda computable.
-/
theorem LambdaComputable2.mult :
  LambdaComputable2 (fun n m => Part.some (n * m)) := by
    use Lambda.mult;
    intro n m k;
    constructor <;> intro hk;
    · norm_num +zetaDelta at *;
      rw [ ← hk ];
      exact Lambda.mult_works n m;
    · have := Lambda.unique_church_reduct hk ( Lambda.mult_works n m ) ; aesop;

/-
Subtraction is Lambda computable.
-/
theorem LambdaComputable2.sub :
  LambdaComputable2 (fun n m => Part.some (n - m)) := by
    use Lambda.sub;
    intro n m k;
    constructor <;> intro hk;
    · norm_num +zetaDelta at *;
      rw [ ← hk ];
      exact Lambda.sub_works n m;
    · have := Lambda.unique_church_reduct hk ( Lambda.sub_works n m ) ; aesop;

/-
The predecessor function is Lambda computable.
-/
theorem LambdaComputable.pred :
  LambdaComputable (fun n => Part.some (n - 1)) := by
    use Lambda.pred;
    -- To prove the equivalence, we split it into two implications.
    intro n m
    constructor;
    · norm_num +zetaDelta at *;
      exact fun h => h ▸ Lambda.pred_works n;
    · intro h;
      have := Lambda.unique_church_reduct h ( Lambda.pred_works n ) ; aesop;



/-
`church n` applied to `\z. t` and `t` reduces to `t` (for closed `t`).
-/
theorem Lambda.church_const_fun (n : ℕ) (t : Lambda) (ht : Lambda.IsClosed t) :
    Lambda.reduces (Lambda.app (Lambda.app (Lambda.church n) (Lambda.lam t)) t) t := by
  have h_beta : ∀ u : Lambda, Lambda.reduces (Lambda.app (Lambda.lam t) u) t := by
    intro u
    refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
    convert Lambda.reduces.refl t using 1
    exact Lambda.IsClosed_imp_subst_eq ht u 0
  apply Lambda.reduces_trans (Lambda.church_reduces_iterate n _ _)
  induction n with
  | zero =>
      simpa [Lambda.iterate_zero] using (Lambda.reduces.refl t)
  | succ n ih =>
      simpa [Lambda.iterate_succ] using
        (Lambda.reduces_trans (Lambda.reduces_app_right ih) (h_beta _))

/-
Definition of strict composition combinator.
-/
-- Note: this combinator only uses `G`; the historical `F` parameter was unused and
-- has been dropped.  The version that also composes with `F` is `strict_comp_func`.
def Lambda.strict_comp (G : Lambda) : Lambda :=
  Lambda.lam (Lambda.app (Lambda.app (Lambda.var 0) (Lambda.lam (Lambda.app (Lambda.lift 2 0 G)
      (Lambda.var 1)))) (Lambda.app (Lambda.lift 1 0 G) (Lambda.var 0)))

/-
Definition of strict composition combinator (correct version).
-/
def Lambda.strict_comp_func (F G : Lambda) : Lambda :=
  Lambda.lam (Lambda.app (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 0) (Lambda.lam (Lambda.app
      (Lambda.lift 2 0 G) (Lambda.var 1)))) (Lambda.app (Lambda.lift 1 0 G) (Lambda.var 0))))
      (Lambda.app (Lambda.lift 1 0 F) (Lambda.var 0)))


/-
Definitions for `seq_apply` and its components.
-/
def Lambda.seq_apply_inner (G : Lambda) : Lambda :=
  Lambda.lam (Lambda.app (Lambda.lift 2 0 G) (Lambda.var 1))
def Lambda.seq_apply_arg (G : Lambda) : Lambda := Lambda.app (Lambda.lift 1 0 G) (Lambda.var 0)
def Lambda.seq_apply_body (G : Lambda) : Lambda :=
  Lambda.app (Lambda.app (Lambda.var 0) (Lambda.seq_apply_inner G)) (Lambda.seq_apply_arg G)
def Lambda.seq_apply (G : Lambda) : Lambda := Lambda.lam (Lambda.seq_apply_body G)

/-
Substitution lemma for `seq_apply_inner` (corrected).
-/
theorem Lambda.subst_seq_apply_inner (G M : Lambda) (hG : Lambda.IsClosed G) (hM : Lambda.IsClosed
    M) :
  Lambda.subst M 0 (Lambda.seq_apply_inner G) = Lambda.lam (Lambda.app G M) := by
  have h_subst_G : Lambda.subst M 1 G = G := by
    exact hG _ _
  simp [Lambda.seq_apply_inner, Lambda.subst, h_subst_G, Lambda.lift_closed hG 2 0,
      Lambda.lift_closed hM 1 0]

/-
Substitution lemma for `seq_apply_arg`.
-/
theorem Lambda.subst_seq_apply_arg (G M : Lambda) (hG : Lambda.IsClosed G) :
  Lambda.subst M 0 (Lambda.seq_apply_arg G) = Lambda.app G M := by
  have h_subst_G : Lambda.subst M 0 G = G := by
    exact hG _ _
  simp [Lambda.seq_apply_arg, Lambda.subst, h_subst_G, Lambda.lift_closed hG 1 0]

/-
`seq_apply G M` reduces to `M (\z. G M) (G M)`.
-/
theorem Lambda.seq_apply_reduces (G M : Lambda) (hG : Lambda.IsClosed G) (hM : Lambda.IsClosed M) :
  Lambda.reduces (Lambda.app (Lambda.seq_apply G) M)
      (Lambda.app (Lambda.app M (Lambda.lam (Lambda.app G M))) (Lambda.app G M)) := by
  rw [Lambda.seq_apply]
  have h_body :
      Lambda.subst M 0 (Lambda.seq_apply_body G) =
        Lambda.app (Lambda.app M (Lambda.lam (Lambda.app G M))) (Lambda.app G M) := by
    simp [Lambda.seq_apply_body, Lambda.subst, Lambda.subst_seq_apply_inner,
        Lambda.subst_seq_apply_arg, hG, hM]
  exact Lambda.reduces.step _ _ _ (Lambda.step.beta _ _) (h_body ▸ Lambda.reduces.refl _)

/-
Substitution lemma for `seq_apply_body`.
-/
theorem Lambda.subst_seq_apply_body (G M : Lambda) (hG : Lambda.IsClosed G) (hM : Lambda.IsClosed M)
    :
  Lambda.subst M 0 (Lambda.seq_apply_body G) = Lambda.app
      (Lambda.app M (Lambda.lam (Lambda.app G M))) (Lambda.app G M) := by
  simp [Lambda.seq_apply_body, Lambda.subst, Lambda.subst_seq_apply_inner,
      Lambda.subst_seq_apply_arg, hG, hM]

/-
Definition of the composition term.
-/
def Lambda.comp_term (F G : Lambda) : Lambda :=
  Lambda.lam (Lambda.app (Lambda.seq_apply G) (Lambda.app (Lambda.lift 1 0 F) (Lambda.var 0)))

/-
`comp_term F G` applied to `n` reduces to `seq_apply G (F n)`.
-/
theorem Lambda.comp_term_reduces (F G : Lambda) (n : ℕ) (hF : Lambda.IsClosed F) (hG :
    Lambda.IsClosed G) :
  Lambda.reduces (Lambda.app (Lambda.comp_term F G) (Lambda.church n))
      (Lambda.app (Lambda.seq_apply G) (Lambda.app F (Lambda.church n))) := by
    have h_comp_term_def : Lambda.reduces (Lambda.app (Lambda.lam (Lambda.app (Lambda.seq_apply G)
        (Lambda.app (Lambda.lift 1 0 F) (Lambda.var 0)))) (Lambda.church n)) (Lambda.app
        (Lambda.seq_apply G) (Lambda.app (Lambda.lift 1 0 F) (Lambda.church n))) := by
      constructor;
      constructor;
      -- Since the substitution of a closed term with another closed term is just the term itself,
      -- we can conclude that the substitution of (church n) into the app of seq_apply G and lift 1
      -- 0 F is equal to the app of seq_apply G and lift 1 0 F.
      have h_subst : Lambda.subst (Lambda.church n) 0
          (Lambda.app (Lambda.seq_apply G) (Lambda.app (Lambda.lift 1 0 F) (Lambda.var 0))) =
          Lambda.app (Lambda.seq_apply G) (Lambda.app (Lambda.lift 1 0 F) (Lambda.church n)) := by
        unfold Lambda.subst;
        congr;
        · apply_rules [ Lambda.IsClosed_imp_subst_eq ];
          -- Since `G` is closed, the term `G.seq_apply` is also closed.
          have h_seq_apply_closed : G.IsClosed → (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 0)
              (Lambda.lam (Lambda.app (Lambda.lift 2 0 G) (Lambda.var 1)))) (Lambda.app (Lambda.lift
              1 0 G) (Lambda.var 0)))).IsClosed := by
            intros h s x; exact (by
            -- By definition of `subst`, we can rewrite the left-hand side of the equation using the
            -- fact that `G` is closed.
            have h_subst : Lambda.lift 2 0 G = G ∧ Lambda.lift 1 0 G = G := by
              exact ⟨ by rw [ Lambda.lift_closed hG ], by rw [ Lambda.lift_closed hG ] ⟩;
            simp +decide only [subst, Nat.right_eq_add, Nat.add_eq_zero_iff, and_false,
              ↓reduceIte, gt_iff_lt, not_lt_zero, h_subst, add_lt_iff_neg_right, lam.injEq,
              app.injEq, and_true, true_and]
            exact ⟨ h _ _, h _ _ ⟩);
          exact h_seq_apply_closed hG;
        · -- Since `F` is closed, `lift 1 0 F` is just `F`.
          have h_lift_F : Lambda.lift 1 0 F = F := by
            exact Lambda.lift_closed hF 1 0;
          unfold Lambda.subst; aesop;
      exact h_subst ▸ by constructor;
    simpa only [Lambda.comp_term, Lambda.lift_closed hF 1 0] using h_comp_term_def


/-
`seq_apply G` applied to a numeral `n` reduces to `G n`.
-/
theorem Lambda.seq_apply_church (G : Lambda) (n : ℕ) (hG : Lambda.IsClosed G) :
  Lambda.reduces (Lambda.app (Lambda.seq_apply G) (Lambda.church n))
      (Lambda.app G (Lambda.church n)) := by
  have h_closed : Lambda.IsClosed (Lambda.app G (Lambda.church n)) := by
    exact Lambda.IsClosed_app hG (Lambda.church_closed n)
  exact Lambda.reduces_trans
    (Lambda.seq_apply_reduces G (Lambda.church n) hG (Lambda.church_closed n))
    (Lambda.church_const_fun n (Lambda.app G (Lambda.church n)) h_closed)




theorem Lambda.seq_apply_closed (G : Lambda) (hG : Lambda.IsClosed G) :
    Lambda.IsClosed (Lambda.seq_apply G) := by
  have h_lift1 : Lambda.IsClosedAt (Lambda.lift 1 0 G) 1 := by
    intro s x hx
    rw [Lambda.lift_closed hG 1 0]
    exact hG s x
  have h_lift2 : Lambda.IsClosedAt (Lambda.lift 2 0 G) 2 := by
    intro s x hx
    rw [Lambda.lift_closed hG 2 0]
    exact hG s x
  have h_inner_body : Lambda.IsClosedAt (Lambda.app (Lambda.lift 2 0 G) (Lambda.var 1)) 2 := by
    exact Lambda.IsClosedAt_app h_lift2 (Lambda.IsClosedAt_var 1 2 (by omega))
  have h_inner : Lambda.IsClosedAt (Lambda.seq_apply_inner G) 1 := by
    simpa [Lambda.seq_apply_inner] using Lambda.IsClosedAt_lam (k := 1) h_inner_body
  have h_arg : Lambda.IsClosedAt (Lambda.seq_apply_arg G) 1 := by
    simpa [Lambda.seq_apply_arg] using
      Lambda.IsClosedAt_app h_lift1 (Lambda.IsClosedAt_var 0 1 (by omega))
  have h_body : Lambda.IsClosedAt (Lambda.seq_apply_body G) 1 := by
    simpa [Lambda.seq_apply_body] using
      Lambda.IsClosedAt_app
        (Lambda.IsClosedAt_app (Lambda.IsClosedAt_var 0 1 (by omega)) h_inner)
        h_arg
  have h_closed_at_zero : Lambda.IsClosedAt (Lambda.seq_apply G) 0 := by
    simpa [Lambda.seq_apply] using Lambda.IsClosedAt_lam (k := 0) h_body
  exact (Lambda.IsClosedAt_zero_iff_IsClosed _).mp h_closed_at_zero

theorem Lambda.comp_term_closed (F G : Lambda) (hF : Lambda.IsClosed F) (hG : Lambda.IsClosed G) :
    Lambda.IsClosed (Lambda.comp_term F G) := by
  -- Apply the fact that `Lift` preserves closedness when the term is closed and the lift amount is
  -- non-negative.
  have h_lift_closed : ∀ (t : Lambda) (n k : ℕ), Lambda.IsClosed t → Lambda.IsClosed
      (Lambda.lift n k t) := by
    -- By definition of `IsClosed`, if `t` is closed, then for any index `k`, `t` is closed.
    intros t n k ht
    simp only [IsClosed] at ht
    generalize_proofs at *; (
    -- By definition of `IsClosed`, if `t` is closed, then for any index `k`, `t` is closed.
    -- Therefore, `lift n k t` is also closed.
    apply Lambda.lift_closed ht n k |> fun h => by
      -- Since `lift � n� k t` is equal to `t`, and `t` is closed by `ht`, we can conclude that
      -- `lift n k t` is closed.
      rw [h]
      exact ht)
  generalize_proofs at *; (
  -- Apply the fact that `Lift` preserves closedness when the term is closed and the lift amount is
  -- non-negative to each part of the term.
  have h_lift_closed_F : Lambda.IsClosed (Lambda.lift 1 0 F) := by
    exact h_lift_closed F 1 0 hF
  have h_lift_closed_G : Lambda.IsClosed (Lambda.lift 1 0 G) := by
    exact h_lift_closed _ _ _ hG
  have h_lift_closed_seq_apply : Lambda.IsClosed (Lambda.seq_apply G) := by
    exact Lambda.seq_apply_closed G hG
  generalize_proofs at *; (
  intro x
  simp_all +decide only [comp_term]
  intro n; exact (by
  exact congr_arg _ ( congr_arg₂ _ ( h_lift_closed_seq_apply _ _ )
    ( congr_arg₂ _ ( h_lift_closed _ _ _ hF _ _ )
      ( by simp +decide [ Lambda.subst ] ) ) ));))

end
