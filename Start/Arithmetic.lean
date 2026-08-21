/-
Church-numeral arithmetic (`Lambda.add`, `Lambda.mult`), injectivity and
normality of Church numerals, and the bridge from lambda computability to
`Partrec`.

Extracted from `Start/Basic.lean` as part of the modular split.
-/

import Start.EvalSound


set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Unfolding lemma for PFun.fix.
-/
theorem PFun.fix_eq {α β} (f : α →. β ⊕ α) (a : α) :
  PFun.fix f a = (f a).bind (Sum.elim Part.some fun a' => PFun.fix f a') := by
    apply Part.ext; intro b; constructor
    · intro hb; rw [PFun.mem_fix_iff] at hb
      rcases hb with hb' | ⟨a', ha', hfix⟩
      · exact Part.mem_bind_iff.mpr ⟨Sum.inl b, hb', Part.mem_some b⟩
      · exact Part.mem_bind_iff.mpr ⟨Sum.inr a', ha', hfix⟩
    · intro hb; rw [Part.mem_bind_iff] at hb
      rcases hb with ⟨s, hs, hb⟩
      cases s with
      | inl b' =>
          simp only [Sum.elim_inl, Part.mem_some_iff] at hb
          subst hb
          exact PFun.fix_stop hs
      | inr a' =>
          simp only [Sum.elim_inr] at hb
          rw [PFun.mem_fix_iff]
          exact Or.inr ⟨a', hs, hb⟩


-- #check Turing.TM2Computable

/-
Iterating a function `n + m` times is the same as iterating it `m` times and then `n` times.
-/
theorem Lambda.iterate_add (f x : Lambda) (n m : ℕ) :
  Lambda.iterate f x (n + m) = Lambda.iterate f (Lambda.iterate f x m) n := by
    induction n <;> simp_all +decide [ Lambda.iterate, Nat.succ_add ];
    simp_all +decide [ List.range_succ ]


/-
Addition of Church numerals is Lambda-computable.
-/
theorem Lambda.subst_church_aux (s : Lambda) (k : ℕ) (n : ℕ) :
  Lambda.subst s k (Lambda.church n) = Lambda.church n := by
  rw [Lambda.church_eq_iterate]
  have h0neq : 0 ≠ k + 2 := by omega
  have h1neq : 1 ≠ k + 2 := by omega
  have h0gt : ¬ 0 > k + 2 := by omega
  have h1gt : ¬ 1 > k + 2 := by omega
  simp [Lambda.subst, Lambda.subst_iterate, h0gt, h1gt]

def Lambda.add : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 3) (Lambda.var
      1)) (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.var 1)) (Lambda.var 0))))))

theorem Lambda.add_works (n m : ℕ) :
    Lambda.reduces (Lambda.app (Lambda.app Lambda.add (Lambda.church n)) (Lambda.church m))
        (Lambda.church (n + m)) := by
  have h1a :
      Lambda.reduces (Lambda.app Lambda.add (Lambda.church n))
        (Lambda.lam
          (Lambda.lam
            (Lambda.lam
              (Lambda.app (Lambda.app (Lambda.church n) (Lambda.var 1))
                (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.var 1)) (Lambda.var 0)))))) := by
    unfold Lambda.add
    convert Lambda.beta_reduces using 1
    simp [Lambda.subst, Lambda.lift_church]
  have h1b :
      Lambda.reduces
        (Lambda.app
          (Lambda.lam
            (Lambda.lam
              (Lambda.lam
                (Lambda.app (Lambda.app (Lambda.church n) (Lambda.var 1))
                  (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.var 1)) (Lambda.var 0))))))
          (Lambda.church m))
        (Lambda.lam
          (Lambda.lam
            (Lambda.app (Lambda.app (Lambda.church n) (Lambda.var 1))
              (Lambda.app (Lambda.app (Lambda.church m) (Lambda.var 1)) (Lambda.var 0))))) := by
    convert Lambda.beta_reduces using 1
    simp [Lambda.subst, Lambda.subst_church_aux, Lambda.lift_church]
  have h1 :
      Lambda.reduces (Lambda.app (Lambda.app Lambda.add (Lambda.church n)) (Lambda.church m))
        (Lambda.lam
          (Lambda.lam
            (Lambda.app (Lambda.app (Lambda.church n) (Lambda.var 1))
              (Lambda.app (Lambda.app (Lambda.church m) (Lambda.var 1)) (Lambda.var 0))))) := by
    exact Lambda.reduces_trans (Lambda.reduces_app_left h1a) h1b
  have h2 :
      Lambda.reduces
        (Lambda.app (Lambda.app (Lambda.church n) (Lambda.var 1))
          (Lambda.app (Lambda.app (Lambda.church m) (Lambda.var 1)) (Lambda.var 0)))
        (Lambda.iterate (Lambda.var 1) (Lambda.iterate (Lambda.var 1) (Lambda.var 0) m) n) := by
    have h3 :
        Lambda.reduces (Lambda.app (Lambda.app (Lambda.church m) (Lambda.var 1)) (Lambda.var 0))
          (Lambda.iterate (Lambda.var 1) (Lambda.var 0) m) := by
      apply Lambda.church_reduces_iterate
    have h4 :
        Lambda.reduces
          (Lambda.app (Lambda.app (Lambda.church n) (Lambda.var 1)) (Lambda.iterate (Lambda.var 1)
              (Lambda.var 0) m))
          (Lambda.iterate (Lambda.var 1) (Lambda.iterate (Lambda.var 1) (Lambda.var 0) m) n) := by
      convert Lambda.church_reduces_iterate n (Lambda.var 1)
          (Lambda.iterate (Lambda.var 1) (Lambda.var 0) m) using 1
    have h5 :
        Lambda.reduces
          (Lambda.app (Lambda.app (Lambda.church n) (Lambda.var 1))
            (Lambda.app (Lambda.app (Lambda.church m) (Lambda.var 1)) (Lambda.var 0)))
          (Lambda.app (Lambda.app (Lambda.church n) (Lambda.var 1)) (Lambda.iterate (Lambda.var 1)
              (Lambda.var 0) m)) := by
      apply_rules [Lambda.reduces_app_right]
    have h6 : ∀ t1 t2 t3 : Lambda, t1.reduces t2 → t2.reduces t3 → t1.reduces t3 := by
      intro t1 t2 t3 h1 h2
      induction h1 with
      | refl => assumption
      | step _ _ _ hs hr ih => exact Lambda.reduces.step _ _ _ hs (ih h2)
    exact h6 _ _ _ h5 h4
  have h3 :
      Lambda.reduces
        (Lambda.lam (Lambda.lam (Lambda.iterate (Lambda.var 1) (Lambda.iterate (Lambda.var 1)
            (Lambda.var 0) m) n)))
        (Lambda.lam (Lambda.lam (Lambda.iterate (Lambda.var 1) (Lambda.var 0) (n + m)))) := by
    apply_rules [Lambda.reduces_lam, Lambda.reduces_lam]
    have h3 : Lambda.iterate (Lambda.var 1) (Lambda.iterate (Lambda.var 1) (Lambda.var 0) m) n =
        Lambda.iterate (Lambda.var 1) (Lambda.var 0) (n + m) := by
      rw [Lambda.iterate_add]
    rw [h3]
    constructor
  have h_trans :
      Lambda.reduces (Lambda.app (Lambda.app Lambda.add (Lambda.church n)) (Lambda.church m))
        (Lambda.lam (Lambda.lam (Lambda.iterate (Lambda.var 1) (Lambda.var 0) (n + m)))) := by
    have h_trans : ∀ {t1 t2 t3 : Lambda}, Lambda.reduces t1 t2 → Lambda.reduces t2 t3 →
        Lambda.reduces t1 t3 := by
      intro t1 t2 t3 h1 h2
      have h_trans : ∀ {t1 t2 t3 : Lambda}, Lambda.reduces t1 t2 → Lambda.reduces t2 t3 →
          Lambda.reduces t1 t3 := by
        intro t1 t2 t3 h1 h2
        exact by
          have h_trans : ∀ {t1 t2 t3 : Lambda}, Lambda.reduces t1 t2 → Lambda.reduces t2 t3 →
              Lambda.reduces t1 t3 := by
            intro t1 t2 t3 h1 h2
            exact by
              induction h1 <;> tauto
          exact h_trans h1 h2
      exact h_trans h1 h2
    exact h_trans h1 (h_trans (Lambda.reduces_lam (Lambda.reduces_lam h2)) h3)
  rw [Lambda.church_eq_iterate (n + m)]
  exact h_trans

/-
Definition of multiplication in Lambda calculus.
-/
def Lambda.mult : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 3) (Lambda.app
      (Lambda.var 2) (Lambda.var 1))) (Lambda.var 0)))))

/-
Helper lemma for multiplication: iterating the application of a Church numeral `n` times corresponds
to iterating the base function `n * m` times.
-/
theorem Lambda.iterate_mul_term (n m : ℕ) :
  Lambda.reduces (Lambda.iterate (Lambda.app (Lambda.church m) (Lambda.var 1)) (Lambda.var 0) n)
                 (Lambda.iterate (Lambda.var 1) (Lambda.var 0) (n * m)) := by
  induction n with
  | zero =>
      simp [Lambda.iterate_zero]
      constructor
  | succ n ih =>
      have h_split :
          Lambda.reduces
            (Lambda.app (Lambda.app (Lambda.church m) (Lambda.var 1))
              (Lambda.iterate (Lambda.app (Lambda.church m) (Lambda.var 1)) (Lambda.var 0) n))
            (Lambda.iterate (Lambda.var 1) (Lambda.var 0) (m + n * m)) := by
        have h_split :
            Lambda.reduces
              (Lambda.app (Lambda.app (Lambda.church m) (Lambda.var 1))
                (Lambda.iterate (Lambda.app (Lambda.church m) (Lambda.var 1)) (Lambda.var 0) n))
              (Lambda.iterate (Lambda.var 1)
                (Lambda.iterate (Lambda.app (Lambda.church m) (Lambda.var 1)) (Lambda.var 0) n)
                    m) := by
          exact
            Lambda.church_reduces_iterate m (Lambda.var 1)
              (Lambda.iterate (Lambda.app (Lambda.church m) (Lambda.var 1)) (Lambda.var 0) n)
        have h_split :
            Lambda.reduces
              (Lambda.iterate (Lambda.var 1)
                (Lambda.iterate (Lambda.app (Lambda.church m) (Lambda.var 1)) (Lambda.var 0) n) m)
              (Lambda.iterate (Lambda.var 1) (Lambda.iterate (Lambda.var 1) (Lambda.var 0) (n * m))
                  m) := by
          have h_split :
              ∀ t t', Lambda.reduces t t' →
                ∀ m, Lambda.reduces (Lambda.iterate (Lambda.var 1) t m)
                    (Lambda.iterate (Lambda.var 1) t' m) := by
            intro t t' h m
            induction m generalizing t t' with
            | zero =>
                simpa [Lambda.iterate] using h
            | succ m ihm =>
                rw [Lambda.iterate_succ, Lambda.iterate_succ]
                exact Lambda.reduces_app_right (ihm t t' h)
          exact h_split _ _ ih m
        have h_split :
            Lambda.reduces
              (Lambda.iterate (Lambda.var 1) (Lambda.iterate (Lambda.var 1) (Lambda.var 0) (n * m))
                  m)
              (Lambda.iterate (Lambda.var 1) (Lambda.var 0) (m + n * m)) := by
          rw [Lambda.iterate_add]
          constructor
        have h_trans :
            ∀ {t1 t2 t3 : Lambda},
              Lambda.reduces t1 t2 → Lambda.reduces t2 t3 → Lambda.reduces t1 t3 := by
          intro t1 t2 t3 h1 h2
          induction h1 with
          | refl =>
              exact h2
          | step _ _ _ hs hr ihr =>
              exact Lambda.reduces.step _ _ _ hs (ihr h2)
        exact h_trans ‹_› (h_trans ‹_› ‹_›)
      convert h_split using 1
      · rw [Lambda.iterate_succ]
      · rw [Nat.succ_mul, Nat.add_comm]

/-
The constant zero function is Lambda-computable.
-/
def Lambda.zero_term : Lambda := Lambda.church 0

theorem LambdaComputable.zero : LambdaComputable (fun _ => Part.some 0) := by
  -- Define the function $F$ as $\lambda x. \lambda y. \lambda z. z$.
  use Lambda.lam (Lambda.lam (Lambda.lam (Lambda.var 0)));
  intro n m;
  constructor;
  · intro h
    have hm : m = 0 := (Part.some_inj.mp h).symm
    subst hm
    -- Let's simplify the goal using the definition of `Lambda.reduces`.
    constructor;
    constructor;
    constructor;
  · intro h;
    have := h;
    cases this;
    rename_i t₂ h₁ h₂;
    cases h₁;
    · unfold Lambda.church at *;
      induction m <;> simp_all +decide [ List.range_succ ];
      cases h₂;
      cases ‹ ( Lambda.var 0 ).lam.lam.step _ ›;
      cases ‹ ( Lambda.var 0 ).lam.step _ ›;
      cases ‹ ( Lambda.var 0 ).step _ ›;
    · cases ‹ ( Lambda.var 0 ).lam.lam.lam.step _›;
      cases ‹ ( Lambda.var 0 ).lam.lam.step _›;
      cases ‹ ( Lambda.var 0 ).lam.step _›;
      cases ‹ ( Lambda.var 0 ).step _›;
    · -- The argument `church n` is normal, so it cannot take a step.
      rename_i t₂' hstep
      exact ((Lambda.church_normal n) t₂' hstep).elim




/-
Church numerals are injective.
-/
theorem Lambda.church_injective {n m : ℕ} (h : Lambda.church n = Lambda.church m) : n = m := by
  have h_body : ∀ {t1 t2 : Lambda}, t1.lam = t2.lam → t1 = t2 := by
    grind
  apply h_body at h
  induction n generalizing m with
  | zero =>
      cases m <;> simp_all +decide [List.range_succ]
  | succ n ih =>
      cases m with
      | zero =>
          simp_all +decide [List.range_succ]
      | succ m =>
          simp_all +decide [List.range_succ]
          grind

/-
Assuming confluence, Church numerals have unique normal forms.
-/
section Confluence

variable (confluence : ∀ {t t1 t2 : Lambda}, Lambda.reduces t t1 → Lambda.reduces t t2 → ∃ t3,
    Lambda.reduces t1 t3 ∧ Lambda.reduces t2 t3)

theorem Lambda.church_unique_normal_form {n m : ℕ} :
  Lambda.reduces (Lambda.church n) (Lambda.church m) → n = m := by
  intro h_reduction
  apply Lambda.church_injective
  have h_normal : ∀ t : Lambda, Lambda.is_normal t → ∀ t' : Lambda, Lambda.reduces t t' → t = t' :=
      by
    intro t ht t' ht'
    induction ht' with
    | refl =>
        rfl
    | step _ _ _ hs _ _ =>
        cases ht _ hs
  exact h_normal _ (Lambda.church_normal _) _ h_reduction ▸ rfl

end Confluence

/-
A normal form reduces only to itself.
-/
theorem Lambda.reduces_normal_eq {t t' : Lambda} (h : Lambda.is_normal t) (r : Lambda.reduces t t')
    : t = t' := by
  cases r <;> tauto


/-
Checking for existence of lemmas.
-/

/-
Checking for existence of Sum.elim_map.
-/

/-
Checking for existence of Part.map_map.
-/

/-
If `f` simulates `g` via `m`, then the image of the fixpoint of `g` is contained in the fixpoint of
`f`.
-/
theorem PFun.fix_map_subset_forward {α β} (f : α →. α ⊕ α) (g : β →. β ⊕ β) (m : β → α)
  (h : ∀ b, f (m b) = (g b).map (Sum.map m m)) :
  ∀ b y, y ∈ PFun.fix g b → m y ∈ PFun.fix f (m b) := by
  intro b y hy
  refine PFun.fixInduction hy ?_
  intro a' ha' ih
  rw [PFun.mem_fix_iff] at ha' ⊢
  rcases ha' with ha' | ⟨a'', ha'', hy''⟩
  · left
    rw [h a']
    exact Part.mem_map _ ha'
  · right
    refine ⟨m a'', ?_, ih a'' ha''⟩
    rw [h a']
    exact Part.mem_map _ ha''


-- #check Turing.TM2Computable

-- #check Computability.FinEncoding
-- #check Turing.TM2Computable



/-
Defining correct Lambda calculus operations (lift, subst, step, reduces) and computability.
-/
def Lambda.lift_correct (n : ℕ) (k : ℕ) : Lambda → Lambda
  | Lambda.var i => if i < k then Lambda.var i else Lambda.var (i + n)
  | Lambda.app t1 t2 => Lambda.app (Lambda.lift_correct n k t1) (Lambda.lift_correct n k t2)
  | Lambda.lam t => Lambda.lam (Lambda.lift_correct n (k + 1) t)

def Lambda.subst_correct (s : Lambda) (x : ℕ) : Lambda → Lambda
  | Lambda.var y => if x = y then s else if y > x then Lambda.var (y - 1) else Lambda.var y
  | Lambda.app t1 t2 => Lambda.app (Lambda.subst_correct s x t1) (Lambda.subst_correct s x t2)
  | Lambda.lam t => Lambda.lam (Lambda.subst_correct (Lambda.lift_correct 1 0 s) (x + 1) t)

inductive Lambda.step_correct : Lambda → Lambda → Prop
  | beta (t₁ t₂ : Lambda) :
      Lambda.step_correct (Lambda.app (Lambda.lam t₁) t₂) (Lambda.subst_correct t₂ 0 t₁)
  | app_left (t₁ t₁' t₂ : Lambda) :
      Lambda.step_correct t₁ t₁' → Lambda.step_correct (Lambda.app t₁ t₂) (Lambda.app t₁' t₂)
  | app_right (t₁ t₂ t₂' : Lambda) :
      Lambda.step_correct t₂ t₂' → Lambda.step_correct (Lambda.app t₁ t₂) (Lambda.app t₁ t₂')
  | lam (t t' : Lambda) :
      Lambda.step_correct t t' → Lambda.step_correct (Lambda.lam t) (Lambda.lam t')

inductive Lambda.reduces_correct : Lambda → Lambda → Prop
  | refl (t : Lambda) : Lambda.reduces_correct t t
  | step (t₁ t₂ t₃ : Lambda) :
      Lambda.step_correct t₁ t₂ → Lambda.reduces_correct t₂ t₃ → Lambda.reduces_correct t₁ t₃

def LambdaComputable_correct (f : ℕ →. ℕ) : Prop :=
  ∃ F : Lambda, ∀ n m, f n = Part.some m ↔ Lambda.reduces_correct (Lambda.app F (Lambda.church n))
      (Lambda.church m)





/-
Definition of EvalCorrectness.

WARNING: this statement is *false*, see `Lambda.not_evalCorrectness` in
`Start/EvalCorrect.lean`.  `Lambda.eval` iterates `Lambda.code_step`, which is built
from the uncorrected substitution `Lambda.subst_code` (it neither shifts the
substituted index nor lifts the substituted code when entering a lambda).  The
corrected statement, for the evaluator `Lambda.eval'`, is
`Lambda.EvalCorrectness'`.
-/
def Lambda.EvalCorrectness : Prop :=
  ∀ t n, Lambda.reduces t (Lambda.church n) ↔ Lambda.eval (Lambda.encode t) = Part.some
      (Lambda.church_code n)


/-
The successor function is Lambda-computable (assuming confluence).
-/
theorem LambdaComputable.succ :
    LambdaComputable (fun n => Part.some (n + 1)) := by
  -- Let's choose the term `F` to be `Lambda.succ`, which increments a Church numeral.
  refine ⟨Lambda.succ, fun n m => ⟨fun h => ?_, fun a => ?_⟩⟩
  · exact Part.some_inj.mp h ▸ Lambda.succ_works n
  -- By the uniqueness of normal forms, if two terms reduce to the same normal form, they must be
  -- equal.
  · have h_unique : ∀ t1 t2, Lambda.reduces t1 t2 → Lambda.is_normal t2 → ∀ t3,
        Lambda.reduces t1 t3 → Lambda.is_normal t3 → t2 = t3 := by
      intros t1 t2 ht1t2 ht2_normal t3 ht1t3 ht3_normal
      obtain ⟨t4, ht4⟩ := Lambda.confluence_theorem ht1t2 ht1t3
      rw [Lambda.reduces_normal_eq ht2_normal ht4.1, Lambda.reduces_normal_eq ht3_normal ht4.2]
    have h_eq : Lambda.church (n + 1) = Lambda.church m :=
      h_unique _ _ (Lambda.succ_works n) (Lambda.church_normal _) _ a (Lambda.church_normal _)
    -- By the injectivity of `Lambda.church`, we have `n + 1 = m`.
    exact congrArg Part.some (Lambda.church_injective h_eq)

/-
Lambda computable functions are partial recursive (assuming evaluation correctness).

Since `Lambda.EvalCorrectness` is refuted by `Lambda.not_evalCorrectness`, this
statement is vacuous; the usable version is
`LambdaComputable_imp_Partrec_unconditional` in `Start/EvalGK.lean`, which assumes
nothing at all (it uses the Gross-Knuth evaluator `Lambda.eval_gk`, proved correct in
`Lambda.evalCorrectnessGK`).  A further variant,
`LambdaComputable_imp_Partrec_of_normalization` in `Start/EvalCorrect.lean`, assumes
only that leftmost-outermost evaluation normalizes.
-/
theorem LambdaComputable_imp_Partrec (h_correct : Lambda.EvalCorrectness) {f : ℕ →. ℕ} (h :
    LambdaComputable f) : Partrec f := by
  obtain ⟨c, hc⟩ := LambdaComputable_imp_compute_fun_aux h_correct h
  have h_partrec : Partrec (Lambda.compute_fun c) := Lambda.compute_fun_partrec c
  have h_eq : f = Lambda.compute_fun c := by
    ext n
    rw [hc]
  rw [h_eq]
  exact h_partrec

end
