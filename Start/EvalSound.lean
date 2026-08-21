/-
Soundness of code-level evaluation: `Lambda.code_step'` mirrors a beta step
on terms, normal forms, and the evaluator `Lambda.eval'` together with
`Lambda.compute_fun'`.

Extracted from `Start/Basic.lean` as part of the modular split.
-/

import Start.CodePrimrec


set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

def Lambda.step_iter' (c : ℕ) : ℕ ⊕ ℕ :=
  match Lambda.code_step' c with
  | some c' => Sum.inr c'
  | none => Sum.inl c

theorem Lambda.step_iter'_primrec : Primrec Lambda.step_iter' := by
  unfold step_iter';
  have := @Lambda.code_step'_primrec;
  convert this.option_casesOn _ _ using 1;
  rotate_left;
  exacts [ fun n => Sum.inl n, fun n c' => Sum.inr c',
    by exact Primrec.sumInl.comp ( Primrec.id ),
    by exact Primrec.sumInr.comp ( Primrec.snd ),
    by ext; cases code_step' ‹_› <;> rfl ]

def Lambda.eval' (c : ℕ) : Part ℕ :=
  PFun.fix (fun c => Part.some (Lambda.step_iter' c)) c

theorem Lambda.eval'_partrec : Partrec Lambda.eval' := by
  have h_eval'_partrec : Partrec (fun c => PFun.fix (fun c => Part.some (step_iter' c)) c) := by
    have h_step_iter'_primrec : Primrec step_iter' := by
      exact Lambda.step_iter'_primrec
    exact Partrec.fix h_step_iter'_primrec.to_comp
  exact h_eval'_partrec

theorem Lambda.code_step'_eq (n : ℕ) :
  Lambda.code_step' n = (Lambda.step_code' ((List.range n).map Lambda.code_step')).join := by
    -- By definition of `code_step'`, we have `code_step' n = (step_code' (List.map code_step'
    -- (List.range n))).join`.
    have h_code_step'_def : ∀ n, code_step' n = (step_code' ((List.range n).map code_step')).join :=
        by
      intro n; exact (by
      rw [ Lambda.code_step' ];
      rw [ Nat.strongRecOn_eq ];
      congr! 2;
      simp +decide [ Lambda.code_step' ]);
    exact h_code_step'_def n

def Lambda.code_step'_sound_prop (t : Lambda) : Prop :=
  match Lambda.code_step' (Lambda.encode t) with
  | some c' => ∃ t', Lambda.encode t' = c' ∧ Lambda.step t t'
  | none => ∀ t', ¬ Lambda.step t t'

theorem Lambda.code_step'_sound_lam (t : Lambda) (ih : Lambda.code_step'_sound_prop t) :
  Lambda.code_step'_sound_prop (Lambda.lam t) := by
    have hu : Nat.unpair (Lambda.encode (Lambda.lam t)) = (2, Lambda.encode t) :=
      Nat.unpair_pair 2 _
    have hlt : Lambda.encode t < Lambda.encode (Lambda.lam t) := by
      have h := Nat.add_le_pair 2 (Lambda.encode t)
      change Lambda.encode t < Nat.pair 2 (Lambda.encode t)
      omega
    have hget : ((List.range (Lambda.encode (Lambda.lam t))).map
        Lambda.code_step')[Lambda.encode t]? = some (Lambda.code_step' (Lambda.encode t)) := by
      simp [hlt]
    -- On a `lam` code, the step function reduces to case 2 of `step_code'`, which reads off the
    -- already computed value for the body.
    have hcase : Lambda.step_code'
        ((List.range (Lambda.encode (Lambda.lam t))).map Lambda.code_step') =
        Lambda.step_code_case2_inner (Lambda.code_step' (Lambda.encode t)) := by
      unfold Lambda.step_code'
      simp only [List.length_map, List.length_range, hu]
      rw [Lambda.step_code_case2_eq]
      simp only [List.length_map, List.length_range, hu]
      rw [if_pos hlt, hget]
      rfl
    have hstep : Lambda.code_step' (Lambda.encode (Lambda.lam t)) =
        (Lambda.step_code_case2_inner (Lambda.code_step' (Lambda.encode t))).join := by
      rw [Lambda.code_step'_eq, hcase]
    unfold Lambda.code_step'_sound_prop at *
    rw [hstep]
    cases h : Lambda.code_step' (Lambda.encode t) with
    | some c' =>
        rw [h] at ih
        obtain ⟨t', ht', hst⟩ := ih
        exact ⟨Lambda.lam t', by rw [← ht']; rfl, Lambda.step.lam t t' hst⟩
    | none =>
        rw [h] at ih
        intro t' hst
        cases hst with
        | lam _ t'' h'' => exact ih t'' h''

theorem Lambda.code_step'_sound_var (n : ℕ) :
  Lambda.code_step'_sound_prop (Lambda.var n) := by
    -- By definition of code_step', we know that if t is a variable, then code_step' (encode t)
    -- returns none.
    have hnone : Lambda.code_step' (Lambda.encode (Lambda.var n)) = none := by
      unfold code_step'
      unfold step_code'
      unfold Lambda.encode
      rw [Nat.strongRecOn_eq]
      simp +zetaDelta
    unfold Lambda.code_step'_sound_prop
    rw [hnone]
    exact fun t' h => by cases h


theorem Lambda.code_step'_beta (t1_body t2 : Lambda) :
  Lambda.code_step' (Lambda.encode (Lambda.app (Lambda.lam t1_body) t2)) =
  some (Lambda.encode (Lambda.subst t2 0 t1_body)) := by
    have h_step : (Lambda.code_step' (Lambda.encode (Lambda.app (Lambda.lam t1_body) t2))) =
        (Lambda.step_code' ((List.range (Lambda.encode (Lambda.app (Lambda.lam t1_body) t2))).map
        Lambda.code_step')).join := by
      apply Lambda.code_step'_eq;
    have h_step : (Lambda.code_step' (Lambda.encode (Lambda.app (Lambda.lam t1_body) t2))) = some
        (Lambda.encode (Lambda.subst t2 0 t1_body)) := by
      have h_step' : (Lambda.step_code' ((List.range (Lambda.encode (Lambda.app (Lambda.lam t1_body)
          t2))).map Lambda.code_step')) = some (some (Lambda.encode (Lambda.subst t2 0 t1_body))) :=
          by
        have h_step' : (Lambda.step_code' ((List.range (Lambda.encode (Lambda.app (Lambda.lam
            t1_body) t2))).map Lambda.code_step')) = some (some (Lambda.subst_code' (Lambda.encode
            t2) (Lambda.encode t1_body) 0)) := by
          -- By definition of `step_code'`, we know that it correctly computes the next step of
          -- reduction for the application of a lambda abstraction.
          have h_step_code_case1 : ∀ (L : List (Option ℕ)), (List.length L) = Nat.pair 1
              (Nat.pair (Nat.pair 2 (Lambda.encode t1_body)) (Lambda.encode t2)) →
              (Lambda.step_code' L) = some
              (some (Lambda.subst_code' (Lambda.encode t2) (Lambda.encode t1_body) 0)) := by
            unfold step_code';
            unfold step_code_case1'
            have hleft : Nat.pair 2 t1_body.encode <
                Nat.pair 1 (Nat.pair (Nat.pair 2 t1_body.encode) t2.encode) :=
              Lambda.left_lt_app_code _ _
            have hright : t2.encode <
                Nat.pair 1 (Nat.pair (Nat.pair 2 t1_body.encode) t2.encode) :=
              Lambda.right_lt_app_code _ _
            aesop
          exact h_step_code_case1 _ ( by simp +decide [ Lambda.encode ] );
        have h_subst_code :
            Lambda.subst_code' (Lambda.encode t2) (Lambda.encode t1_body) 0 =
              Lambda.encode (Lambda.subst t2 0 t1_body) := by
          simpa [Lambda.lift_zero] using (Lambda.subst_code'_correct t2 0 t1_body)
        rw [h_step', h_subst_code]
      grind;
    exact h_step

/-
If a term is not a lambda abstraction, its encoding tag is not 2.
-/
theorem Lambda.encode_tag_ne_2_of_not_lam (t : Lambda) (h : ∀ t', t ≠ Lambda.lam t') :
  (Lambda.encode t).unpair.1 ≠ 2 := by
    -- If the tag were 2, then t would be a lambda abstraction, contradicting h.
    by_contra h_contra
    obtain ⟨t', ht'⟩ : ∃ t', t = Lambda.lam t' := by
      unfold Lambda.encode at h_contra; aesop;
    exact h t' ht'

theorem Lambda.code_step'_app_left (t1 t2 : Lambda) (c1' : ℕ)
  (h_not_lam : ∀ t, t1 ≠ Lambda.lam t)
  (h_step1 : Lambda.code_step' (Lambda.encode t1) = some c1') :
  Lambda.code_step' (Lambda.encode (Lambda.app t1 t2)) = some
      (Lambda.app_code c1' (Lambda.encode t2)) := by
    have hlt1 : Lambda.encode t1 < Lambda.encode (Lambda.app t1 t2) :=
      Lambda.left_lt_app_code _ _
    have hlt2 : Lambda.encode t2 < Lambda.encode (Lambda.app t1 t2) :=
      Lambda.right_lt_app_code _ _
    have h_get :
        ((List.range (Lambda.encode (Lambda.app t1 t2))).map Lambda.code_step')[Lambda.encode t1]? =
        some (some c1') := by
      rw [List.getElem?_map, List.getElem?_range hlt1, Option.map_some, h_step1]
    have h_step : Lambda.step_code_case1'
        ((List.range (Lambda.encode (Lambda.app t1 t2))).map Lambda.code_step') = some
        (some (Lambda.app_code c1' (Lambda.encode t2))) := by
      rw [step_code_case1', List.length_map, List.length_range,
        show (Nat.unpair (Nat.unpair (Lambda.encode (Lambda.app t1 t2))).2)
            = (Lambda.encode t1, Lambda.encode t2) from by rw [Lambda.encode]; simp]
      dsimp only
      rw [if_pos ⟨hlt1, hlt2⟩]
      rcases hc1 : Nat.unpair (Lambda.encode t1) with ⟨a, b⟩
      have ha : a ≠ 2 := by
        have h2 := Lambda.encode_tag_ne_2_of_not_lam t1 h_not_lam
        rw [hc1] at h2
        exact h2
      obtain _ | _ | _ | k := a
      · rw [h_get]
        rfl
      · rw [h_get]
        rfl
      · exact absurd rfl ha
      · rw [h_get]
        rfl
    rw [code_step'_eq, step_code']
    rw [List.length_map, List.length_range,
      show Nat.unpair (Lambda.encode (Lambda.app t1 t2))
          = (1, Nat.pair (Lambda.encode t1) (Lambda.encode t2)) from by rw [Lambda.encode]; simp]
    rw [h_step]
    rfl

theorem Lambda.code_step'_app_right (t1 t2 : Lambda) (c2' : ℕ)
  (h_not_lam : ∀ t, t1 ≠ Lambda.lam t)
  (h_step1 : Lambda.code_step' (Lambda.encode t1) = none)
  (h_step2 : Lambda.code_step' (Lambda.encode t2) = some c2') :
  Lambda.code_step' (Lambda.encode (Lambda.app t1 t2)) = some
      (Lambda.app_code (Lambda.encode t1) c2') := by
    have hlt1 : Lambda.encode t1 < Lambda.encode (Lambda.app t1 t2) :=
      Lambda.left_lt_app_code _ _
    have hlt2 : Lambda.encode t2 < Lambda.encode (Lambda.app t1 t2) :=
      Lambda.right_lt_app_code _ _
    have h_get1 :
        ((List.range (Lambda.encode (Lambda.app t1 t2))).map Lambda.code_step')[Lambda.encode t1]? =
        some none := by
      rw [List.getElem?_map, List.getElem?_range hlt1, Option.map_some, h_step1]
    have h_get2 :
        ((List.range (Lambda.encode (Lambda.app t1 t2))).map Lambda.code_step')[Lambda.encode t2]? =
        some (some c2') := by
      rw [List.getElem?_map, List.getElem?_range hlt2, Option.map_some, h_step2]
    have h_step : Lambda.step_code_case1'
        ((List.range (Lambda.encode (Lambda.app t1 t2))).map Lambda.code_step') = some
        (some (Lambda.app_code (Lambda.encode t1) c2')) := by
      rw [step_code_case1', List.length_map, List.length_range,
        show (Nat.unpair (Nat.unpair (Lambda.encode (Lambda.app t1 t2))).2)
            = (Lambda.encode t1, Lambda.encode t2) from by rw [Lambda.encode]; simp]
      dsimp only
      rw [if_pos ⟨hlt1, hlt2⟩]
      rcases hc1 : Nat.unpair (Lambda.encode t1) with ⟨a, b⟩
      have ha : a ≠ 2 := by
        have h2 := Lambda.encode_tag_ne_2_of_not_lam t1 h_not_lam
        rw [hc1] at h2
        exact h2
      obtain _ | _ | _ | k := a
      · rw [h_get1, Option.bind_some, h_get2]
        rfl
      · rw [h_get1, Option.bind_some, h_get2]
        rfl
      · exact absurd rfl ha
      · rw [h_get1, Option.bind_some, h_get2]
        rfl
    rw [code_step'_eq, step_code']
    rw [List.length_map, List.length_range,
      show Nat.unpair (Lambda.encode (Lambda.app t1 t2))
          = (1, Nat.pair (Lambda.encode t1) (Lambda.encode t2)) from by rw [Lambda.encode]; simp]
    rw [h_step]
    rfl

theorem Lambda.code_step'_app_none (t1 t2 : Lambda)
  (h_not_lam : ∀ t, t1 ≠ Lambda.lam t)
  (h_step1 : Lambda.code_step' (Lambda.encode t1) = none)
  (h_step2 : Lambda.code_step' (Lambda.encode t2) = none) :
  Lambda.code_step' (Lambda.encode (Lambda.app t1 t2)) = none := by
    have hlt1 : Lambda.encode t1 < Lambda.encode (Lambda.app t1 t2) :=
      Lambda.left_lt_app_code _ _
    have hlt2 : Lambda.encode t2 < Lambda.encode (Lambda.app t1 t2) :=
      Lambda.right_lt_app_code _ _
    have h_get1 :
        ((List.range (Lambda.encode (Lambda.app t1 t2))).map Lambda.code_step')[Lambda.encode t1]? =
        some none := by
      rw [List.getElem?_map, List.getElem?_range hlt1, Option.map_some, h_step1]
    have h_get2 :
        ((List.range (Lambda.encode (Lambda.app t1 t2))).map Lambda.code_step')[Lambda.encode t2]? =
        some none := by
      rw [List.getElem?_map, List.getElem?_range hlt2, Option.map_some, h_step2]
    have h_step : Lambda.step_code_case1'
        ((List.range (Lambda.encode (Lambda.app t1 t2))).map Lambda.code_step') = some none := by
      rw [step_code_case1', List.length_map, List.length_range,
        show (Nat.unpair (Nat.unpair (Lambda.encode (Lambda.app t1 t2))).2)
            = (Lambda.encode t1, Lambda.encode t2) from by rw [Lambda.encode]; simp]
      dsimp only
      rw [if_pos ⟨hlt1, hlt2⟩]
      rcases hc1 : Nat.unpair (Lambda.encode t1) with ⟨a, b⟩
      have ha : a ≠ 2 := by
        have h2 := Lambda.encode_tag_ne_2_of_not_lam t1 h_not_lam
        rw [hc1] at h2
        exact h2
      obtain _ | _ | _ | k := a
      · rw [h_get1, Option.bind_some, h_get2]
        rfl
      · rw [h_get1, Option.bind_some, h_get2]
        rfl
      · exact absurd rfl ha
      · rw [h_get1, Option.bind_some, h_get2]
        rfl
    rw [code_step'_eq, step_code']
    rw [List.length_map, List.length_range,
      show Nat.unpair (Lambda.encode (Lambda.app t1 t2))
          = (1, Nat.pair (Lambda.encode t1) (Lambda.encode t2)) from by rw [Lambda.encode]; simp]
    rw [h_step]
    rfl

theorem Lambda.code_step'_sound_app (t1 t2 : Lambda)
  (ih1 : Lambda.code_step'_sound_prop t1)
  (ih2 : Lambda.code_step'_sound_prop t2) :
  Lambda.code_step'_sound_prop (Lambda.app t1 t2) := by
    by_cases ht1 : ∃ t, t1 = Lambda.lam t;
    · obtain ⟨w, rfl⟩ := ht1
      -- By `Lambda.code_step'_beta`, `Lambda.code_step' (Lambda.encode (Lambda.app (Lambda.lam w)
      -- t2)) = some (Lambda.encode (Lambda.subst t2 0 w))`.
      have h_beta : Lambda.code_step' (Lambda.encode (Lambda.app (Lambda.lam w) t2)) = some
          (Lambda.encode (Lambda.subst t2 0 w)) := by
        apply_rules [ Lambda.code_step'_beta ];
      unfold Lambda.code_step'_sound_prop; simp_all only;
      exact ⟨ _, rfl, by constructor ⟩;
    · by_cases h_step1 : Lambda.code_step' (Lambda.encode t1) = none;
      · by_cases h_step2 : Lambda.code_step' (Lambda.encode t2) = none;
        · -- Since `t1` and `t2` are both normal, their application `t1.app t2` is also normal.
          have h_normal : ∀ t', ¬Lambda.step (Lambda.app t1 t2) t' := by
            rintro t' ( h | h ) <;> simp_all +decide [ Lambda.code_step'_sound_prop ];
          -- Since `t1` and `t2` are both normal, their application `t1.app t2` is also normal, and
          -- thus `code_step' (Lambda.encode (Lambda.app t1 t2)) = none`.
          have h_code_step_none : Lambda.code_step' (Lambda.encode (Lambda.app t1 t2)) = none := by
            convert Lambda.code_step'_app_none t1 t2 _ _ _;
            · exact fun t ht => ht1 ⟨ t, ht ⟩;
            · assumption;
            · assumption;
          unfold Lambda.code_step'_sound_prop; aesop;
        · -- If `code_step' (encode t2)` is not `none`, then there exists `t2'` such that
          -- `encode t2' = code_step' (encode t2)` and `step t2 t2'`.
          obtain ⟨t2', ht2', ht2'_step⟩ : ∃ t2', Lambda.encode t2' = Lambda.code_step'
              (Lambda.encode t2) ∧ Lambda.step t2 t2' := by
            unfold Lambda.code_step'_sound_prop at ih2; aesop;
          -- By `Lambda.code_step'_app_right`, we have `code_step' (encode (app t1 t2)) = some
          -- (app_code (encode t1) (encode t2'))`.
          have h_step_right : Lambda.code_step' (Lambda.encode (Lambda.app t1 t2)) = some
              (Lambda.app_code (Lambda.encode t1) (Lambda.encode t2')) := by
            rw [ Lambda.code_step'_app_right ] <;> aesop;
          -- By `Lambda.app_code_correct`, we have `app_code (encode t1) (encode t2') = encode (app
          -- t1 t2')`.
          have h_app_code : Lambda.app_code (Lambda.encode t1) (Lambda.encode t2') = Lambda.encode
              (Lambda.app t1 t2') := by
            rfl;
          -- By `Lambda.step.app_right`, we have `step (app t1 t2) (app t1 t2')`.
          have h_step_right : Lambda.step (Lambda.app t1 t2) (Lambda.app t1 t2') := by
            apply_rules [ Lambda.step.app_right ];
          unfold Lambda.code_step'_sound_prop; aesop;
      · obtain ⟨c1', hc1'⟩ : ∃ c1', Lambda.code_step' (Lambda.encode t1) = some c1' := by
          exact Option.ne_none_iff_exists'.mp h_step1;
        obtain ⟨t1', ht1'⟩ : ∃ t1', Lambda.encode t1' = c1' ∧ Lambda.step t1 t1' := by
          unfold Lambda.code_step'_sound_prop at ih1; aesop;
        have h_step : Lambda.code_step' (Lambda.encode (Lambda.app t1 t2)) = some
            (Lambda.app_code c1' (Lambda.encode t2)) := by
          apply_rules [ Lambda.code_step'_app_left ];
          exact fun t ht => ht1 ⟨ t, ht ⟩;
        have h_step : Lambda.app_code c1' (Lambda.encode t2) = Lambda.encode (Lambda.app t1' t2) :=
            by
          rw [ ← ht1'.1, Lambda.app_code_correct ];
        unfold Lambda.code_step'_sound_prop
        simp_all only [not_exists, reduceCtorEq, not_false_eq_true];
        exact ⟨ _, rfl, by constructor; tauto ⟩

theorem Lambda.code_step'_sound_app_final (t1 t2 : Lambda)
  (ih1 : Lambda.code_step'_sound_prop t1)
  (ih2 : Lambda.code_step'_sound_prop t2) :
  Lambda.code_step'_sound_prop (Lambda.app t1 t2) := by
    exact Lambda.code_step'_sound_app t1 t2 ih1 ih2

theorem Lambda.code_step'_sound_app_lam (t1_body t2 : Lambda) :
  Lambda.code_step'_sound_prop (Lambda.app (Lambda.lam t1_body) t2) := by
    unfold Lambda.code_step'_sound_prop;
    rw [ Lambda.code_step'_beta ];
    exact ⟨ _, rfl, by constructor ⟩

theorem Lambda.code_step'_sound_app_thm (t1 t2 : Lambda)
  (ih1 : Lambda.code_step'_sound_prop t1)
  (ih2 : Lambda.code_step'_sound_prop t2) :
  Lambda.code_step'_sound_prop (Lambda.app t1 t2) := by
    convert Lambda.code_step'_sound_app t1 t2 ih1 ih2 using 1

/-
Soundness of `code_step'` for all terms.
-/
theorem Lambda.code_step'_sound (t : Lambda) : Lambda.code_step'_sound_prop t := by
  induction t with
  | var n =>
      exact Lambda.code_step'_sound_var n
  | app t1 t2 ih1 ih2 =>
      exact Lambda.code_step'_sound_app_thm t1 t2 ih1 ih2
  | lam t ih =>
      exact Lambda.code_step'_sound_lam t ih

/-
Definition of normal forms.
-/
def Lambda.is_normal (t : Lambda) : Prop := ∀ t', ¬ Lambda.step t t'

/-
Variables are normal forms.
-/
theorem Lambda.var_normal (n : ℕ) : Lambda.is_normal (Lambda.var n) := by
  exact fun x => by cases x <;> tauto;

/-
Lambda abstractions of normal forms are normal forms.
-/
theorem Lambda.lam_normal {t : Lambda} (h : Lambda.is_normal t) :
    Lambda.is_normal (Lambda.lam t) := by
  rintro t' ⟨ ht' ⟩;
  exact h _ ‹_›

/-
Applications of normal forms (where the left side is not a lambda) are normal forms.
-/
theorem Lambda.app_normal {t1 t2 : Lambda} (h1 : Lambda.is_normal t1) (h2 : Lambda.is_normal t2)
    (h_not_lam : ∀ t, t1 ≠ Lambda.lam t) : Lambda.is_normal (Lambda.app t1 t2) := by
  intro t' ht';
  cases ht' <;> tauto

/-
`Lambda.compute_fun'` is partial recursive.
-/
def Lambda.compute_fun' (F_code : ℕ) (n : ℕ) : Part ℕ :=
  (Lambda.eval' (Lambda.app_code F_code (Lambda.church_code n))).bind
      (fun c => Lambda.unchurch_code c)

theorem Lambda.compute_fun'_partrec (F_code : ℕ) : Partrec (Lambda.compute_fun' F_code) := by
  have h_eval' : Partrec Lambda.eval' := by
    exact Lambda.eval'_partrec;
  refine ( Partrec.bind ?_ ?_ );
  · have h_app_code : Primrec (fun a => app_code F_code (church_code a)) := by
      exact Primrec₂.comp ( Lambda.app_code_primrec ) ( Primrec.const F_code )
          ( Lambda.church_code_primrec );
    exact h_eval'.comp h_app_code.to_comp;
  · have h_unchurch : Primrec Lambda.unchurch_code := by
      convert Lambda.unchurch_code_primrec;
    apply_rules [ Partrec.comp, h_unchurch.to_comp ];
    any_goals exact Computable.id;
    · -- The function `Part.ofOption` is primitive recursive.
      apply Computable.ofOption;
      exact Computable.id;
    · exact Computable.comp ( h_unchurch.to_comp ) ( Computable.snd )

/-
Iterating a normal function (which is not a lambda) on a normal argument produces a normal term.
-/
theorem Lambda.iterate_normal (f x : Lambda) (n : ℕ)
  (hf : Lambda.is_normal f) (hx : Lambda.is_normal x)
  (hf_not_lam : ∀ t, f ≠ Lambda.lam t) :
  Lambda.is_normal (Lambda.iterate f x n) := by
    induction n <;> simp +arith +decide [ *, Lambda.iterate ];
    simpa [ List.range_succ ] using Lambda.app_normal hf ‹_› hf_not_lam

/-
Church numerals are normal forms.
-/
theorem Lambda.church_normal (n : ℕ) : Lambda.is_normal (Lambda.church n) := by
  -- By definition of Church numerals, `var 1` and `var 0` are normal.
  have h_var1 : Lambda.is_normal (Lambda.var 1) := by
    apply Lambda.var_normal
  have h_var0 : Lambda.is_normal (Lambda.var 0) := by
    -- By definition of `is_normal`, we need to show that there is no term `t'` such that
    -- `Lambda.var 0` steps to `t'`.
    apply var_normal;
  apply_rules [ Lambda.lam_normal, Lambda.iterate_normal ];
  grind


/-
Step case for `Lambda.eval'` using `PFun.fix_fwd_eq`.
-/
theorem Lambda.eval'_step {c c' : ℕ} (h : Lambda.code_step' c = some c') :
  Lambda.eval' c = Lambda.eval' c' := by
    have h_step_iter : Lambda.step_iter' c = Sum.inr c' := by
      unfold step_iter';
      rw [ h ];
    apply PFun.fix_fwd_eq;
    aesop

/-
Base case for `Lambda.eval'` using `PFun.fix_stop`.
-/
theorem Lambda.eval'_base {c : ℕ} (h : Lambda.code_step' c = none) :
  Lambda.eval' c = Part.some c := by
    -- By definition of `eval'`, if `Lambda.step_iter' c = Sum.inl c`, then `c ∈ eval' c`.
    have h_eval' : c ∈ Lambda.eval' c := by
      have h_step_iter : Lambda.step_iter' c = Sum.inl c := by
        unfold Lambda.step_iter'; aesop;
      exact PFun.fix_stop <| by aesop;
    exact Part.eq_some_iff.mpr h_eval'


/-
Auxiliary lemma for soundness of `Lambda.eval'`.
-/
theorem Lambda.eval'_sound_aux (c c' : ℕ) (h : c' ∈ Lambda.eval' c) :
  ∀ t, Lambda.encode t = c → ∃ t', Lambda.encode t' = c' ∧ Lambda.reduces t t' ∧ Lambda.is_normal t'
      := by
    unfold eval' at h
    refine PFun.fixInduction h ?_
    intro a' ha ih t ht
    subst ht
    have hsound := Lambda.code_step'_sound t
    unfold Lambda.code_step'_sound_prop at hsound
    cases heq : Lambda.code_step' (Lambda.encode t) with
    | some c1 =>
        rw [heq] at hsound
        obtain ⟨u, hu_enc, hu_step⟩ := hsound
        have hih : ∀ u : Lambda, Lambda.encode u = c1 →
            ∃ t', Lambda.encode t' = c' ∧ Lambda.reduces u t' ∧ Lambda.is_normal t' := by
          refine ih c1 ?_
          unfold Lambda.step_iter'
          rw [heq]
          exact Part.mem_some _
        obtain ⟨t', ht₁, ht₂, ht₃⟩ := hih u hu_enc
        exact ⟨t', ht₁, Lambda.reduces.step _ _ _ hu_step ht₂, ht₃⟩
    | none =>
        rw [heq] at hsound
        have hstep : Lambda.step_iter' (Lambda.encode t) = Sum.inl (Lambda.encode t) := by
          unfold Lambda.step_iter'
          rw [heq]
        have ha' : c' ∈ PFun.fix
            ((fun c => Lambda.step_iter' c : ℕ → ℕ ⊕ ℕ) : ℕ →. ℕ ⊕ ℕ) (Lambda.encode t) := ha
        rw [PFun.mem_fix_iff] at ha'
        simp only [PFun.coe_val, hstep, Part.mem_some_iff] at ha'
        rcases ha' with ha' | ⟨a'', ha'', -⟩
        · exact ⟨t, (Sum.inl_injective ha').symm, Lambda.reduces.refl t, hsound⟩
        · simp at ha''

/-
Soundness of `Lambda.eval'`.
-/
theorem Lambda.eval'_sound (t : Lambda) (c' : ℕ) (h : Lambda.eval' (Lambda.encode t) = Part.some c')
    :
  ∃ t', Lambda.encode t' = c' ∧ Lambda.reduces t t' ∧ Lambda.is_normal t' := by
    convert ( Lambda.eval'_sound_aux _ _ ( show c' ∈ eval' t.encode from ?_ ) ) t rfl ; aesop





/-
Definition of normal order reduction step for Lambda terms.
-/
def Lambda.step_normal : Lambda → Option Lambda
  | Lambda.var _ => none
  | Lambda.lam t => (Lambda.step_normal t).map Lambda.lam
  | Lambda.app t1 t2 =>
    match t1 with
    | Lambda.lam t1_body => some (Lambda.subst t2 0 t1_body)
    | _ =>
      match Lambda.step_normal t1 with
      | some t1' => some (Lambda.app t1' t2)
      | none =>
        match Lambda.step_normal t2 with
        | some t2' => some (Lambda.app t1 t2')
        | none => none

/-
Equivalence between code-based reduction step and term-based normal order reduction step.
-/
theorem Lambda.code_step'_eq_step_normal (t : Lambda) :
  Lambda.code_step' (Lambda.encode t) = (Lambda.step_normal t).map Lambda.encode := by
  induction t with
  | var n =>
      rw [Lambda.code_step'_eq]
      unfold Lambda.step_code' Lambda.step_normal
      simp [Lambda.encode]
  | app t1 t2 ih1 ih2 =>
      cases t1 with
      | lam t1_body =>
          simpa [Lambda.step_normal] using Lambda.code_step'_beta t1_body t2
      | var n =>
          have h_not_lam : ∀ t, Lambda.var n ≠ Lambda.lam t := by
            intro t h
            cases h
          have h_step1 : Lambda.code_step' (Lambda.encode (Lambda.var n)) = none := by
            simpa [Lambda.step_normal] using ih1
          cases h2 : Lambda.step_normal t2 with
          | some t2' =>
              have h_step2 : Lambda.code_step' (Lambda.encode t2) = some (Lambda.encode t2') := by
                simpa [h2] using ih2
              rw [Lambda.code_step'_app_right (Lambda.var n) t2 (Lambda.encode t2') h_not_lam
                  h_step1 h_step2]
              simp [Lambda.step_normal, h2, Lambda.app_code_correct]
          | none =>
              have h_step2 : Lambda.code_step' (Lambda.encode t2) = none := by
                simpa [h2] using ih2
              rw [Lambda.code_step'_app_none (Lambda.var n) t2 h_not_lam h_step1 h_step2]
              simp [Lambda.step_normal, h2]
      | app a b =>
          have h_not_lam : ∀ t, Lambda.app a b ≠ Lambda.lam t := by
            intro t h
            cases h
          cases h1 : Lambda.step_normal (Lambda.app a b) with
          | some t1' =>
              have h_step1 : Lambda.code_step' (Lambda.encode (Lambda.app a b)) = some
                  (Lambda.encode t1') := by
                simpa [h1] using ih1
              rw [Lambda.code_step'_app_left (Lambda.app a b) t2 (Lambda.encode t1') h_not_lam
                  h_step1]
              change
                some (Lambda.encode (Lambda.app t1' t2)) =
                  Option.map Lambda.encode
                    (match Lambda.step_normal (Lambda.app a b) with
                    | some t1' => some (Lambda.app t1' t2)
                    | none =>
                        match Lambda.step_normal t2 with
                        | some t2' => some (Lambda.app (Lambda.app a b) t2')
                        | none => none)
              rw [h1]
              rfl
          | none =>
              have h_step1 : Lambda.code_step' (Lambda.encode (Lambda.app a b)) = none := by
                simpa [h1] using ih1
              cases h2 : Lambda.step_normal t2 with
              | some t2' =>
                  have h_step2 : Lambda.code_step' (Lambda.encode t2) = some (Lambda.encode t2') :=
                      by
                    simpa [h2] using ih2
                  rw [Lambda.code_step'_app_right (Lambda.app a b) t2 (Lambda.encode t2') h_not_lam
                      h_step1 h_step2]
                  change
                    some (Lambda.encode (Lambda.app (Lambda.app a b) t2')) =
                      Option.map Lambda.encode
                        (match Lambda.step_normal (Lambda.app a b) with
                        | some t1' => some (Lambda.app t1' t2)
                        | none =>
                            match Lambda.step_normal t2 with
                            | some t2' => some (Lambda.app (Lambda.app a b) t2')
                            | none => none)
                  rw [h1, h2]
                  rfl
              | none =>
                  have h_step2 : Lambda.code_step' (Lambda.encode t2) = none := by
                    simpa [h2] using ih2
                  rw [Lambda.code_step'_app_none (Lambda.app a b) t2 h_not_lam h_step1 h_step2]
                  change
                    none =
                      Option.map Lambda.encode
                        (match Lambda.step_normal (Lambda.app a b) with
                        | some t1' => some (Lambda.app t1' t2)
                        | none =>
                            match Lambda.step_normal t2 with
                            | some t2' => some (Lambda.app (Lambda.app a b) t2')
                            | none => none)
                  rw [h1, h2]
                  rfl
  | lam t ih =>
      rw [Lambda.code_step'_eq]
      unfold Lambda.step_code'
      rw [List.length_map, List.length_range]
      simp only [encode, Nat.unpair_pair]
      rw [Lambda.step_code_case2_eq]
      rw [List.length_map, List.length_range]
      simp only [Nat.unpair_pair, List.getElem?_map]
      have hlt : Lambda.encode t < Nat.pair 2 (Lambda.encode t) := by
        exact Lambda.decode_lt_3 (by simp )
      rw [if_pos hlt]
      have hget :
          Option.map Lambda.code_step' ((List.range t.lam.encode)[t.encode]?) =
            some (Lambda.code_step' t.encode) := by
        simp [List.getElem?_range hlt, Lambda.encode]
      change
        ((Option.map Lambda.code_step' ((List.range t.lam.encode)[t.encode]?)).bind
            Lambda.step_code_case2_inner).join =
          Option.map Lambda.encode (Lambda.step_normal (Lambda.lam t))
      rw [hget]
      cases h : Lambda.step_normal t with
      | some t' =>
          have h_step : Lambda.code_step' (Lambda.encode t) = some (Lambda.encode t') := by
            simpa [h] using ih
          rw [h_step]
          unfold Lambda.step_code_case2_inner
          simp [Lambda.step_normal, h, Lambda.lam_code, Lambda.encode]
      | none =>
          have h_step : Lambda.code_step' (Lambda.encode t) = none := by
            simpa [h] using ih
          rw [h_step]
          simp [Lambda.step_normal, h, Lambda.step_code_case2_inner]

/-
Definition of normal order evaluation for Lambda terms.
-/
def Lambda.eval_normal (t : Lambda) : Part Lambda :=
  PFun.fix (fun t => Part.some
    (match Lambda.step_normal t with | some t' => Sum.inl t' | none => Sum.inr t)) t

/-
Correct definition of normal order evaluation (iterated reduction until normal form).
-/
def Lambda.eval_norm (t : Lambda) : Part Lambda :=
  PFun.fix (fun t => Part.some
    (match Lambda.step_normal t with | some t' => Sum.inr t' | none => Sum.inl t)) t

/-
Definition of the step iteration function for normal order reduction, and its correspondence to the
code-based step iteration.
-/
def Lambda.step_iter_norm (t : Lambda) : Lambda ⊕ Lambda :=
  match Lambda.step_normal t with
  | some t' => Sum.inr t'
  | none => Sum.inl t

theorem Lambda.step_iter'_eq_step_iter_norm (t : Lambda) :
  Lambda.step_iter' (Lambda.encode t) = (Lambda.step_iter_norm t).map Lambda.encode Lambda.encode :=
      by
    have := @Lambda.code_step'_eq_step_normal;
    unfold step_iter' step_iter_norm at * ; aesop;


/-
Checking for PFun.mem_fix_iff
-/

/-
Checking for PFun.fixInduction and Part.map
-/

end
