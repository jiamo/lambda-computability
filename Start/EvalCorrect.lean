/-
Correctness analysis of the code-level evaluators.

Two code-level beta steps are available in this development:

* `Lambda.code_step`, built from the *uncorrected* substitution `Lambda.subst_code`
  (which neither shifts the substituted variable index when entering a lambda nor
  lifts the substituted code), and
* `Lambda.code_step'`, built from `Lambda.subst_code'`, which is proved correct in
  `Lambda.subst_code'_correct`.

`Lambda.eval` iterates the first one and `Lambda.eval'` the second.  This file
shows that the hypothesis `Lambda.EvalCorrectness` — the correctness statement for
`Lambda.eval` that `LambdaComputable_imp_Partrec` assumes — is in fact *false*, so
that bridge theorem is vacuous.  It then sets up the corrected version based on
`Lambda.eval'`: the soundness half is proved outright, the remaining half is
isolated as `Lambda.EvalNormalization` (the statement that leftmost-outermost
evaluation finds an existing Church-numeral normal form), and the bridge to
`Partrec` is re-proved from that single hypothesis.
-/

import Start.Arithmetic


set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

------------------------------------------------------------------------
-- Basic facts about `Lambda.encode`
------------------------------------------------------------------------

/-- The encoding of lambda terms as naturals is injective. -/
theorem Lambda.encode_injective : Function.Injective Lambda.encode := by
  intro a
  induction a with
  | var n =>
      intro b hb
      cases b <;> simp [Lambda.encode, Nat.pair_eq_pair] at hb ⊢
      omega
  | app t1 t2 ih1 ih2 =>
      intro b hb
      cases b with
      | var m => simp [Lambda.encode, Nat.pair_eq_pair] at hb
      | app s1 s2 =>
          simp only [Lambda.encode, Nat.pair_eq_pair] at hb
          exact congrArg₂ Lambda.app (ih1 hb.2.1) (ih2 hb.2.2)
      | lam s => simp [Lambda.encode, Nat.pair_eq_pair] at hb
  | lam t ih =>
      intro b hb
      cases b with
      | var m => simp [Lambda.encode, Nat.pair_eq_pair] at hb
      | app s1 s2 => simp [Lambda.encode, Nat.pair_eq_pair] at hb
      | lam s =>
          simp only [Lambda.encode, Nat.pair_eq_pair] at hb
          exact congrArg Lambda.lam (ih hb.2)

------------------------------------------------------------------------
-- The uncorrected evaluator `Lambda.eval`
------------------------------------------------------------------------

/-- Unfolding lemma for `Lambda.code_step`, mirroring `Lambda.code_step'_eq`. -/
theorem Lambda.code_step_eq (n : ℕ) :
    Lambda.code_step n = (Lambda.step_code ((List.range n).map Lambda.code_step)).join := by
  rw [Lambda.code_step, Nat.strongRecOn_eq]
  congr! 2
  simp +decide [Lambda.code_step]

/-- The uncorrected code-level beta step uses the uncorrected `Lambda.subst_code`. -/
theorem Lambda.code_step_beta (t1_body t2 : Lambda) :
    Lambda.code_step (Lambda.encode (Lambda.app (Lambda.lam t1_body) t2)) =
      some (Lambda.subst_code (Lambda.encode t2) 0 (Lambda.encode t1_body)) := by
  have h_join : Lambda.code_step (Lambda.encode (Lambda.app (Lambda.lam t1_body) t2)) =
      (Lambda.step_code ((List.range
        (Lambda.encode (Lambda.app (Lambda.lam t1_body) t2))).map Lambda.code_step)).join :=
    Lambda.code_step_eq _
  have h_case1 : ∀ L : List (Option ℕ), L.length = Nat.pair 1
      (Nat.pair (Nat.pair 2 (Lambda.encode t1_body)) (Lambda.encode t2)) →
      Lambda.step_code L =
        some (some (Lambda.subst_code (Lambda.encode t2) 0 (Lambda.encode t1_body))) := by
    intro L hL
    -- Both components of the encoded redex are smaller than the code of the redex itself.
    have h1 : Nat.pair 2 (Lambda.encode t1_body) <
        Nat.pair 1 (Nat.pair (Nat.pair 2 (Lambda.encode t1_body)) (Lambda.encode t2)) := by
      unfold Nat.pair; simp +arith +decide
      split_ifs <;> nlinarith
    have h2 : Lambda.encode t2 <
        Nat.pair 1 (Nat.pair (Nat.pair 2 (Lambda.encode t1_body)) (Lambda.encode t2)) := by
      unfold Nat.pair; simp +arith +decide
      split_ifs <;> nlinarith
    unfold Lambda.step_code
    unfold Lambda.step_code_case1
    simp only [hL, Nat.unpair_pair]
    rw [if_pos (And.intro h1 h2)]
  rw [h_join, h_case1 _ (by simp +decide [Lambda.encode])]
  rfl

/-- Step case for `Lambda.eval`, mirroring `Lambda.eval'_step`. -/
theorem Lambda.eval_step_of_code_step {c c' : ℕ} (h : Lambda.code_step c = some c') :
    Lambda.eval c = Lambda.eval c' := by
  have h_step : Lambda.eval_step_part c = Sum.inr c' := by
    unfold Lambda.eval_step_part Lambda.eval_step
    rw [h]
  apply PFun.fix_fwd_eq
  aesop

/-- Unfolding `Lambda.subst_code` at a lambda code. -/
theorem Lambda.subst_code_lam_code (s x c : ℕ) :
    Lambda.subst_code s x (Nat.pair 2 c) = Nat.pair 2 (Lambda.subst_code s x c) := by
  conv_lhs => rw [Lambda.subst_code, Nat.strongRecOn_eq]
  split <;> rename_i h <;> simp only [Nat.unpair_pair, Prod.mk.injEq] at h
  · omega
  · omega
  · obtain ⟨-, rfl⟩ := h
    simp only [Lambda.lam_code]
    congr 1
  · exact (h c ⟨trivial, rfl⟩).elim

/-- Unfolding `Lambda.subst_code` at a variable code. -/
theorem Lambda.subst_code_var_code (s x y : ℕ) :
    Lambda.subst_code s x (Nat.pair 0 y) = if x = y then s else Nat.pair 0 y := by
  conv_lhs => rw [Lambda.subst_code, Nat.strongRecOn_eq]
  split <;> rename_i h <;> simp only [Nat.unpair_pair, Prod.mk.injEq] at h
  · obtain ⟨-, rfl⟩ := h
    rfl
  · omega
  · omega
  · rename_i h0 _
    exact (h0 y (Nat.unpair_pair 0 y)).elim

/-- The uncorrected substitution substitutes into bound occurrences: replacing the
free variable `0` in `church 0 = λ λ 0` produces `λ λ s` instead of `church 0`. -/
theorem Lambda.subst_code_church_zero (s : Lambda) :
    Lambda.subst_code (Lambda.encode s) 0 (Lambda.encode (Lambda.church 0)) =
      Lambda.encode (Lambda.lam (Lambda.lam s)) := by
  have hch : Lambda.church 0 = Lambda.lam (Lambda.lam (Lambda.var 0)) := by
    simp [Lambda.church]
  rw [hch]
  simp only [Lambda.encode, Lambda.subst_code_lam_code, Lambda.subst_code_var_code]
  simp

/-- `Lambda.EvalCorrectness` is false: `Lambda.eval` uses the uncorrected
substitution `Lambda.subst_code`, which substitutes into bound variables. -/
theorem Lambda.not_evalCorrectness : ¬ Lambda.EvalCorrectness := by
  intro h
  -- `t` beta-reduces to `church 0`, since `church 0` has no free occurrence of `0`.
  set s : Lambda := Lambda.var 7 with hs
  set t : Lambda := Lambda.app (Lambda.lam (Lambda.church 0)) s with ht
  set t' : Lambda := Lambda.lam (Lambda.lam s) with ht'
  have h_subst : Lambda.subst s 0 (Lambda.church 0) = Lambda.church 0 := by
    simp [Lambda.church, Lambda.subst, hs]
  have h_red : Lambda.reduces t (Lambda.church 0) := by
    refine Lambda.reduces.step _ _ _ ?_ (Lambda.reduces.refl _)
    have := Lambda.step.beta (Lambda.church 0) s
    rwa [h_subst] at this
  -- but the uncorrected evaluator substitutes into the bound variable, reaching `t'`.
  have h_code : Lambda.code_step (Lambda.encode t) = some (Lambda.encode t') := by
    rw [ht, Lambda.code_step_beta, Lambda.subst_code_church_zero]
  have h_eval : Lambda.eval (Lambda.encode t) = Lambda.eval (Lambda.encode t') :=
    Lambda.eval_step_of_code_step h_code
  have h_t' : Lambda.eval (Lambda.encode t') = Part.some (Lambda.church_code 0) := by
    rw [← h_eval]
    exact (h t 0).1 h_red
  -- so correctness would force `t'` to reduce to `church 0`, but `t'` is normal.
  have h_red' : Lambda.reduces t' (Lambda.church 0) := (h t' 0).2 h_t'
  have h_normal : Lambda.is_normal t' :=
    Lambda.lam_normal (Lambda.lam_normal (Lambda.var_normal 7))
  have := Lambda.reduces_normal_eq h_normal h_red'
  simp [ht', hs, Lambda.church] at this

------------------------------------------------------------------------
-- The corrected evaluator `Lambda.eval'`
------------------------------------------------------------------------

/-- Soundness half of correctness for the corrected evaluator: if `eval'` returns the
code of a Church numeral, the term really reduces to that Church numeral. -/
theorem Lambda.eval'_church_sound (t : Lambda) (n : ℕ)
    (h : Lambda.eval' (Lambda.encode t) = Part.some (Lambda.church_code n)) :
    Lambda.reduces t (Lambda.church n) := by
  obtain ⟨t', he, hr, -⟩ := Lambda.eval'_sound t _ h
  have : t' = Lambda.church n :=
    Lambda.encode_injective (by rw [he, Lambda.church_code_correct])
  rwa [this] at hr

/-- Completeness half, isolated as a hypothesis: leftmost-outermost evaluation finds
a Church-numeral normal form whenever one exists. -/
def Lambda.EvalNormalization : Prop :=
  ∀ t n, Lambda.reduces t (Lambda.church n) →
    Lambda.eval' (Lambda.encode t) = Part.some (Lambda.church_code n)

/-- The corrected correctness statement, for `Lambda.eval'`. -/
def Lambda.EvalCorrectness' : Prop :=
  ∀ t n, Lambda.reduces t (Lambda.church n) ↔
    Lambda.eval' (Lambda.encode t) = Part.some (Lambda.church_code n)

/-- Correctness of the corrected evaluator follows from normalization alone. -/
theorem Lambda.evalCorrectness'_of_normalization (h : Lambda.EvalNormalization) :
    Lambda.EvalCorrectness' :=
  fun t n => ⟨h t n, Lambda.eval'_church_sound t n⟩

/-- Lambda-computable functions are computed by `Lambda.compute_fun'`. -/
theorem LambdaComputable_imp_compute_fun'_aux (h : Lambda.EvalNormalization)
    {f : ℕ →. ℕ} (hf : LambdaComputable f) :
    ∃ c, ∀ n, Lambda.compute_fun' c n = f n := by
  obtain ⟨F, hF⟩ := hf
  refine ⟨Lambda.encode F, fun n => ?_⟩
  have hcode : Lambda.app_code (Lambda.encode F) (Lambda.church_code n) =
      Lambda.encode (Lambda.app F (Lambda.church n)) := by
    simp [Lambda.app_code, Lambda.encode, Lambda.encode_church_eq_church_code]
  unfold Lambda.compute_fun'
  rw [hcode]
  apply Part.ext
  intro m
  constructor
  · intro hm
    rw [Part.mem_bind_iff] at hm
    obtain ⟨c'', hc'', hmem⟩ := hm
    have hu : Lambda.unchurch_code c'' = some m := by simpa using hmem
    have hc : c'' = Lambda.church_code m := (Lambda.unchurch_code_eq_some_iff c'' m).1 hu
    have heval : Lambda.eval' (Lambda.encode (Lambda.app F (Lambda.church n))) =
        Part.some (Lambda.church_code m) := by
      rw [← hc]
      exact Part.eq_some_iff.2 hc''
    exact Part.eq_some_iff.1 ((hF n m).2 (Lambda.eval'_church_sound _ m heval))
  · intro hm
    have hred : Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church m) :=
      (hF n m).1 (Part.eq_some_iff.2 hm)
    rw [h _ m hred]
    simp [Lambda.unchurch_code_correct]

/-- Lambda-computable functions are partial recursive, assuming only normalization
of leftmost-outermost evaluation. -/
theorem LambdaComputable_imp_Partrec_of_normalization (h : Lambda.EvalNormalization)
    {f : ℕ →. ℕ} (hf : LambdaComputable f) : Partrec f := by
  obtain ⟨c, hc⟩ := LambdaComputable_imp_compute_fun'_aux h hf
  exact Partrec.of_eq (Lambda.compute_fun'_partrec c) hc

end
