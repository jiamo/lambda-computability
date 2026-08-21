/-
The code-level Gross–Knuth evaluator and the unconditional bridge from lambda
computability to `Partrec`.

`Lambda.rho_code` arithmetizes the complete development `Lambda.rho`, and
`Lambda.eval_gk` iterates it until it reaches a fixed point.  Combined with the
normalization theorem `Lambda.rho_iterate_eq_of_reduces_normal`, this yields
`LambdaComputable_imp_Partrec_unconditional`: every lambda-computable partial
function is partial recursive, with no correctness hypothesis assumed.
-/

import Start.GrossKnuth
import Start.EvalCorrect


set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

------------------------------------------------------------------------
-- The code-level complete development
------------------------------------------------------------------------

/-- One layer of the code-level complete development: `L` holds the values of
`Lambda.rho_code` on all codes below `L.length`, and `Lambda.rho_step L` computes
the value at `L.length`. -/
def Lambda.rho_step (L : List ℕ) : ℕ :=
  let c := L.length
  let m := c.unpair.2
  if c.unpair.1 = 1 then
    if m.unpair.1.unpair.1 = 2 then
      Lambda.subst_code' (L.getD m.unpair.2 0) (L.getD m.unpair.1.unpair.2 0) 0
    else
      Lambda.app_code (L.getD m.unpair.1 0) (L.getD m.unpair.2 0)
  else if c.unpair.1 = 2 then
    Lambda.lam_code (L.getD m 0)
  else c

/-- The code-level complete development. -/
def Lambda.rho_code (n : ℕ) : ℕ :=
  Nat.strongRecOn n fun n ih =>
    Lambda.rho_step ((List.range n).attach.map fun x => ih x.1 (List.mem_range.1 x.2))

/-- Unfolding lemma for `Lambda.rho_code`. -/
theorem Lambda.rho_code_eq (n : ℕ) :
    Lambda.rho_code n = Lambda.rho_step ((List.range n).map Lambda.rho_code) := by
  rw [Lambda.rho_code, Nat.strongRecOn_eq]
  congr! 2
  simp +decide [Lambda.rho_code]

/-- Reading back a value from the table of previous values. -/
theorem Lambda.getD_range_map {f : ℕ → ℕ} {n i : ℕ} (h : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_map, List.getElem?_range h]
  rfl

------------------------------------------------------------------------
-- Correctness of the code-level complete development
------------------------------------------------------------------------

/-- `Lambda.rho_code` on a lambda code. -/
theorem Lambda.rho_code_lam (c : ℕ) :
    Lambda.rho_code (Nat.pair 2 c) = Nat.pair 2 (Lambda.rho_code c) := by
  have hu : (Nat.pair 2 c).unpair = (2, c) := Nat.unpair_pair 2 c
  have hlt : c < Nat.pair 2 c := Lambda.decode_lt_3 hu
  have hlen : ((List.range (Nat.pair 2 c)).map Lambda.rho_code).length = Nat.pair 2 c := by
    simp
  rw [Lambda.rho_code_eq, Lambda.rho_step]
  simp only [hlen, hu]
  rw [Lambda.getD_range_map hlt]
  norm_num [Lambda.lam_code]

/-- `Lambda.rho_code` computes the code of `Lambda.rho`. -/
theorem Lambda.rho_code_correct (t : Lambda) :
    Lambda.rho_code (Lambda.encode t) = Lambda.encode (Lambda.rho t) := by
  induction t with
  | var y =>
      rw [Lambda.rho_code_eq]
      simp [Lambda.rho_step, Lambda.encode, Lambda.rho]
  | app t1 t2 ih1 ih2 =>
      have hlen : ((List.range (Lambda.encode (Lambda.app t1 t2))).map Lambda.rho_code).length =
          Lambda.encode (Lambda.app t1 t2) := by
        simp
      have hc : Lambda.encode (Lambda.app t1 t2) =
          Nat.pair 1 (Nat.pair (Lambda.encode t1) (Lambda.encode t2)) := rfl
      have hu : (Lambda.encode (Lambda.app t1 t2)).unpair =
          (1, Nat.pair (Lambda.encode t1) (Lambda.encode t2)) := by
        rw [hc, Nat.unpair_pair]
      have hm : (Nat.pair (Lambda.encode t1) (Lambda.encode t2)).unpair =
          (Lambda.encode t1, Lambda.encode t2) := Nat.unpair_pair _ _
      have h1 : Lambda.encode t1 < Lambda.encode (Lambda.app t1 t2) := Lambda.decode_lt_1 hu hm
      have h2 : Lambda.encode t2 < Lambda.encode (Lambda.app t1 t2) := Lambda.decode_lt_2 hu hm
      rw [Lambda.rho_code_eq, Lambda.rho_step]
      simp only [hlen, hu, hm]
      cases t1 with
      | lam b =>
          have hb : (Lambda.encode (Lambda.lam b)).unpair = (2, Lambda.encode b) :=
            Nat.unpair_pair 2 (Lambda.encode b)
          have hblt : Lambda.encode b < Lambda.encode (Lambda.app (Lambda.lam b) t2) :=
            lt_trans (Lambda.decode_lt_3 hb) h1
          simp only [hb]
          rw [Lambda.getD_range_map h2, Lambda.getD_range_map hblt, ih2]
          have ihb : Lambda.rho_code (Lambda.encode b) = Lambda.encode (Lambda.rho b) := by
            have h := ih1
            rw [show Lambda.encode (Lambda.lam b) = Nat.pair 2 (Lambda.encode b) from rfl,
              Lambda.rho_code_lam,
              show Lambda.encode (Lambda.rho (Lambda.lam b))
                = Nat.pair 2 (Lambda.encode (Lambda.rho b)) from rfl] at h
            exact (Nat.pair_eq_pair.mp h).2
          rw [ihb, Lambda.subst_code'_correct, Lambda.lift_zero]
          rfl
      | var n =>
          have h0 : (Lambda.encode (Lambda.var n)).unpair = (0, n) := Nat.unpair_pair 0 n
          have hb : (Lambda.encode (Lambda.var n)).unpair.1 ≠ 2 := by
            simp [h0]
          simp only [if_neg hb]
          rw [Lambda.getD_range_map h1, Lambda.getD_range_map h2, ih1, ih2]
          rfl
      | app a b =>
          have h0 : (Lambda.encode (Lambda.app a b)).unpair =
              (1, Nat.pair (Lambda.encode a) (Lambda.encode b)) :=
            Nat.unpair_pair 1 (Nat.pair (Lambda.encode a) (Lambda.encode b))
          have hb : (Lambda.encode (Lambda.app a b)).unpair.1 ≠ 2 := by
            simp [h0]
          simp only [if_neg hb]
          rw [Lambda.getD_range_map h1, Lambda.getD_range_map h2, ih1, ih2]
          rfl
  | lam b ih =>
      rw [show Lambda.encode (Lambda.lam b) = Nat.pair 2 (Lambda.encode b) from rfl,
        Lambda.rho_code_lam, ih]
      rfl

/-- Iterating the code-level complete development computes iterated `Lambda.rho`. -/
theorem Lambda.rho_code_iterate_correct (t : Lambda) (k : ℕ) :
    Lambda.rho_code^[k] (Lambda.encode t) = Lambda.encode (Lambda.rho^[k] t) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Lambda.rho_code_correct, ih]

------------------------------------------------------------------------
-- Primitive recursiveness of the code-level complete development
------------------------------------------------------------------------

theorem Lambda.rho_step_primrec : Primrec Lambda.rho_step := by
  have hlen : Primrec (fun L : List ℕ => L.length) := Primrec.list_length
  have hc1 : Primrec (fun L : List ℕ => (Nat.unpair L.length).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hlen)
  have hm : Primrec (fun L : List ℕ => (Nat.unpair L.length).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hlen)
  have hm1 : Primrec (fun L : List ℕ => (Nat.unpair (Nat.unpair L.length).2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hm)
  have hm2 : Primrec (fun L : List ℕ => (Nat.unpair (Nat.unpair L.length).2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hm)
  have hm11 : Primrec (fun L : List ℕ => (Nat.unpair (Nat.unpair (Nat.unpair L.length).2).1).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hm1)
  have hm12 : Primrec (fun L : List ℕ => (Nat.unpair (Nat.unpair (Nat.unpair L.length).2).1).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hm1)
  have hget : ∀ {g : List ℕ → ℕ}, Primrec g → Primrec (fun L : List ℕ => L.getD (g L) 0) :=
    fun hg => (Primrec.list_getD 0).comp Primrec.id hg
  have hsubst : Primrec (fun L : List ℕ =>
      Lambda.subst_code' (L.getD (Nat.unpair (Nat.unpair L.length).2).2 0)
        (L.getD (Nat.unpair (Nat.unpair (Nat.unpair L.length).2).1).2 0) 0) := by
    have := Lambda.subst_code_uncurried_primrec.comp
      (Primrec.pair (hget hm2) (Primrec.pair (hget hm12) (Primrec.const 0)))
    exact this
  have happ : Primrec (fun L : List ℕ =>
      Lambda.app_code (L.getD (Nat.unpair (Nat.unpair L.length).2).1 0)
        (L.getD (Nat.unpair (Nat.unpair L.length).2).2 0)) :=
    Lambda.app_code_primrec.comp (hget hm1) (hget hm2)
  have hlam : Primrec (fun L : List ℕ =>
      Lambda.lam_code (L.getD (Nat.unpair L.length).2 0)) :=
    Lambda.lam_code_primrec.comp (hget hm)
  have hite2 : Primrec (fun L : List ℕ =>
      if (Nat.unpair (Nat.unpair (Nat.unpair L.length).2).1).1 = 2 then
        Lambda.subst_code' (L.getD (Nat.unpair (Nat.unpair L.length).2).2 0)
          (L.getD (Nat.unpair (Nat.unpair (Nat.unpair L.length).2).1).2 0) 0
      else
        Lambda.app_code (L.getD (Nat.unpair (Nat.unpair L.length).2).1 0)
          (L.getD (Nat.unpair (Nat.unpair L.length).2).2 0)) :=
    Primrec.ite (Primrec.eq.comp hm11 (Primrec.const 2)) hsubst happ
  have hite1 : Primrec (fun L : List ℕ =>
      if (Nat.unpair L.length).1 = 2 then
        Lambda.lam_code (L.getD (Nat.unpair L.length).2 0)
      else L.length) :=
    Primrec.ite (Primrec.eq.comp hc1 (Primrec.const 2)) hlam hlen
  exact Primrec.ite (Primrec.eq.comp hc1 (Primrec.const 1)) hite2 hite1

theorem Lambda.rho_code_primrec : Primrec Lambda.rho_code := by
  have h : Primrec₂ (fun (_ : Unit) (L : List ℕ) => some (Lambda.rho_step L)) :=
    (Primrec.option_some.comp Lambda.rho_step_primrec).comp Primrec.snd
  have hstrong : Primrec₂ (fun (_ : Unit) (n : ℕ) => Lambda.rho_code n) := by
    refine Primrec.nat_strong_rec (fun (_ : Unit) (n : ℕ) => Lambda.rho_code n) h ?_
    intro _ n
    exact congrArg some (Lambda.rho_code_eq n).symm
  exact hstrong.comp (Primrec.const ()) Primrec.id

------------------------------------------------------------------------
-- The Gross–Knuth evaluator
------------------------------------------------------------------------

/-- One iteration step of the Gross–Knuth evaluator: stop at a fixed point of the
complete development, otherwise continue. -/
def Lambda.gk_step (c : ℕ) : ℕ ⊕ ℕ :=
  if Lambda.rho_code c = c then Sum.inl c else Sum.inr (Lambda.rho_code c)

theorem Lambda.gk_step_primrec : Primrec Lambda.gk_step := by
  have hcond : PrimrecPred (fun c : ℕ => Lambda.rho_code c = c) :=
    Primrec.eq.comp Lambda.rho_code_primrec Primrec.id
  exact Primrec.ite hcond (Primrec.sumInl.comp Primrec.id)
    (Primrec.sumInr.comp Lambda.rho_code_primrec)

/-- The Gross–Knuth evaluator: iterate the complete development to a fixed point. -/
def Lambda.eval_gk (c : ℕ) : Part ℕ :=
  PFun.fix (fun c => Part.some (Lambda.gk_step c)) c

theorem Lambda.eval_gk_partrec : Partrec Lambda.eval_gk := by
  have h : Partrec (fun c : ℕ => Part.some (Lambda.gk_step c)) :=
    Lambda.gk_step_primrec.to_comp
  exact Partrec.fix h

theorem Lambda.eval_gk_stop {c : ℕ} (h : Lambda.rho_code c = c) :
    Lambda.eval_gk c = Part.some c := by
  refine Part.eq_some_iff.mpr (PFun.fix_stop ?_)
  simp [Lambda.gk_step, h]

theorem Lambda.eval_gk_forward {c : ℕ} (h : Lambda.rho_code c ≠ c) :
    Lambda.eval_gk c = Lambda.eval_gk (Lambda.rho_code c) := by
  refine PFun.fix_fwd_eq ?_
  simp [Lambda.gk_step, h]

/-- If iterating the code-level complete development reaches a fixed point, the
evaluator returns it. -/
theorem Lambda.eval_gk_of_iterate {c d : ℕ} (k : ℕ) (h : Lambda.rho_code^[k] c = d)
    (hd : Lambda.rho_code d = d) : Lambda.eval_gk c = Part.some d := by
  induction k generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply] at h
      subst h
      exact Lambda.eval_gk_stop hd
  | succ k ih =>
      by_cases hc : Lambda.rho_code c = c
      · have : Lambda.rho_code^[k + 1] c = c := by
          simpa [hc] using Function.iterate_fixed hc (k + 1)
        rw [this] at h
        subst h
        exact Lambda.eval_gk_stop hc
      · rw [Lambda.eval_gk_forward hc]
        exact ih (by rwa [← Function.iterate_succ_apply])

------------------------------------------------------------------------
-- Soundness of the Gross–Knuth evaluator
------------------------------------------------------------------------

theorem Lambda.eval_gk_sound_aux (c c' : ℕ) (h : c' ∈ Lambda.eval_gk c) :
    ∀ t, Lambda.encode t = c → ∃ u, Lambda.encode u = c' ∧ Lambda.reduces t u := by
  refine PFun.fixInduction h ?_
  intro a ha ih t hta
  by_cases hfix : Lambda.rho_code a = a
  · have hval : c' = a := by
      have hmem : c' ∈ PFun.fix
          ((fun c => Lambda.gk_step c : ℕ → ℕ ⊕ ℕ) : ℕ →. ℕ ⊕ ℕ) a := ha
      rw [PFun.mem_fix_iff] at hmem
      rcases hmem with hstop | ⟨a', ha', -⟩
      · simpa [PFun.coe_val, Lambda.gk_step, hfix] using hstop
      · simp [PFun.coe_val, Lambda.gk_step, hfix] at ha'
    exact ⟨t, by rw [hta, hval], Lambda.reduces.refl t⟩
  · have hstep : Sum.inr (Lambda.rho_code a) ∈
        (fun c => Part.some (Lambda.gk_step c) : ℕ →. ℕ ⊕ ℕ) a := by
      simp [Lambda.gk_step, hfix]
    have hcode : Lambda.rho_code a = Lambda.encode (Lambda.rho t) := by
      rw [← hta, Lambda.rho_code_correct]
    obtain ⟨u, hu1, hu2⟩ := ih _ hstep (Lambda.rho t) hcode.symm
    exact ⟨u, hu1, Lambda.reduces_trans (Lambda.reduces_rho t) hu2⟩

theorem Lambda.eval_gk_sound (t : Lambda) (c' : ℕ)
    (h : Lambda.eval_gk (Lambda.encode t) = Part.some c') :
    ∃ u, Lambda.encode u = c' ∧ Lambda.reduces t u :=
  Lambda.eval_gk_sound_aux _ _ (Part.eq_some_iff.mp h) t rfl

/-- Completeness of the Gross–Knuth evaluator on terms with a normal form. -/
theorem Lambda.eval_gk_complete {t u : Lambda} (h : Lambda.reduces t u)
    (hu : Lambda.is_normal u) : Lambda.eval_gk (Lambda.encode t) = Part.some (Lambda.encode u) := by
  obtain ⟨k, hk⟩ := Lambda.rho_iterate_eq_of_reduces_normal h hu
  refine Lambda.eval_gk_of_iterate k ?_ ?_
  · rw [Lambda.rho_code_iterate_correct, hk]
  · rw [Lambda.rho_code_correct, Lambda.rho_normal hu]

/-- Normalization statement for the Gross–Knuth evaluator, in the shape of
`Lambda.EvalNormalization`: on every normalizing input the evaluator returns the
code of the normal form. -/
def Lambda.EvalNormalizationGK : Prop :=
  ∀ t u, Lambda.reduces t u → Lambda.is_normal u →
    Lambda.eval_gk (Lambda.encode t) = Part.some (Lambda.encode u)

/-- **The Gross–Knuth evaluator is normalizing**: unlike the corresponding statement
`Lambda.EvalNormalization` for the leftmost evaluator, this is a theorem. -/
theorem Lambda.evalNormalizationGK : Lambda.EvalNormalizationGK :=
  fun _ _ h hu => Lambda.eval_gk_complete h hu

/-- The correctness statement for the Gross–Knuth evaluator, in the shape of
`Lambda.EvalCorrectness`. -/
def Lambda.EvalCorrectnessGK : Prop :=
  ∀ t n, Lambda.reduces t (Lambda.church n) ↔
    Lambda.eval_gk (Lambda.encode t) = Part.some (Lambda.church_code n)

/-- **Correctness of the Gross–Knuth evaluator.**  Unlike `Lambda.EvalCorrectness`
(which is refuted by `Lambda.not_evalCorrectness`), this statement is a theorem: a term
reduces to the Church numeral `n` exactly when the evaluator returns its code. -/
theorem Lambda.evalCorrectnessGK : Lambda.EvalCorrectnessGK := by
  intro t n
  constructor
  · intro h
    rw [Lambda.eval_gk_complete h (Lambda.church_normal n), Lambda.church_code_correct]
  · intro h
    obtain ⟨u, hu1, hu2⟩ := Lambda.eval_gk_sound t _ h
    have : u = Lambda.church n :=
      Lambda.encode_injective (by rw [hu1, Lambda.church_code_correct])
    rwa [this] at hu2

------------------------------------------------------------------------
-- The unconditional bridge to `Partrec`
------------------------------------------------------------------------

/-- The partial function computed by the encoded lambda term `F_code` using the
Gross–Knuth evaluator. -/
def Lambda.compute_fun_gk (F_code : ℕ) (n : ℕ) : Part ℕ :=
  (Lambda.eval_gk (Lambda.app_code F_code (Lambda.church_code n))).bind
    (fun c => Lambda.unchurch_code c)

theorem Lambda.compute_fun_gk_partrec (F_code : ℕ) : Partrec (Lambda.compute_fun_gk F_code) := by
  refine Partrec.bind ?_ ?_
  · have h_app_code : Primrec (fun a => Lambda.app_code F_code (Lambda.church_code a)) :=
      Primrec₂.comp Lambda.app_code_primrec (Primrec.const F_code) Lambda.church_code_primrec
    exact Lambda.eval_gk_partrec.comp h_app_code.to_comp
  · have h_unchurch : Primrec Lambda.unchurch_code := Lambda.unchurch_code_primrec
    exact (Computable.ofOption Computable.id).comp (h_unchurch.to_comp.comp Computable.snd)

theorem LambdaComputable_imp_compute_fun_gk {f : ℕ →. ℕ} (hf : LambdaComputable f) :
    ∃ c, ∀ n, Lambda.compute_fun_gk c n = f n := by
  obtain ⟨F, hF⟩ := hf
  refine ⟨Lambda.encode F, fun n => ?_⟩
  have hcode : Lambda.app_code (Lambda.encode F) (Lambda.church_code n) =
      Lambda.encode (Lambda.app F (Lambda.church n)) := by
    rw [Lambda.church_code_correct, Lambda.app_code_correct]
  unfold Lambda.compute_fun_gk
  rw [hcode]
  refine Part.ext fun m => ?_
  constructor
  · intro hm
    rw [Part.mem_bind_iff] at hm
    obtain ⟨c, hc, hmem⟩ := hm
    have hu : Lambda.unchurch_code c = some m := by simpa using hmem
    have hce : c = Lambda.church_code m := (Lambda.unchurch_code_eq_some_iff c m).1 hu
    obtain ⟨v, hv1, hv2⟩ :=
      Lambda.eval_gk_sound _ c (Part.eq_some_iff.2 hc)
    have hvc : v = Lambda.church m := by
      refine Lambda.encode_injective ?_
      rw [hv1, hce, Lambda.church_code_correct]
    rw [hvc] at hv2
    exact Part.eq_some_iff.1 ((hF n m).2 hv2)
  · intro hm
    have hred : Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church m) :=
      (hF n m).1 (Part.eq_some_iff.2 hm)
    rw [Lambda.eval_gk_complete hred (Lambda.church_normal m)]
    simp [← Lambda.church_code_correct, Lambda.unchurch_code_correct]

/-- **Lambda-computable partial functions are partial recursive.**  Unlike
`LambdaComputable_imp_Partrec`, this version assumes no correctness hypothesis about
the code-level evaluator. -/
theorem LambdaComputable_imp_Partrec_unconditional {f : ℕ →. ℕ} (hf : LambdaComputable f) :
    Partrec f := by
  obtain ⟨c, hc⟩ := LambdaComputable_imp_compute_fun_gk hf
  exact Partrec.of_eq (Lambda.compute_fun_gk_partrec c) hc

end
