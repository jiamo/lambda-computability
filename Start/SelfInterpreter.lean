/-
A self-interpreter (Barendregt's *enumerator*) for the untyped lambda calculus.

The arithmetized evaluator `Lambda.eval_gk` works on *codes*: it maps the code of a term to the
code of its normal form.  What is proved here is the genuinely lambda-level statement: there is a
single closed lambda term `E` with

    E ⌜M⌝  ↠  M      for every closed term `M`,

where `⌜M⌝ = church (encode M)` is the Church numeral of the Gödel code of `M`.  Note that this is
a *reduction*, not merely a beta conversion.

The construction is the standard environment-passing interpreter, made available by the fixed-point
combinator `Lambda.Theta`:

    Ev = Θ (λ ev c e. if tag c = 0 then e (arg c)
                      else if tag c = 1 then (ev (left c) e) (ev (right c) e)
                      else λ x. ev (arg c) (extend e x))

Here `tag`, `arg`, `left`, `right` are the numeric destructors of the pairing-based encoding
`Lambda.encode`; they are computable, so `Lambda.exists_realizer_of_computable` supplies closed
lambda terms realizing them.  An *environment* is a lambda term `E` with `E (church k) ↠ u k`; the
interpreter run in the environment `u` produces the parallel substitution `Lambda.substEnv u t`
(`Lambda.selfEval_correct`).  For a closed term the environment is irrelevant, which yields the
self-interpreter `Lambda.exists_self_interpreter`.
-/

import Start.PartrecLambda
import Start.FixedPoint

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Structural closedness
------------------------------------------------------------------------

/-- `freeBelow k t` says that every free variable of `t` is `< k`; a structural rendering of
`Lambda.IsClosedAt`. -/
def freeBelow : ℕ → Lambda → Prop
  | k, Lambda.var n => n < k
  | k, Lambda.app a b => freeBelow k a ∧ freeBelow k b
  | k, Lambda.lam t => freeBelow (k + 1) t

/-- If some free variable of `t` is `≥ k`, then substituting at `k` really changes `t`. -/
theorem subst_ne_self_of_not_freeBelow :
    ∀ (t : Lambda) (k : ℕ), ¬ freeBelow k t → Lambda.subst (Lambda.var (k + 1)) k t ≠ t := by
  intro t
  induction t with
  | var n =>
      intro k h
      simp only [freeBelow, not_lt] at h
      rcases Nat.lt_or_ge k n with hn | hn
      · have hne : n ≠ k := by omega
        simp only [Lambda.subst, hne, if_false, gt_iff_lt, hn, if_true]
        intro hc
        have : n - 1 = n := by injection hc
        omega
      · have hnk : n = k := le_antisymm hn h
        subst hnk
        simp only [Lambda.subst, if_true]
        intro hc
        have : n + 1 = n := by injection hc
        omega
  | app a b iha ihb =>
      intro k h
      simp only [freeBelow, not_and_or] at h
      intro hc
      simp only [Lambda.subst, Lambda.app.injEq] at hc
      rcases h with h | h
      · exact iha k h hc.1
      · exact ihb k h hc.2
  | lam t ih =>
      intro k h
      simp only [freeBelow] at h
      intro hc
      simp only [Lambda.subst, Lambda.lift, Nat.not_lt_zero, if_false,
        Lambda.lam.injEq] at hc
      exact ih (k + 1) h hc

theorem freeBelow_of_isClosedAt {t : Lambda} {k : ℕ} (h : Lambda.IsClosedAt t k) :
    freeBelow k t := by
  by_contra hc
  exact subst_ne_self_of_not_freeBelow t k hc (h _ k (le_refl k))

theorem freeBelow_zero_of_isClosed {t : Lambda} (h : Lambda.IsClosed t) : freeBelow 0 t :=
  freeBelow_of_isClosedAt ((Lambda.IsClosedAt_zero_iff_IsClosed t).2 h)

------------------------------------------------------------------------
-- Parallel substitution
------------------------------------------------------------------------

/-- Extending an environment when passing under a binder. -/
def envCons (u : ℕ → Lambda) : ℕ → Lambda
  | 0 => Lambda.var 0
  | (k + 1) => Lambda.lift 1 0 (u k)

/-- Simultaneous (parallel) substitution of the terms `u 0, u 1, …` for the free variables of a
term. -/
def substEnv (u : ℕ → Lambda) : Lambda → Lambda
  | Lambda.var n => u n
  | Lambda.app a b => Lambda.app (substEnv u a) (substEnv u b)
  | Lambda.lam t => Lambda.lam (substEnv (envCons u) t)

theorem substEnv_var_id (t : Lambda) : substEnv (fun k => Lambda.var k) t = t := by
  have h : ∀ (t : Lambda) (u : ℕ → Lambda), (∀ k, u k = Lambda.var k) → substEnv u t = t := by
    intro t
    induction t with
    | var n => intro u hu; simp only [substEnv, hu]
    | app a b iha ihb => intro u hu; simp only [substEnv, iha u hu, ihb u hu]
    | lam t ih =>
        intro u hu
        refine congrArg Lambda.lam (ih (envCons u) ?_)
        intro k
        cases k with
        | zero => rfl
        | succ k => simp [envCons, hu, Lambda.lift]
  exact h t _ (fun _ => rfl)

theorem substEnv_congr : ∀ (t : Lambda) (k : ℕ) (u v : ℕ → Lambda), freeBelow k t →
    (∀ j, j < k → u j = v j) → substEnv u t = substEnv v t := by
  intro t
  induction t with
  | var n => intro k u v h huv; exact huv n h
  | app a b iha ihb =>
      intro k u v h huv
      simp only [substEnv, iha k u v h.1 huv, ihb k u v h.2 huv]
  | lam t ih =>
      intro k u v h huv
      refine congrArg Lambda.lam (ih (k + 1) (envCons u) (envCons v) h ?_)
      intro j hj
      cases j with
      | zero => rfl
      | succ j => simp only [envCons, huv j (by omega)]

theorem substEnv_of_isClosed {M : Lambda} (h : Lambda.IsClosed M) (u : ℕ → Lambda) :
    substEnv u M = M := by
  rw [substEnv_congr M 0 u (fun k => Lambda.var k) (freeBelow_zero_of_isClosed h)
    (by intro j hj; omega)]
  exact substEnv_var_id M

------------------------------------------------------------------------
-- Reduction is preserved by lifting
------------------------------------------------------------------------

/- `Lambda.reduces_lift` lives in `Start/Reduction.lean`, next to the parallel-reduction lemmas
it is proved from. -/

------------------------------------------------------------------------
-- A two-way branch on "is the numeral zero?"
------------------------------------------------------------------------

/-- `zeroBranch n a b` evaluates to `a` if `n` reduces to `church 0`, and to `b` if `n` reduces to
a positive Church numeral. -/
def zeroBranch (n a b : Lambda) : Lambda :=
  Lambda.app (Lambda.app (Lambda.app Lambda.isZero n) a) b

theorem zeroBranch_zero {n : Lambda} (h : Lambda.reduces n (Lambda.church 0)) (a b : Lambda) :
    Lambda.reduces (zeroBranch n a b) a := by
  have h1 : Lambda.reduces (Lambda.app Lambda.isZero n) Lambda.true :=
    Lambda.reduces_trans (Lambda.reduces_app_right h) Lambda.isZero_zero
  exact Lambda.reduces_trans (Lambda.reduces_app_left (Lambda.reduces_app_left h1))
    (Lambda.true_works a b)

theorem zeroBranch_succ {n : Lambda} {m : ℕ} (h : Lambda.reduces n (Lambda.church (m + 1)))
    (a b : Lambda) : Lambda.reduces (zeroBranch n a b) b := by
  have h1 : Lambda.reduces (Lambda.app Lambda.isZero n) Lambda.false :=
    Lambda.reduces_trans (Lambda.reduces_app_right h) (Lambda.isZero_succ m)
  exact Lambda.reduces_trans (Lambda.reduces_app_left (Lambda.reduces_app_left h1))
    (Lambda.false_works a b)

------------------------------------------------------------------------
-- The numeric destructors of the encoding
------------------------------------------------------------------------

/-- The constructor tag of a code: `0` for variables, `1` for applications, `2` for abstractions. -/
def tagOf (c : ℕ) : ℕ := c.unpair.1

/-- The argument part of a code. -/
def argOf (c : ℕ) : ℕ := c.unpair.2

/-- The code of the function part of an application code. -/
def leftOf (c : ℕ) : ℕ := (argOf c).unpair.1

/-- The code of the argument part of an application code. -/
def rightOf (c : ℕ) : ℕ := (argOf c).unpair.2

theorem tagOf_computable : Computable tagOf :=
  (Primrec.fst.comp Primrec.unpair).to_comp

theorem argOf_computable : Computable argOf :=
  (Primrec.snd.comp Primrec.unpair).to_comp

theorem leftOf_computable : Computable leftOf :=
  (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp

theorem rightOf_computable : Computable rightOf :=
  (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp

@[simp] theorem tagOf_var (n : ℕ) : tagOf (Lambda.encode (Lambda.var n)) = 0 := by
  simp [tagOf, Lambda.encode]

@[simp] theorem argOf_var (n : ℕ) : argOf (Lambda.encode (Lambda.var n)) = n := by
  simp [argOf, Lambda.encode]

@[simp] theorem tagOf_app (a b : Lambda) : tagOf (Lambda.encode (Lambda.app a b)) = 1 := by
  simp [tagOf, Lambda.encode]

@[simp] theorem leftOf_app (a b : Lambda) :
    leftOf (Lambda.encode (Lambda.app a b)) = Lambda.encode a := by
  simp [leftOf, argOf, Lambda.encode]

@[simp] theorem rightOf_app (a b : Lambda) :
    rightOf (Lambda.encode (Lambda.app a b)) = Lambda.encode b := by
  simp [rightOf, argOf, Lambda.encode]

@[simp] theorem tagOf_lam (t : Lambda) : tagOf (Lambda.encode (Lambda.lam t)) = 2 := by
  simp [tagOf, Lambda.encode]

@[simp] theorem argOf_lam (t : Lambda) :
    argOf (Lambda.encode (Lambda.lam t)) = Lambda.encode t := by
  simp [argOf, Lambda.encode]

------------------------------------------------------------------------
-- The interpreter
------------------------------------------------------------------------

/-- Extending an environment term by a new value bound to index `0`; the value is the variable
`var 0` of the enclosing abstraction, so `envExt E` is meant to be used under one binder. -/
def envExt (E : Lambda) : Lambda :=
  Lambda.lam (zeroBranch (Lambda.var 0) (Lambda.var 1)
    (Lambda.app (Lambda.lift 1 0 E) (Lambda.app Lambda.pred (Lambda.var 0))))

/-- The body of the interpreter, abstracted over the recursive call `ev` (`var 2`), the code `c`
(`var 1`) and the environment `e` (`var 0`). -/
def evStep (T A L R : Lambda) : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam
    (zeroBranch (Lambda.app T (Lambda.var 1))
      (Lambda.app (Lambda.var 0) (Lambda.app A (Lambda.var 1)))
      (zeroBranch (Lambda.app Lambda.pred (Lambda.app T (Lambda.var 1)))
        (Lambda.app
          (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.app L (Lambda.var 1))) (Lambda.var 0))
          (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.app R (Lambda.var 1))) (Lambda.var 0)))
        (Lambda.lam
          (Lambda.app (Lambda.app (Lambda.var 3) (Lambda.app A (Lambda.var 2)))
            (Lambda.lam (zeroBranch (Lambda.var 0) (Lambda.var 1)
              (Lambda.app (Lambda.var 2) (Lambda.app Lambda.pred (Lambda.var 0)))))))))))

/-- The interpreter itself. -/
def selfEval (T A L R : Lambda) : Lambda := Lambda.app Lambda.Theta (evStep T A L R)

/-- One unfolding of the interpreter on a code `c` in an environment `e`. -/
def evBody (V T A L R c e : Lambda) : Lambda :=
  zeroBranch (Lambda.app T c)
    (Lambda.app e (Lambda.app A c))
    (zeroBranch (Lambda.app Lambda.pred (Lambda.app T c))
      (Lambda.app (Lambda.app (Lambda.app V (Lambda.app L c)) e)
        (Lambda.app (Lambda.app V (Lambda.app R c)) e))
      (Lambda.lam (Lambda.app (Lambda.app V (Lambda.app A (Lambda.lift 1 0 c)))
        (envExt (Lambda.lift 1 0 e)))))

theorem evStep_closed {T A L R : Lambda} (hT : Lambda.IsClosed T) (hA : Lambda.IsClosed A)
    (hL : Lambda.IsClosed L) (hR : Lambda.IsClosed R) : Lambda.IsClosed (evStep T A L R) := by
  intro s x
  simp [evStep, zeroBranch, Lambda.subst,
    Lambda.IsClosed_imp_subst_eq hT, Lambda.IsClosed_imp_subst_eq hA,
    Lambda.IsClosed_imp_subst_eq hL, Lambda.IsClosed_imp_subst_eq hR,
    Lambda.IsClosed_imp_subst_eq Lambda.isZero_closed,
    Lambda.IsClosed_imp_subst_eq Lambda.pred_closed]

theorem selfEval_closed {T A L R : Lambda} (hT : Lambda.IsClosed T) (hA : Lambda.IsClosed A)
    (hL : Lambda.IsClosed L) (hR : Lambda.IsClosed R) : Lambda.IsClosed (selfEval T A L R) :=
  Lambda.IsClosed_app Lambda.Theta_closed (evStep_closed hT hA hL hR)

theorem selfEval_unfold {T A L R : Lambda} (hT : Lambda.IsClosed T) (hA : Lambda.IsClosed A)
    (hL : Lambda.IsClosed L) (hR : Lambda.IsClosed R) (c e : Lambda) :
    Lambda.reduces (Lambda.app (Lambda.app (selfEval T A L R) c) e)
      (evBody (selfEval T A L R) T A L R c e) := by
  have hV : Lambda.IsClosed (selfEval T A L R) := selfEval_closed hT hA hL hR
  refine Lambda.reduces_trans (Lambda.reduces_app_left (Lambda.reduces_app_left
    (Lambda.Theta_reduces (evStep T A L R)))) ?_
  change Lambda.reduces (Lambda.app (Lambda.app (Lambda.app (evStep T A L R)
    (selfEval T A L R)) c) e) _
  rw [evStep]
  refine Lambda.reduces.step _ _ _ (.app_left _ _ _ (.app_left _ _ _ (.beta _ _))) ?_
  refine Lambda.reduces.step _ _ _ (.app_left _ _ _ (.beta _ _)) ?_
  refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
  have hcl : Lambda.lift 1 0 (Lambda.lift 1 0 c) = Lambda.lift 1 1 (Lambda.lift 1 0 c) := by
    simpa using Lambda.lift_lift c 1 1 0 0 (le_refl 0)
  simp [evBody, envExt, zeroBranch, Lambda.subst, hcl, Lambda.subst_lift,
    Lambda.IsClosed_imp_subst_eq hT, Lambda.IsClosed_imp_subst_eq hA,
    Lambda.IsClosed_imp_subst_eq hL, Lambda.IsClosed_imp_subst_eq hR,
    Lambda.IsClosed_imp_subst_eq Lambda.isZero_closed,
    Lambda.IsClosed_imp_subst_eq Lambda.pred_closed,
    Lambda.IsClosed_imp_subst_eq hV, Lambda.lift_closed hV, Lambda.reduces.refl]

/-- The environment term `envExt E` behaves like the extended environment `envCons u`. -/
theorem envExt_spec {E : Lambda} {u : ℕ → Lambda}
    (hE : ∀ k, Lambda.reduces (Lambda.app E (Lambda.church k)) (u k)) (k : ℕ) :
    Lambda.reduces (Lambda.app (envExt (Lambda.lift 1 0 E)) (Lambda.church k))
      (envCons u k) := by
  have hbeta : Lambda.reduces (Lambda.app (envExt (Lambda.lift 1 0 E)) (Lambda.church k))
      (zeroBranch (Lambda.church k) (Lambda.var 0)
        (Lambda.app (Lambda.lift 1 0 E) (Lambda.app Lambda.pred (Lambda.church k)))) := by
    rw [envExt]
    refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
    simp [zeroBranch, Lambda.subst, Lambda.subst_lift,
      Lambda.IsClosed_imp_subst_eq Lambda.isZero_closed,
      Lambda.IsClosed_imp_subst_eq Lambda.pred_closed, Lambda.reduces.refl]
  refine Lambda.reduces_trans hbeta ?_
  cases k with
  | zero => exact zeroBranch_zero (Lambda.reduces.refl _) _ _
  | succ m =>
      refine Lambda.reduces_trans (zeroBranch_succ (Lambda.reduces.refl _) _ _) ?_
      have h1 : Lambda.reduces (Lambda.app Lambda.pred (Lambda.church (m + 1)))
          (Lambda.church m) := by simpa using Lambda.pred_works (m + 1)
      refine Lambda.reduces_trans (Lambda.reduces_app_right h1) ?_
      have h2 := reduces_lift (hE m) 1 0
      simpa [Lambda.lift, Lambda.lift_church, envCons] using h2

/-- **Correctness of the interpreter.**  Running the interpreter on the code of `t` in an
environment realizing `u` reduces to the parallel substitution `substEnv u t`. -/
theorem selfEval_correct {T A L R : Lambda} (hT : Lambda.Realizes T tagOf)
    (hA : Lambda.Realizes A argOf) (hL : Lambda.Realizes L leftOf)
    (hR : Lambda.Realizes R rightOf) :
    ∀ (t : Lambda) (u : ℕ → Lambda) (E : Lambda),
      (∀ k, Lambda.reduces (Lambda.app E (Lambda.church k)) (u k)) →
      Lambda.reduces (Lambda.app (Lambda.app (selfEval T A L R) (Lambda.church (Lambda.encode t)))
        E) (substEnv u t) := by
  intro t
  induction t with
  | var n =>
      intro u E hE
      refine Lambda.reduces_trans (selfEval_unfold hT.1 hA.1 hL.1 hR.1 _ _) ?_
      have htag : Lambda.reduces (Lambda.app T (Lambda.church (Lambda.encode (Lambda.var n))))
          (Lambda.church 0) := by simpa using hT.2 (Lambda.encode (Lambda.var n))
      refine Lambda.reduces_trans (zeroBranch_zero htag _ _) ?_
      have harg : Lambda.reduces (Lambda.app A (Lambda.church (Lambda.encode (Lambda.var n))))
          (Lambda.church n) := by simpa using hA.2 (Lambda.encode (Lambda.var n))
      exact Lambda.reduces_trans (Lambda.reduces_app_right harg) (hE n)
  | app a b iha ihb =>
      intro u E hE
      refine Lambda.reduces_trans (selfEval_unfold hT.1 hA.1 hL.1 hR.1 _ _) ?_
      have htag : Lambda.reduces (Lambda.app T (Lambda.church (Lambda.encode (Lambda.app a b))))
          (Lambda.church (0 + 1)) := by simpa using hT.2 (Lambda.encode (Lambda.app a b))
      refine Lambda.reduces_trans (zeroBranch_succ htag _ _) ?_
      have htag0 : Lambda.reduces (Lambda.app Lambda.pred
          (Lambda.app T (Lambda.church (Lambda.encode (Lambda.app a b))))) (Lambda.church 0) :=
        Lambda.reduces_trans (Lambda.reduces_app_right htag)
          (by simpa using Lambda.pred_works 1)
      refine Lambda.reduces_trans (zeroBranch_zero htag0 _ _) ?_
      have hl : Lambda.reduces (Lambda.app L (Lambda.church (Lambda.encode (Lambda.app a b))))
          (Lambda.church (Lambda.encode a)) := by simpa using hL.2 (Lambda.encode (Lambda.app a b))
      have hr : Lambda.reduces (Lambda.app R (Lambda.church (Lambda.encode (Lambda.app a b))))
          (Lambda.church (Lambda.encode b)) := by simpa using hR.2 (Lambda.encode (Lambda.app a b))
      refine Lambda.reduces_trans (Lambda.reduces_app
        (Lambda.reduces_app_left (Lambda.reduces_app_right hl))
        (Lambda.reduces_app_left (Lambda.reduces_app_right hr))) ?_
      exact Lambda.reduces_app (iha u E hE) (ihb u E hE)
  | lam t ih =>
      intro u E hE
      refine Lambda.reduces_trans (selfEval_unfold hT.1 hA.1 hL.1 hR.1 _ _) ?_
      have htag : Lambda.reduces (Lambda.app T (Lambda.church (Lambda.encode (Lambda.lam t))))
          (Lambda.church (1 + 1)) := by simpa using hT.2 (Lambda.encode (Lambda.lam t))
      refine Lambda.reduces_trans (zeroBranch_succ htag _ _) ?_
      have htag1 : Lambda.reduces (Lambda.app Lambda.pred
          (Lambda.app T (Lambda.church (Lambda.encode (Lambda.lam t))))) (Lambda.church (0 + 1)) :=
        Lambda.reduces_trans (Lambda.reduces_app_right htag)
          (by simpa using Lambda.pred_works 2)
      refine Lambda.reduces_trans (zeroBranch_succ htag1 _ _) ?_
      simp only [substEnv, Lambda.lift_church]
      refine Lambda.reduces_lam ?_
      have harg : Lambda.reduces (Lambda.app A (Lambda.church (Lambda.encode (Lambda.lam t))))
          (Lambda.church (Lambda.encode t)) := by simpa using hA.2 (Lambda.encode (Lambda.lam t))
      refine Lambda.reduces_trans (Lambda.reduces_app_left (Lambda.reduces_app_right harg)) ?_
      exact ih (envCons u) (envExt (Lambda.lift 1 0 E)) (fun k => envExt_spec hE k)

/-- **A self-interpreter for the lambda calculus.**  There is a closed term `E` such that for every
closed term `M`, `E ⌜M⌝` reduces to `M`, where `⌜M⌝` is the Church numeral of the code of `M`. -/
theorem exists_self_interpreter :
    ∃ E : Lambda, Lambda.IsClosed E ∧
      ∀ M : Lambda, Lambda.IsClosed M →
        Lambda.reduces (Lambda.app E (Lambda.church (Lambda.encode M))) M := by
  obtain ⟨T, hT⟩ := Lambda.exists_realizer_of_computable tagOf_computable
  obtain ⟨A, hA⟩ := Lambda.exists_realizer_of_computable argOf_computable
  obtain ⟨L, hL⟩ := Lambda.exists_realizer_of_computable leftOf_computable
  obtain ⟨R, hR⟩ := Lambda.exists_realizer_of_computable rightOf_computable
  have hV : Lambda.IsClosed (selfEval T A L R) := selfEval_closed hT.1 hA.1 hL.1 hR.1
  refine ⟨Lambda.lam (Lambda.app (Lambda.app (selfEval T A L R) (Lambda.var 0)) Lambda.I),
    ?_, ?_⟩
  · intro s x
    simp [Lambda.subst, Lambda.IsClosed_imp_subst_eq hV,
      Lambda.IsClosed_imp_subst_eq Lambda.I_closed]
  · intro M hM
    have hstep : Lambda.reduces
        (Lambda.app (Lambda.lam (Lambda.app (Lambda.app (selfEval T A L R) (Lambda.var 0))
          Lambda.I)) (Lambda.church (Lambda.encode M)))
        (Lambda.app (Lambda.app (selfEval T A L R) (Lambda.church (Lambda.encode M)))
          Lambda.I) := by
      refine Lambda.reduces.step _ _ _ (.beta _ _) ?_
      simp [Lambda.subst, Lambda.IsClosed_imp_subst_eq hV,
        Lambda.IsClosed_imp_subst_eq Lambda.I_closed, Lambda.reduces.refl]
    refine Lambda.reduces_trans hstep ?_
    have hmain := selfEval_correct hT hA hL hR M (fun k => Lambda.church k) Lambda.I
      (fun k => Lambda.I_works _)
    rwa [substEnv_of_isClosed hM] at hmain

/-- **Quoting is not lambda-definable.**  The self-interpreter cannot be inverted: no term `Q`
satisfies `Q M ↠ church (encode M)` for every closed `M`.  The reason is that reduction cannot
distinguish a term from its reducts, while the code can: `I` and `I I` reduce to one another's
common reduct but have different codes. -/
theorem not_exists_quote :
    ¬ ∃ Q : Lambda, ∀ M : Lambda, Lambda.IsClosed M →
        Lambda.reduces (Lambda.app Q M) (Lambda.church (Lambda.encode M)) := by
  rintro ⟨Q, hQ⟩
  have hII : Lambda.IsClosed (Lambda.app Lambda.I Lambda.I) :=
    Lambda.IsClosed_app Lambda.I_closed Lambda.I_closed
  have h1 := hQ Lambda.I Lambda.I_closed
  have h2 := hQ (Lambda.app Lambda.I Lambda.I) hII
  have h4 : Lambda.reduces (Lambda.app Q (Lambda.app Lambda.I Lambda.I))
      (Lambda.church (Lambda.encode Lambda.I)) :=
    Lambda.reduces_trans (Lambda.reduces_app_right (Lambda.I_works Lambda.I)) h1
  obtain ⟨t3, ha, hb⟩ := Lambda.confluence_theorem h2 h4
  have ea := Lambda.reduces_normal_eq (Lambda.church_normal _) ha
  have eb := Lambda.reduces_normal_eq (Lambda.church_normal _) hb
  have : Lambda.encode (Lambda.app Lambda.I Lambda.I) = Lambda.encode Lambda.I :=
    Lambda.church_injective (ea.trans eb.symm)
  simp [Lambda.encode, Lambda.I, Nat.pair] at this

/-- Sanity check that the self-interpreter statement is not vacuous: applied to the code of a
Church numeral, the interpreter returns that Church numeral. -/
theorem exists_self_interpreter_church :
    ∃ E : Lambda, Lambda.IsClosed E ∧
      ∀ k : ℕ, Lambda.reduces (Lambda.app E (Lambda.church (Lambda.encode (Lambda.church k))))
        (Lambda.church k) := by
  obtain ⟨E, hE, hcorrect⟩ := exists_self_interpreter
  exact ⟨E, hE, fun k => hcorrect _ (Lambda.church_closed k)⟩

end Lambda
