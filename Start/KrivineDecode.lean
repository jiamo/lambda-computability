/-
**The Krivine machine implements weak head reduction, step for step.**

`Start/Krivine.lean` defines the machine; this module relates it to the calculus.  A state is
*decoded* to the term it represents by unfolding its environment into its code and applying the
result to the decoded stack (`Krivine.State.decode`), and then:

* `Krivine.Trans.decode_eq` — the two administrative transitions do not change the decoding:
  they only move the sharing around;
* `Krivine.Trans.decode_wstep` — a `beta` transition performs exactly one **weak head** β-step
  of the decoded term;
* `Krivine.Run.decode_starN`, `Krivine.Run.decode_reducesIn` — a run of the machine with `b` β
  transitions is a weak head reduction of exactly `b` steps;
* `Krivine.IsFinal.isWhnf_decode` — a final state decodes to a weak head normal form, so
  `Krivine.eval_sound`: what the machine returns is reached from the initial term in as many β
  steps as it made β transitions.

The converse — that the machine finds the weak head normal form whenever there is one — is
`Krivine.exists_final_of_whnIn`: the two administrative transitions cannot go on forever, because
`app` shrinks the code and `var` descends into a structurally shallower environment
(`Krivine.envDepth`), so between two β transitions the machine always comes back to rest.
Together the two directions are the bisimulation between the machine and the weak head strategy
of `Start/WeakHead.lean`.
-/

import Start.Krivine
import Start.ParallelSubst
import Start.WeakHead

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Krivine

/-! ### Decoding a state -/

mutual

/-- The term a closure stands for: its code, with its environment substituted in. -/
def Clos.unfold : Clos → Lambda
  | Clos.mk t e => Lambda.substEnv (unfoldEnv e) t

/-- The parallel substitution an environment stands for; the indices it does not bind are
shifted down, as the machine leaves them free. -/
def unfoldEnv : Env → ℕ → Lambda
  | [], i => Lambda.var i
  | c :: _, 0 => Clos.unfold c
  | _ :: e, i + 1 => unfoldEnv e i

end

@[simp] theorem Clos.unfold_mk (t : Lambda) (e : Env) :
    (Clos.mk t e).unfold = Lambda.substEnv (unfoldEnv e) t := rfl

@[simp] theorem unfoldEnv_nil (i : ℕ) : unfoldEnv [] i = Lambda.var i := rfl
@[simp] theorem unfoldEnv_cons_zero (c : Clos) (e : Env) : unfoldEnv (c :: e) 0 = c.unfold := rfl
@[simp] theorem unfoldEnv_cons_succ (c : Clos) (e : Env) (i : ℕ) :
    unfoldEnv (c :: e) (i + 1) = unfoldEnv e i := rfl

theorem unfoldEnv_cons (c : Clos) (e : Env) :
    unfoldEnv (c :: e) = Lambda.envScons c.unfold (unfoldEnv e) := by
  funext i
  cases i <;> rfl

/-- Looking a variable up in the environment is reading off the decoding. -/
theorem unfoldEnv_of_getElem? {e : Env} {n : ℕ} {c : Clos} (h : e[n]? = some c) :
    unfoldEnv e n = c.unfold := by
  induction e generalizing n with
  | nil => simp at h
  | cons d e ih =>
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some_inj] at h
          subst h
          rfl
      | succ n =>
          simp only [List.getElem?_cons_succ] at h
          simpa using ih h

/-- The spine of applications a stack stands for. -/
def spine (t : Lambda) : List Clos → Lambda
  | [] => t
  | c :: π => spine (Lambda.app t c.unfold) π

@[simp] theorem spine_nil (t : Lambda) : spine t [] = t := rfl
@[simp] theorem spine_cons (t : Lambda) (c : Clos) (π : List Clos) :
    spine t (c :: π) = spine (Lambda.app t c.unfold) π := rfl

/-- **The term a state stands for**: the unfolded code, applied to the unfolded stack. -/
def State.decode (s : State) : Lambda := spine (Clos.mk s.code s.env).unfold s.stack

@[simp] theorem State.decode_mk (t : Lambda) (e : Env) (π : List Clos) :
    State.decode ⟨t, e, π⟩ = spine (Lambda.substEnv (unfoldEnv e) t) π := rfl

@[simp] theorem State.decode_init (t : Lambda) : (State.init t).decode = t := by
  simp only [State.init, State.decode_mk, spine_nil]
  exact Lambda.substEnv_var_id t

/-! ### The simulation -/

/-- A weak head step of the head of a spine is a weak head step of the spine. -/
theorem wstep_spine {t t' : Lambda} (h : Lambda.wstep t t') (π : List Clos) :
    Lambda.wstep (spine t π) (spine t' π) := by
  induction π generalizing t t' with
  | nil => exact h
  | cons c π ih => exact ih (Lambda.wstep.app _ h)

/-- **The administrative transitions do not change the term**: they only redistribute the
sharing. -/
theorem Trans.decode_eq {l : Label} {s s' : State} (h : Trans l s s') (hl : l ≠ Label.beta) :
    s.decode = s'.decode := by
  cases h with
  | app t u e π => simp [State.decode_mk, Lambda.substEnv]
  | beta t e c π => exact absurd rfl hl
  | var n e c π hn =>
      cases c with
      | mk t' e' =>
          simp only [State.decode_mk, Clos.code_mk, Clos.env_mk, Lambda.substEnv]
          rw [unfoldEnv_of_getElem? hn]
          rfl

/-- **A `beta` transition is one weak head β-step of the decoded term.** -/
theorem Trans.decode_wstep {s s' : State} (h : Trans Label.beta s s') :
    Lambda.wstep s.decode s'.decode := by
  cases h with
  | beta t e c π =>
      simp only [State.decode_mk, Lambda.substEnv, spine_cons]
      refine wstep_spine ?_ π
      have hbeta := Lambda.wstep.beta (Lambda.substEnv (Lambda.envCons (unfoldEnv e)) t) c.unfold
      rwa [Lambda.subst_zero_substEnv, ← unfoldEnv_cons] at hbeta

/-- **The machine performs exactly the weak head steps**: a run with `b` β transitions is a weak
head reduction of `b` steps. -/
theorem Run.decode_starN {n b : ℕ} {s s' : State} (h : Run n b s s') :
    Rewriting.StarN Lambda.wstep b s.decode s'.decode := by
  induction h with
  | refl s => exact Rewriting.StarN.refl _
  | @cons l n b s₁ s₂ s₃ hstep _ ih =>
      cases l with
      | beta =>
          simpa using Rewriting.StarN.step (Trans.decode_wstep hstep) ih
      | app =>
          rw [Trans.decode_eq hstep (by simp)]
          simpa using ih
      | var =>
          rw [Trans.decode_eq hstep (by simp)]
          simpa using ih

/-- A run without β transitions does not change the decoded term. -/
theorem Run.decode_eq_of_no_beta {n b : ℕ} {s s' : State} (h : Run n b s s') (hb : b = 0) :
    s.decode = s'.decode := by
  induction h with
  | refl s => rfl
  | @cons l n' b' s₁ s₂ s₃ hstep _ ih =>
      cases l with
      | beta => simp only [Label.betaCount_beta] at hb; omega
      | app =>
          rw [Trans.decode_eq hstep (by simp)]
          exact ih (by simpa using hb)
      | var =>
          rw [Trans.decode_eq hstep (by simp)]
          exact ih (by simpa using hb)

/-- A run with `b` β transitions is a β-reduction of exactly `b` steps. -/
theorem Run.decode_reducesIn {n b : ℕ} {s s' : State} (h : Run n b s s') :
    Lambda.reducesIn b s.decode s'.decode := by
  refine Lambda.reducesIn_iff_starN.2 ?_
  exact (h.decode_starN).mono (fun _ _ hw => Lambda.wstep_imp_step hw)

/-! ### Final states -/

/-- A spine over a weak head normal form which is not an abstraction is a weak head normal
form. -/
theorem isWhnf_spine {t : Lambda} (ht : Lambda.IsWhnf t) (hnl : ∀ P, t ≠ Lambda.lam P)
    (π : List Clos) : Lambda.IsWhnf (spine t π) ∧ ∀ P, spine t π ≠ Lambda.lam P := by
  induction π generalizing t with
  | nil => exact ⟨ht, hnl⟩
  | cons c π ih =>
      refine ih (Lambda.isWhnf_app_iff.2 ⟨ht, hnl⟩) ?_
      intro P h
      exact Lambda.noConfusion h

/-- The decoding of an environment beyond what it binds is a variable. -/
theorem unfoldEnv_of_getElem?_none {e : Env} {n : ℕ} (h : e[n]? = none) :
    ∃ m, unfoldEnv e n = Lambda.var m := by
  induction e generalizing n with
  | nil => exact ⟨n, rfl⟩
  | cons d e ih =>
      cases n with
      | zero => simp at h
      | succ n =>
          simp only [List.getElem?_cons_succ] at h
          simpa using ih h

/-- **A final state decodes to a weak head normal form.** -/
theorem IsFinal.isWhnf_decode {s : State} (h : IsFinal s) : Lambda.IsWhnf s.decode := by
  rcases (isFinal_iff s).1 h with ⟨⟨t, ht⟩, hπ⟩ | ⟨n, hn, hnone⟩
  · obtain ⟨c, e, π⟩ := s
    simp only at ht hπ
    subst ht
    subst hπ
    simpa [State.decode_mk, Lambda.substEnv] using Lambda.isWhnf_lam _
  · obtain ⟨c, e, π⟩ := s
    simp only at hn hnone
    subst hn
    obtain ⟨m, hm⟩ := unfoldEnv_of_getElem?_none hnone
    have : Lambda.substEnv (unfoldEnv e) (Lambda.var n) = Lambda.var m := hm
    simp only [State.decode_mk, this]
    exact (isWhnf_spine (Lambda.isWhnf_var m) (fun P h => Lambda.noConfusion h) π).1

/-- **Soundness of the machine**: if the machine halts, its result is reached from the initial
term by exactly as many β-steps as it made β transitions, and it is a weak head normal form. -/
theorem eval_sound {t : Lambda} {n b : ℕ} {s : State} (h : Run n b (State.init t) s)
    (hf : IsFinal s) : Lambda.reducesIn b t s.decode ∧ Lambda.IsWhnf s.decode := by
  refine ⟨?_, hf.isWhnf_decode⟩
  have := h.decode_reducesIn
  rwa [State.decode_init] at this

/-! ### The machine always comes back to rest -/

/-- The administrative transitions terminate: from any state the machine reaches, without any β
transition, either a final state or one that is about to perform a β transition. -/
theorem exists_beta_or_final_aux (d : ℕ)
    (ihd : ∀ s : State, envDepth s.env < d →
      ∃ n s', Run n 0 s s' ∧ (IsFinal s' ∨ ∃ s'', Trans Label.beta s' s'')) :
    ∀ (m : ℕ) (s : State), envDepth s.env ≤ d → Lambda.size s.code ≤ m →
      ∃ n s', Run n 0 s s' ∧ (IsFinal s' ∨ ∃ s'', Trans Label.beta s' s'') := by
  intro m
  induction m with
  | zero =>
      intro s _ hm
      exact absurd (Lambda.size_pos s.code) (by omega)
  | succ m ih =>
      intro s hd hm
      obtain ⟨t, e, π⟩ := s
      cases t with
      | var n =>
          cases hn : e[n]? with
          | none =>
              refine ⟨0, _, Run.refl _, Or.inl ?_⟩
              exact (isFinal_iff _).2 (Or.inr ⟨n, rfl, hn⟩)
          | some c =>
              have hstep : Trans Label.var ⟨Lambda.var n, e, π⟩ ⟨c.code, c.env, π⟩ :=
                Trans.var n e c π hn
              have hlt : envDepth c.env < d := by
                have hmem : c ∈ e := mem_of_getElem? hn
                have := envDepth_env_lt hmem
                simp only at hd
                omega
              obtain ⟨k, s', hrun, hfin⟩ := ihd ⟨c.code, c.env, π⟩ hlt
              exact ⟨k + 1, s', by simpa using Run.cons hstep hrun, hfin⟩
      | app a b =>
          have hstep : Trans Label.app ⟨Lambda.app a b, e, π⟩ ⟨a, e, Clos.mk b e :: π⟩ :=
            Trans.app a b e π
          have hsize : Lambda.size a ≤ m := by
            simp only [Lambda.size] at hm ⊢
            have := Lambda.size_pos b
            omega
          obtain ⟨k, s', hrun, hfin⟩ := ih ⟨a, e, Clos.mk b e :: π⟩ hd hsize
          exact ⟨k + 1, s', by simpa using Run.cons hstep hrun, hfin⟩
      | lam t' =>
          cases π with
          | nil =>
              refine ⟨0, _, Run.refl _, Or.inl ?_⟩
              exact (isFinal_iff _).2 (Or.inl ⟨⟨t', rfl⟩, rfl⟩)
          | cons c π' =>
              exact ⟨0, _, Run.refl _, Or.inr ⟨_, Trans.beta t' e c π'⟩⟩

theorem exists_beta_or_final (s : State) :
    ∃ n s', Run n 0 s s' ∧ (IsFinal s' ∨ ∃ s'', Trans Label.beta s' s'') := by
  suffices h : ∀ d : ℕ, ∀ s : State, envDepth s.env ≤ d →
      ∃ n s', Run n 0 s s' ∧ (IsFinal s' ∨ ∃ s'', Trans Label.beta s' s'') from
    h (envDepth s.env) s le_rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
      intro s hs
      exact exists_beta_or_final_aux d
        (fun s' hs' => ih (envDepth s'.env) (by omega) s' le_rfl) (Lambda.size s.code) s hs le_rfl

/-- **Completeness of the machine**: if the term a state stands for is weak head normalising,
the machine reaches a final state, with as many β transitions as the strategy needs steps. -/
theorem exists_final_of_whnIn :
    ∀ (k : ℕ) (s : State), Lambda.WHNIn k s.decode →
      ∃ (n b : ℕ) (s' : State), Run n b s s' ∧ IsFinal s' ∧ b ≤ k := by
  intro k
  induction k with
  | zero =>
      intro s hs
      obtain ⟨n, s', hrun, hfin⟩ := exists_beta_or_final s
      rcases hfin with hfin | ⟨s'', hbeta⟩
      · exact ⟨n, 0, s', hrun, hfin, le_rfl⟩
      · exfalso
        have hdec : s.decode = s'.decode := hrun.decode_eq_of_no_beta rfl
        have : Lambda.wstep s'.decode s''.decode := Trans.decode_wstep hbeta
        rw [← hdec] at this
        exact hs _ this
  | succ k ih =>
      intro s hs
      obtain ⟨n, s', hrun, hfin⟩ := exists_beta_or_final s
      have hdec : s.decode = s'.decode := hrun.decode_eq_of_no_beta rfl
      rcases hfin with hfin | ⟨s'', hbeta⟩
      · exact ⟨n, 0, s', hrun, hfin, by omega⟩
      · have hw : Lambda.wstep s'.decode s''.decode := Trans.decode_wstep hbeta
        have hnotwhnf : ¬ Lambda.IsWhnf s.decode := by
          intro hcon
          exact hcon _ (by rw [hdec]; exact hw)
        rcases hs with hcon | ⟨u, hu, hu'⟩
        · exact absurd hcon hnotwhnf
        · have huu : u = s''.decode := by
            have : Lambda.wstep s.decode s''.decode := by rw [hdec]; exact hw
            exact Lambda.wstep_deterministic hu this
          subst huu
          obtain ⟨n', b', s₃, hrun', hfin', hle⟩ := ih s'' hu'
          have hstep : Run (n' + 1) (b' + 1) s' s₃ := by simpa using Run.cons hbeta hrun'
          exact ⟨n + (n' + 1), 0 + (b' + 1), s₃, hrun.trans hstep, hfin', by omega⟩

end Krivine
