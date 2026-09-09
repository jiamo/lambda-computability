/-
**Polynomial invariance: the number of β-steps is a reasonable time cost model.**

`Start/KrivineDecode.lean` shows that the β transitions of the Krivine machine are exactly the
weak head β-steps of the term the machine is evaluating.  That alone does not make the number of
β-steps a *reasonable* cost measure: the machine also performs administrative transitions, and
one has to know that there are not too many of them.  This module bounds them.

The two invariants that do the work are

* `Krivine.State.maxCode` — every piece of code the machine ever holds is a subterm of the
  initial term, so its size never exceeds the initial size (`Krivine.Trans.maxCode_le`); this is
  the reason the machine can afford to keep the result shared instead of writing it down, which
  `Start/SizeExplosion.lean` shows is impossible;
* `Krivine.State.depthBound` — the structural depth of the environments, which only a β
  transition can increase, and then by one (`Krivine.Trans.depthBound_le`).

The potential `Krivine.State.potential` (the size of the code plus the depth of the environment,
weighted by the maximal code size) then decreases at every administrative transition, so their
number is controlled by the β transitions:

* `Krivine.run_length_le` — the general bound along a run;
* `Krivine.run_length_le_init` — **from the initial state on `t`, a run with `b` β transitions
  has at most `b + |t| · (1 + b · (b + 1))` transitions in all**;
* `Krivine.beta_le_length` (from `Krivine.Run.beta_le`) — and at least `b`.

So the two measures — β-steps of the calculus and transitions of the machine — are polynomially
related in the size of the initial term and in each other, which is the invariance statement for
weak head evaluation:

* `Krivine.eval_cost` — a term that the weak head strategy normalises in `k` steps is evaluated
  by the machine in at most `k` β transitions and `k + |t| · (1 + k · (k + 1))` transitions in
  all, and the result is the weak head normal form.

## Boundary

What is bounded here is the *number of transitions*.  Turning that into a bound on the running
time of an implementation needs, in addition, that a single transition can be performed in time
polynomial in the size of the machine state on a concrete machine model; that half is not
formalised here, and the library's machine models (`Start/CookLevin.lean` and the Cobham terms)
are not connected to the Krivine machine.
-/

import Start.KrivineDecode

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Krivine

/-! ### The code the machine holds -/

mutual

/-- The largest piece of code inside a closure. -/
def Clos.maxCode : Clos → ℕ
  | Clos.mk t e => max (Lambda.size t) (envMaxCode e)

/-- The largest piece of code inside a list of closures. -/
def envMaxCode : List Clos → ℕ
  | [] => 0
  | c :: e => max (Clos.maxCode c) (envMaxCode e)

end

@[simp] theorem Clos.maxCode_mk (t : Lambda) (e : Env) :
    (Clos.mk t e).maxCode = max (Lambda.size t) (envMaxCode e) := rfl

@[simp] theorem envMaxCode_nil : envMaxCode [] = 0 := rfl

@[simp] theorem envMaxCode_cons (c : Clos) (e : List Clos) :
    envMaxCode (c :: e) = max c.maxCode (envMaxCode e) := rfl

theorem maxCode_le_envMaxCode {c : Clos} {e : List Clos} (h : c ∈ e) :
    c.maxCode ≤ envMaxCode e := by
  induction e with
  | nil => cases h
  | cons d e ih =>
      rcases List.mem_cons.1 h with rfl | hmem
      · simp only [envMaxCode_cons]
        omega
      · have := ih hmem
        simp only [envMaxCode_cons]
        omega

/-- The largest piece of code a state holds. -/
def State.maxCode (s : State) : ℕ :=
  max (Lambda.size s.code) (max (envMaxCode s.env) (envMaxCode s.stack))

@[simp] theorem State.maxCode_mk (t : Lambda) (e : Env) (π : List Clos) :
    State.maxCode ⟨t, e, π⟩ = max (Lambda.size t) (max (envMaxCode e) (envMaxCode π)) := rfl

@[simp] theorem State.maxCode_init (t : Lambda) : (State.init t).maxCode = Lambda.size t := by
  simp [State.init, State.maxCode]

/-- **The code stays small**: no transition ever produces a piece of code larger than one the
machine already held. -/
theorem Trans.maxCode_le {l : Label} {s s' : State} (h : Trans l s s') :
    s'.maxCode ≤ s.maxCode := by
  cases h with
  | app t u e π =>
      simp only [State.maxCode_mk, envMaxCode_cons, Clos.maxCode_mk, Lambda.size_app]
      omega
  | beta t e c π =>
      simp only [State.maxCode_mk, envMaxCode_cons, Lambda.size_lam]
      omega
  | var n e c π hn =>
      have hmem : c ∈ e := mem_of_getElem? hn
      have hc : c.maxCode ≤ envMaxCode e := maxCode_le_envMaxCode hmem
      cases c with
      | mk t' e' =>
          simp only [State.maxCode_mk, Clos.code_mk, Clos.env_mk, Clos.maxCode_mk] at hc ⊢
          omega

theorem Run.maxCode_le {n b : ℕ} {s s' : State} (h : Run n b s s') :
    s'.maxCode ≤ s.maxCode := by
  induction h with
  | refl s => exact le_rfl
  | cons hstep _ ih => exact le_trans ih hstep.maxCode_le

theorem State.size_code_le_maxCode (s : State) : Lambda.size s.code ≤ s.maxCode := by
  simp only [State.maxCode]
  omega

/-! ### The depth of the environments -/

/-- The depth of the deepest closure on a stack. -/
def maxClosDepth : List Clos → ℕ
  | [] => 0
  | c :: π => max c.depth (maxClosDepth π)

@[simp] theorem maxClosDepth_nil : maxClosDepth [] = 0 := rfl

@[simp] theorem maxClosDepth_cons (c : Clos) (π : List Clos) :
    maxClosDepth (c :: π) = max c.depth (maxClosDepth π) := rfl

/-- A bound on the depth of everything the state holds. -/
def State.depthBound (s : State) : ℕ := max (envDepth s.env) (maxClosDepth s.stack)

@[simp] theorem State.depthBound_mk (t : Lambda) (e : Env) (π : List Clos) :
    State.depthBound ⟨t, e, π⟩ = max (envDepth e) (maxClosDepth π) := rfl

@[simp] theorem State.depthBound_init (t : Lambda) : (State.init t).depthBound = 0 := by
  simp [State.init, State.depthBound]

/-- **Only a β transition deepens the environments**, and it deepens them by one. -/
theorem Trans.depthBound_le {l : Label} {s s' : State} (h : Trans l s s') :
    s'.depthBound ≤ s.depthBound + l.betaCount := by
  cases h with
  | app t u e π =>
      simp only [State.depthBound_mk, maxClosDepth_cons, Clos.depth_mk, Label.betaCount_app]
      omega
  | beta t e c π =>
      simp only [State.depthBound_mk, maxClosDepth_cons, envDepth_cons, Label.betaCount_beta]
      omega
  | var n e c π hn =>
      have hmem : c ∈ e := mem_of_getElem? hn
      have hc : envDepth c.env < envDepth e := envDepth_env_lt hmem
      simp only [State.depthBound_mk, Label.betaCount_var]
      omega

/-! ### The potential of a state -/

/-- The potential of a state, weighted by a bound `S` on the code it holds: every administrative
transition makes it strictly smaller. -/
def State.potential (S : ℕ) (s : State) : ℕ := Lambda.size s.code + S * envDepth s.env

@[simp] theorem State.potential_init (S : ℕ) (t : Lambda) :
    State.potential S (State.init t) = Lambda.size t := by
  simp [State.init, State.potential]

/-- An administrative transition strictly decreases the potential. -/
theorem Trans.potential_lt {l : Label} {s s' : State} (h : Trans l s s') (hl : l ≠ Label.beta)
    {S : ℕ} (hS : s.maxCode ≤ S) :
    State.potential S s' + 1 ≤ State.potential S s := by
  cases h with
  | app t u e π =>
      simp only [State.potential, Lambda.size_app]
      have := Lambda.size_pos u
      omega
  | beta t e c π => exact absurd rfl hl
  | var n e c π hn =>
      have hmem : c ∈ e := mem_of_getElem? hn
      have hdepth : envDepth c.env < envDepth e := envDepth_env_lt hmem
      have hcode : Lambda.size c.code ≤ S := by
        have hc : c.maxCode ≤ envMaxCode e := maxCode_le_envMaxCode hmem
        have : Lambda.size c.code ≤ c.maxCode := by
          cases c with
          | mk t' e' => simp only [Clos.code_mk, Clos.maxCode_mk]; omega
        simp only [State.maxCode_mk] at hS
        omega
      have hmul : S * envDepth c.env + S ≤ S * envDepth e := by
        have : S * (envDepth c.env + 1) ≤ S * envDepth e := Nat.mul_le_mul_left S (by omega)
        simpa [Nat.mul_add] using this
      simp only [State.potential]
      have hpos := Lambda.size_pos (Lambda.var n)
      omega

/-- A β transition increases the potential by at most `S * (B + 1)`, where `B` bounds the depth
of the state. -/
theorem Trans.potential_beta_le {s s' : State} (h : Trans Label.beta s s')
    {S B : ℕ} (hB : s.depthBound ≤ B) :
    State.potential S s' ≤ State.potential S s + S * (B + 1) := by
  cases h with
  | beta t e c π =>
      simp only [State.depthBound_mk, maxClosDepth_cons] at hB
      have hd : envDepth (c :: e) ≤ B + 1 := by
        simp only [envDepth_cons]
        omega
      have hmul : S * envDepth (c :: e) ≤ S * (B + 1) := Nat.mul_le_mul_left S hd
      simp only [State.potential, Lambda.size_lam]
      omega

/-! ### The bound -/

/-- **The administrative transitions are polynomially many.**  Along a run with `b` β
transitions, out of a state whose code has size at most `S` and whose environments have depth at
most `B`, the machine performs at most `b + (potential) + b · S · (B + b + 1)` transitions. -/
theorem run_length_le {S : ℕ} : ∀ {n b : ℕ} {s s' : State}, Run n b s s' →
    s.maxCode ≤ S → ∀ {B : ℕ}, s.depthBound ≤ B →
      n ≤ b + State.potential S s + b * (S * (B + b + 1)) := by
  intro n b s s' h
  induction h with
  | refl s => intro _ B _; omega
  | @cons l n' b' s₁ s₂ s₃ hstep _ ih =>
      intro hS B hB
      have hS₂ : s₂.maxCode ≤ S := le_trans hstep.maxCode_le hS
      cases l with
      | app =>
          have hpot := hstep.potential_lt (by simp) hS
          have hB₂ : s₂.depthBound ≤ B := by
            have := hstep.depthBound_le
            simp only [Label.betaCount_app] at this
            omega
          have := ih hS₂ hB₂
          simp only [Label.betaCount_app, Nat.add_zero] at *
          omega
      | var =>
          have hpot := hstep.potential_lt (by simp) hS
          have hB₂ : s₂.depthBound ≤ B := by
            have := hstep.depthBound_le
            simp only [Label.betaCount_var] at this
            omega
          have := ih hS₂ hB₂
          simp only [Label.betaCount_var, Nat.add_zero] at *
          omega
      | beta =>
          have hpot := hstep.potential_beta_le (S := S) hB
          have hB₂ : s₂.depthBound ≤ B + 1 := by
            have := hstep.depthBound_le
            simp only [Label.betaCount_beta] at this
            omega
          have hih := ih hS₂ hB₂
          simp only [Label.betaCount_beta] at *
          have hstep' : b' * (S * (B + 1 + b' + 1)) + S * (B + 1)
              ≤ (b' + 1) * (S * (B + (b' + 1) + 1)) := by
            have h1 : B + 1 + b' + 1 = B + (b' + 1) + 1 := by omega
            rw [h1, Nat.succ_mul]
            have h2 : S * (B + 1) ≤ S * (B + (b' + 1) + 1) := Nat.mul_le_mul_left S (by omega)
            omega
          omega

/-- **The invariance bound**: a run of the machine on `t` with `b` β transitions has at most
`b + |t| · (1 + b · (b + 1))` transitions in all — polynomial in the size of the term and in the
number of β-steps. -/
theorem run_length_le_init {t : Lambda} {n b : ℕ} {s : State} (h : Run n b (State.init t) s) :
    n ≤ b + Lambda.size t * (1 + b * (b + 1)) := by
  have hbound := run_length_le (S := Lambda.size t) h (by simp) (B := 0) (by simp)
  simp only [State.potential_init] at hbound
  have hmul : b * (Lambda.size t * (0 + b + 1)) = Lambda.size t * (b * (b + 1)) := by ring
  rw [hmul] at hbound
  have : Lambda.size t + Lambda.size t * (b * (b + 1)) = Lambda.size t * (1 + b * (b + 1)) := by
    ring
  omega

/-- **The number of β-steps is a reasonable time cost model for weak head evaluation.**  If the
weak head strategy normalises `t` in `k` steps, the machine evaluates `t` to the weak head normal
form with at most `k` β transitions and at most `k + |t| · (1 + k · (k + 1))` transitions in all,
and the term it returns is reached from `t` by exactly as many β-steps as it made β
transitions. -/
theorem eval_cost {t : Lambda} {k : ℕ} (h : Lambda.WHNIn k t) :
    ∃ (n b : ℕ) (s : State), Run n b (State.init t) s ∧ IsFinal s ∧ b ≤ k ∧
      n ≤ b + Lambda.size t * (1 + b * (b + 1)) ∧
      Lambda.reducesIn b t s.decode ∧ Lambda.IsWhnf s.decode := by
  have hdec : Lambda.WHNIn k (State.init t).decode := by
    rwa [State.decode_init]
  obtain ⟨n, b, s, hrun, hfin, hle⟩ := exists_final_of_whnIn k (State.init t) hdec
  obtain ⟨hred, hwhnf⟩ := eval_sound hrun hfin
  exact ⟨n, b, s, hrun, hfin, hle, run_length_le_init hrun, hred, hwhnf⟩

/-! ### A worked example -/

section Example

/-- The identity, as a piece of code. -/
private def idTerm : Lambda := Lambda.lam (Lambda.var 0)

/-- The machine on `(λx. x) (λx. x)`: unload the argument, consume it, look the variable up.
Three transitions, one of them a β transition. -/
example :
    Run 3 1 (State.init (Lambda.app idTerm idTerm)) ⟨idTerm, [], []⟩ := by
  have h₁ : Trans Label.app (State.init (Lambda.app idTerm idTerm))
      ⟨idTerm, [], [Clos.mk idTerm []]⟩ := Trans.app idTerm idTerm [] []
  have h₂ : Trans Label.beta ⟨idTerm, [], [Clos.mk idTerm []]⟩
      ⟨Lambda.var 0, [Clos.mk idTerm []], []⟩ :=
    Trans.beta (Lambda.var 0) [] (Clos.mk idTerm []) []
  have h₃ : Trans Label.var ⟨Lambda.var 0, [Clos.mk idTerm []], []⟩ ⟨idTerm, [], []⟩ :=
    Trans.var 0 [Clos.mk idTerm []] (Clos.mk idTerm []) [] rfl
  have := Run.cons h₁ (Run.cons h₂ (Run.cons h₃ (Run.refl _)))
  simpa using this

/-- The final state of that run decodes to the identity, as it should. -/
example : (⟨idTerm, [], []⟩ : State).decode = idTerm := by
  simp [State.decode_mk, idTerm, Lambda.substEnv, Lambda.envCons]

end Example

end Krivine
