/-
**The Krivine abstract machine: states and transitions.**

A *reasonable* time cost model for the λ-calculus has to be backed by a machine: the number of
β-steps is only a legitimate measure of time if a machine can perform them with polynomial
overhead.  `Start/SizeExplosion.lean` is the reason this is delicate — a term of linear size can
reach, in a linear number of steps, a normal form of exponential size, so the machine can never
write the result down.  The classical answer is to keep the result *shared*, as a piece of code
together with an environment, which is exactly what an environment machine does.

This module is the first of three.  It defines the machine itself, in the standard call-by-name
form (Krivine):

* `Krivine.Clos` — a **closure**: a piece of code with an environment for its free variables;
* `Krivine.State` — a state: code, environment, and a stack of arguments;
* `Krivine.Trans` — the three **transitions**, labelled (`Krivine.Label`) so that the β
  transitions can be counted separately from the administrative ones:
  `app` unloads an application onto the stack, `beta` consumes an argument, `var` looks a
  variable up in the environment;
* `Krivine.Run` — a run of the machine, counting the transitions and the β transitions
  separately; `Krivine.Run.starN` bridges it to the abstract rewriting interface of
  `Start/Rewriting.lean`.

The elementary theory proved here is what the other two modules need:

* `Krivine.Trans.deterministic` — the machine is deterministic;
* `Krivine.isFinal_iff` — a state is stuck exactly when its code is an abstraction with an empty
  stack (the result) or a variable that the environment does not bind;
* `Krivine.Clos.depth`, `Krivine.envDepth` and `Krivine.depth_lt_envDepth_of_mem` — the
  structural depth of the environments, which strictly decreases at a `var` transition; this is
  what makes the machine terminate on a weak head normalising term, and it is the source of the
  quantitative bound of `Start/KrivineBound.lean`.
-/

import Start.ReducesIn
import Start.TermSize

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Krivine

/-! ### Closures, environments and states -/

/-- A **closure**: a piece of code together with an environment binding its free variables. -/
inductive Clos where
  /-- The closure of the code `code` in the environment `env`. -/
  | mk (code : Lambda) (env : List Clos)

namespace Clos

/-- The code of a closure. -/
def code : Clos → Lambda
  | Clos.mk t _ => t

/-- The environment of a closure. -/
def env : Clos → List Clos
  | Clos.mk _ e => e

@[simp] theorem code_mk (t : Lambda) (e : List Clos) : (Clos.mk t e).code = t := rfl
@[simp] theorem env_mk (t : Lambda) (e : List Clos) : (Clos.mk t e).env = e := rfl

@[simp] theorem mk_code_env (c : Clos) : Clos.mk c.code c.env = c := by
  cases c; rfl

end Clos

/-- An **environment**: a list of closures, one for each de Bruijn index it binds. -/
abbrev Env := List Clos

/-- A **state** of the machine: the code being evaluated, an environment for its free variables,
and the stack of arguments it has been applied to. -/
structure State where
  /-- The code. -/
  code : Lambda
  /-- The environment. -/
  env : Env
  /-- The stack of arguments, outermost first. -/
  stack : List Clos

/-- The initial state on a term: no environment and no arguments. -/
def State.init (t : Lambda) : State := ⟨t, [], []⟩

@[simp] theorem State.init_code (t : Lambda) : (State.init t).code = t := rfl
@[simp] theorem State.init_env (t : Lambda) : (State.init t).env = [] := rfl
@[simp] theorem State.init_stack (t : Lambda) : (State.init t).stack = [] := rfl

/-! ### The transitions -/

/-- The three kinds of transition.  Only `beta` performs a β-step; the other two are
administrative. -/
inductive Label where
  /-- Unload an application onto the stack. -/
  | app : Label
  /-- Consume an argument: the β transition. -/
  | beta : Label
  /-- Look a variable up in the environment. -/
  | var : Label
  deriving DecidableEq

/-- The number of β-steps a transition performs: one for `beta`, none for the others. -/
def Label.betaCount : Label → ℕ
  | Label.beta => 1
  | _ => 0

@[simp] theorem Label.betaCount_beta : Label.beta.betaCount = 1 := rfl
@[simp] theorem Label.betaCount_app : Label.app.betaCount = 0 := rfl
@[simp] theorem Label.betaCount_var : Label.var.betaCount = 0 := rfl

/-- **The transitions of the Krivine machine.** -/
inductive Trans : Label → State → State → Prop
  /-- An application unloads its argument, as a closure, onto the stack. -/
  | app (t u : Lambda) (e : Env) (π : List Clos) :
      Trans Label.app ⟨Lambda.app t u, e, π⟩ ⟨t, e, Clos.mk u e :: π⟩
  /-- An abstraction consumes the top of the stack: the β transition. -/
  | beta (t : Lambda) (e : Env) (c : Clos) (π : List Clos) :
      Trans Label.beta ⟨Lambda.lam t, e, c :: π⟩ ⟨t, c :: e, π⟩
  /-- A variable is replaced by the closure the environment binds it to. -/
  | var (n : ℕ) (e : Env) (c : Clos) (π : List Clos) (h : e[n]? = some c) :
      Trans Label.var ⟨Lambda.var n, e, π⟩ ⟨c.code, c.env, π⟩

/-- One transition, with the label forgotten. -/
def Step (s s' : State) : Prop := ∃ l, Trans l s s'

theorem Step.of_trans {l : Label} {s s' : State} (h : Trans l s s') : Step s s' := ⟨l, h⟩

/-- The machine is deterministic: a state has at most one transition, with one label. -/
theorem Trans.deterministic {l l' : Label} {s s₁ s₂ : State}
    (h₁ : Trans l s s₁) (h₂ : Trans l' s s₂) : l = l' ∧ s₁ = s₂ := by
  cases h₁ with
  | app t u e π => cases h₂ with | app _ _ _ _ => exact ⟨rfl, rfl⟩
  | beta t e c π => cases h₂ with | beta _ _ _ _ => exact ⟨rfl, rfl⟩
  | var n e c π h =>
      cases h₂ with
      | var _ _ c' _ h' =>
          refine ⟨rfl, ?_⟩
          have : c = c' := by
            rw [h] at h'
            exact Option.some_inj.1 h'
          subst this
          rfl

theorem Step.deterministic {s s₁ s₂ : State} (h₁ : Step s s₁) (h₂ : Step s s₂) : s₁ = s₂ := by
  obtain ⟨_, h₁⟩ := h₁
  obtain ⟨_, h₂⟩ := h₂
  exact (Trans.deterministic h₁ h₂).2

/-! ### Final states -/

/-- A state is **final** when no transition applies. -/
def IsFinal (s : State) : Prop := ∀ s', ¬ Step s s'

/-- The final states are exactly the results (an abstraction with nothing left to consume) and
the states blocked on an unbound variable. -/
theorem isFinal_iff (s : State) :
    IsFinal s ↔
      ((∃ t, s.code = Lambda.lam t) ∧ s.stack = []) ∨
        (∃ n, s.code = Lambda.var n ∧ s.env[n]? = none) := by
  obtain ⟨t, e, π⟩ := s
  constructor
  · intro h
    cases t with
    | var n =>
        refine Or.inr ⟨n, rfl, ?_⟩
        cases hn : e[n]? with
        | none => rfl
        | some c => exact absurd (Step.of_trans (Trans.var n e c π hn)) (h _)
    | app a b => exact absurd (Step.of_trans (Trans.app a b e π)) (h _)
    | lam t' =>
        refine Or.inl ⟨⟨t', rfl⟩, ?_⟩
        cases π with
        | nil => rfl
        | cons c π' => exact absurd (Step.of_trans (Trans.beta t' e c π')) (h _)
  · rintro (⟨⟨t', ht⟩, hπ⟩ | ⟨n, hn, hnone⟩) s' ⟨l, hl⟩
    · simp only at ht hπ
      subst ht
      subst hπ
      cases hl
    · simp only at hn
      subst hn
      cases hl with
      | var m e' c π' h =>
          rw [hnone] at h
          exact absurd h.symm (Option.some_ne_none c)

/-- A state that is not final does have a transition. -/
theorem exists_step_of_not_isFinal {s : State} (h : ¬ IsFinal s) : ∃ s', Step s s' := by
  by_contra hcon
  exact h fun s' hs' => hcon ⟨s', hs'⟩

/-! ### Runs -/

/-- A **run** of the machine: `Run n b s s'` says that `s` reaches `s'` in `n` transitions, of
which `b` are β transitions. -/
inductive Run : ℕ → ℕ → State → State → Prop
  /-- The empty run. -/
  | refl (s : State) : Run 0 0 s s
  /-- One transition, followed by a run. -/
  | cons {l : Label} {n b : ℕ} {s₁ s₂ s₃ : State} :
      Trans l s₁ s₂ → Run n b s₂ s₃ → Run (n + 1) (b + l.betaCount) s₁ s₃

/-- **Bridge to the abstract rewriting interface** (`Start/Rewriting.lean`): the transitions of a
run are the counted reflexive–transitive closure of `Krivine.Step`. -/
theorem Run.starN {n b : ℕ} {s s' : State} (h : Run n b s s') : Rewriting.StarN Step n s s' := by
  induction h with
  | refl s => exact Rewriting.StarN.refl s
  | cons hstep _ ih => exact Rewriting.StarN.step (Step.of_trans hstep) ih

/-- At most one transition in `n` is a β transition. -/
theorem Run.beta_le {n b : ℕ} {s s' : State} (h : Run n b s s') : b ≤ n := by
  induction h with
  | refl s => exact le_rfl
  | @cons l _ _ _ _ _ _ _ ih =>
      cases l <;> simp only [Label.betaCount] at * <;> omega

theorem Run.single {l : Label} {s s' : State} (h : Trans l s s') : Run 1 l.betaCount s s' := by
  have := Run.cons h (Run.refl s')
  simpa using this

theorem Run.trans {n₁ b₁ n₂ b₂ : ℕ} {s₁ s₂ s₃ : State}
    (h₁ : Run n₁ b₁ s₁ s₂) (h₂ : Run n₂ b₂ s₂ s₃) : Run (n₁ + n₂) (b₁ + b₂) s₁ s₃ := by
  induction h₁ with
  | refl s => simpa using h₂
  | @cons l n b _ _ _ hstep _ ih =>
      have h := Run.cons hstep (ih h₂)
      have hn : n + n₂ + 1 = n + 1 + n₂ := by omega
      have hb : b + b₂ + l.betaCount = b + l.betaCount + b₂ := by omega
      rwa [hn, hb] at h

/-- A run is determined by its length: the machine is deterministic. -/
theorem Run.deterministic {n b b' : ℕ} {s s₁ s₂ : State}
    (h₁ : Run n b s s₁) (h₂ : Run n b' s s₂) : b = b' ∧ s₁ = s₂ := by
  induction h₁ generalizing b' s₂ with
  | refl s => cases h₂ with | refl _ => exact ⟨rfl, rfl⟩
  | cons hstep _ ih =>
      cases h₂ with
      | cons hstep' hrun' =>
          obtain ⟨hl, hs⟩ := Trans.deterministic hstep hstep'
          subst hl
          subst hs
          obtain ⟨hb, hs⟩ := ih hrun'
          exact ⟨by omega, hs⟩

/-! ### The depth of an environment -/

mutual

/-- The structural depth of a closure: the depth of its environment. -/
def Clos.depth : Clos → ℕ
  | Clos.mk _ e => envDepth e

/-- The structural depth of an environment: one more than the depth of its deepest closure. -/
def envDepth : Env → ℕ
  | [] => 0
  | c :: e => max (Clos.depth c + 1) (envDepth e)

end

@[simp] theorem Clos.depth_mk (t : Lambda) (e : Env) : (Clos.mk t e).depth = envDepth e := rfl
@[simp] theorem envDepth_nil : envDepth [] = 0 := rfl
@[simp] theorem envDepth_cons (c : Clos) (e : Env) :
    envDepth (c :: e) = max (c.depth + 1) (envDepth e) := rfl

/-- **A lookup descends**: the environment of a closure of `e` is strictly shallower than `e`.
This is what makes a `var` transition progress. -/
theorem depth_lt_envDepth_of_mem {c : Clos} {e : Env} (h : c ∈ e) : c.depth < envDepth e := by
  induction e with
  | nil => cases h
  | cons d e ih =>
      rcases List.mem_cons.1 h with rfl | hmem
      · simp only [envDepth_cons]
        omega
      · have := ih hmem
        simp only [envDepth_cons]
        omega

theorem envDepth_env_lt {c : Clos} {e : Env} (h : c ∈ e) : envDepth c.env < envDepth e := by
  have := depth_lt_envDepth_of_mem h
  cases c with
  | mk t e' => simpa using this

theorem mem_of_getElem? {e : Env} {n : ℕ} {c : Clos} (h : e[n]? = some c) : c ∈ e :=
  List.mem_of_getElem? h

end Krivine
