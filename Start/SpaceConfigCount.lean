/-
Counting the configurations of a space-bounded machine, and the consequences: a space-bounded
machine has only exponentially many configurations, so an accepting run can always be taken
short, and acceptance is reachability in a finite graph.

This is the bridge between the machine model of `Start/SpaceMachine.lean` and the graph-theoretic
core of `Start/SavitchReach.lean`.  A configuration of a machine running in space `s` on an input
of length `n` is determined by its control state, the position of the input head (which the model
clamps to `0, …, n`), the contents of at most `s` work cells and the position of the work head:
`q · (n + 1) · (s + 1)² · 2 ^ s` possibilities.  Those configurations therefore form a finite
graph under the one-step relation, and everything about space-bounded computation is a statement
about that graph.

Main definitions:

* `Complexity.Space.BoundedCfg M x s` — the configurations of `M` on `x` inside the bound;
* `Complexity.Space.cfgBound M x s` — the explicit count `q · (n+1) · (s+1)² · 2 ^ s`;
* `Complexity.Space.BoundedCfg.step` — the one-step relation of the machine on them.

Main results:

* `Complexity.Space.card_boundedCfg_le` — the counting bound;
* `Complexity.Space.steps_boundedCfg` — a run of the machine is a walk in that finite graph;
* `Complexity.Space.accepts_iff_exists_reachable_accepting` — acceptance is reachability;
* `Complexity.Space.exists_short_accepting_run` — an accepting run can be taken of length less
  than the number of configurations.
-/

import Mathlib
import Start.SpaceMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

open Complexity.Reach

variable {M : Machine} {x : List Bool} {s : ℕ}

/-- The configurations of `M` on the input `x` that respect the space bound `s`: the state is one
of the machine's states, the input head is on the input or its end marker, and the work tape uses
at most `s` cells. -/
def BoundedCfg (M : Machine) (x : List Bool) (s : ℕ) : Type :=
  {c : Config // c.state < M.states ∧ c.inHead ≤ x.length ∧ c.space ≤ s}

namespace BoundedCfg

instance : DecidableEq (BoundedCfg M x s) := fun a b =>
  decidable_of_iff (a.1 = b.1) Subtype.ext_iff.symm

/-- The data a bounded configuration is made of. -/
private def code (c : BoundedCfg M x s) :
    Fin M.states × Fin (x.length + 1) × Fin (s + 1) × (Fin s → Bool) × Fin (s + 1) :=
  (⟨c.1.state, c.2.1⟩, ⟨c.1.inHead, Nat.lt_succ_of_le c.2.2.1⟩,
    ⟨c.1.tape.length, by have h := c.2.2.2; simp only [Config.space] at h; omega⟩,
    fun i => c.1.tape.getD i false,
    ⟨c.1.wHead, by have h := c.2.2.2; simp only [Config.space] at h; omega⟩)

private theorem code_injective : Function.Injective (@code M x s) := by
  rintro ⟨⟨q₁, i₁, t₁, w₁⟩, h₁⟩ ⟨⟨q₂, i₂, t₂, w₂⟩, h₂⟩ h
  simp only [code, Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨hq, hi, hlen, hget, hw⟩ := h
  have ht : t₁ = t₂ := by
    apply List.ext_getElem hlen
    intro n hn₁ hn₂
    have hns : n < s := by
      have h := h₁.2.2
      simp only [Config.space] at h
      omega
    have := congrFun hget ⟨n, hns⟩
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hn₁, hn₂] using this
  subst hq; subst hi; subst ht; subst hw
  rfl

noncomputable instance : Fintype (BoundedCfg M x s) := Fintype.ofInjective _ code_injective

/-- The one-step relation of the machine, read on the bounded configurations. -/
def step (M : Machine) (x : List Bool) (s : ℕ) (a b : BoundedCfg M x s) : Prop :=
  M.Step x a.1 b.1

instance : DecidableRel (step M x s) := fun a b =>
  inferInstanceAs (Decidable (b.1 ∈ M.stepList x a.1))

/-- The one-step relation as a Boolean function, which is what the decision procedures use. -/
def stepB (M : Machine) (x : List Bool) (s : ℕ) (a b : BoundedCfg M x s) : Bool :=
  decide (step M x s a b)

@[simp] theorem stepB_eq_true {a b : BoundedCfg M x s} :
    stepB M x s a b = true ↔ step M x s a b := by simp [stepB]

end BoundedCfg

/-- The explicit bound on the number of configurations of `M` on `x` inside space `s`. -/
def cfgBound (M : Machine) (x : List Bool) (s : ℕ) : ℕ :=
  M.states * (x.length + 1) * (s + 1) * 2 ^ s * (s + 1)

theorem card_boundedCfg_le (M : Machine) (x : List Bool) (s : ℕ) :
    Fintype.card (BoundedCfg M x s) ≤ cfgBound M x s := by
  classical
  have h := Fintype.card_le_of_injective _ (BoundedCfg.code_injective (M := M) (x := x) (s := s))
  simpa [cfgBound, Fintype.card_prod, Fintype.card_fun, mul_assoc] using h

/-! ### Runs are walks in the finite graph -/

/-- Every configuration reachable from the initial one is a bounded configuration. -/
theorem mem_boundedCfg_of_steps (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s)
    {n : ℕ} {c : Config} (h : Reach.steps (M.Step x) n init c) :
    c.state < M.states ∧ c.inHead ≤ x.length ∧ c.space ≤ s :=
  ⟨Machine.state_lt_of_steps hwf h, Machine.inHead_le_of_steps h, hsp n c h⟩

/-- The initial configuration, as a bounded configuration. -/
def initB (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s) : BoundedCfg M x s :=
  ⟨init, mem_boundedCfg_of_steps hwf hsp (n := 0) (c := init) rfl⟩

/-- A run of the machine is a walk in the graph of bounded configurations. -/
theorem steps_boundedCfg (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s) :
    ∀ (n : ℕ) {c : Config} (h : Reach.steps (M.Step x) n init c),
      Reach.steps (BoundedCfg.step M x s) n (initB hwf hsp)
        ⟨c, mem_boundedCfg_of_steps hwf hsp h⟩ := by
  intro n
  induction n with
  | zero =>
      intro c h
      cases h
      rfl
  | succ n ih =>
      rintro c ⟨m, hm, hstep⟩
      exact ⟨⟨m, mem_boundedCfg_of_steps hwf hsp hm⟩, ih hm, hstep⟩

/-- Conversely, a walk in the graph of bounded configurations is a run of the machine. -/
theorem steps_of_boundedCfg :
    ∀ (n : ℕ) (a b : BoundedCfg M x s),
      Reach.steps (BoundedCfg.step M x s) n a b → Reach.steps (M.Step x) n a.1 b.1 := by
  intro n
  induction n with
  | zero =>
      intro a b h
      cases h
      rfl
  | succ n ih =>
      rintro a b ⟨m, hm, hstep⟩
      exact ⟨m.1, ih a m hm, hstep⟩

/-- Acceptance is reachability of an accepting configuration in the finite configuration graph. -/
theorem accepts_iff_exists_reachable_accepting (hwf : M.WellFormed)
    (hsp : M.SpaceBoundedOn x s) :
    M.Accepts x ↔ ∃ (n : ℕ) (c : BoundedCfg M x s),
      Reach.steps (BoundedCfg.step M x s) n (initB hwf hsp) c ∧ M.accept c.1.state = true := by
  constructor
  · rintro ⟨n, c, hc, hacc⟩
    exact ⟨n, ⟨c, mem_boundedCfg_of_steps hwf hsp hc⟩, steps_boundedCfg hwf hsp n hc, hacc⟩
  · rintro ⟨n, c, hc, hacc⟩
    exact ⟨n, c.1, steps_of_boundedCfg n _ _ hc, hacc⟩

/-- An accepting run can always be taken of length less than the number of configurations, hence
of length less than `cfgBound M x s`. -/
theorem exists_short_accepting_run (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s)
    (h : M.Accepts x) :
    ∃ (n : ℕ) (c : Config), n < cfgBound M x s ∧ Reach.steps (M.Step x) n init c ∧
      M.accept c.state = true := by
  classical
  obtain ⟨n, c, hc, hacc⟩ := (accepts_iff_exists_reachable_accepting hwf hsp).1 h
  obtain ⟨m, hm, hm'⟩ := Reach.exists_steps_lt_card (r := BoundedCfg.step M x s) n hc
  exact ⟨m, c.1, lt_of_lt_of_le hm (card_boundedCfg_le M x s), steps_of_boundedCfg m _ _ hm',
    hacc⟩

end Complexity.Space
