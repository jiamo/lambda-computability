import Start.SpaceMachine

/-!
# Randomized logarithmic space on the host machine

This library's own module (task `M27-HOST-RANDOMIZED-SPACE`).  It defines fair-coin machines,
acceptance probability within a clock, and the classes `HostRL` and `HostBPL` on the offline
machine of `Start/SpaceMachine.lean`, using nothing from `Start/Logspace*.lean`.

The model is the textbook probabilistic machine (Arora–Barak, *Computational Complexity*,
chapter 7; Saks 1996): in every situation at most two instructions are available, and when there
are two, each is taken with probability `1/2`.  Acceptance is by reaching an accepting state.

* `Complexity.Space.Machine.FairCoin` — at most two instructions in every situation;
* `Complexity.Space.Machine.acceptWithin` — the probability of reaching an accepting state within
  `t` steps from a configuration;
* `Complexity.Space.Machine.RunsWithin` — every run on `x` has at most `T` steps;
* `Complexity.Space.HostBPL`, `Complexity.Space.HostRL` — the classes, with the space bound of
  `LOGSPACE` on every reachable configuration and a polynomial time bound on every run.
-/

set_option autoImplicit false

namespace Complexity.Space

open Complexity (PolyBound)

namespace Machine

/-- A fair-coin machine offers at most two instructions in every situation. -/
def FairCoin (M : Machine) : Prop := ∀ q a b, (M.delta q a b).length ≤ 2

/-- The probability of reaching an accepting state within `t` steps from `c`: an accepting
state counts `1`, a halting non-accepting configuration `0`, a single instruction is followed,
and two instructions are each followed with probability `1/2`. -/
def acceptWithin (M : Machine) (x : List Bool) : ℕ → Config → ℚ
  | 0, c => if M.accept c.state then 1 else 0
  | t + 1, c =>
      if M.accept c.state then 1 else
      match M.stepList x c with
      | [] => 0
      | [c'] => M.acceptWithin x t c'
      | c₁ :: c₂ :: _ => (M.acceptWithin x t c₁ + M.acceptWithin x t c₂) / 2

/-- Every run of `M` on `x` has at most `T` steps. -/
def RunsWithin (M : Machine) (x : List Bool) (T : ℕ) : Prop :=
  ∀ c, ¬ Reach.steps (M.Step x) (T + 1) init c

end Machine

/-- **Host bounded-error randomized logarithmic space.** -/
def HostBPL (A : Language) : Prop :=
  ∃ (M : Machine) (a : ℕ) (T : ℕ → ℕ),
    M.WellFormed ∧ M.FairCoin ∧ PolyBound T ∧
    M.SpaceBounded (fun n => a * (Nat.log 2 (n + 1) + 1)) ∧
    ∀ x, M.RunsWithin x (T x.length) ∧
      (A x → (2 / 3 : ℚ) ≤ M.acceptWithin x (T x.length) init) ∧
      (¬ A x → M.acceptWithin x (T x.length) init ≤ 1 / 3)

/-- **Host one-sided-error randomized logarithmic space.** -/
def HostRL (A : Language) : Prop :=
  ∃ (M : Machine) (a : ℕ) (T : ℕ → ℕ),
    M.WellFormed ∧ M.FairCoin ∧ PolyBound T ∧
    M.SpaceBounded (fun n => a * (Nat.log 2 (n + 1) + 1)) ∧
    ∀ x, M.RunsWithin x (T x.length) ∧
      (A x → (1 / 2 : ℚ) ≤ M.acceptWithin x (T x.length) init) ∧
      (¬ A x → M.acceptWithin x (T x.length) init = 0)

end Complexity.Space
