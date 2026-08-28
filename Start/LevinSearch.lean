/-
Levin's universal search and its optimality.

Fix a step-indexed evaluator `run p t` ("the output of program number `p` after `t` steps, if it
has halted") and a verifier `V` deciding whether a candidate output is a solution.  *Universal
search* runs, at stage `b`, every program `p ≤ b` for `2 ^ (b - p)` steps and returns the first
accepted output; the stages are then tried in turn.  The point of the construction is that the
budget is split so that program `p` gets an exponentially larger share of the time as the stage
grows, which makes the search essentially as fast as any single program:

* `Complexity.levinStage`, `Complexity.levinSearch` — the search;
* `Complexity.levinSearch_sound` — anything it returns is verified, and is really the output of
  some program;
* `Complexity.stageCost`, `Complexity.searchCost` — the number of simulated steps, with
  `Complexity.stageCost_eq`, `Complexity.searchCost_le` (`searchCost b ≤ 2 ^ (b + 2)`);
* `Complexity.levinSearch_isSome_of_run` — **completeness**: if program `p` produces an accepted
  output in `t` steps, the search has succeeded by stage `p + log₂ t + 1`;
* `Complexity.levin_optimal` — **optimality**: universal search then finds a verified solution
  within `8 * 2 ^ p * t` simulated steps, i.e. within a factor depending only on `p` — not on the
  input — of the running time of *any* program solving the problem.

Nothing here is specific to a machine model: `run` is an arbitrary step-indexed function whose
only assumed property is that a halted computation stays halted.
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Log

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

variable {α : Type*}

/-! ### The search -/

/-- Stage `b` of universal search: run every program `p ≤ b` for `2 ^ (b - p)` steps, and return
the first output accepted by `V`. -/
def levinStage (run : ℕ → ℕ → Option α) (V : α → Bool) (b : ℕ) : Option α :=
  (List.range (b + 1)).findSome? fun p =>
    (run p (2 ^ (b - p))).bind fun a => if V a then some a else none

/-- Universal search up to budget `b`: the result of the first successful stage. -/
def levinSearch (run : ℕ → ℕ → Option α) (V : α → Bool) (b : ℕ) : Option α :=
  (List.range (b + 1)).findSome? (levinStage run V)

/-! ### Soundness -/

theorem levinStage_sound {run : ℕ → ℕ → Option α} {V : α → Bool} {b : ℕ} {a : α}
    (h : levinStage run V b = some a) :
    V a = true ∧ ∃ p ≤ b, run p (2 ^ (b - p)) = some a := by
  obtain ⟨p, hp, hfp⟩ := List.exists_of_findSome?_eq_some h
  rw [List.mem_range] at hp
  rcases hrun : run p (2 ^ (b - p)) with _ | a'
  · rw [hrun] at hfp; simp at hfp
  · rw [hrun] at hfp
    by_cases hV : V a'
    · simp only [Option.bind_some, hV, if_pos] at hfp
      cases hfp
      exact ⟨hV, p, by omega, hrun⟩
    · simp [hV] at hfp

/-- Whatever universal search returns is a verified output of some program. -/
theorem levinSearch_sound {run : ℕ → ℕ → Option α} {V : α → Bool} {b : ℕ} {a : α}
    (h : levinSearch run V b = some a) : V a = true ∧ ∃ p t : ℕ, run p t = some a := by
  obtain ⟨c, _, hc⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨hV, p, _, hrun⟩ := levinStage_sound hc
  exact ⟨hV, p, 2 ^ (c - p), hrun⟩

/-! ### Completeness -/

private theorem findSome?_isSome_of_mem {β : Type*} {f : β → Option α} {l : List β} {x : β}
    (hx : x ∈ l) (hfx : (f x).isSome) : (l.findSome? f).isSome := by
  rcases h : l.findSome? f with _ | a
  · rw [List.findSome?_eq_none_iff] at h
    rw [h x hx] at hfx
    simp at hfx
  · simp

/-- **Completeness.**  If program `p` outputs an accepted `a` after `t` steps, and halted
computations stay halted, then stage `p + log₂ t + 1` of the search already succeeds. -/
theorem levinStage_isSome_of_run {run : ℕ → ℕ → Option α} {V : α → Bool}
    (hmono : ∀ (p t t' : ℕ) (a : α), t ≤ t' → run p t = some a → run p t' = some a)
    {p t : ℕ} {a : α} (hrun : run p t = some a) (hV : V a = true) :
    (levinStage run V (p + Nat.log 2 t + 1)).isSome := by
  set b := p + Nat.log 2 t + 1 with hb
  have hbp : b - p = Nat.log 2 t + 1 := by omega
  have hlt : t < 2 ^ (Nat.log 2 t + 1) := Nat.lt_pow_succ_log_self (by omega) t
  have hrun' : run p (2 ^ (b - p)) = some a := by
    refine hmono p t _ a ?_ hrun
    rw [hbp]
    omega
  refine findSome?_isSome_of_mem (x := p) ?_ ?_
  · rw [List.mem_range]; omega
  · rw [hrun']
    simp [hV]

/-- The search itself succeeds by that stage. -/
theorem levinSearch_isSome_of_run {run : ℕ → ℕ → Option α} {V : α → Bool}
    (hmono : ∀ (p t t' : ℕ) (a : α), t ≤ t' → run p t = some a → run p t' = some a)
    {p t : ℕ} {a : α} (hrun : run p t = some a) (hV : V a = true) :
    (levinSearch run V (p + Nat.log 2 t + 1)).isSome := by
  refine findSome?_isSome_of_mem (x := p + Nat.log 2 t + 1) ?_ ?_
  · rw [List.mem_range]; omega
  · exact levinStage_isSome_of_run hmono hrun hV

/-! ### Cost -/

/-- The number of steps simulated at stage `b`. -/
def stageCost (b : ℕ) : ℕ := ∑ p ∈ Finset.range (b + 1), 2 ^ (b - p)

/-- The number of steps simulated by the whole search up to budget `b`. -/
def searchCost (b : ℕ) : ℕ := ∑ c ∈ Finset.range (b + 1), stageCost c

private theorem sum_range_two_pow (n : ℕ) : (∑ k ∈ Finset.range n, 2 ^ k) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [pow_succ]
      omega

theorem stageCost_eq (b : ℕ) : stageCost b + 1 = 2 ^ (b + 1) := by
  have : stageCost b = ∑ k ∈ Finset.range (b + 1), 2 ^ k := by
    rw [stageCost, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    congr 1
    omega
  rw [this, sum_range_two_pow]

theorem stageCost_le (b : ℕ) : stageCost b ≤ 2 ^ (b + 1) := by
  have := stageCost_eq b
  omega

/-- The whole search up to budget `b` costs less than `2 ^ (b + 2)` simulated steps. -/
theorem searchCost_le (b : ℕ) : searchCost b ≤ 2 ^ (b + 2) := by
  induction b with
  | zero => simp [searchCost, stageCost]
  | succ b ih =>
      have hexp : b + 1 + 2 = b + 3 := by omega
      rw [searchCost, Finset.sum_range_succ, ← searchCost, hexp]
      have h1 : stageCost (b + 1) ≤ 2 ^ (b + 2) := stageCost_le (b + 1)
      have h2 : (2 : ℕ) ^ (b + 3) = 2 ^ (b + 2) + 2 ^ (b + 2) := by
        rw [show b + 3 = (b + 2) + 1 from rfl, pow_succ]
        omega
      omega

/-- **Levin's optimality theorem.**  If *some* program `p` produces, in `t` steps, an output the
verifier accepts, then universal search finds a verified output after simulating at most
`8 * 2 ^ p * t` steps: within a factor `8 * 2 ^ p`, depending only on the program and not on the
problem instance, of the running time of that program. -/
theorem levin_optimal {run : ℕ → ℕ → Option α} {V : α → Bool}
    (hmono : ∀ (p t t' : ℕ) (a : α), t ≤ t' → run p t = some a → run p t' = some a)
    {p t : ℕ} {a : α} (ht : t ≠ 0) (hrun : run p t = some a) (hV : V a = true) :
    ∃ a' : α, levinSearch run V (p + Nat.log 2 t + 1) = some a' ∧ V a' = true ∧
      searchCost (p + Nat.log 2 t + 1) ≤ 8 * 2 ^ p * t := by
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (levinSearch_isSome_of_run hmono hrun hV)
  refine ⟨a', ha', (levinSearch_sound ha').1, ?_⟩
  have hcost := searchCost_le (p + Nat.log 2 t + 1)
  have hlog : 2 ^ Nat.log 2 t ≤ t := Nat.pow_log_le_self 2 ht
  have hpow : (2 : ℕ) ^ (p + Nat.log 2 t + 1 + 2) = 8 * 2 ^ p * 2 ^ Nat.log 2 t := by
    rw [pow_add, pow_add]
    ring
  have : 8 * 2 ^ p * 2 ^ Nat.log 2 t ≤ 8 * 2 ^ p * t :=
    Nat.mul_le_mul_left _ hlog
  omega

end Complexity
