/-
Bounded reachability in a directed graph, and the midpoint recursion that Savitch's theorem runs
on.

The combinatorial content of Savitch's theorem is entirely about a directed graph: reachability
by a walk of length at most `2 ^ (k + 1)` is the same as the existence of a midpoint from which
both legs are reachable in at most `2 ^ k` steps.  That identity is what turns a search for a
walk — which naively costs one vertex of memory per edge — into a recursion of depth `k` which
only ever stores one vertex per level.  This module proves the identity, together with the two
facts that make the recursion decide reachability on a finite graph: a walk can always be
shortened to one of length less than the number of vertices, and consequently the recursion at
any depth `k` with `2 ^ k` at least the number of vertices decides reachability outright.

Main definitions:

* `Complexity.Reach.steps r n a b` — there is a walk with exactly `n` edges from `a` to `b`;
* `Complexity.Reach.reachLe r k a b` — there is a walk with at most `2 ^ k` edges;
* `Complexity.Reach.reachB r k a b` — the decision procedure: the midpoint recursion of depth `k`.

Main results:

* `Complexity.Reach.steps_add` — walks compose and decompose;
* `Complexity.Reach.reachLe_succ_iff` — the midpoint identity `reachLe (k+1) ↔ ∃ m, ...`;
* `Complexity.Reach.exists_steps_lt_card` — a walk in a finite graph shortens to one of length
  less than the number of vertices;
* `Complexity.Reach.reachB_iff` — the recursion decides bounded reachability;
* `Complexity.Reach.reachB_iff_exists_steps` — at depth `k` with `Fintype.card C ≤ 2 ^ k` it
  decides reachability outright.
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Reach

variable {C : Type*}

/-! ### Walks of a given length -/

/-- `steps r n a b` holds when there is a walk with exactly `n` edges from `a` to `b`. -/
def steps (r : C → C → Prop) : ℕ → C → C → Prop
  | 0, a, b => a = b
  | n + 1, a, b => ∃ m, steps r n a m ∧ r m b

@[simp] theorem steps_zero (r : C → C → Prop) (a b : C) : steps r 0 a b ↔ a = b := Iff.rfl

theorem steps_succ (r : C → C → Prop) (n : ℕ) (a b : C) :
    steps r (n + 1) a b ↔ ∃ m, steps r n a m ∧ r m b := Iff.rfl

@[simp] theorem steps_refl (r : C → C → Prop) (a : C) : steps r 0 a a := rfl

theorem steps_one (r : C → C → Prop) (a b : C) : steps r 1 a b ↔ r a b := by
  constructor
  · rintro ⟨m, hm, h⟩
    cases hm
    exact h
  · intro h
    exact ⟨a, rfl, h⟩

/-- Walks compose and decompose at any intermediate length. -/
theorem steps_add (r : C → C → Prop) (i j : ℕ) (a b : C) :
    steps r (i + j) a b ↔ ∃ m, steps r i a m ∧ steps r j m b := by
  induction j generalizing b with
  | zero => exact ⟨fun h => ⟨b, h, rfl⟩, fun ⟨_, hm, h⟩ => by cases h; exact hm⟩
  | succ j ih =>
      constructor
      · rintro ⟨c, hc, hcb⟩
        obtain ⟨m, hm, hmc⟩ := (ih c).1 hc
        exact ⟨m, hm, c, hmc, hcb⟩
      · rintro ⟨m, hm, c, hmc, hcb⟩
        exact ⟨c, (ih c).2 ⟨m, hm, hmc⟩, hcb⟩

/-! ### Walks as functions on indices -/

/-- A walk of length `n` from `a` to `b`, presented as a function on the indices. -/
def IsWalk (r : C → C → Prop) (n : ℕ) (f : ℕ → C) (a b : C) : Prop :=
  f 0 = a ∧ f n = b ∧ ∀ i < n, r (f i) (f (i + 1))

theorem exists_isWalk {r : C → C → Prop} {n : ℕ} {a b : C} (h : steps r n a b) :
    ∃ f : ℕ → C, IsWalk r n f a b := by
  induction n generalizing b with
  | zero =>
      exact ⟨fun _ => a, rfl, h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
      obtain ⟨m, hm, hmb⟩ := h
      obtain ⟨f, hf0, hfn, hstep⟩ := ih hm
      refine ⟨fun i => if i ≤ n then f i else b, by simpa using hf0, by simp, ?_⟩
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
      · have h1 : i ≤ n := le_of_lt hi'
        have h2 : i + 1 ≤ n := hi'
        simp only [if_pos h1, if_pos h2]
        exact hstep i hi'
      · have h2 : ¬ i + 1 ≤ i := by omega
        simp only [if_pos (le_refl i), if_neg h2]
        rw [← hfn] at hmb
        exact hmb

/-- A chain of edges along consecutive indices is a walk. -/
theorem steps_of_chain {r : C → C → Prop} (f : ℕ → C) :
    ∀ n, (∀ i < n, r (f i) (f (i + 1))) → steps r n (f 0) (f n)
  | 0, _ => rfl
  | n + 1, h => ⟨f n, steps_of_chain f n fun i hi => h i (by omega), h n (by omega)⟩

theorem steps_of_isWalk {r : C → C → Prop} {n : ℕ} {f : ℕ → C} {a b : C}
    (h : IsWalk r n f a b) : steps r n a b := by
  obtain ⟨h0, hn, hstep⟩ := h
  subst h0; subst hn
  exact steps_of_chain f n hstep

/-! ### Shortening a walk in a finite graph -/

/-- In a graph with finitely many vertices every walk shortens to one of length less than the
number of vertices. -/
theorem exists_steps_lt_card [Fintype C] {r : C → C → Prop} :
    ∀ (n : ℕ) {a b : C}, steps r n a b → ∃ m, m < Fintype.card C ∧ steps r m a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b h
    by_cases hn : n < Fintype.card C
    · exact ⟨n, hn, h⟩
    · have hn : Fintype.card C ≤ n := Nat.le_of_not_lt hn
      obtain ⟨f, hf0, hfn, hstep⟩ := exists_isWalk h
      have hcard : Fintype.card C < Fintype.card (Fin (n + 1)) := by
        simpa using Nat.lt_succ_of_le hn
      obtain ⟨i, j, hij, hfij⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (n + 1) => f i) hcard
      -- normalise so that `i < j`
      obtain ⟨i, j, hlt, hfij⟩ :
          ∃ i j : Fin (n + 1), i < j ∧ f i = f j := by
        rcases lt_or_gt_of_ne hij with h' | h'
        · exact ⟨i, j, h', hfij⟩
        · exact ⟨j, i, h', hfij.symm⟩
      set d : ℕ := (j : ℕ) - (i : ℕ) with hd
      have hd0 : 0 < d := by
        have : (i : ℕ) < (j : ℕ) := hlt
        omega
      have hjn : (j : ℕ) ≤ n := by omega
      have hij' : (i : ℕ) + d = (j : ℕ) := by omega
      refine ih (n - d) (by omega) ?_
      refine steps_of_isWalk (f := fun k => if k < (i : ℕ) then f k else f (k + d)) ?_
      refine ⟨?_, ?_, ?_⟩
      · by_cases h0 : 0 < (i : ℕ)
        · simp only [if_pos h0]
          exact hf0
        · have hi0 : (i : ℕ) = 0 := by omega
          simp only [if_neg h0]
          rw [show 0 + d = (j : ℕ) by omega, ← hfij, hi0]
          exact hf0
      · have hge : ¬ (n - d < (i : ℕ)) := by omega
        simp only [if_neg hge]
        rw [show n - d + d = n by omega, hfn]
      · intro k hk
        by_cases hki : k + 1 < (i : ℕ)
        · have hki' : k < (i : ℕ) := by omega
          simp only [if_pos hki, if_pos hki']
          exact hstep k (by omega)
        · by_cases hki2 : k < (i : ℕ)
          · have hk1 : k + 1 = (i : ℕ) := by omega
            simp only [if_pos hki2, if_neg hki]
            rw [show k + 1 + d = (j : ℕ) by omega, ← hfij, ← hk1]
            exact hstep k (by omega)
          · simp only [if_neg hki2, if_neg hki]
            rw [show k + 1 + d = (k + d) + 1 by omega]
            exact hstep (k + d) (by omega)

/-! ### Reachability within `2 ^ k` steps, and the midpoint recursion -/

/-- `reachLe r k a b` : there is a walk with at most `2 ^ k` edges from `a` to `b`. -/
def reachLe (r : C → C → Prop) (k : ℕ) (a b : C) : Prop := ∃ n ≤ 2 ^ k, steps r n a b

theorem reachLe_zero_iff (r : C → C → Prop) (a b : C) :
    reachLe r 0 a b ↔ a = b ∨ r a b := by
  constructor
  · rintro ⟨n, hn, h⟩
    interval_cases n
    · exact Or.inl h
    · exact Or.inr ((steps_one r a b).1 h)
  · rintro (h | h)
    · exact ⟨0, by simp, h⟩
    · exact ⟨1, by simp, (steps_one r a b).2 h⟩

/-- The midpoint identity: the whole point of Savitch's recursion. -/
theorem reachLe_succ_iff (r : C → C → Prop) (k : ℕ) (a b : C) :
    reachLe r (k + 1) a b ↔ ∃ m, reachLe r k a m ∧ reachLe r k m b := by
  constructor
  · rintro ⟨n, hn, h⟩
    by_cases hsmall : n ≤ 2 ^ k
    · exact ⟨b, ⟨n, hsmall, h⟩, ⟨0, Nat.zero_le _, rfl⟩⟩
    · have hsmall : 2 ^ k < n := Nat.lt_of_not_le hsmall
      have hsplit : 2 ^ k + (n - 2 ^ k) = n := by omega
      rw [← hsplit] at h
      obtain ⟨m, h1, h2⟩ := (steps_add r (2 ^ k) (n - 2 ^ k) a b).1 h
      refine ⟨m, ⟨2 ^ k, le_rfl, h1⟩, ⟨n - 2 ^ k, ?_, h2⟩⟩
      have : n ≤ 2 ^ k + 2 ^ k := by
        have : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
        omega
      omega
  · rintro ⟨m, ⟨n₁, hn₁, h₁⟩, ⟨n₂, hn₂, h₂⟩⟩
    refine ⟨n₁ + n₂, ?_, (steps_add r n₁ n₂ a b).2 ⟨m, h₁, h₂⟩⟩
    have : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    omega

/-- The decision procedure of Savitch's theorem: the midpoint recursion of depth `k`. -/
def reachB [Fintype C] [DecidableEq C] (r : C → C → Bool) : ℕ → C → C → Bool
  | 0, a, b => (a == b) || r a b
  | k + 1, a, b => decide (∃ m : C, reachB r k a m = true ∧ reachB r k m b = true)

@[simp] theorem reachB_zero [Fintype C] [DecidableEq C] (r : C → C → Bool) (a b : C) :
    reachB r 0 a b = ((a == b) || r a b) := rfl

theorem reachB_succ [Fintype C] [DecidableEq C] (r : C → C → Bool) (k : ℕ) (a b : C) :
    reachB r (k + 1) a b = true ↔ ∃ m : C, reachB r k a m = true ∧ reachB r k m b = true := by
  simp [reachB]

/-- The recursion decides reachability within `2 ^ k` steps. -/
theorem reachB_iff [Fintype C] [DecidableEq C] (r : C → C → Bool) (k : ℕ) (a b : C) :
    reachB r k a b = true ↔ reachLe (fun x y => r x y = true) k a b := by
  induction k generalizing a b with
  | zero =>
      rw [reachB_zero, reachLe_zero_iff]
      simp
  | succ k ih =>
      rw [reachB_succ, reachLe_succ_iff]
      exact exists_congr fun m => and_congr (ih a m) (ih m b)

/-- At depth `k` with `2 ^ k` at least the number of vertices, the recursion decides reachability
outright. -/
theorem reachB_iff_exists_steps [Fintype C] [DecidableEq C] (r : C → C → Bool) (k : ℕ)
    (hk : Fintype.card C ≤ 2 ^ k) (a b : C) :
    reachB r k a b = true ↔ ∃ n, steps (fun x y => r x y = true) n a b := by
  rw [reachB_iff]
  constructor
  · rintro ⟨n, _, h⟩
    exact ⟨n, h⟩
  · rintro ⟨n, h⟩
    obtain ⟨m, hm, h'⟩ := exists_steps_lt_card n h
    exact ⟨m, by omega, h'⟩

end Complexity.Reach
