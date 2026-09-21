/-
**The formula of the reduction is closed.**

`Start/QbfMachine.lean` builds, for a machine running in space `s` on an input `x`, a quantified
Boolean formula `machineF M x s` whose value is the acceptance of `x`.  To speak of it as an
instance of `Complexity.Qbf.TQBF` — the *true closed* quantified Boolean formulas — one has to
know that it has no free variable.  This module proves that, by tracking which variables each
piece of the construction can leave free.

Everything is stated in terms of blocks: `Complexity.Qbf.QBF.InBlock m a i` says that the variable
`i` is one of the `m` variables of block `a`.  The constant `tt` that closes a conjunction over a
list mentions the variable `0`, so every bound below carries the extra alternative `i = 0`; in the
final formula that variable lies in block `0`, which is quantified away with the rest.

Main definitions:

* `Complexity.Qbf.QBF.InBlock` — a variable belongs to a block.

Main results:

* `Complexity.Qbf.QBF.mem_free_exBits`, `.mem_free_allBits` — quantifying over a block removes its
  variables;
* `Complexity.Qbf.QBF.mem_free_reachF` — the reachability formula is free only in its two endpoint
  blocks (and the variable `0`);
* `Complexity.Qbf.QBF.mem_free_stepF`, `.mem_free_initF`, `.mem_free_accF` — likewise for the
  formulas of the machine;
* `Complexity.Qbf.QBF.closed_machineF` — **the formula of the reduction is closed**;
* `Complexity.Qbf.QBF.tqbf_machineF_iff` — hence it is a true quantified Boolean formula exactly
  when the machine accepts the input.
-/

import Mathlib
import Start.QbfMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

open Complexity.Space

variable {M : Machine} {x : List Bool} {s : ℕ}

/-- The variable `i` is one of the `m` variables of block `a`. -/
def InBlock (m a i : ℕ) : Prop := a * m ≤ i ∧ i < (a + 1) * m

theorem inBlock_iff_lt_of_zero (m i : ℕ) : InBlock m 0 i ↔ i < m := by
  simp [InBlock]

/-! ### Free variables of the generic constructions -/

theorem free_tt : tt.free = [0, 0] := rfl

theorem free_ff : ff.free = [0, 0] := rfl

theorem free_litF (i : ℕ) (b : Bool) : (litF i b).free = [i] := by
  cases b <;> rfl

theorem mem_free_litF {i j : ℕ} {b : Bool} (h : j ∈ (litF i b).free) : j = i := by
  rw [free_litF] at h
  simpa using h

theorem mem_free_iffVar {a b j : ℕ} (h : j ∈ (iffVar a b).free) : j = a ∨ j = b := by
  simp only [iffVar, free, List.mem_append, List.mem_singleton] at h
  tauto

theorem mem_free_conjAll : ∀ {ps : List QBF} {i : ℕ}, i ∈ (conjAll ps).free →
    i = 0 ∨ ∃ p ∈ ps, i ∈ p.free
  | [], i, h => by
      rw [conjAll, free_tt] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact Or.inl (by tauto)
  | p :: ps, i, h => by
      simp only [conjAll, free, List.mem_append] at h
      rcases h with h | h
      · exact Or.inr ⟨p, List.mem_cons_self .., h⟩
      · rcases mem_free_conjAll h with h | ⟨q, hq, hq'⟩
        · exact Or.inl h
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hq'⟩

theorem mem_free_disjAny : ∀ {ps : List QBF} {i : ℕ}, i ∈ (disjAny ps).free →
    i = 0 ∨ ∃ p ∈ ps, i ∈ p.free
  | [], i, h => by
      rw [disjAny, free_ff] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact Or.inl (by tauto)
  | p :: ps, i, h => by
      simp only [disjAny, free, List.mem_append] at h
      rcases h with h | h
      · exact Or.inr ⟨p, List.mem_cons_self .., h⟩
      · rcases mem_free_disjAny h with h | ⟨q, hq, hq'⟩
        · exact Or.inl h
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hq'⟩

theorem mem_free_exBits {o n : ℕ} {p : QBF} {i : ℕ} (h : i ∈ (exBits o n p).free) :
    i ∈ p.free ∧ (i < o ∨ o + n ≤ i) := by
  induction n generalizing o with
  | zero => exact ⟨h, by omega⟩
  | succ n ih =>
      simp only [exBits, free, List.mem_filter, ne_eq, decide_not, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not] at h
      obtain ⟨h₁, h₂⟩ := h
      obtain ⟨h₃, h₄⟩ := ih h₁
      exact ⟨h₃, by omega⟩

theorem mem_free_allBits {o n : ℕ} {p : QBF} {i : ℕ} (h : i ∈ (allBits o n p).free) :
    i ∈ p.free ∧ (i < o ∨ o + n ≤ i) := by
  induction n generalizing o with
  | zero => exact ⟨h, by omega⟩
  | succ n ih =>
      simp only [allBits, free, List.mem_filter, ne_eq, decide_not, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not] at h
      obtain ⟨h₁, h₂⟩ := h
      obtain ⟨h₃, h₄⟩ := ih h₁
      exact ⟨h₃, by omega⟩

theorem mem_free_eqBlock {m a b i : ℕ} (h : i ∈ (eqBlock m a b).free) :
    i = 0 ∨ InBlock m a i ∨ InBlock m b i := by
  rcases mem_free_conjAll h with h | ⟨p, hp, hp'⟩
  · exact Or.inl h
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hp
    have hlm : l < m := List.mem_range.1 hl
    have ha : (a + 1) * m = a * m + m := by ring
    have hb : (b + 1) * m = b * m + m := by ring
    rcases mem_free_iffVar hp' with rfl | rfl
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)

theorem mem_free_imp {p q : QBF} {i : ℕ} (h : i ∈ (imp p q).free) :
    i ∈ p.free ∨ i ∈ q.free := by
  simp only [imp, free, List.mem_append] at h
  exact h

/-! ### Free variables of the reachability formula -/

theorem mem_free_reachF {stepF : ℕ → ℕ → QBF} {m : ℕ}
    (hstep : ∀ u v i, i ∈ (stepF u v).free → i = 0 ∨ InBlock m u i ∨ InBlock m v i) :
    ∀ (k a b t : ℕ), a < t → b < t → ∀ i, i ∈ (reachF stepF m k a b t).free →
      i = 0 ∨ InBlock m a i ∨ InBlock m b i := by
  intro k
  induction k with
  | zero =>
      intro a b t _ _ i hi
      rw [reachF_zero] at hi
      simp only [free, List.mem_append] at hi
      rcases hi with hi | hi
      · exact mem_free_eqBlock hi
      · exact hstep a b i hi
  | succ k ih =>
      intro a b t ha hb i hi
      rw [reachF_succ] at hi
      obtain ⟨hi, hq0⟩ := mem_free_exBits hi
      obtain ⟨hi, hq1⟩ := mem_free_allBits hi
      obtain ⟨hi, hq2⟩ := mem_free_allBits hi
      have e0 : (t + 1) * m = t * m + m := by ring
      have e1 : (t + 2) * m = (t + 1) * m + m := by ring
      have e2 : (t + 3) * m = (t + 2) * m + m := by ring
      -- the variable `i` is outside the three scratch blocks
      have hnt : ¬ InBlock m t i := by
        rintro ⟨h₁, h₂⟩
        have : (t + 1) * m = t * m + m := e0
        omega
      have hnt1 : ¬ InBlock m (t + 1) i := by
        rintro ⟨h₁, h₂⟩
        have e1' : (t + 1 + 1) * m = (t + 1) * m + m := by ring
        omega
      have hnt2 : ¬ InBlock m (t + 2) i := by
        rintro ⟨h₁, h₂⟩
        have e2' : (t + 2 + 1) * m = (t + 2) * m + m := by ring
        omega
      rcases mem_free_imp hi with hi | hi
      · -- the guard
        simp only [free, List.mem_append] at hi
        rcases hi with (hi | hi) | (hi | hi) <;>
          rcases mem_free_eqBlock hi with h | h | h
        · exact Or.inl h
        · exact absurd h hnt1
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact absurd h hnt2
        · exact absurd h hnt
        · exact Or.inl h
        · exact absurd h hnt1
        · exact absurd h hnt
        · exact Or.inl h
        · exact absurd h hnt2
        · exact Or.inr (Or.inr h)
      · -- the recursive call
        rcases ih (t + 1) (t + 2) (t + 3) (by omega) (by omega) i hi with h | h | h
        · exact Or.inl h
        · exact absurd h hnt1
        · exact absurd h hnt2

/-! ### Free variables of the formulas of the machine -/

theorem mem_free_cfgF {a q i j v : ℕ} (h : v ∈ (cfgF M x s a q i j).free) :
    v = 0 ∨ InBlock (cfgWidth M x s) a v := by
  rcases mem_free_conjAll h with h | ⟨p, hp, hp'⟩
  · exact Or.inl h
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hp
    have hlm : l < cfgWidth M x s := List.mem_range.1 hl
    have ha : (a + 1) * cfgWidth M x s = a * cfgWidth M x s + cfgWidth M x s := by ring
    by_cases h1 : l < M.states
    · rw [if_pos h1] at hp'
      have := mem_free_litF hp'
      exact Or.inr ⟨by omega, by omega⟩
    · rw [if_neg h1] at hp'
      by_cases h2 : l < M.states + (x.length + 1)
      · rw [if_pos h2] at hp'
        have := mem_free_litF hp'
        exact Or.inr ⟨by omega, by omega⟩
      · rw [if_neg h2] at hp'
        by_cases h3 : l < M.states + (x.length + 1) + s
        · rw [if_pos h3, free_tt] at hp'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          exact Or.inl (by tauto)
        · rw [if_neg h3] at hp'
          have := mem_free_litF hp'
          exact Or.inr ⟨by omega, by omega⟩

theorem mem_free_tgtF {a b q' i' j' : ℕ} {w : Bool} {j v : ℕ}
    (h : v ∈ (tgtF M x s a b q' i' j' w j).free) :
    v = 0 ∨ InBlock (cfgWidth M x s) a v ∨ InBlock (cfgWidth M x s) b v := by
  rcases mem_free_conjAll h with h | ⟨p, hp, hp'⟩
  · exact Or.inl h
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hp
    have hlm : l < cfgWidth M x s := List.mem_range.1 hl
    have ha : (a + 1) * cfgWidth M x s = a * cfgWidth M x s + cfgWidth M x s := by ring
    have hb : (b + 1) * cfgWidth M x s = b * cfgWidth M x s + cfgWidth M x s := by ring
    by_cases h1 : l < M.states
    · rw [if_pos h1] at hp'
      have := mem_free_litF hp'
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · rw [if_neg h1] at hp'
      by_cases h2 : l < M.states + (x.length + 1)
      · rw [if_pos h2] at hp'
        have := mem_free_litF hp'
        exact Or.inr (Or.inr ⟨by omega, by omega⟩)
      · rw [if_neg h2] at hp'
        by_cases h3 : l < M.states + (x.length + 1) + s
        · rw [if_pos h3] at hp'
          by_cases h4 : l - (M.states + (x.length + 1)) = j
          · rw [if_pos h4] at hp'
            have := mem_free_litF hp'
            exact Or.inr (Or.inr ⟨by omega, by omega⟩)
          · rw [if_neg h4] at hp'
            rcases mem_free_iffVar hp' with rfl | rfl
            · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
            · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
        · rw [if_neg h3] at hp'
          have := mem_free_litF hp'
          exact Or.inr (Or.inr ⟨by omega, by omega⟩)

theorem mem_free_stepF (a b : ℕ) (v : ℕ) (h : v ∈ (stepF M x s a b).free) :
    v = 0 ∨ InBlock (cfgWidth M x s) a v ∨ InBlock (cfgWidth M x s) b v := by
  rcases mem_free_disjAny h with h | ⟨p, hp, hp'⟩
  · exact Or.inl h
  · obtain ⟨⟨q, i0, j, bit, tr⟩, hz, rfl⟩ := List.mem_map.1 hp
    obtain ⟨-, -, hj, -, -, -⟩ := mem_caseList.1 hz
    simp only [stepCase, free, List.mem_append] at hp'
    have ha : (a + 1) * cfgWidth M x s = a * cfgWidth M x s + cfgWidth M x s := by ring
    have hw : M.states + (x.length + 1) + j < cfgWidth M x s := by
      simp only [cfgWidth]; omega
    rcases hp' with (hp' | hp') | hp'
    · rcases mem_free_cfgF hp' with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have := mem_free_litF hp'
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact mem_free_tgtF hp'

theorem mem_free_initF (a v : ℕ) (h : v ∈ (initF M x s a).free) :
    v = 0 ∨ InBlock (cfgWidth M x s) a v := by
  simp only [initF, free, List.mem_append] at h
  have ha : (a + 1) * cfgWidth M x s = a * cfgWidth M x s + cfgWidth M x s := by ring
  rcases h with h | h
  · exact mem_free_cfgF h
  · rcases mem_free_conjAll h with h | ⟨p, hp, hp'⟩
    · exact Or.inl h
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hp
      have hlm : l < s := List.mem_range.1 hl
      have hw : M.states + (x.length + 1) + l < cfgWidth M x s := by
        simp only [cfgWidth]; omega
      have := mem_free_litF hp'
      exact Or.inr ⟨by omega, by omega⟩

theorem mem_free_accF (b v : ℕ) (h : v ∈ (accF M x s b).free) :
    v = 0 ∨ InBlock (cfgWidth M x s) b v := by
  rcases mem_free_disjAny h with h | ⟨p, hp, hp'⟩
  · exact Or.inl h
  · obtain ⟨z, -, rfl⟩ := List.mem_map.1 hp
    exact mem_free_cfgF hp'

/-! ### The formula of the reduction is closed -/

theorem cfgWidth_pos (M : Machine) (x : List Bool) (s : ℕ) : 0 < cfgWidth M x s := by
  simp only [cfgWidth]; omega

/-- **The formula of the reduction is closed.** -/
theorem closed_machineF (M : Machine) (x : List Bool) (s : ℕ) : (machineF M x s).Closed := by
  have hw := cfgWidth_pos M x s
  refine List.eq_nil_iff_forall_not_mem.2 fun i hi => ?_
  rw [machineF] at hi
  obtain ⟨hi, h0⟩ := mem_free_exBits hi
  obtain ⟨hi, h1⟩ := mem_free_exBits hi
  have hbound : i < 2 * cfgWidth M x s := by
    simp only [free, List.mem_append] at hi
    have h2 : (0 + 1) * cfgWidth M x s = cfgWidth M x s := by ring
    have h3 : (1 + 1) * cfgWidth M x s = 2 * cfgWidth M x s := by ring
    rcases hi with (hi | hi) | hi
    · rcases mem_free_initF 0 i hi with h | h
      · omega
      · obtain ⟨-, h⟩ := h
        omega
    · rcases mem_free_accF 1 i hi with h | h
      · omega
      · obtain ⟨-, h⟩ := h
        omega
    · rcases mem_free_reachF (m := cfgWidth M x s) (stepF := stepF M x s)
        (fun u v j hj => mem_free_stepF u v j hj) (savitchDepth M x s) 0 1 2
        (by omega) (by omega) i hi with h | h | h
      · omega
      · obtain ⟨-, h⟩ := h
        omega
      · obtain ⟨-, h⟩ := h
        omega
  omega

/-- **The formula of the reduction is a true quantified Boolean formula exactly when the machine
accepts the input.** -/
theorem tqbf_machineF_iff (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s) (hs : 0 < s) :
    TQBF (machineF M x s) ↔ M.Accepts x := by
  constructor
  · rintro ⟨-, h⟩
    exact (eval_machineF hwf hsp hs _).1 h
  · intro h
    exact ⟨closed_machineF M x s, (eval_machineF hwf hsp hs _).2 h⟩

end QBF

end Complexity.Qbf
