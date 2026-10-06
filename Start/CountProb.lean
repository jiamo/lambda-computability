/-
**Probabilities by counting.**

The interactive proofs of `Start/InteractiveProof.lean` and the sum-check game of
`Start/SumCheck.lean` measure acceptance probabilities as finite averages: the fraction of the
random strings of a prescribed length on which the verifier accepts.  No measure theory is
involved.  This module provides the counting function and the few facts about it that the
soundness proofs use.

`Complexity.cntL n E` is the number of lists of length `n` over a finite alphabet `α` on which the
Boolean test `E` holds, defined by recursion on `n` so that the induction in the soundness proofs
peels off one random symbol at a time; `Complexity.cntL_eq_card` identifies it with the cardinality
of the corresponding set of tuples.

Main definitions:

* `Complexity.sumL` — the sum of a function over all lists of length `n`;
* `Complexity.cntL` — the number of lists of length `n` satisfying a test.

Main results:

* `Complexity.cntL_eq_card` — `cntL` counts the tuples `Fin n → α` satisfying the test;
* `Complexity.sumL_append` — a sum over lists of length `n + m` splits into a sum over the first
  `n` symbols of a sum over the last `m`;
* `Complexity.cntL_le_pow`, `Complexity.cntL_mono`, `Complexity.cntL_true` — the basic bounds.
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

variable {α : Type*} [Fintype α]

/-- The sum of `f` over all lists of length `n`. -/
def sumL : ℕ → (List α → ℕ) → ℕ
  | 0, f => f []
  | n + 1, f => ∑ s : α, sumL n (fun ρ => f (s :: ρ))

/-- The number of lists of length `n` on which the test `E` holds. -/
def cntL (n : ℕ) (E : List α → Bool) : ℕ := sumL n (fun ρ => if E ρ then 1 else 0)

@[simp] theorem sumL_zero (f : List α → ℕ) : sumL 0 f = f [] := rfl

theorem sumL_succ (n : ℕ) (f : List α → ℕ) :
    sumL (n + 1) f = ∑ s : α, sumL n (fun ρ => f (s :: ρ)) := rfl

theorem cntL_succ (n : ℕ) (E : List α → Bool) :
    cntL (n + 1) E = ∑ s : α, cntL n (fun ρ => E (s :: ρ)) := rfl

theorem sumL_mono {n : ℕ} {f g : List α → ℕ} (h : ∀ ρ, f ρ ≤ g ρ) : sumL n f ≤ sumL n g := by
  induction n generalizing f g with
  | zero => exact h []
  | succ n ih => exact Finset.sum_le_sum fun s _ => ih fun ρ => h (s :: ρ)

theorem sumL_const (n : ℕ) (c : ℕ) : sumL n (fun _ : List α => c) = Fintype.card α ^ n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sumL_succ]
      simp only [ih, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      ring

theorem sumL_add (n : ℕ) (f g : List α → ℕ) :
    sumL n (fun ρ => f ρ + g ρ) = sumL n f + sumL n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
      simp only [sumL_succ, ih, Finset.sum_add_distrib]

theorem sumL_mul_left (n : ℕ) (c : ℕ) (f : List α → ℕ) :
    sumL n (fun ρ => c * f ρ) = c * sumL n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [sumL_succ, ih, Finset.mul_sum]

/-- **Splitting a sum over lists of length `n + m`.** -/
theorem sumL_append (n m : ℕ) (f : List α → ℕ) :
    sumL (n + m) f = sumL n (fun ρ₁ => sumL m (fun ρ₂ => f (ρ₁ ++ ρ₂))) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_right_comm, sumL_succ, sumL_succ]
      exact Finset.sum_congr rfl fun s _ => ih _

/-- The sum only depends on the values on lists of the right length. -/
theorem sumL_congr {n : ℕ} {f g : List α → ℕ} (h : ∀ ρ, ρ.length = n → f ρ = g ρ) :
    sumL n f = sumL n g := by
  induction n generalizing f g with
  | zero => exact h [] rfl
  | succ n ih =>
      exact Finset.sum_congr rfl fun s _ => ih fun ρ hρ => h (s :: ρ) (by simp [hρ])

theorem sumL_le_of_length {n : ℕ} {f g : List α → ℕ} (h : ∀ ρ, ρ.length = n → f ρ ≤ g ρ) :
    sumL n f ≤ sumL n g := by
  induction n generalizing f g with
  | zero => exact h [] rfl
  | succ n ih =>
      exact Finset.sum_le_sum fun s _ => ih fun ρ hρ => h (s :: ρ) (by simp [hρ])

theorem cntL_le_pow (n : ℕ) (E : List α → Bool) : cntL n E ≤ Fintype.card α ^ n := by
  have := sumL_mono (n := n) (f := fun ρ => if E ρ then 1 else 0) (g := fun _ => 1)
    (fun ρ => by split <;> simp)
  rw [sumL_const, mul_one] at this
  exact this

theorem cntL_mono {n : ℕ} {E F : List α → Bool} (h : ∀ ρ, E ρ = true → F ρ = true) :
    cntL n E ≤ cntL n F :=
  sumL_mono fun ρ => by
    by_cases hE : E ρ = true
    · simp [hE, h ρ hE]
    · simp [hE]

theorem cntL_true (n : ℕ) {E : List α → Bool} (h : ∀ ρ, ρ.length = n → E ρ = true) :
    cntL n E = Fintype.card α ^ n := by
  rw [cntL, sumL_congr (g := fun _ => 1) (fun ρ hρ => by simp [h ρ hρ]), sumL_const, mul_one]

theorem cntL_false (n : ℕ) {E : List α → Bool} (h : ∀ ρ, ρ.length = n → E ρ = false) :
    cntL n E = 0 := by
  rw [cntL, sumL_congr (g := fun _ => 0) (fun ρ hρ => by simp [h ρ hρ]), sumL_const, mul_zero]

/-- `cntL` counts the tuples `Fin n → α` on which the test holds. -/
theorem cntL_eq_card (n : ℕ) (E : List α → Bool) :
    cntL n E = (Finset.univ.filter (fun f : Fin n → α => E (List.ofFn f) = true)).card := by
  induction n generalizing E with
  | zero =>
      rw [Finset.card_filter]
      simp [cntL]
  | succ n ih =>
      rw [cntL_succ]
      simp only [ih]
      rw [← Finset.card_sigma]
      refine Finset.card_bij (fun p _ => Fin.cons p.1 p.2) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hp ⊢
        simpa [List.ofFn_succ] using hp
      · intro p _ q _ h
        have h1 := congrArg (fun f => f 0) h
        have h2 := congrArg (fun f => Fin.tail f) h
        simp only [Fin.cons_zero, Fin.tail_cons] at h1 h2
        exact Sigma.ext h1 (heq_of_eq h2)
      · intro f hf
        refine ⟨⟨f 0, Fin.tail f⟩, ?_, by simp⟩
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hf ⊢
        simp only [List.ofFn_succ] at hf
        exact hf

end Complexity
