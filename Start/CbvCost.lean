/-
**The overhead of the CEK machine is linear.**

A run of the CEK machine of `Start/CbvMachine.lean` from a term `t` that performs `b` β
transitions performs at most `b + 3 |t| (b + 1)` transitions in total
(`CEK.run_length_le`): the administrative transitions cost at most `3 |t|` per β transition, plus
`3 |t|` to start.  With the simulation of `Start/CbvMachine.lean`, where the β transitions are
exactly the call-by-value steps, the length of a machine run is bounded linearly in the number of
call-by-value steps and in the size of the term (`CEK.run_length_le_of_cbvIn`).

The proof is a potential argument.  The measure of `Start/CbvMachine.lean`
(`3 · size(code) + Σ_{arg u} (3 · size u + 2)`) decreases with every administrative transition,
and a β transition raises it by `3 · size(body)` at most.  Codes never grow: every code met in a
run — the code being evaluated, the code of an argument frame, and the code of every closure,
however deeply nested in environments — has size at most `|t|` (`CEK.State.Bounded`), so a β
transition raises the potential by at most `3 |t|`.
-/

import Start.CbvMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace CEK

open Krivine (Clos Env)

/-! ### Codes stay small -/

/-- A closure is **bounded by `S`** when its code and, recursively, the codes of its environment
have size at most `S`. -/
inductive BoundedClos (S : ℕ) : Clos → Prop
  /-- The only rule. -/
  | mk (t : Lambda) (e : Env) : Lambda.size t ≤ S → (∀ c ∈ e, BoundedClos S c) →
      BoundedClos S (Clos.mk t e)

/-- A frame bounded by `S`. -/
def Frame.Bounded (S : ℕ) : Frame → Prop
  | .arg u e => Lambda.size u ≤ S ∧ ∀ c ∈ e, BoundedClos S c
  | .fn c => BoundedClos S c

/-- A state all of whose codes have size at most `S`. -/
def State.Bounded (S : ℕ) : State → Prop
  | .eval t e k => Lambda.size t ≤ S ∧ (∀ c ∈ e, BoundedClos S c) ∧ ∀ f ∈ k, f.Bounded S
  | .ret c k => BoundedClos S c ∧ ∀ f ∈ k, f.Bounded S

theorem State.bounded_init (t : Lambda) : (State.init t).Bounded (Lambda.size t) := by
  simp [State.init, State.Bounded]

/-- Transitions keep the codes bounded. -/
theorem Trans.bounded {S : ℕ} {l : Label} {s s' : State} (h : Trans l s s') (hs : s.Bounded S) :
    s'.Bounded S := by
  cases h with
  | app t u e k =>
      obtain ⟨ht, he, hk⟩ := hs
      simp only [Lambda.size_app] at ht
      refine ⟨by omega, he, ?_⟩
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact ⟨by omega, he⟩
      · exact hk f hf
  | lam t e k =>
      obtain ⟨ht, he, hk⟩ := hs
      exact ⟨BoundedClos.mk _ _ ht he, hk⟩
  | var n e c k hn =>
      obtain ⟨_, he, hk⟩ := hs
      exact ⟨he c (List.mem_of_getElem? hn), hk⟩
  | free n e k hn =>
      obtain ⟨ht, he, hk⟩ := hs
      exact ⟨BoundedClos.mk _ _ ht he, hk⟩
  | swap c u e k =>
      obtain ⟨hc, hk⟩ := hs
      obtain ⟨hu, he⟩ : Lambda.size u ≤ S ∧ ∀ c ∈ e, BoundedClos S c := hk (Frame.arg u e) (by simp)
      refine ⟨hu, he, ?_⟩
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hc
      · exact hk f (by simp [hf])
  | beta t e v k =>
      obtain ⟨hv, hk⟩ := hs
      have hfn : BoundedClos S (Clos.mk (.lam t) e) := hk (Frame.fn (Clos.mk (.lam t) e)) (by simp)
      cases hfn with
      | mk _ _ ht he =>
          simp only [Lambda.size_lam] at ht
          refine ⟨by omega, ?_, fun f hf => hk f (by simp [hf])⟩
          intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact hv
          · exact he c hc

/-! ### The potential -/

/-- A β transition raises the potential by at most `3 S`. -/
theorem Trans.measure_beta_le {S : ℕ} {s s' : State} (h : Trans .beta s s') (hs : s.Bounded S) :
    measure s' ≤ measure s + 3 * S := by
  have hs' := h.bounded hs
  cases h with
  | beta t e v k =>
      obtain ⟨ht, _, _⟩ := hs'
      simp only [measure, kWeight]
      omega

/-- **The potential bound on a run**: `n` transitions with `b` β transitions satisfy
`n + μ(s') ≤ b + μ(s) + 3 S b`. -/
theorem Run.length_add_measure_le {S : ℕ} {n b : ℕ} {s s' : State} (h : Run n b s s')
    (hs : s.Bounded S) : n + measure s' ≤ b + measure s + 3 * S * b := by
  induction h with
  | refl => simp
  | @cons l n b s₁ s₂ s₃ ht _ ih =>
      have ih' := ih (ht.bounded hs)
      cases l with
      | admin =>
          have := ht.measure_lt
          simp only [Label.betaCount, Nat.add_zero]
          omega
      | beta =>
          have := ht.measure_beta_le hs
          simp only [Label.betaCount]
          rw [Nat.mul_add]
          omega

/-- At most every transition is a β transition. -/
theorem Run.beta_le {n b : ℕ} {s s' : State} (h : Run n b s s') : b ≤ n := by
  induction h with
  | refl => exact le_rfl
  | @cons l _ _ _ _ _ _ _ ih => cases l <;> simp only [Label.betaCount] <;> omega

/-- **The CEK machine has linear overhead**: a run from `t` with `b` β transitions has at most
`b + 3 |t| (b + 1)` transitions. -/
theorem run_length_le {t : Lambda} {n b : ℕ} {s : State} (h : Run n b (State.init t) s) :
    n ≤ b + 3 * Lambda.size t * (b + 1) := by
  have := h.length_add_measure_le (State.bounded_init t)
  simp only [State.init, measure, kWeight] at this
  rw [Nat.mul_add]
  omega

/-- **The machine time is linear in the call-by-value time**: if `t` reaches a normal form in `k`
call-by-value steps, the machine started on `t` halts on that normal form after at most
`k + 3 |t| (k + 1)` transitions, of which exactly `k` are β transitions. -/
theorem run_length_le_of_cbvIn {t N : Lambda} {k : ℕ} (hred : Lambda.cbvIn k t N)
    (hN : Lambda.CbvNormal N) :
    ∃ (n : ℕ) (s : State), Run n k (State.init t) s ∧ IsFinal s ∧ s.decode = N ∧
      k ≤ n ∧ n ≤ k + 3 * Lambda.size t * (k + 1) := by
  obtain ⟨n, s, hrun, hfin, hdec⟩ := eval_complete hred hN
  exact ⟨n, s, hrun, hfin, hdec, hrun.beta_le, run_length_le hrun⟩

end CEK
