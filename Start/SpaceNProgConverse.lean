/-
**Nondeterministic tape programs: the converse of compiler correctness (M22-NONDET-PROG).**

* `NProg.exec_of_run` — every run of a machine hosting a program at base `b` with an exit `e`
  outside the program's block, which starts in `b` and ends outside the block, first passes through
  the exit, and the part up to the exit is an execution of the program;
* `NProg.exec_of_accepts` — **every accepting run of the compiled machine comes from an
  execution**: if `p.machine` accepts `x`, then `p` has an execution from the initial
  configuration.
-/

import Start.SpaceNProg

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace NProg

/-- Inversion of one machine step. -/
theorem step_at_inv {M : Machine} {x : List Bool} {c d : Config} {q : ℕ}
    (h : M.Step x (c.at q) d) :
    ∃ i ∈ M.delta q (rdIn x c) (rdW c), d = (eff x c (i.2.1, i.2.2.1, i.2.2.2)).at i.1 := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  exact ⟨t, ht, rfl⟩

/-- A run that ends outside the block it starts in makes a first step. -/
theorem first_step {M : Machine} {x : List Bool} {n : ℕ} {a d : Config}
    (h : Reach.steps (M.Step x) n a d) (hne : a.state ≠ d.state) :
    ∃ k a₁, n = k + 1 ∧ M.Step x a a₁ ∧ Reach.steps (M.Step x) k a₁ d := by
  cases n with
  | zero => cases h; exact absurd rfl hne
  | succ k =>
    rw [Nat.add_comm, Reach.steps_add] at h
    obtain ⟨m, h1, h2⟩ := h
    rw [Reach.steps_one] at h1
    exact ⟨k, m, rfl, h1, h2⟩

theorem touch_eq (x : List Bool) (c : Config) :
    eff x c (rdW c, Dir.stay, Dir.stay) = touch x c := rfl

/-- **Runs decompose along the program**: a run from the base `b` of a hosted program that ends
outside its block passes through the exit `e`, and its part up to the exit is an execution. -/
theorem exec_of_run {M : Machine} {x : List Bool} :
    ∀ (p : NProg) (b e : ℕ), Hosts M p b e → (e < b ∨ b + p.size ≤ e) →
    ∀ (n : ℕ) (c d : Config), Reach.steps (M.Step x) n (c.at b) d →
      ¬ (b ≤ d.state ∧ d.state < b + p.size) →
      ∃ c' m, m ≤ n ∧ Exec x (fun _ => True) p c c' ∧
        Reach.steps (M.Step x) (n - m) (c'.at e) d
  | act f, b, e, hM, _, n, c, d, hrun, hout => by
    obtain ⟨k, d₁, rfl, h1, h2⟩ := first_step hrun (by simp only [Config.at_state, size] at hout ⊢; omega)
    obtain ⟨i, hi, rfl⟩ := step_at_inv h1
    rw [hM b le_rfl (by simp [size])] at hi
    simp only [delta, ↓reduceIte, List.mem_singleton] at hi
    subst hi
    exact ⟨_, 1, by omega, Exec.act trivial, by simpa using h2⟩
  | seq p q, b, e, hM, he, n, c, d, hrun, hout => by
    have hp := size_pos p; have hq := size_pos q
    simp only [size] at he hout
    obtain ⟨c₁, m₁, hm₁, hx₁, hr₁⟩ :=
      exec_of_run p b (b + p.size) hM.seq_left (by omega) n c d hrun (by omega)
    obtain ⟨c₂, m₂, hm₂, hx₂, hr₂⟩ :=
      exec_of_run q (b + p.size) e hM.seq_right (by omega) (n - m₁) c₁ d hr₁ (by omega)
    exact ⟨c₂, m₁ + m₂, by omega, Exec.seq hx₁ hx₂, by rwa [Nat.sub_add_eq]⟩
  | ite t p q, b, e, hM, he, n, c, d, hrun, hout => by
    have hp := size_pos p; have hq := size_pos q
    simp only [size] at he hout
    obtain ⟨k, d₁, rfl, h1, h2⟩ := first_step hrun (by simp only [Config.at_state]; omega)
    obtain ⟨i, hi, rfl⟩ := step_at_inv h1
    rw [hM.test] at hi
    simp only [List.mem_singleton] at hi
    subst hi
    cases ht : t (rdIn x c) (rdW c) with
    | true =>
      simp only [ht, ↓reduceIte, touch_eq] at h2
      obtain ⟨c', m, hm, hx, hr⟩ :=
        exec_of_run p (b + 1) e hM.ite_left (by omega) k (touch x c) d h2 (by omega)
      exact ⟨c', m + 1, by omega, Exec.iteT trivial ht hx, by
        rwa [show k + 1 - (m + 1) = k - m by omega]⟩
    | false =>
      simp only [ht, Bool.false_eq_true, ↓reduceIte, touch_eq] at h2
      obtain ⟨c', m, hm, hx, hr⟩ :=
        exec_of_run q (b + 1 + p.size) e hM.ite_right (by omega) k (touch x c) d h2 (by omega)
      exact ⟨c', m + 1, by omega, Exec.iteF trivial ht hx, by
        rwa [show k + 1 - (m + 1) = k - m by omega]⟩
  | choose p q, b, e, hM, he, n, c, d, hrun, hout => by
    have hp := size_pos p; have hq := size_pos q
    simp only [size] at he hout
    obtain ⟨k, d₁, rfl, h1, h2⟩ := first_step hrun (by simp only [Config.at_state]; omega)
    obtain ⟨i, hi, rfl⟩ := step_at_inv h1
    rw [hM.choice] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simp only [touch_eq] at h2
      obtain ⟨c', m, hm, hx, hr⟩ :=
        exec_of_run p (b + 1) e hM.choose_left (by omega) k (touch x c) d h2 (by omega)
      exact ⟨c', m + 1, by omega, Exec.chooseL trivial hx, by
        rwa [show k + 1 - (m + 1) = k - m by omega]⟩
    · simp only [touch_eq] at h2
      obtain ⟨c', m, hm, hx, hr⟩ :=
        exec_of_run q (b + 1 + p.size) e hM.choose_right (by omega) k (touch x c) d h2 (by omega)
      exact ⟨c', m + 1, by omega, Exec.chooseR trivial hx, by
        rwa [show k + 1 - (m + 1) = k - m by omega]⟩
  | loop t p, b, e, hM, he, n, c, d, hrun, hout => by
    have hp := size_pos p
    simp only [size] at he hout
    induction n using Nat.strong_induction_on generalizing c with
    | _ n ih =>
    obtain ⟨k, d₁, rfl, h1, h2⟩ := first_step hrun (by simp only [Config.at_state]; omega)
    obtain ⟨i, hi, rfl⟩ := step_at_inv h1
    rw [hM.loop_test] at hi
    simp only [List.mem_singleton] at hi
    subst hi
    cases ht : t (rdIn x c) (rdW c) with
    | true =>
      simp only [ht, ↓reduceIte, touch_eq] at h2
      obtain ⟨c₁, m₁, hm₁, hx₁, hr₁⟩ :=
        exec_of_run p (b + 1) b hM.loop_body (by omega) k (touch x c) d h2 (by omega)
      obtain ⟨c₂, m₂, hm₂, hx₂, hr₂⟩ := ih (k - m₁) (by omega) c₁ hr₁
      exact ⟨c₂, m₁ + m₂ + 1, by omega, Exec.loopT trivial ht hx₁ hx₂, by
        rwa [show k + 1 - (m₁ + m₂ + 1) = k - m₁ - m₂ by omega]⟩
    | false =>
      simp only [ht, Bool.false_eq_true, ↓reduceIte, touch_eq] at h2
      exact ⟨touch x c, 1, by omega, Exec.loopF trivial ht, by simpa using h2⟩

/-- **Completeness of acceptance**: every accepting run of the compiled machine comes from an
execution of the program from the initial configuration. -/
theorem exec_of_accepts (p : NProg) (x : List Bool) (h : p.machine.Accepts x) :
    ∃ c', NProg.Exec x (fun _ => True) p init c' := by
  obtain ⟨n, d, hrun, hacc⟩ := h
  rw [machine_accept, decide_eq_true_eq] at hacc
  obtain ⟨c', _, _, hx, _⟩ :=
    exec_of_run p 0 p.size (machine_hosts p) (by omega) n init d hrun (by omega)
  exact ⟨c', hx⟩

/-- **`NSPACE` from executions**: a language whose members are exactly the inputs on which the
program has an execution from the initial configuration is in `NSPACE s`, as soon as every
configuration reachable by the compiled machine fits in `B x ≤ s |x|` cells. -/
theorem nspace_of_exec {p : NProg} {B : List Bool → ℕ} {s : ℕ → ℕ} {L : Language}
    (hsafe : ∀ x n c, Reach.steps (p.machine.Step x) n init c → c.space ≤ B x)
    (hL : ∀ x, L x ↔ ∃ c', Exec x (fun _ => True) p init c')
    (hB : ∀ x, B x ≤ s x.length) : NSPACE s L := by
  refine ⟨p.machine, machine_wellFormed p, fun x n c hc => (hsafe x n c hc).trans (hB x),
    fun x => ?_⟩
  rw [hL x]
  exact ⟨fun ⟨c', h⟩ => accepts_of_exec h, exec_of_accepts p x⟩

end NProg

end Complexity.Space
