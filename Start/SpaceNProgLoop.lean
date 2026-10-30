/-
**Nondeterministic tape programs: `NSPACE` from the loop form (M22-NONDET-PROG, exit criterion 2).**

* `NProg.delta_shift` — the compiled table of a program laid out at base `b + k` is the table laid
  out at `b`, with every target relabelled (`+ k` inside the block, the exit to the new exit);
* `NProg.loop_reach_inv` — every configuration reachable by the machine of `loop t body` is either
  in the test state and satisfies the loop invariant, or in the final state, or is (shifted by one)
  a configuration reached by the machine of `body` started on an iteration;
* `NProg.nspace_loop` — **membership in `NSPACE` from the loop form**: the invariant `I` holds
  initially and bounds the space; every partial run of the body from an iteration stays within
  `B x` cells and, when it finishes, restores the invariant; the language consists of the inputs on
  which the loop has an execution.
-/

import Start.SpaceNProgConverse

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace NProg

/-- **Relocation of the compiled table.** -/
theorem delta_shift : ∀ (p : NProg) (b k e e' : ℕ) (g : ℕ → ℕ), g e' = e →
    (∀ j, b ≤ j → j < b + p.size → g j = j + k) →
    ∀ q a w, b ≤ q → q < b + p.size →
      delta p (b + k) e (q + k) a w = (delta p b e' q a w).map (fun i => (g i.1, i.2))
  | act f, b, k, e, e', g, hg, _, q, a, w, h1, h2 => by
    simp only [size] at h2
    have hq : q = b := by omega
    subst hq
    simp [delta, hg]
  | seq p r, b, k, e, e', g, hg, hgb, q, a, w, h1, h2 => by
    have hp := size_pos p; have hr := size_pos r
    simp only [size] at h2 hgb
    simp only [delta]
    by_cases hq : q < b + p.size
    · rw [ite_eq_left (by omega), ite_eq_left hq]
      exact delta_shift p b k (b + k + p.size) (b + p.size) g (by rw [hgb _ (by omega) (by omega)]; omega)
        (fun j hj1 hj2 => hgb j hj1 (by omega)) q a w h1 hq
    · rw [ite_eq_right (by omega), ite_eq_right hq, show b + k + p.size = b + p.size + k by omega]
      exact delta_shift r (b + p.size) k e e' g hg
        (fun j hj1 hj2 => hgb j (by omega) (by omega)) q a w (by omega) (by omega)
  | ite t p r, b, k, e, e', g, hg, hgb, q, a, w, h1, h2 => by
    have hp := size_pos p; have hr := size_pos r
    simp only [size] at h2 hgb
    simp only [delta]
    by_cases hqb : q = b
    · subst hqb
      rw [ite_eq_left rfl, ite_eq_left rfl]
      cases t a w
      · simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, List.cons.injEq,
          Prod.mk.injEq, and_true]
        rw [hgb _ (by omega) (by omega)]; omega
      · simp only [↓reduceIte, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
          and_true]
        rw [hgb _ (by omega) (by omega)]; omega
    · rw [ite_eq_right (by omega), ite_eq_right hqb]
      by_cases hq : q < b + 1 + p.size
      · rw [ite_eq_left (by omega), ite_eq_left hq, show b + k + 1 = b + 1 + k by omega]
        exact delta_shift p (b + 1) k e e' g hg
          (fun j hj1 hj2 => hgb j (by omega) (by omega)) q a w (by omega) hq
      · rw [ite_eq_right (by omega), ite_eq_right hq, show b + k + 1 + p.size = b + 1 + p.size + k by omega]
        exact delta_shift r (b + 1 + p.size) k e e' g hg
          (fun j hj1 hj2 => hgb j (by omega) (by omega)) q a w (by omega) (by omega)
  | loop t p, b, k, e, e', g, hg, hgb, q, a, w, h1, h2 => by
    have hp := size_pos p
    simp only [size] at h2 hgb
    simp only [delta]
    by_cases hqb : q = b
    · subst hqb
      rw [ite_eq_left rfl, ite_eq_left rfl]
      cases t a w
      · simp [hg]
      · simp only [↓reduceIte, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
          and_true]
        rw [hgb _ (by omega) (by omega)]; omega
    · rw [ite_eq_right (by omega), ite_eq_right hqb, show b + k + 1 = b + 1 + k by omega]
      exact delta_shift p (b + 1) k (b + k) b g (hgb b le_rfl (by omega))
        (fun j hj1 hj2 => hgb j (by omega) (by omega)) q a w (by omega) (by omega)
  | choose p r, b, k, e, e', g, hg, hgb, q, a, w, h1, h2 => by
    have hp := size_pos p; have hr := size_pos r
    simp only [size] at h2 hgb
    simp only [delta]
    by_cases hqb : q = b
    · subst hqb
      rw [ite_eq_left rfl, ite_eq_left rfl]
      simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true]
      rw [hgb (q + 1) (by omega) (by omega), hgb (q + 1 + p.size) (by omega) (by omega)]
      omega
    · rw [ite_eq_right (by omega), ite_eq_right hqb]
      by_cases hq : q < b + 1 + p.size
      · rw [ite_eq_left (by omega), ite_eq_left hq, show b + k + 1 = b + 1 + k by omega]
        exact delta_shift p (b + 1) k e e' g hg
          (fun j hj1 hj2 => hgb j (by omega) (by omega)) q a w (by omega) hq
      · rw [ite_eq_right (by omega), ite_eq_right hq, show b + k + 1 + p.size = b + 1 + p.size + k by omega]
        exact delta_shift r (b + 1 + p.size) k e e' g hg
          (fun j hj1 hj2 => hgb j (by omega) (by omega)) q a w (by omega) (by omega)

/-- The machine of a loop, inside its body, is the machine of the body shifted by one. -/
theorem loop_delta_body (t : Test) (body : NProg) (q : ℕ) (hq : q < body.size) (a : Option Bool)
    (w : Bool) :
    (loop t body).machine.delta (q + 1) a w =
      (body.machine.delta q a w).map
        (fun i => ((fun j => if j = body.size then 0 else j + 1) i.1, i.2)) := by
  have hM := (machine_hosts (loop t body)).loop_body
  rw [hM (q + 1) (by omega) (by omega) a w]
  have h := delta_shift body 0 1 0 body.size (fun j => if j = body.size then 0 else j + 1)
    (by simp) (fun j _ hj => by simp only [zero_add] at hj; simp [show j ≠ body.size by omega])
    q a w (Nat.zero_le _) (by omega)
  simp only [zero_add] at h
  rw [h]
  simp only [machine, ite_eq_left hq]

/-- The invariant of reachable configurations of the machine of a loop. -/
def LoopInv (t : Test) (body : NProg) (x : List Bool) (I : Config → Prop) (B : ℕ)
    (d : Config) : Prop :=
  (d.state = 0 ∧ I d) ∨ (d.state = (loop t body).size ∧ d.space ≤ B) ∨
    ∃ c n d', I c ∧ t (rdIn x c) (rdW c) = true ∧
      Reach.steps (body.machine.Step x) n ((touch x c).at 0) d' ∧ d'.state < body.size ∧
        d = d'.at (d'.state + 1)

theorem loop_reach_inv {t : Test} {body : NProg} {x : List Bool} {I : Config → Prop} {B : ℕ}
    (h0 : I init) (hsp : ∀ c, I c → c.space ≤ B)
    (hbody : ∀ c, I c → t (rdIn x c) (rdW c) = true → ∀ n d,
      Reach.steps (body.machine.Step x) n ((touch x c).at 0) d →
        d.space ≤ B ∧ (d.state = body.size → I (d.at 0))) :
    ∀ n d, Reach.steps ((loop t body).machine.Step x) n init d → LoopInv t body x I B d := by
  intro n
  induction n with
  | zero => rintro d rfl; exact Or.inl ⟨rfl, h0⟩
  | succ n ih =>
    rintro d₂ ⟨d, hd, hstep⟩
    rcases ih d hd with ⟨hs, hI⟩ | ⟨hs, _⟩ | ⟨c, m, d', hI, ht, hrun, hlt, rfl⟩
    · -- the test state
      rw [← Config.at_self d, hs] at hstep
      obtain ⟨i, hi, rfl⟩ := step_at_inv hstep
      rw [(machine_hosts (loop t body)).loop_test] at hi
      simp only [List.mem_singleton] at hi
      subst hi
      have hd0 : d.at 0 = d := by rw [← hs]; rfl
      cases htd : t (rdIn x d) (rdW d) with
      | true =>
        simp only [↓reduceIte, touch_eq]
        exact Or.inr (Or.inr ⟨d, 0, (touch x d).at 0, hI, htd, rfl, size_pos body, rfl⟩)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, touch_eq]
        refine Or.inr (Or.inl ⟨rfl, ?_⟩)
        rw [Config.at_space, Prog.space_touch]
        exact hsp d hI
    · -- the final state halts
      rw [Machine.Step, machine_final_halts _ _ _ hs] at hstep
      simp at hstep
    · -- inside the body
      obtain ⟨i, hi, rfl⟩ := step_at_inv hstep
      rw [loop_delta_body t body _ hlt] at hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
      have hj' : j ∈ body.machine.delta d'.state (rdIn x d') (rdW d') := hj
      have hstep' := step_of_mem hj'
      have hrun' : Reach.steps (body.machine.Step x) (m + 1) ((touch x c).at 0)
          ((eff x d' (j.2.1, j.2.2.1, j.2.2.2)).at j.1) := ⟨d', hrun, hstep'⟩
      have hjt : j.1 ≤ body.size := by
        have := (machine_wellFormed body).2 _ _ _ j hj
        simp only [machine] at this; omega
      by_cases hje : j.1 = body.size
      · simp only [hje, ↓reduceIte]
        have := (hbody c hI ht _ _ hrun').2 (by simp [hje])
        exact Or.inl ⟨rfl, by simpa using this⟩
      · simp only [hje, ↓reduceIte]
        exact Or.inr (Or.inr ⟨c, m + 1, _, hI, ht, hrun', by simp; omega, rfl⟩)

/-- **Membership in `NSPACE` from the loop form.** -/
theorem nspace_loop {t : Test} {body : NProg} {I : List Bool → Config → Prop}
    {B : List Bool → ℕ} {s : ℕ → ℕ} {L : Language}
    (h0 : ∀ x, I x init) (hsp : ∀ x c, I x c → c.space ≤ B x)
    (hbody : ∀ x c, I x c → t (rdIn x c) (rdW c) = true → ∀ n d,
      Reach.steps (body.machine.Step x) n ((touch x c).at 0) d →
        d.space ≤ B x ∧ (d.state = body.size → I x (d.at 0)))
    (hL : ∀ x, L x ↔ ∃ c', Exec x (fun _ => True) (loop t body) init c')
    (hB : ∀ x, B x ≤ s x.length) : NSPACE s L := by
  refine nspace_of_exec (B := B) (fun x n d hd => ?_) hL hB
  rcases loop_reach_inv (h0 x) (hsp x) (hbody x) n d hd with ⟨_, hI⟩ | ⟨_, h⟩ |
    ⟨c, m, d', hI, ht, hrun, _, rfl⟩
  · exact hsp x d hI
  · exact h
  · rw [Config.at_space]; exact (hbody x c hI ht m d' hrun).1

end NProg

end Complexity.Space
