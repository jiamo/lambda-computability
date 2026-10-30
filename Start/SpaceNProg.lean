/-
**Nondeterministic tape programs (M22-NONDET-PROG, first exit criterion).**

The structured tape programs of `Start/SpaceProg.lean` extended by a nondeterministic choice
`choose p q`: one step, after which either branch may run.  The compiled table offers two
instructions in the choice state, so the compiled machine is a well-formed *nondeterministic*
offline machine of `Start/SpaceMachine.lean`.

* `Complexity.Space.NProg` — the programs; `NProg.ofProg` embeds the deterministic programs;
* `NProg.Exec` — big-step semantics (an execution follows one branch of each choice), with a side
  condition on every configuration before the last; `Exec.loop_of_variant` — the while rule;
* `NProg.delta`, `NProg.machine` — compilation;
* `NProg.path_of_exec` — **compiler correctness**: an execution is a run of every machine hosting
  the program;
* `NProg.machine_wellFormed`, `NProg.loop_seg`, `NProg.loop_exit`, `NProg.accepts_of_exec_loop` —
  the compiled machine is well formed, iterations of a main loop are segments, and an execution of
  the main loop that leaves it is an accepting run.
-/

import Start.SpaceProg

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

/-- Nondeterministic structured tape programs. -/
inductive NProg where
  | act (f : Option Bool → Bool → Bool × Dir × Dir)
  | seq (p q : NProg)
  | ite (t : Test) (p q : NProg)
  | loop (t : Test) (p : NProg)
  /-- Nondeterministic choice; it costs one step. -/
  | choose (p q : NProg)

namespace NProg

/-- The number of control states a program occupies. -/
def size : NProg → ℕ
  | act _ => 1
  | seq p q => p.size + q.size
  | ite _ p q => 1 + p.size + q.size
  | loop _ p => 1 + p.size
  | choose p q => 1 + p.size + q.size

theorem size_pos : ∀ p : NProg, 0 < p.size
  | act _ => by simp [size]
  | seq p _ => by have := size_pos p; simp [size]; omega
  | ite _ _ _ => by simp [size]
  | loop _ _ => by simp [size]
  | choose _ _ => by simp [size]

/-- The deterministic programs. -/
def ofProg : Prog → NProg
  | .act f => act f
  | .seq p q => seq (ofProg p) (ofProg q)
  | .ite t p q => ite t (ofProg p) (ofProg q)
  | .loop t p => loop t (ofProg p)

/-- Big-step semantics. -/
inductive Exec (x : List Bool) (P : Config → Prop) : NProg → Config → Config → Prop
  | act {f : Option Bool → Bool → Bool × Dir × Dir} {c : Config} (hc : P c) :
      Exec x P (act f) c (eff x c (f (rdIn x c) (rdW c)))
  | seq {p q : NProg} {c d e : Config} (hp : Exec x P p c d) (hq : Exec x P q d e) :
      Exec x P (seq p q) c e
  | iteT {t : Test} {p q : NProg} {c e : Config} (hc : P c) (ht : t (rdIn x c) (rdW c) = true)
      (hp : Exec x P p (touch x c) e) : Exec x P (ite t p q) c e
  | iteF {t : Test} {p q : NProg} {c e : Config} (hc : P c) (ht : t (rdIn x c) (rdW c) = false)
      (hq : Exec x P q (touch x c) e) : Exec x P (ite t p q) c e
  | loopT {t : Test} {p : NProg} {c d e : Config} (hc : P c) (ht : t (rdIn x c) (rdW c) = true)
      (hp : Exec x P p (touch x c) d) (hl : Exec x P (loop t p) d e) :
      Exec x P (loop t p) c e
  | loopF {t : Test} {p : NProg} {c : Config} (hc : P c) (ht : t (rdIn x c) (rdW c) = false) :
      Exec x P (loop t p) c (touch x c)
  /-- Choose the left branch. -/
  | chooseL {p q : NProg} {c e : Config} (hc : P c) (hp : Exec x P p (touch x c) e) :
      Exec x P (choose p q) c e
  /-- Choose the right branch. -/
  | chooseR {p q : NProg} {c e : Config} (hc : P c) (hq : Exec x P q (touch x c) e) :
      Exec x P (choose p q) c e

/-- Deterministic executions are executions. -/
theorem Exec.ofProg {x : List Bool} {P : Config → Prop} {p : Prog} {c d : Config}
    (h : Prog.Exec x P p c d) : Exec x P (ofProg p) c d := by
  induction h with
  | act hc => exact .act hc
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteT hc ht _ ih => exact .iteT hc ht ih
  | iteF hc ht _ ih => exact .iteF hc ht ih
  | loopT hc ht _ _ ih₁ ih₂ => exact .loopT hc ht ih₁ ih₂
  | loopF hc ht => exact .loopF hc ht

/-- **The while rule.** -/
theorem Exec.loop_of_variant {x : List Bool} {P : Config → Prop} {t : Test} {body : NProg}
    (I : Config → Prop) (μ : Config → ℕ) (hP : ∀ c, I c → P c)
    (hbody : ∀ c, I c → t (rdIn x c) (rdW c) = true →
      ∃ d, Exec x P body (touch x c) d ∧ I d ∧ μ d < μ c) :
    ∀ c, I c → ∃ c', I c' ∧ t (rdIn x c') (rdW c') = false ∧
      Exec x P (loop t body) c (touch x c') := by
  intro c
  induction h : μ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    intro hc
    cases ht : t (rdIn x c) (rdW c) with
    | false => exact ⟨c, hc, ht, Exec.loopF (hP c hc) ht⟩
    | true =>
        obtain ⟨d, hd, hId, hlt⟩ := hbody c hc ht
        obtain ⟨c', hc', ht', hl⟩ := ih (μ d) (h ▸ hlt) d rfl hId
        exact ⟨c', hc', ht', Exec.loopT (hP c hc) ht hd hl⟩

theorem Exec.mono {x : List Bool} {P Q : Config → Prop} (hPQ : ∀ c, P c → Q c) {p : NProg}
    {c d : Config} (h : Exec x P p c d) : Exec x Q p c d := by
  induction h with
  | act hc => exact .act (hPQ _ hc)
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteT hc ht _ ih => exact .iteT (hPQ _ hc) ht ih
  | iteF hc ht _ ih => exact .iteF (hPQ _ hc) ht ih
  | loopT hc ht _ _ ih₁ ih₂ => exact .loopT (hPQ _ hc) ht ih₁ ih₂
  | loopF hc ht => exact .loopF (hPQ _ hc) ht
  | chooseL hc _ ih => exact .chooseL (hPQ _ hc) ih
  | chooseR hc _ ih => exact .chooseR (hPQ _ hc) ih

theorem exec_state {x : List Bool} {P : Config → Prop} {p : NProg} {c c' : Config}
    (h : Exec x P p c c') : c'.state = 0 := by
  induction h <;> first | rfl | assumption

/-! ### Compilation -/

/-- The compiled transition table, laid out from the base state `b` with exit state `e`. -/
def delta : NProg → ℕ → ℕ → ℕ → Option Bool → Bool → List (ℕ × Bool × Dir × Dir)
  | act f, b, e => fun q a w => if q = b then [(e, f a w)] else []
  | seq p q, b, e => fun st a w =>
      if st < b + p.size then delta p b (b + p.size) st a w
      else delta q (b + p.size) e st a w
  | ite t p q, b, e => fun st a w =>
      if st = b then [(if t a w then b + 1 else b + 1 + p.size, w, .stay, .stay)]
      else if st < b + 1 + p.size then delta p (b + 1) e st a w
      else delta q (b + 1 + p.size) e st a w
  | loop t p, b, e => fun st a w =>
      if st = b then [(if t a w then b + 1 else e, w, .stay, .stay)]
      else delta p (b + 1) b st a w
  | choose p q, b, e => fun st a w =>
      if st = b then [(b + 1, w, .stay, .stay), (b + 1 + p.size, w, .stay, .stay)]
      else if st < b + 1 + p.size then delta p (b + 1) e st a w
      else delta q (b + 1 + p.size) e st a w

/-- The compiled table only jumps inside the program or to its exit. -/
theorem delta_target : ∀ (p : NProg) (b e q : ℕ) (a : Option Bool) (w : Bool),
    ∀ i ∈ delta p b e q a w, (b ≤ i.1 ∧ i.1 < b + p.size) ∨ i.1 = e
  | act f, b, e, q, a, w => by
      intro i hi; unfold delta at hi; split at hi <;> simp_all
  | seq p r, b, e, q, a, w => by
      have := size_pos r
      intro i hi; unfold delta at hi; simp only [size]; split at hi
      · rcases delta_target p _ _ _ _ _ i hi with h | h <;> omega
      · rcases delta_target r _ _ _ _ _ i hi with h | h <;> omega
  | ite t p r, b, e, q, a, w => by
      have := size_pos p; have := size_pos r
      intro i hi; unfold delta at hi; simp only [size]; split at hi
      · simp only [List.mem_singleton] at hi; subst hi; split <;> simp <;> omega
      · split at hi
        · rcases delta_target p _ _ _ _ _ i hi with h | h <;> omega
        · rcases delta_target r _ _ _ _ _ i hi with h | h <;> omega
  | loop t p, b, e, q, a, w => by
      have := size_pos p
      intro i hi; unfold delta at hi; simp only [size]; split at hi
      · simp only [List.mem_singleton] at hi; subst hi; split
        · simp; omega
        · simp
      · rcases delta_target p _ _ _ _ _ i hi with h | h <;> omega
  | choose p r, b, e, q, a, w => by
      have := size_pos p; have := size_pos r
      intro i hi; unfold delta at hi; simp only [size]; split at hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> simp <;> omega
      · split at hi
        · rcases delta_target p _ _ _ _ _ i hi with h | h <;> omega
        · rcases delta_target r _ _ _ _ _ i hi with h | h <;> omega

/-! ### Compiler correctness -/

/-- A machine hosts `p` at base `b` with exit `e`. -/
def Hosts (M : Machine) (p : NProg) (b e : ℕ) : Prop :=
  ∀ q, b ≤ q → q < b + p.size → ∀ a w, M.delta q a w = delta p b e q a w

theorem step_of_mem {M : Machine} {x : List Bool} {c : Config} {i : ℕ × Bool × Dir × Dir}
    (h : i ∈ M.delta c.state (rdIn x c) (rdW c)) :
    M.Step x c ((eff x c (i.2.1, i.2.2.1, i.2.2.2)).at i.1) := by
  unfold Machine.Step Machine.stepList
  unfold rdIn rdW at h
  exact List.mem_map.2 ⟨i, h, by simp [eff, Config.at]⟩

theorem Hosts.seq_left {M : Machine} {p q : NProg} {b e : ℕ} (h : Hosts M (seq p q) b e) :
    Hosts M p b (b + p.size) := by
  intro st h1 h2 a w
  rw [h st h1 (by simp only [size]; omega) a w]
  simp only [delta, ite_eq_left h2]

theorem Hosts.seq_right {M : Machine} {p q : NProg} {b e : ℕ} (h : Hosts M (seq p q) b e) :
    Hosts M q (b + p.size) e := by
  intro st h1 h2 a w
  rw [h st (by omega) (by simp only [size]; omega) a w]
  simp only [delta, ite_eq_right (show ¬ st < b + p.size by omega)]

theorem Hosts.ite_left {M : Machine} {t : Test} {p q : NProg} {b e : ℕ}
    (h : Hosts M (ite t p q) b e) : Hosts M p (b + 1) e := by
  intro st h1 h2 a w
  rw [h st (by omega) (by simp only [size]; omega) a w]
  simp only [delta, ite_eq_right (show st ≠ b by omega), ite_eq_left h2]

theorem Hosts.ite_right {M : Machine} {t : Test} {p q : NProg} {b e : ℕ}
    (h : Hosts M (ite t p q) b e) : Hosts M q (b + 1 + p.size) e := by
  intro st h1 h2 a w
  rw [h st (by omega) (by simp only [size]; omega) a w]
  simp only [delta, ite_eq_right (show st ≠ b by omega), ite_eq_right (show ¬ st < b + 1 + p.size by omega)]

theorem Hosts.choose_left {M : Machine} {p q : NProg} {b e : ℕ}
    (h : Hosts M (choose p q) b e) : Hosts M p (b + 1) e := by
  intro st h1 h2 a w
  rw [h st (by omega) (by simp only [size]; omega) a w]
  simp only [delta, ite_eq_right (show st ≠ b by omega), ite_eq_left h2]

theorem Hosts.choose_right {M : Machine} {p q : NProg} {b e : ℕ}
    (h : Hosts M (choose p q) b e) : Hosts M q (b + 1 + p.size) e := by
  intro st h1 h2 a w
  rw [h st (by omega) (by simp only [size]; omega) a w]
  simp only [delta, ite_eq_right (show st ≠ b by omega), ite_eq_right (show ¬ st < b + 1 + p.size by omega)]

theorem Hosts.loop_body {M : Machine} {t : Test} {p : NProg} {b e : ℕ}
    (h : Hosts M (loop t p) b e) : Hosts M p (b + 1) b := by
  intro st h1 h2 a w
  rw [h st (by omega) (by simp only [size]; omega) a w]
  simp only [delta, ite_eq_right (show st ≠ b by omega)]

theorem Hosts.test {M : Machine} {t : Test} {p q : NProg} {b e : ℕ}
    (h : Hosts M (ite t p q) b e) (a : Option Bool) (w : Bool) :
    M.delta b a w = [(if t a w then b + 1 else b + 1 + p.size, w, .stay, .stay)] := by
  rw [h b le_rfl (by simp only [size]; omega) a w]
  simp only [delta, ↓reduceIte]

theorem Hosts.loop_test {M : Machine} {t : Test} {p : NProg} {b e : ℕ}
    (h : Hosts M (loop t p) b e) (a : Option Bool) (w : Bool) :
    M.delta b a w = [(if t a w then b + 1 else e, w, .stay, .stay)] := by
  rw [h b le_rfl (by simp only [size]; omega) a w]
  simp only [delta, ↓reduceIte]

theorem Hosts.choice {M : Machine} {p q : NProg} {b e : ℕ}
    (h : Hosts M (choose p q) b e) (a : Option Bool) (w : Bool) :
    M.delta b a w = [(b + 1, w, .stay, .stay), (b + 1 + p.size, w, .stay, .stay)] := by
  rw [h b le_rfl (by simp only [size]; omega) a w]
  simp only [delta, ↓reduceIte]

/-- **Compiler correctness.** -/
theorem path_of_exec {M : Machine} {x : List Bool} {P : Config → Prop} {p : NProg}
    {c c' : Config} (h : Exec x P p c c') : c.state = 0 → ∀ {b e : ℕ}, Hosts M p b e →
      M.Path x (fun d => P (d.at 0) ∧ b ≤ d.state ∧ d.state < b + p.size) (c.at b) (c'.at e) := by
  induction h with
  | @act f c hc =>
      intro hc0 b e hM
      have hd : (e, f (rdIn x c) (rdW c)) ∈
          M.delta (c.at b).state (rdIn x (c.at b)) (rdW (c.at b)) := by
        rw [Config.at_state, hM b le_rfl (by simp [size]) _ _]
        simp [delta]
      refine Machine.Path.single ⟨?_, le_rfl, by simp [size]⟩ (step_of_mem hd)
      rw [Config.at_at, ← hc0]
      exact hc
  | @seq p q c d e hp hq ihp ihq =>
      intro hc0 b e' hM
      refine Machine.Path.trans ((ihp hc0 hM.seq_left).mono ?_)
        ((ihq (exec_state hp) hM.seq_right).mono ?_)
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, h2, by simp only [size]; omega⟩
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩
  | @iteT t p q c e hc ht hp ihp =>
      intro hc0 b e' hM
      have hd : (b + 1, rdW c, Dir.stay, Dir.stay) ∈
          M.delta (c.at b).state (rdIn x (c.at b)) (rdW (c.at b)) := by
        rw [Config.at_state, hM.test]; simp [ht]
      refine Machine.Path.head ⟨?_, le_rfl, by simp only [Config.at_state, size]; omega⟩
        (step_of_mem hd) ((ihp rfl hM.ite_left).mono ?_)
      · rw [Config.at_at, ← hc0]; exact hc
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩
  | @iteF t p q c e hc ht hq ihq =>
      intro hc0 b e' hM
      have hd : (b + 1 + p.size, rdW c, Dir.stay, Dir.stay) ∈
          M.delta (c.at b).state (rdIn x (c.at b)) (rdW (c.at b)) := by
        rw [Config.at_state, hM.test]; simp [ht]
      refine Machine.Path.head ⟨?_, le_rfl, by simp only [Config.at_state, size]; omega⟩
        (step_of_mem hd) ((ihq rfl hM.ite_right).mono ?_)
      · rw [Config.at_at, ← hc0]; exact hc
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩
  | @loopT t p c d e hc ht hp hl ihp ihl =>
      intro hc0 b e' hM
      have hd : (b + 1, rdW c, Dir.stay, Dir.stay) ∈
          M.delta (c.at b).state (rdIn x (c.at b)) (rdW (c.at b)) := by
        rw [Config.at_state, hM.loop_test]; simp [ht]
      refine Machine.Path.head ⟨?_, le_rfl, by simp only [Config.at_state, size]; omega⟩
        (step_of_mem hd)
        (Machine.Path.trans ((ihp rfl hM.loop_body).mono ?_) (ihl (exec_state hp) hM))
      · rw [Config.at_at, ← hc0]; exact hc
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩
  | @loopF t p c hc ht =>
      intro hc0 b e' hM
      have hd : (e', rdW c, Dir.stay, Dir.stay) ∈
          M.delta (c.at b).state (rdIn x (c.at b)) (rdW (c.at b)) := by
        rw [Config.at_state, hM.loop_test]; simp [ht]
      refine Machine.Path.single ⟨?_, le_rfl, by simp only [Config.at_state, size]; omega⟩
        (step_of_mem hd)
      rw [Config.at_at, ← hc0]; exact hc
  | @chooseL p q c e hc hp ihp =>
      intro hc0 b e' hM
      have hd : (b + 1, rdW c, Dir.stay, Dir.stay) ∈
          M.delta (c.at b).state (rdIn x (c.at b)) (rdW (c.at b)) := by
        rw [Config.at_state, hM.choice]; simp
      refine Machine.Path.head ⟨?_, le_rfl, by simp only [Config.at_state, size]; omega⟩
        (step_of_mem hd) ((ihp rfl hM.choose_left).mono ?_)
      · rw [Config.at_at, ← hc0]; exact hc
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩
  | @chooseR p q c e hc hq ihq =>
      intro hc0 b e' hM
      have hd : (b + 1 + p.size, rdW c, Dir.stay, Dir.stay) ∈
          M.delta (c.at b).state (rdIn x (c.at b)) (rdW (c.at b)) := by
        rw [Config.at_state, hM.choice]; simp
      refine Machine.Path.head ⟨?_, le_rfl, by simp only [Config.at_state, size]; omega⟩
        (step_of_mem hd) ((ihq rfl hM.choose_right).mono ?_)
      · rw [Config.at_at, ← hc0]; exact hc
      · rintro d' ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by simp only [size]; omega⟩

/-! ### The machine of a program -/

/-- The offline machine of a program, with one final accepting halting state `size p`. -/
def machine (p : NProg) : Machine where
  states := p.size + 1
  accept q := decide (q = p.size)
  delta q a w := if q < p.size then delta p 0 p.size q a w else []

theorem machine_hosts (p : NProg) : Hosts p.machine p 0 p.size := by
  intro q _ hq a w
  simp only [machine, zero_add] at hq ⊢
  rw [ite_eq_left hq]

/-- **The compiled machine is a well-formed nondeterministic machine.** -/
theorem machine_wellFormed (p : NProg) : p.machine.WellFormed := by
  refine ⟨Nat.succ_pos _, ?_⟩
  intro q a w i hi
  simp only [machine] at hi ⊢
  split at hi
  · rcases delta_target p 0 p.size q a w i hi with h | h <;> omega
  · simp at hi

theorem machine_final_halts (p : NProg) (x : List Bool) (c : Config) (hc : c.state = p.size) :
    p.machine.stepList x c = [] := by
  simp [Machine.stepList, machine, hc]

theorem machine_accept (p : NProg) (q : ℕ) : p.machine.accept q = decide (q = p.size) := rfl

/-- One iteration of a main loop is a segment of the compiled machine. -/
theorem loop_seg {t : Test} {body : NProg} {x : List Bool} {B : ℕ} {c d : Config}
    (ht : t (rdIn x c) (rdW c) = true)
    (hb : Exec x (fun c => c.space ≤ B) body (touch x c) d) :
    (loop t body).machine.Seg x B (c.at 0) (d.at 0) := by
  have hM := machine_hosts (loop t body)
  have hd : (1, rdW c, Dir.stay, Dir.stay) ∈
      (loop t body).machine.delta (c.at 0).state (rdIn x (c.at 0)) (rdW (c.at 0)) := by
    rw [Config.at_state, hM.loop_test]; simp [ht]
  refine ⟨(touch x c).at 1, step_of_mem hd, ?_⟩
  refine (path_of_exec hb rfl (b := 0 + 1) (e := 0) hM.loop_body).mono ?_
  rintro d' ⟨h1, _, h3⟩
  refine ⟨by simpa using h1, ?_⟩
  rw [machine_accept, decide_eq_false_iff_not]
  simp only [size] at h3 ⊢
  omega

/-- Leaving the main loop reaches the final accepting state. -/
theorem loop_exit {t : Test} {body : NProg} {x : List Bool} {c : Config}
    (ht : t (rdIn x c) (rdW c) = false) :
    (loop t body).machine.Step x (c.at 0) ((touch x c).at (loop t body).size) := by
  have hM := machine_hosts (loop t body)
  have hd : ((loop t body).size, rdW c, Dir.stay, Dir.stay) ∈
      (loop t body).machine.delta (c.at 0).state (rdIn x (c.at 0)) (rdW (c.at 0)) := by
    rw [Config.at_state, hM.loop_test]; simp [ht]
  exact step_of_mem hd

/-- **Soundness of acceptance**: an execution of a program from the initial configuration is an
accepting run of its machine. -/
theorem accepts_of_exec {p : NProg} {x : List Bool} {P : Config → Prop} {c' : Config}
    (h : Exec x P p init c') : p.machine.Accepts x := by
  have hpath := path_of_exec (M := p.machine) h rfl (machine_hosts p)
  obtain ⟨n, hn⟩ := hpath.exists_steps
  refine ⟨n, c'.at p.size, ?_, ?_⟩
  · simpa [Config.at, init] using hn
  · simp [machine_accept]

end NProg

end Complexity.Space
