/-
**The shape of a run of sum-check: histories, replays, causality.**

`Start/SumCheck.lean` runs the protocol against a prover strategy that sees the whole history of
the interaction.  To turn the game into an interactive proof (`Start/InteractiveProof.lean`), in
which the prover only sees a transcript word and the verifier's random points are drawn from its
coins, three structural facts about a run are needed, none of which involves the arithmetic of the
protocol:

* **the history of an accepting run** is the history it started from followed by the messages
  interleaved with the random points, one message and one point per round
  (`Complexity.Qbf.run_out`);
* **replaying a run**: a strategy that answers every query of an accepting run with the message
  recorded at that position of its history produces the same run (`Complexity.Qbf.run_replay`) —
  this is how a prover that only sees a transcript is shown to be as good as the honest one;
* **causality**: the `k`-th message of an accepting run only depends on the first `k` random
  points (`Complexity.Qbf.run_causal`);
* **congruence**: two strategies that agree on every history whose points are a prefix of the
  points of the run produce the same verdict (`Complexity.Qbf.run_congr`).

Main definitions:

* `Complexity.Qbf.inter` — messages interleaved with points;
* `Complexity.Qbf.ptsOf` — the random points recorded in a history.
-/

import Start.SumCheck

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

variable {F : Type*} [Field F] [DecidableEq F]

section Lists
omit [DecidableEq F]

/-- Messages interleaved with points: `[m₀, [s₀], m₁, [s₁], …]`. -/
def inter : List (List F) → List F → List (List F)
  | m :: ms, s :: ρ => m :: [s] :: inter ms ρ
  | _, _ => []

omit [Field F] in
theorem inter_append : ∀ (ms₁ ms₂ : List (List F)) (ρ₁ ρ₂ : List F), ms₁.length = ρ₁.length →
    inter (ms₁ ++ ms₂) (ρ₁ ++ ρ₂) = inter ms₁ ρ₁ ++ inter ms₂ ρ₂
  | [], _, [], _, _ => rfl
  | _ :: ms₁, ms₂, _ :: ρ₁, ρ₂, h => by
      simp only [List.cons_append, inter, inter_append ms₁ ms₂ ρ₁ ρ₂ (by simpa using h)]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h

omit [Field F] in
theorem length_inter : ∀ (ms : List (List F)) (ρ : List F), ms.length = ρ.length →
    (inter ms ρ).length = 2 * ρ.length
  | [], [], _ => rfl
  | _ :: ms, _ :: ρ, h => by
      simp only [inter, List.length_cons, length_inter ms ρ (by simpa using h)]; ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The random points recorded in a history: the entries at odd positions. -/
def ptsOf : List (List F) → List F
  | _ :: s :: H => s.headD 0 :: ptsOf H
  | _ => []

theorem ptsOf_append : ∀ (H X : List (List F)), Even H.length → ptsOf (H ++ X) = ptsOf H ++ ptsOf X
  | [], X, _ => rfl
  | [_], _, h => by simp at h
  | m :: s :: H, X, h => by
      simp only [List.cons_append, ptsOf, List.cons_append, List.cons.injEq, true_and]
      exact ptsOf_append H X (by simpa [Nat.even_add_one] using h)

theorem ptsOf_inter : ∀ (ms : List (List F)) (ρ : List F), ms.length = ρ.length →
    ptsOf (inter ms ρ) = ρ
  | [], [], _ => rfl
  | _ :: ms, _ :: ρ, h => by simp [inter, ptsOf, ptsOf_inter ms ρ (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

end Lists

/-! ### The history of a run -/

omit [Field F] [DecidableEq F] in
theorem rounds_conj_tail {p q : Op} {ρ : List F} (h : ρ.length = (Op.conj p q).rounds) :
    (ρ.tail.take p.rounds).length = p.rounds ∧ (ρ.tail.drop p.rounds).length = q.rounds := by
  simp only [Op.rounds] at h
  simp only [List.length_take, List.length_drop, List.length_tail, h]
  omega

/-- The history only grows. -/
theorem run_prefix (d : ℕ) (P : Strat F) :
    ∀ (t : Op) (a : ℕ → F) (v : F) (hist : List (List F)) (ρ : List F),
      hist <+: (run d P t a v hist ρ).2 := by
  intro t
  induction t with
  | var i => intro a v hist ρ; simp [run]
  | neg p ih => intro a v hist ρ; exact ih a _ hist ρ
  | conj p q ihp ihq =>
      intro a v hist ρ
      simp only [run]
      split
      · split
        · exact ((List.prefix_append _ _).trans (ihp _ _ _ _)).trans (ihq _ _ _ _)
        · exact List.prefix_refl _
      · exact List.prefix_refl _
  | disj p q ihp ihq =>
      intro a v hist ρ
      simp only [run]
      split
      · split
        · exact ((List.prefix_append _ _).trans (ihp _ _ _ _)).trans (ihq _ _ _ _)
        · exact List.prefix_refl _
      · exact List.prefix_refl _
  | all i p ih =>
      intro a v hist ρ
      simp only [run]
      split
      · exact (List.prefix_append _ _).trans (ih _ _ _ _)
      · exact List.prefix_refl _
  | ex i p ih =>
      intro a v hist ρ
      simp only [run]
      split
      · exact (List.prefix_append _ _).trans (ih _ _ _ _)
      · exact List.prefix_refl _
  | lin j p ih =>
      intro a v hist ρ
      simp only [run]
      split
      · exact (List.prefix_append _ _).trans (ih _ _ _ _)
      · exact List.prefix_refl _

/-- An accepted run at a binary node, unfolded. -/
theorem run_bin_accept (d : ℕ) (P : Strat F) (p q t : Op) (comb : F → F → F)
    (a : ℕ → F) (v : F) (hist : List (List F)) (ρ : List F)
    (hrun : run d P t a v hist ρ =
      match P hist t a with
      | [b, c] =>
          if comb b c = v then
            ((run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)).1 &&
              (run d P q a c (run d P p a b (hist ++ [[b, c], [ρ.headD 0]])
                (ρ.tail.take p.rounds)).2 (ρ.tail.drop p.rounds)).1,
             (run d P q a c (run d P p a b (hist ++ [[b, c], [ρ.headD 0]])
                (ρ.tail.take p.rounds)).2 (ρ.tail.drop p.rounds)).2)
          else (false, hist)
      | _ => (false, hist))
    (h : (run d P t a v hist ρ).1 = true) :
    ∃ b c, P hist t a = [b, c] ∧ comb b c = v ∧
      (run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)).1 = true ∧
      (run d P q a c (run d P p a b (hist ++ [[b, c], [ρ.headD 0]])
        (ρ.tail.take p.rounds)).2 (ρ.tail.drop p.rounds)).1 = true ∧
      (run d P t a v hist ρ).2 = (run d P q a c (run d P p a b (hist ++ [[b, c], [ρ.headD 0]])
        (ρ.tail.take p.rounds)).2 (ρ.tail.drop p.rounds)).2 := by
  rw [hrun] at h ⊢
  split at h
  · rename_i b c hm
    split at h
    · rename_i hbc
      simp only [Bool.and_eq_true] at h
      exact ⟨b, c, hm, hbc, h.1, h.2, by simp [hbc]⟩
    · simp at h
  · simp at h

theorem run_conj_def (d : ℕ) (P : Strat F) (p q : Op) (a : ℕ → F) (v : F)
    (hist : List (List F)) (ρ : List F) :
    run d P (.conj p q) a v hist ρ =
      match P hist (.conj p q) a with
      | [b, c] =>
          if b * c = v then
            ((run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)).1 &&
              (run d P q a c (run d P p a b (hist ++ [[b, c], [ρ.headD 0]])
                (ρ.tail.take p.rounds)).2 (ρ.tail.drop p.rounds)).1,
             (run d P q a c (run d P p a b (hist ++ [[b, c], [ρ.headD 0]])
                (ρ.tail.take p.rounds)).2 (ρ.tail.drop p.rounds)).2)
          else (false, hist)
      | _ => (false, hist) := by
  rw [run]; rfl

theorem run_disj_def (d : ℕ) (P : Strat F) (p q : Op) (a : ℕ → F) (v : F)
    (hist : List (List F)) (ρ : List F) :
    run d P (.disj p q) a v hist ρ =
      match P hist (.disj p q) a with
      | [b, c] =>
          if 1 - (1 - b) * (1 - c) = v then
            ((run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)).1 &&
              (run d P q a c (run d P p a b (hist ++ [[b, c], [ρ.headD 0]])
                (ρ.tail.take p.rounds)).2 (ρ.tail.drop p.rounds)).1,
             (run d P q a c (run d P p a b (hist ++ [[b, c], [ρ.headD 0]])
                (ρ.tail.take p.rounds)).2 (ρ.tail.drop p.rounds)).2)
          else (false, hist)
      | _ => (false, hist) := by
  rw [run]; rfl

/-- An accepted run at a round node, unfolded. -/
theorem run_round_accept (d : ℕ) (P : Strat F) (p t : Op) (i : ℕ) (check : List F → Prop)
    [DecidablePred check] (a : ℕ → F) (v : F) (hist : List (List F)) (ρ : List F)
    (hrun : run d P t a v hist ρ =
      if (P hist t a).length ≤ d + 1 ∧ check (P hist t a) then
        run d P p (Function.update a i (ρ.headD 0)) (evalL (P hist t a) (ρ.headD 0))
          (hist ++ [P hist t a, [ρ.headD 0]]) ρ.tail
      else (false, hist))
    (h : (run d P t a v hist ρ).1 = true) :
    (P hist t a).length ≤ d + 1 ∧ check (P hist t a) ∧
      run d P t a v hist ρ =
        run d P p (Function.update a i (ρ.headD 0)) (evalL (P hist t a) (ρ.headD 0))
          (hist ++ [P hist t a, [ρ.headD 0]]) ρ.tail := by
  rw [hrun] at h ⊢
  split at h
  · rename_i hc; exact ⟨hc.1, hc.2, by rw [if_pos hc]⟩
  · simp at h

theorem run_all_def (d : ℕ) (P : Strat F) (p : Op) (i : ℕ) (a : ℕ → F) (v : F)
    (hist : List (List F)) (ρ : List F) :
    run d P (.all i p) a v hist ρ =
      if (P hist (.all i p) a).length ≤ d + 1 ∧
          (fun m => evalL m 0 * evalL m 1 = v) (P hist (.all i p) a) then
        run d P p (Function.update a i (ρ.headD 0)) (evalL (P hist (.all i p) a) (ρ.headD 0))
          (hist ++ [P hist (.all i p) a, [ρ.headD 0]]) ρ.tail
      else (false, hist) := by
  rw [run]

theorem run_ex_def (d : ℕ) (P : Strat F) (p : Op) (i : ℕ) (a : ℕ → F) (v : F)
    (hist : List (List F)) (ρ : List F) :
    run d P (.ex i p) a v hist ρ =
      if (P hist (.ex i p) a).length ≤ d + 1 ∧
          (fun m => 1 - (1 - evalL m 0) * (1 - evalL m 1) = v) (P hist (.ex i p) a) then
        run d P p (Function.update a i (ρ.headD 0)) (evalL (P hist (.ex i p) a) (ρ.headD 0))
          (hist ++ [P hist (.ex i p) a, [ρ.headD 0]]) ρ.tail
      else (false, hist) := by
  rw [run]

theorem run_lin_def (d : ℕ) (P : Strat F) (p : Op) (j : ℕ) (a : ℕ → F) (v : F)
    (hist : List (List F)) (ρ : List F) :
    run d P (.lin j p) a v hist ρ =
      if (P hist (.lin j p) a).length ≤ d + 1 ∧
          (fun m => a j * evalL m 1 + (1 - a j) * evalL m 0 = v) (P hist (.lin j p) a) then
        run d P p (Function.update a j (ρ.headD 0)) (evalL (P hist (.lin j p) a) (ρ.headD 0))
          (hist ++ [P hist (.lin j p) a, [ρ.headD 0]]) ρ.tail
      else (false, hist) := by
  rw [run]

/-- **The history of an accepting run**: the starting history, then one message and one random
point per round. -/
theorem run_out (d : ℕ) (P : Strat F) :
    ∀ (t : Op) (a : ℕ → F) (v : F) (hist : List (List F)) (ρ : List F),
      ρ.length = t.rounds → (run d P t a v hist ρ).1 = true →
      ∃ ms : List (List F), ms.length = t.rounds ∧ (∀ m ∈ ms, ∃ H n x, m = P H n x) ∧
        (run d P t a v hist ρ).2 = hist ++ inter ms ρ := by
  intro t
  induction t with
  | var i =>
      intro a v hist ρ hρ _
      simp only [Op.rounds, List.length_eq_zero_iff] at hρ
      subst hρ
      exact ⟨[], rfl, by simp, by simp [run, inter]⟩
  | neg p ih => intro a v hist ρ hρ h; exact ih a _ hist ρ hρ h
  | conj p q ihp ihq =>
      intro a v hist ρ hρ h
      obtain ⟨b, c, hbc, _, h1, h2, hout⟩ :=
        run_bin_accept d P p q _ (· * ·) a v hist ρ (run_conj_def d P p q a v hist ρ) h
      obtain ⟨hl1, hl2⟩ := rounds_conj_tail hρ
      obtain ⟨ms₁, hm₁, hP₁, he₁⟩ := ihp _ _ _ _ hl1 h1
      obtain ⟨ms₂, hm₂, hP₂, he₂⟩ := ihq _ _ _ _ hl2 h2
      obtain ⟨s, ρ', rfl⟩ : ∃ s ρ', ρ = s :: ρ' := by
        cases ρ with
        | nil => simp [Op.rounds] at hρ
        | cons s ρ' => exact ⟨s, ρ', rfl⟩
      refine ⟨[b, c] :: (ms₁ ++ ms₂), by simp [Op.rounds, hm₁, hm₂]; try omega, ?_, ?_⟩
      · intro m hm
        simp only [List.mem_cons, List.mem_append] at hm
        rcases hm with rfl | hm | hm
        · exact ⟨_, _, _, hbc.symm⟩
        · exact hP₁ m hm
        · exact hP₂ m hm
      rw [hout, he₂, he₁]
      simp only [List.headD_cons, List.tail_cons] at hl1 ⊢
      rw [show inter ([b, c] :: (ms₁ ++ ms₂)) (s :: ρ') =
          [b, c] :: [s] :: inter (ms₁ ++ ms₂) (ρ'.take p.rounds ++ ρ'.drop p.rounds) by
        rw [List.take_append_drop]; rfl, inter_append _ _ _ _ (by rw [hm₁, hl1])]
      simp
  | disj p q ihp ihq =>
      intro a v hist ρ hρ h
      obtain ⟨b, c, hbc, _, h1, h2, hout⟩ := run_bin_accept d P p q _
        (fun b c => 1 - (1 - b) * (1 - c)) a v hist ρ (run_disj_def d P p q a v hist ρ) h
      obtain ⟨hl1, hl2⟩ := rounds_conj_tail (q := q) (by simpa [Op.rounds] using hρ)
      obtain ⟨ms₁, hm₁, hP₁, he₁⟩ := ihp _ _ _ _ hl1 h1
      obtain ⟨ms₂, hm₂, hP₂, he₂⟩ := ihq _ _ _ _ hl2 h2
      obtain ⟨s, ρ', rfl⟩ : ∃ s ρ', ρ = s :: ρ' := by
        cases ρ with
        | nil => simp [Op.rounds] at hρ
        | cons s ρ' => exact ⟨s, ρ', rfl⟩
      refine ⟨[b, c] :: (ms₁ ++ ms₂), by simp [Op.rounds, hm₁, hm₂]; try omega, ?_, ?_⟩
      · intro m hm
        simp only [List.mem_cons, List.mem_append] at hm
        rcases hm with rfl | hm | hm
        · exact ⟨_, _, _, hbc.symm⟩
        · exact hP₁ m hm
        · exact hP₂ m hm
      rw [hout, he₂, he₁]
      simp only [List.headD_cons, List.tail_cons] at hl1 ⊢
      rw [show inter ([b, c] :: (ms₁ ++ ms₂)) (s :: ρ') =
          [b, c] :: [s] :: inter (ms₁ ++ ms₂) (ρ'.take p.rounds ++ ρ'.drop p.rounds) by
        rw [List.take_append_drop]; rfl, inter_append _ _ _ _ (by rw [hm₁, hl1])]
      simp
  | all i p ih =>
      intro a v hist ρ hρ h
      obtain ⟨_, _, heq⟩ := run_round_accept d P p _ i (fun m => evalL m 0 * evalL m 1 = v) a v hist ρ (run_all_def d P p i a v hist ρ) h
      obtain ⟨s, ρ', rfl⟩ : ∃ s ρ', ρ = s :: ρ' := by
        cases ρ with
        | nil => simp [Op.rounds] at hρ
        | cons s ρ' => exact ⟨s, ρ', rfl⟩
      rw [heq] at h ⊢
      obtain ⟨ms, hm, hP, he⟩ := ih _ _ _ _ (by simpa [Op.rounds] using hρ) h
      refine ⟨P hist (Op.all i p) a :: ms, by simp [Op.rounds, hm], ?_, by rw [he]; simp [inter]⟩
      intro m hm'
      rcases List.mem_cons.1 hm' with rfl | hm'
      · exact ⟨_, _, _, rfl⟩
      · exact hP m hm'
  | ex i p ih =>
      intro a v hist ρ hρ h
      obtain ⟨_, _, heq⟩ := run_round_accept d P p _ i (fun m => 1 - (1 - evalL m 0) * (1 - evalL m 1) = v) a v hist ρ
        (run_ex_def d P p i a v hist ρ) h
      obtain ⟨s, ρ', rfl⟩ : ∃ s ρ', ρ = s :: ρ' := by
        cases ρ with
        | nil => simp [Op.rounds] at hρ
        | cons s ρ' => exact ⟨s, ρ', rfl⟩
      rw [heq] at h ⊢
      obtain ⟨ms, hm, hP, he⟩ := ih _ _ _ _ (by simpa [Op.rounds] using hρ) h
      refine ⟨P hist (Op.ex i p) a :: ms, by simp [Op.rounds, hm], ?_, by rw [he]; simp [inter]⟩
      intro m hm'
      rcases List.mem_cons.1 hm' with rfl | hm'
      · exact ⟨_, _, _, rfl⟩
      · exact hP m hm'
  | lin j p ih =>
      intro a v hist ρ hρ h
      obtain ⟨_, _, heq⟩ := run_round_accept d P p _ j (fun m => a j * evalL m 1 + (1 - a j) * evalL m 0 = v) a v hist ρ
        (run_lin_def d P p j a v hist ρ) h
      obtain ⟨s, ρ', rfl⟩ : ∃ s ρ', ρ = s :: ρ' := by
        cases ρ with
        | nil => simp [Op.rounds] at hρ
        | cons s ρ' => exact ⟨s, ρ', rfl⟩
      rw [heq] at h ⊢
      obtain ⟨ms, hm, hP, he⟩ := ih _ _ _ _ (by simpa [Op.rounds] using hρ) h
      refine ⟨P hist (Op.lin j p) a :: ms, by simp [Op.rounds, hm], ?_, by rw [he]; simp [inter]⟩
      intro m hm'
      rcases List.mem_cons.1 hm' with rfl | hm'
      · exact ⟨_, _, _, rfl⟩
      · exact hP m hm'

omit [Field F] [DecidableEq F] in
theorem prefix_getD {α : Type*} {A B : List α} (h : A <+: B) {i : ℕ} (hi : i < A.length) (x : α) :
    B.getD i x = A.getD i x := by
  obtain ⟨C, rfl⟩ := h
  exact List.getD_append A C x i hi

omit [Field F] [DecidableEq F] in
theorem prefix_take {α : Type*} {A B : List α} (h : A <+: B) {i : ℕ} (hi : i ≤ A.length) :
    B.take i = A.take i := by
  obtain ⟨C, rfl⟩ := h
  exact List.take_append_of_le_length hi

theorem length_run_out (d : ℕ) (P : Strat F) (t : Op) (a : ℕ → F) (v : F) (hist : List (List F))
    (ρ : List F) (hρ : ρ.length = t.rounds) (h : (run d P t a v hist ρ).1 = true) :
    (run d P t a v hist ρ).2.length = hist.length + 2 * t.rounds := by
  obtain ⟨ms, hm, _, he⟩ := run_out d P t a v hist ρ hρ h
  rw [he, List.length_append, length_inter ms ρ (by rw [hm, hρ]), hρ]

/-! ### Replaying a run -/

/-- **Replaying an accepting run**: a strategy that answers every query with the message recorded
at that position of the history of the run produces the same run. -/
theorem run_replay (d : ℕ) (P Q : Strat F) :
    ∀ (t : Op) (a : ℕ → F) (v : F) (hist : List (List F)) (ρ : List F),
      ρ.length = t.rounds → (run d P t a v hist ρ).1 = true →
      (∀ H n x, H <+: (run d P t a v hist ρ).2 → H.length < (run d P t a v hist ρ).2.length →
        Q H n x = (run d P t a v hist ρ).2.getD H.length []) →
      run d Q t a v hist ρ = run d P t a v hist ρ := by
  intro t
  induction t with
  | var i => intro a v hist ρ _ _ _; rfl
  | neg p ih => intro a v hist ρ hρ h hQ; exact ih a _ hist ρ hρ h hQ
  | conj p q ihp ihq =>
      intro a v hist ρ hρ h hQ
      obtain ⟨b, c, hm, hbc, h1, h2, hout⟩ :=
        run_bin_accept d P p q _ (· * ·) a v hist ρ (run_conj_def d P p q a v hist ρ) h
      obtain ⟨hl1, hl2⟩ := rounds_conj_tail hρ
      have hp1 := run_prefix d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)
      have hp2 : (run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)).2 <+:
          (run d P (.conj p q) a v hist ρ).2 := by rw [hout]; exact run_prefix ..
      have hp0 := hp1.trans hp2
      have hQm : Q hist (.conj p q) a = [b, c] := by
        rw [hQ hist _ _ ((List.prefix_append _ _).trans hp0)
          (lt_of_lt_of_le (by simp) hp0.length_le), prefix_getD hp0 (by simp)]
        simp
      have e1 := ihp a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds) hl1 h1
        (fun H n x hH hlt => by
          rw [hQ H n x (hH.trans hp2) (lt_of_lt_of_le hlt hp2.length_le), prefix_getD hp2 hlt])
      have e2 := ihq a c _ (ρ.tail.drop p.rounds) hl2 h2
        (fun H n x hH hlt => by rw [← hout] at hH hlt ⊢; exact hQ H n x hH hlt)
      rw [run_conj_def, run_conj_def, hQm, hm]
      simp only [if_pos hbc, e1, e2]
  | disj p q ihp ihq =>
      intro a v hist ρ hρ h hQ
      obtain ⟨b, c, hm, hbc, h1, h2, hout⟩ := run_bin_accept d P p q _
        (fun b c => 1 - (1 - b) * (1 - c)) a v hist ρ (run_disj_def d P p q a v hist ρ) h
      obtain ⟨hl1, hl2⟩ := rounds_conj_tail (q := q) (by simpa [Op.rounds] using hρ)
      have hp1 := run_prefix d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)
      have hp2 : (run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)).2 <+:
          (run d P (.disj p q) a v hist ρ).2 := by rw [hout]; exact run_prefix ..
      have hp0 := hp1.trans hp2
      have hQm : Q hist (.disj p q) a = [b, c] := by
        rw [hQ hist _ _ ((List.prefix_append _ _).trans hp0)
          (lt_of_lt_of_le (by simp) hp0.length_le), prefix_getD hp0 (by simp)]
        simp
      have e1 := ihp a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds) hl1 h1
        (fun H n x hH hlt => by
          rw [hQ H n x (hH.trans hp2) (lt_of_lt_of_le hlt hp2.length_le), prefix_getD hp2 hlt])
      have e2 := ihq a c _ (ρ.tail.drop p.rounds) hl2 h2
        (fun H n x hH hlt => by rw [← hout] at hH hlt ⊢; exact hQ H n x hH hlt)
      rw [run_disj_def, run_disj_def, hQm, hm]
      simp only [if_pos hbc, e1, e2]
  | all i p ih =>
      intro a v hist ρ hρ h hQ
      obtain ⟨hl, hc, heq⟩ := run_round_accept d P p _ i (fun m => evalL m 0 * evalL m 1 = v)
        a v hist ρ (run_all_def d P p i a v hist ρ) h
      have hp0 : hist ++ [P hist (.all i p) a, [ρ.headD 0]] <+:
          (run d P (.all i p) a v hist ρ).2 := by rw [heq]; exact run_prefix ..
      have hQm : Q hist (.all i p) a = P hist (.all i p) a := by
        rw [hQ hist _ _ ((List.prefix_append _ _).trans hp0)
          (lt_of_lt_of_le (by simp) hp0.length_le), prefix_getD hp0 (by simp)]
        simp
      rw [heq] at h hQ ⊢
      rw [run_all_def, hQm, if_pos ⟨hl, hc⟩]
      exact ih _ _ _ _ (by simp only [Op.rounds] at hρ; simp [hρ]) h hQ
  | ex i p ih =>
      intro a v hist ρ hρ h hQ
      obtain ⟨hl, hc, heq⟩ := run_round_accept d P p _ i
        (fun m => 1 - (1 - evalL m 0) * (1 - evalL m 1) = v)
        a v hist ρ (run_ex_def d P p i a v hist ρ) h
      have hp0 : hist ++ [P hist (.ex i p) a, [ρ.headD 0]] <+:
          (run d P (.ex i p) a v hist ρ).2 := by rw [heq]; exact run_prefix ..
      have hQm : Q hist (.ex i p) a = P hist (.ex i p) a := by
        rw [hQ hist _ _ ((List.prefix_append _ _).trans hp0)
          (lt_of_lt_of_le (by simp) hp0.length_le), prefix_getD hp0 (by simp)]
        simp
      rw [heq] at h hQ ⊢
      rw [run_ex_def, hQm, if_pos ⟨hl, hc⟩]
      exact ih _ _ _ _ (by simp only [Op.rounds] at hρ; simp [hρ]) h hQ
  | lin j p ih =>
      intro a v hist ρ hρ h hQ
      obtain ⟨hl, hc, heq⟩ := run_round_accept d P p _ j
        (fun m => a j * evalL m 1 + (1 - a j) * evalL m 0 = v)
        a v hist ρ (run_lin_def d P p j a v hist ρ) h
      have hp0 : hist ++ [P hist (.lin j p) a, [ρ.headD 0]] <+:
          (run d P (.lin j p) a v hist ρ).2 := by rw [heq]; exact run_prefix ..
      have hQm : Q hist (.lin j p) a = P hist (.lin j p) a := by
        rw [hQ hist _ _ ((List.prefix_append _ _).trans hp0)
          (lt_of_lt_of_le (by simp) hp0.length_le), prefix_getD hp0 (by simp)]
        simp
      rw [heq] at h hQ ⊢
      rw [run_lin_def, hQm, if_pos ⟨hl, hc⟩]
      exact ih _ _ _ _ (by simp only [Op.rounds] at hρ; simp [hρ]) h hQ

/-! ### Causality -/

omit [Field F] [DecidableEq F] in
theorem take_eq_of_le {α : Type*} {l l' : List α} {m k : ℕ} (h : l.take m = l'.take m)
    (hk : k ≤ m) : l.take k = l'.take k := by
  have := congrArg (List.take k) h
  rwa [List.take_take, List.take_take, min_eq_left hk] at this

omit [Field F] [DecidableEq F] in
theorem take_take_le {α : Type*} {l : List α} {n k : ℕ} (h : k ≤ n) :
    (l.take n).take k = l.take k := by
  rw [List.take_take, min_eq_left h]

omit [Field F] [DecidableEq F] in
theorem take_tail_eq {α : Type*} {l l' : List α} {k : ℕ} (h : l.take (k + 1) = l'.take (k + 1)) :
    l.tail.take k = l'.tail.take k := by
  cases l <;> cases l' <;> simp_all

omit [Field F] [DecidableEq F] in
theorem headD_eq_of_take {α : Type*} {l l' : List α} {k : ℕ} (x : α)
    (h : l.take (k + 1) = l'.take (k + 1)) : l.headD x = l'.headD x := by
  cases l <;> cases l' <;> simp_all

omit [Field F] [DecidableEq F] in
/-- The first `|H| + 1` entries of a history extending `H ++ [m, s]` are `H ++ [m]`. -/
theorem take_succ_of_prefix {α : Type*} {H X : List α} {m s : α} (h : H ++ [m, s] <+: X) :
    X.take (H.length + 1) = H ++ [m] := by
  rw [prefix_take h (by simp)]
  simp [List.take_append]

/-- The binary step of the causality induction. -/
theorem run_causal_bin (d : ℕ) (P : Strat F) (p q : Op) (hist : List (List F)) (a : ℕ → F)
    (b c : F) (ρ ρ' : List F) (k : ℕ) (hρ : ρ.length = (Op.conj p q).rounds)
    (hρ' : ρ'.length = (Op.conj p q).rounds)
    (h1 : (run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)).1 = true)
    (h2 : (run d P q a c (run d P p a b (hist ++ [[b, c], [ρ.headD 0]])
      (ρ.tail.take p.rounds)).2 (ρ.tail.drop p.rounds)).1 = true)
    (h1' : (run d P p a b (hist ++ [[b, c], [ρ'.headD 0]]) (ρ'.tail.take p.rounds)).1 = true)
    (h2' : (run d P q a c (run d P p a b (hist ++ [[b, c], [ρ'.headD 0]])
      (ρ'.tail.take p.rounds)).2 (ρ'.tail.drop p.rounds)).1 = true)
    (hk : ρ.take k = ρ'.take k)
    (ihp : ∀ (a : ℕ → F) (v : F) (hist : List (List F)) (ρ ρ' : List F) (k : ℕ),
      ρ.length = p.rounds → ρ'.length = p.rounds →
      (run d P p a v hist ρ).1 = true → (run d P p a v hist ρ').1 = true →
      ρ.take k = ρ'.take k →
      (run d P p a v hist ρ).2.take (hist.length + 2 * k + 1) =
        (run d P p a v hist ρ').2.take (hist.length + 2 * k + 1))
    (ihq : ∀ (a : ℕ → F) (v : F) (hist : List (List F)) (ρ ρ' : List F) (k : ℕ),
      ρ.length = q.rounds → ρ'.length = q.rounds →
      (run d P q a v hist ρ).1 = true → (run d P q a v hist ρ').1 = true →
      ρ.take k = ρ'.take k →
      (run d P q a v hist ρ).2.take (hist.length + 2 * k + 1) =
        (run d P q a v hist ρ').2.take (hist.length + 2 * k + 1)) :
    (run d P q a c (run d P p a b (hist ++ [[b, c], [ρ.headD 0]])
      (ρ.tail.take p.rounds)).2 (ρ.tail.drop p.rounds)).2.take (hist.length + 2 * k + 1) =
    (run d P q a c (run d P p a b (hist ++ [[b, c], [ρ'.headD 0]])
      (ρ'.tail.take p.rounds)).2 (ρ'.tail.drop p.rounds)).2.take (hist.length + 2 * k + 1) := by
  obtain ⟨hl1, hl2⟩ := rounds_conj_tail hρ
  obtain ⟨hl1', hl2'⟩ := rounds_conj_tail hρ'
  rcases k with _ | k
  · rw [take_succ_of_prefix ((run_prefix ..).trans (run_prefix ..)),
      take_succ_of_prefix ((run_prefix ..).trans (run_prefix ..))]
  · have hs := headD_eq_of_take 0 hk
    have ht := take_tail_eq hk
    rw [← hs] at h1' h2' ⊢
    have hlen := length_run_out d P p a b _ _ hl1 h1
    have hlen' := length_run_out d P p a b _ _ hl1' h1'
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen hlen'
    by_cases hkp : k < p.rounds
    · have e := ihp a b (hist ++ [[b, c], [ρ.headD 0]]) _ _ k hl1 hl1' h1 h1'
        (by rw [take_take_le hkp.le, take_take_le hkp.le]; exact ht)
      simp only [List.length_append, List.length_cons, List.length_nil] at e
      have hw : hist.length + 2 * (k + 1) + 1 = hist.length + (0 + 1 + 1) + 2 * k + 1 := by ring
      have hA : hist.length + (0 + 1 + 1) + 2 * k + 1 ≤
          (run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)).2.length := by
        omega
      have hA' : hist.length + (0 + 1 + 1) + 2 * k + 1 ≤
          (run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ'.tail.take p.rounds)).2.length := by
        omega
      rw [hw, prefix_take (run_prefix d P q a c _ (ρ.tail.drop p.rounds)) hA,
        prefix_take (run_prefix d P q a c _ (ρ'.tail.drop p.rounds)) hA', e]
    · rw [not_lt] at hkp
      have e := ihp a b (hist ++ [[b, c], [ρ.headD 0]]) _ _ p.rounds hl1 hl1' h1 h1'
        (by rw [take_take_le le_rfl, take_take_le le_rfl]; exact take_eq_of_le ht hkp)
      have hA : (run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)).2.length ≤
          (hist ++ [[b, c], [ρ.headD 0]]).length + 2 * p.rounds + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hA' : (run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ'.tail.take p.rounds)).2.length ≤
          (hist ++ [[b, c], [ρ.headD 0]]).length + 2 * p.rounds + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [List.take_of_length_le hA, List.take_of_length_le hA'] at e
      rw [← e] at h2' ⊢
      have e2 := ihq a c _ _ _ (k - p.rounds) hl2 hl2' h2 h2'
        (by rw [List.take_drop, List.take_drop, Nat.add_sub_cancel' hkp, ht])
      rw [hlen] at e2
      have hw : hist.length + 2 * (k + 1) + 1 =
          hist.length + (0 + 1 + 1) + 2 * p.rounds + 2 * (k - p.rounds) + 1 := by omega
      rw [hw, e2]

/-- **Causality**: in two accepting runs whose random points agree up to `k`, the histories agree
up to and including the `k`-th message. -/
theorem run_causal (d : ℕ) (P : Strat F) :
    ∀ (t : Op) (a : ℕ → F) (v : F) (hist : List (List F)) (ρ ρ' : List F) (k : ℕ),
      ρ.length = t.rounds → ρ'.length = t.rounds →
      (run d P t a v hist ρ).1 = true → (run d P t a v hist ρ').1 = true →
      ρ.take k = ρ'.take k →
      (run d P t a v hist ρ).2.take (hist.length + 2 * k + 1) =
        (run d P t a v hist ρ').2.take (hist.length + 2 * k + 1) := by
  intro t
  induction t with
  | var i => intro a v hist ρ ρ' k _ _ _ _ _; rfl
  | neg p ih => intro a v hist ρ ρ' k hρ hρ' h h' hk; exact ih a _ hist ρ ρ' k hρ hρ' h h' hk
  | conj p q ihp ihq =>
      intro a v hist ρ ρ' k hρ hρ' h h' hk
      obtain ⟨b, c, hm, hbc, h1, h2, hout⟩ :=
        run_bin_accept d P p q _ (· * ·) a v hist ρ (run_conj_def d P p q a v hist ρ) h
      obtain ⟨b', c', hm', hbc', h1', h2', hout'⟩ :=
        run_bin_accept d P p q _ (· * ·) a v hist ρ' (run_conj_def d P p q a v hist ρ') h'
      rw [hm] at hm'
      simp only [List.cons.injEq, and_true] at hm'
      obtain ⟨rfl, rfl⟩ := hm'
      rw [hout, hout']
      exact run_causal_bin d P p q hist a b c ρ ρ' k hρ hρ' h1 h2 h1' h2' hk ihp ihq
  | disj p q ihp ihq =>
      intro a v hist ρ ρ' k hρ hρ' h h' hk
      obtain ⟨b, c, hm, hbc, h1, h2, hout⟩ := run_bin_accept d P p q _
        (fun b c => 1 - (1 - b) * (1 - c)) a v hist ρ (run_disj_def d P p q a v hist ρ) h
      obtain ⟨b', c', hm', hbc', h1', h2', hout'⟩ := run_bin_accept d P p q _
        (fun b c => 1 - (1 - b) * (1 - c)) a v hist ρ' (run_disj_def d P p q a v hist ρ') h'
      rw [hm] at hm'
      simp only [List.cons.injEq, and_true] at hm'
      obtain ⟨rfl, rfl⟩ := hm'
      rw [hout, hout']
      exact run_causal_bin d P p q hist a b c ρ ρ' k (by simpa [Op.rounds] using hρ)
        (by simpa [Op.rounds] using hρ') h1 h2 h1' h2' hk ihp ihq
  | all i p ih =>
      intro a v hist ρ ρ' k hρ hρ' h h' hk
      obtain ⟨hl, hc, heq⟩ := run_round_accept d P p _ i (fun m => evalL m 0 * evalL m 1 = v)
        a v hist ρ (run_all_def d P p i a v hist ρ) h
      obtain ⟨hl', hc', heq'⟩ := run_round_accept d P p _ i (fun m => evalL m 0 * evalL m 1 = v)
        a v hist ρ' (run_all_def d P p i a v hist ρ') h'
      rw [heq] at h ⊢
      rw [heq'] at h' ⊢
      rcases k with _ | k
      · rw [take_succ_of_prefix (run_prefix ..), take_succ_of_prefix (run_prefix ..)]
      · rw [← headD_eq_of_take 0 hk] at h' ⊢
        have e := ih _ _ _ _ _ k (by simp only [Op.rounds] at hρ; simp [hρ])
          (by simp only [Op.rounds] at hρ'; simp [hρ']) h h' (take_tail_eq hk)
        simp only [List.length_append, List.length_cons, List.length_nil] at e
        rw [show hist.length + 2 * (k + 1) + 1 = hist.length + (0 + 1 + 1) + 2 * k + 1 by ring, e]
  | ex i p ih =>
      intro a v hist ρ ρ' k hρ hρ' h h' hk
      obtain ⟨hl, hc, heq⟩ := run_round_accept d P p _ i
        (fun m => 1 - (1 - evalL m 0) * (1 - evalL m 1) = v)
        a v hist ρ (run_ex_def d P p i a v hist ρ) h
      obtain ⟨hl', hc', heq'⟩ := run_round_accept d P p _ i
        (fun m => 1 - (1 - evalL m 0) * (1 - evalL m 1) = v)
        a v hist ρ' (run_ex_def d P p i a v hist ρ') h'
      rw [heq] at h ⊢
      rw [heq'] at h' ⊢
      rcases k with _ | k
      · rw [take_succ_of_prefix (run_prefix ..), take_succ_of_prefix (run_prefix ..)]
      · rw [← headD_eq_of_take 0 hk] at h' ⊢
        have e := ih _ _ _ _ _ k (by simp only [Op.rounds] at hρ; simp [hρ])
          (by simp only [Op.rounds] at hρ'; simp [hρ']) h h' (take_tail_eq hk)
        simp only [List.length_append, List.length_cons, List.length_nil] at e
        rw [show hist.length + 2 * (k + 1) + 1 = hist.length + (0 + 1 + 1) + 2 * k + 1 by ring, e]
  | lin j p ih =>
      intro a v hist ρ ρ' k hρ hρ' h h' hk
      obtain ⟨hl, hc, heq⟩ := run_round_accept d P p _ j
        (fun m => a j * evalL m 1 + (1 - a j) * evalL m 0 = v)
        a v hist ρ (run_lin_def d P p j a v hist ρ) h
      obtain ⟨hl', hc', heq'⟩ := run_round_accept d P p _ j
        (fun m => a j * evalL m 1 + (1 - a j) * evalL m 0 = v)
        a v hist ρ' (run_lin_def d P p j a v hist ρ') h'
      rw [heq] at h ⊢
      rw [heq'] at h' ⊢
      rcases k with _ | k
      · rw [take_succ_of_prefix (run_prefix ..), take_succ_of_prefix (run_prefix ..)]
      · rw [← headD_eq_of_take 0 hk] at h' ⊢
        have e := ih _ _ _ _ _ k (by simp only [Op.rounds] at hρ; simp [hρ])
          (by simp only [Op.rounds] at hρ'; simp [hρ']) h h' (take_tail_eq hk)
        simp only [List.length_append, List.length_cons, List.length_nil] at e
        rw [show hist.length + 2 * (k + 1) + 1 = hist.length + (0 + 1 + 1) + 2 * k + 1 by ring, e]

/-! ### Congruence -/

omit [DecidableEq F] in
theorem ptsOf_pair (m : List F) (s : F) : ptsOf [m, [s]] = [s] := rfl

omit [DecidableEq F] in
theorem ptsOf_hist_pair {hist : List (List F)} (he : Even hist.length) (m : List F) (s : F) :
    ptsOf (hist ++ [m, [s]]) = ptsOf hist ++ [s] := by
  rw [ptsOf_append _ _ he, ptsOf_pair]

omit [Field F] [DecidableEq F] in
theorem even_hist_pair {hist : List (List F)} (he : Even hist.length) (m₁ m₂ : List F) :
    Even (hist ++ [m₁, m₂]).length := by
  simpa [Nat.even_add_one] using he

/-- The round step of the congruence induction. -/
theorem run_congr_round (d : ℕ) (P Q : Strat F) (p : Op) (hist : List (List F)) (m : List F)
    (ρ R : List F) (a' : F → ℕ → F) (v' : F → F) (hρ : ρ.length = p.rounds + 1)
    (he : Even hist.length)
    (hPQ : ∀ H n x, Even H.length → ptsOf H <+: ptsOf hist ++ ρ ++ R → P H n x = Q H n x)
    (ih : ∀ (a : ℕ → F) (v : F) (hist : List (List F)) (ρ R : List F),
      ρ.length = p.rounds → Even hist.length →
      (∀ H n x, Even H.length → ptsOf H <+: ptsOf hist ++ ρ ++ R → P H n x = Q H n x) →
      (run d P p a v hist ρ).1 = (run d Q p a v hist ρ).1 ∧
        ((run d P p a v hist ρ).1 = true → (run d P p a v hist ρ).2 = (run d Q p a v hist ρ).2)) :
    (run d P p (a' (ρ.headD 0)) (v' (ρ.headD 0)) (hist ++ [m, [ρ.headD 0]]) ρ.tail).1 =
        (run d Q p (a' (ρ.headD 0)) (v' (ρ.headD 0)) (hist ++ [m, [ρ.headD 0]]) ρ.tail).1 ∧
      ((run d P p (a' (ρ.headD 0)) (v' (ρ.headD 0)) (hist ++ [m, [ρ.headD 0]]) ρ.tail).1 = true →
        (run d P p (a' (ρ.headD 0)) (v' (ρ.headD 0)) (hist ++ [m, [ρ.headD 0]]) ρ.tail).2 =
          (run d Q p (a' (ρ.headD 0)) (v' (ρ.headD 0)) (hist ++ [m, [ρ.headD 0]]) ρ.tail).2) := by
  obtain ⟨s, ρ', rfl⟩ : ∃ s ρ', ρ = s :: ρ' := by
    cases ρ with
    | nil => simp at hρ
    | cons s ρ' => exact ⟨s, ρ', rfl⟩
  refine ih _ _ _ _ R (by simpa using hρ) (even_hist_pair he _ _) fun H n x hH hp => hPQ H n x hH ?_
  rw [ptsOf_hist_pair he] at hp
  simpa using hp

/-- **Congruence**: two strategies that agree on every history whose recorded points are a prefix
of the points of the run give the same verdict, and the same history when they accept. -/
theorem run_congr (d : ℕ) (P Q : Strat F) :
    ∀ (t : Op) (a : ℕ → F) (v : F) (hist : List (List F)) (ρ R : List F),
      ρ.length = t.rounds → Even hist.length →
      (∀ H n x, Even H.length → ptsOf H <+: ptsOf hist ++ ρ ++ R → P H n x = Q H n x) →
      (run d P t a v hist ρ).1 = (run d Q t a v hist ρ).1 ∧
        ((run d P t a v hist ρ).1 = true →
          (run d P t a v hist ρ).2 = (run d Q t a v hist ρ).2) := by
  intro t
  induction t with
  | var i => intro a v hist ρ R _ _ _; exact ⟨rfl, fun _ => rfl⟩
  | neg p ih => intro a v hist ρ R hρ he hPQ; exact ih a _ hist ρ R hρ he hPQ
  | conj p q ihp ihq =>
      intro a v hist ρ R hρ he hPQ
      have hm : Q hist (.conj p q) a = P hist (.conj p q) a :=
        (hPQ hist _ _ he ((List.prefix_append _ _).trans (List.prefix_append _ _))).symm
      obtain ⟨hl1, hl2⟩ := rounds_conj_tail hρ
      obtain ⟨s, ρ', rfl⟩ : ∃ s ρ', ρ = s :: ρ' := by
        cases ρ with
        | nil => simp [Op.rounds] at hρ
        | cons s ρ' => exact ⟨s, ρ', rfl⟩
      simp only [List.tail_cons] at hl1 hl2
      rw [run_conj_def, run_conj_def, hm]
      generalize P hist (.conj p q) a = M
      rcases M with _ | ⟨b, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩ <;> try exact ⟨rfl, fun _ => rfl⟩
      simp only [List.headD_cons, List.tail_cons]
      by_cases hbc : b * c = v
      · simp only [if_pos hbc]
        obtain ⟨e1v, e1o⟩ := ihp a b (hist ++ [[b, c], [s]]) (ρ'.take p.rounds)
          (ρ'.drop p.rounds ++ R) hl1 (even_hist_pair he _ _) fun H n x hH hp => hPQ H n x hH (by
            have heq : ptsOf (hist ++ [[b, c], [s]]) ++ ρ'.take p.rounds ++
                (ρ'.drop p.rounds ++ R) = ptsOf hist ++ s :: ρ' ++ R := by
              rw [ptsOf_hist_pair he, List.append_assoc _ (List.take _ _),
                ← List.append_assoc (List.take _ _), List.take_append_drop]
              simp
            rwa [heq] at hp)
        by_cases hacc : (run d P p a b (hist ++ [[b, c], [s]]) (ρ'.take p.rounds)).1 = true
        · rw [← e1o hacc, ← e1v]
          obtain ⟨ms, hms, _, hout⟩ := run_out d P p a b _ _ hl1 hacc
          obtain ⟨e2v, e2o⟩ := ihq a c (run d P p a b (hist ++ [[b, c], [s]]) (ρ'.take p.rounds)).2
            (ρ'.drop p.rounds) R hl2 (by
              rw [hout, List.length_append, length_inter _ _ (by rw [hms, hl1])]
              exact (even_hist_pair he _ _).add (even_two_mul _))
            fun H n x hH hp => hPQ H n x hH (by
              rw [hout, ptsOf_append _ _ (even_hist_pair he _ _), ptsOf_hist_pair he,
                ptsOf_inter _ _ (by rw [hms, hl1])] at hp
              simpa using hp)
          exact ⟨by rw [e2v], fun h => e2o (by simp_all)⟩
        · simp only [Bool.not_eq_true] at hacc
          rw [hacc] at e1v
          simp [hacc, ← e1v]
      · simp [if_neg hbc]
  | disj p q ihp ihq =>
      intro a v hist ρ R hρ he hPQ
      have hm : Q hist (.disj p q) a = P hist (.disj p q) a :=
        (hPQ hist _ _ he ((List.prefix_append _ _).trans (List.prefix_append _ _))).symm
      obtain ⟨hl1, hl2⟩ := rounds_conj_tail (q := q) (by simpa [Op.rounds] using hρ)
      obtain ⟨s, ρ', rfl⟩ : ∃ s ρ', ρ = s :: ρ' := by
        cases ρ with
        | nil => simp [Op.rounds] at hρ
        | cons s ρ' => exact ⟨s, ρ', rfl⟩
      simp only [List.tail_cons] at hl1 hl2
      rw [run_disj_def, run_disj_def, hm]
      generalize P hist (.disj p q) a = M
      rcases M with _ | ⟨b, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩ <;> try exact ⟨rfl, fun _ => rfl⟩
      simp only [List.headD_cons, List.tail_cons]
      by_cases hbc : 1 - (1 - b) * (1 - c) = v
      · simp only [if_pos hbc]
        obtain ⟨e1v, e1o⟩ := ihp a b (hist ++ [[b, c], [s]]) (ρ'.take p.rounds)
          (ρ'.drop p.rounds ++ R) hl1 (even_hist_pair he _ _) fun H n x hH hp => hPQ H n x hH (by
            have heq : ptsOf (hist ++ [[b, c], [s]]) ++ ρ'.take p.rounds ++
                (ρ'.drop p.rounds ++ R) = ptsOf hist ++ s :: ρ' ++ R := by
              rw [ptsOf_hist_pair he, List.append_assoc _ (List.take _ _),
                ← List.append_assoc (List.take _ _), List.take_append_drop]
              simp
            rwa [heq] at hp)
        by_cases hacc : (run d P p a b (hist ++ [[b, c], [s]]) (ρ'.take p.rounds)).1 = true
        · rw [← e1o hacc, ← e1v]
          obtain ⟨ms, hms, _, hout⟩ := run_out d P p a b _ _ hl1 hacc
          obtain ⟨e2v, e2o⟩ := ihq a c (run d P p a b (hist ++ [[b, c], [s]]) (ρ'.take p.rounds)).2
            (ρ'.drop p.rounds) R hl2 (by
              rw [hout, List.length_append, length_inter _ _ (by rw [hms, hl1])]
              exact (even_hist_pair he _ _).add (even_two_mul _))
            fun H n x hH hp => hPQ H n x hH (by
              rw [hout, ptsOf_append _ _ (even_hist_pair he _ _), ptsOf_hist_pair he,
                ptsOf_inter _ _ (by rw [hms, hl1])] at hp
              simpa using hp)
          exact ⟨by rw [e2v], fun h => e2o (by simp_all)⟩
        · simp only [Bool.not_eq_true] at hacc
          rw [hacc] at e1v
          simp [hacc, ← e1v]
      · simp [if_neg hbc]
  | all i p ih =>
      intro a v hist ρ R hρ he hPQ
      have hm : Q hist (.all i p) a = P hist (.all i p) a :=
        (hPQ hist _ _ he ((List.prefix_append _ _).trans (List.prefix_append _ _))).symm
      rw [run_all_def, run_all_def, hm]
      split_ifs
      · exact run_congr_round d P Q p hist _ ρ R (fun s => Function.update a i s)
          (fun s => evalL (P hist (.all i p) a) s) hρ he hPQ ih
      · exact ⟨rfl, fun _ => rfl⟩
  | ex i p ih =>
      intro a v hist ρ R hρ he hPQ
      have hm : Q hist (.ex i p) a = P hist (.ex i p) a :=
        (hPQ hist _ _ he ((List.prefix_append _ _).trans (List.prefix_append _ _))).symm
      rw [run_ex_def, run_ex_def, hm]
      split_ifs
      · exact run_congr_round d P Q p hist _ ρ R (fun s => Function.update a i s)
          (fun s => evalL (P hist (.ex i p) a) s) hρ he hPQ ih
      · exact ⟨rfl, fun _ => rfl⟩
  | lin j p ih =>
      intro a v hist ρ R hρ he hPQ
      have hm : Q hist (.lin j p) a = P hist (.lin j p) a :=
        (hPQ hist _ _ he ((List.prefix_append _ _).trans (List.prefix_append _ _))).symm
      rw [run_lin_def, run_lin_def, hm]
      split_ifs
      · exact run_congr_round d P Q p hist _ ρ R (fun s => Function.update a j s)
          (fun s => evalL (P hist (.lin j p) a) s) hρ he hPQ ih
      · exact ⟨rfl, fun _ => rfl⟩

end Complexity.Qbf
