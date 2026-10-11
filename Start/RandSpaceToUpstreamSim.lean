import Start.RandSpaceToUpstream

/-!
# Host fair-coin machines into upstream machines: exact acceptance probability

This library's own module (task `M27-HOST-RANDOMIZED-SPACE`).  For the compiled machine
`RandToLogspace.rcompile M` of `Start/RandSpaceToUpstream.lean`:

* `RandToLogspace.sim` — from the encoding of a host configuration `c` whose runs have at most
  `T` steps, after any `t ≥ 2 T + 1` coin flips the compiled machine has accepted with probability
  exactly `M.acceptWithin x T c`, and it has an output on every coin sequence;
* `RandToLogspace.rcompile_acceptanceProbability`, `RandToLogspace.rcompile_haltsBy` — the same
  from the initial configuration, for `t ≥ 2 T + 2`.
-/

set_option autoImplicit false

namespace Complexity.Space

namespace RandToLogspace

open ExactDerandomization (Word InputSymbol Direction FMachine FAction FConfig readInput CoinTape)
open ToLogspace (inPos succCfg moveInput_inPos)

variable {M : Machine} {x : Word}

/-! ### Probability and halting from a configuration of the compiled machine -/

variable (M x) in
/-- The probability that the compiled machine, started from `u`, has output `true` after `t`
coin flips. -/
noncomputable def P (t : ℕ) (u : FConfig (RPh M.states) 2 1 x.length) : ℚ :=
  (rcompile M).probFrom x t (FMachine.cfgMap u)

variable (M x) in
/-- After `t` steps from `u`, the compiled machine has an output on every coin sequence. -/
def Hl (t : ℕ) (u : FConfig (RPh M.states) 2 1 x.length) : Prop :=
  ∀ coins : CoinTape, ∃ v : Bool,
    (rcompile M).output ((rcompile M).runFrom x (FMachine.cfgMap u) coins t).state = some v

theorem output_cfgMap (u : FConfig (RPh M.states) 2 1 x.length) :
    (rcompile M).output (FMachine.cfgMap u).state = rout u.state := by
  simp [rcompile, FMachine.toMachine, FMachine.cfgMap, rfcompile]

theorem step_cfgMap (b : Bool) (u : FConfig (RPh M.states) 2 1 x.length) :
    (rcompile M).step x b (FMachine.cfgMap u) = FMachine.cfgMap (rstep M x b u) :=
  FMachine.toMachine_step _ _ _ _

theorem P_zero (u : FConfig (RPh M.states) 2 1 x.length) :
    P M x 0 u = if rout u.state = some true then 1 else 0 := by
  simp only [P, ExactDerandomization.Machine.probFrom, output_cfgMap]

theorem P_succ (t : ℕ) (u : FConfig (RPh M.states) 2 1 x.length) :
    P M x (t + 1) u = (P M x t (rstep M x false u) + P M x t (rstep M x true u)) / 2 := by
  simp only [P, ExactDerandomization.Machine.probFrom, step_cfgMap]

theorem Hl_succ {t : ℕ} {u : FConfig (RPh M.states) 2 1 x.length}
    (h : ∀ b, Hl M x t (rstep M x b u)) : Hl M x (t + 1) u := by
  intro coins
  simp only [ExactDerandomization.Machine.runFrom, step_cfgMap]
  exact h _ _

theorem P_out {u : FConfig (RPh M.states) 2 1 x.length} {v : Bool} (h : rout u.state = some v) :
    ∀ t, P M x t u = if v = true then 1 else 0
  | 0 => by rw [P_zero, h]; cases v <;> simp
  | t + 1 => by rw [P_succ, rstep_out h, rstep_out h, P_out h t]; ring

theorem Hl_out {u : FConfig (RPh M.states) 2 1 x.length} {v : Bool} (h : rout u.state = some v) :
    ∀ t, Hl M x t u
  | 0 => fun _ => ⟨v, by rw [ExactDerandomization.Machine.runFrom, output_cfgMap, h]⟩
  | t + 1 => Hl_succ fun b => by rw [rstep_out h]; exact Hl_out h t

/-- A step that ignores the coin. -/
theorem P_det {t : ℕ} {u u' : FConfig (RPh M.states) 2 1 x.length}
    (h : ∀ b, rstep M x b u = u') : P M x (t + 1) u = P M x t u' := by
  rw [P_succ, h, h]; ring

theorem Hl_det {t : ℕ} {u u' : FConfig (RPh M.states) 2 1 x.length}
    (h : ∀ b, rstep M x b u = u') (h' : Hl M x t u') : Hl M x (t + 1) u :=
  Hl_succ fun b => by rw [h]; exact h'

/-! ### Host runs -/

variable (M x) in
/-- Every host run from `c` has at most `T` steps. -/
def RunsFrom (c : Config) (T : ℕ) : Prop := ∀ c', ¬ Reach.steps (M.Step x) (T + 1) c c'

theorem RunsFrom.step {c c' : Config} {T : ℕ} (h : RunsFrom M x c (T + 1)) (hs : M.Step x c c') :
    RunsFrom M x c' T := by
  intro d hd
  apply h d
  have := (Reach.steps_add (M.Step x) 1 (T + 1) c d).2 ⟨c', (Reach.steps_one _ _ _).2 hs, hd⟩
  rwa [Nat.add_comm 1 (T + 1)] at this

theorem RunsFrom.not_step {c c' : Config} (h : RunsFrom M x c 0) (hs : M.Step x c c') : False :=
  h c' ((Reach.steps_one _ _ _).2 hs)

theorem stepList_eq (c : Config) :
    M.stepList x c = (M.delta c.state x[c.inHead]? (c.tape.getD c.wHead false)).map
      (fun t => succCfg x.length c t.1 t.2.1 t.2.2.1 t.2.2.2) := rfl

/-- One host instruction: the `run` step followed by the `fix` step. -/
theorem macro_step {q : Fin M.states} {c : Config} {b : Bool} (hi : c.inHead ≤ x.length)
    (hacc : M.accept q = false) {q' : ℕ} {bw : Bool} {dI dW : Dir}
    (hd : choose b (M.delta q x[c.inHead]? (c.tape.getD c.wHead false)) = some (q', bw, dI, dW))
    (hq' : q' < M.states) (b' : Bool) :
    rstep M x b' (rstep M x b (enc (.run q) c)) =
      enc (.run ⟨q', hq'⟩) (succCfg x.length c q' bw dI dW) := by
  rw [rstep_run hi hacc hd hq']
  exact rstep_fix b' (moveInput_inPos hi dI)

/-! ### The simulation -/

section Sim

variable (hwf : M.WellFormed) (hfc : M.FairCoin)
include hwf hfc

/-- **Exact simulation**: from the encoding of a host configuration whose runs have at most `T`
steps, after `t ≥ 2 T + 1` coin flips the compiled machine has output `true` with probability
exactly `M.acceptWithin x T c`, and has an output on every coin sequence. -/
theorem sim : ∀ (T : ℕ) (c : Config) (hq : c.state < M.states), c.inHead ≤ x.length →
    RunsFrom M x c T → ∀ t, 2 * T + 1 ≤ t →
      P M x t (enc (.run ⟨c.state, hq⟩) c) = M.acceptWithin x T c ∧
        Hl M x t (enc (.run ⟨c.state, hq⟩) c) := by
  intro T
  induction T with
  | zero =>
      intro c hq hi hR t ht
      obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      by_cases hacc : M.accept c.state = true
      · have hs : ∀ b, rstep M x b (enc (.run ⟨c.state, hq⟩) c) = encR .acc c _ :=
          fun b => rstep_run_acc (q := ⟨c.state, hq⟩) hacc b
        refine ⟨?_, Hl_det hs (Hl_out rfl t)⟩
        rw [P_det hs, P_out rfl, Machine.acceptWithin]
        simp [hacc]
      · have hacc' : M.accept c.state = false := by simpa using hacc
        rcases hd : M.delta c.state x[c.inHead]? (c.tape.getD c.wHead false) with _ | ⟨i, rest⟩
        · have hs : ∀ b, rstep M x b (enc (.run ⟨c.state, hq⟩) c) = enc .rej c :=
            fun b => rstep_run_halt (q := ⟨c.state, hq⟩) hi hacc' hd
          refine ⟨?_, Hl_det hs (Hl_out rfl t)⟩
          rw [P_det hs, P_out rfl, Machine.acceptWithin]
          simp [hacc']
        · exfalso
          refine hR.not_step (c' := succCfg x.length c i.1 i.2.1 i.2.2.1 i.2.2.2) ?_
          show _ ∈ M.stepList x c
          rw [stepList_eq, hd]
          exact List.mem_map_of_mem List.mem_cons_self
  | succ T ih =>
      intro c hq hi hR t ht
      obtain ⟨t, rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
      by_cases hacc : M.accept c.state = true
      · have hs : ∀ b, rstep M x b (enc (.run ⟨c.state, hq⟩) c) = encR .acc c _ :=
          fun b => rstep_run_acc (q := ⟨c.state, hq⟩) hacc b
        refine ⟨?_, Hl_det hs (Hl_out rfl _)⟩
        rw [P_det hs, P_out rfl, Machine.acceptWithin]
        simp [hacc]
      · have hacc' : M.accept c.state = false := by simpa using hacc
        have hmem : ∀ i ∈ M.delta c.state x[c.inHead]? (c.tape.getD c.wHead false),
            M.Step x c (succCfg x.length c i.1 i.2.1 i.2.2.1 i.2.2.2) := fun i hi' => by
          show _ ∈ M.stepList x c
          rw [stepList_eq]
          exact List.mem_map_of_mem hi'
        have hlt : ∀ i ∈ M.delta c.state x[c.inHead]? (c.tape.getD c.wHead false),
            i.1 < M.states := fun i hi' => hwf.2 _ _ _ i hi'
        have hlen := hfc c.state x[c.inHead]? (c.tape.getD c.wHead false)
        have hsub : ∀ (b : Bool) (i : ℕ × Bool × Dir × Dir),
            choose b (M.delta c.state x[c.inHead]? (c.tape.getD c.wHead false)) = some i →
            ∃ hi' : i.1 < M.states,
              P M x (t + 1) (rstep M x b (enc (.run ⟨c.state, hq⟩) c)) =
                M.acceptWithin x T (succCfg x.length c i.1 i.2.1 i.2.2.1 i.2.2.2) ∧
              Hl M x (t + 1) (rstep M x b (enc (.run ⟨c.state, hq⟩) c)) := by
          intro b i hch
          obtain ⟨q', bw, dI, dW⟩ := i
          have hin := choose_mem hch
          have hq' := hlt _ hin
          refine ⟨hq', ?_⟩
          have hm := fun b' => macro_step (q := ⟨c.state, hq⟩) (b := b) hi hacc' hch hq' b'
          obtain ⟨h1, h2⟩ := ih (succCfg x.length c q' bw dI dW) hq'
            (moveIn_le _ _ _ hi) (hR.step (hmem _ hin)) t (by omega)
          exact ⟨by rw [P_det hm]; exact h1, Hl_det hm h2⟩
        rcases hd : M.delta c.state x[c.inHead]? (c.tape.getD c.wHead false) with
          _ | ⟨i, _ | ⟨i₂, rest⟩⟩
        · have hs : ∀ b, rstep M x b (enc (.run ⟨c.state, hq⟩) c) = enc .rej c :=
            fun b => rstep_run_halt (q := ⟨c.state, hq⟩) hi hacc' hd
          refine ⟨?_, Hl_det hs (Hl_out rfl _)⟩
          rw [P_det hs, P_out rfl, Machine.acceptWithin, stepList_eq, hd]
          simp [hacc']
        · rw [hd] at hsub
          obtain ⟨_, a0, b0⟩ := hsub false i rfl
          obtain ⟨_, a1, b1⟩ := hsub true i rfl
          refine ⟨?_, Hl_succ fun b => by cases b; exacts [b0, b1]⟩
          rw [P_succ, a0, a1, Machine.acceptWithin, stepList_eq, hd]
          simp [hacc']
        · rw [hd] at hsub hlen
          have hrest : rest = [] := by simpa using hlen
          subst hrest
          obtain ⟨_, a0, b0⟩ := hsub false i rfl
          obtain ⟨_, a1, b1⟩ := hsub true i₂ rfl
          refine ⟨?_, Hl_succ fun b => by cases b; exacts [b0, b1]⟩
          rw [P_succ, a0, a1, Machine.acceptWithin, stepList_eq, hd]
          simp [hacc']

/-- From the initial configuration. -/
theorem sim_init {T : ℕ} (hT : M.RunsWithin x T) (t : ℕ) (ht : 2 * T + 2 ≤ t) :
    P M x t ((rfcompile M).initial x.length) = M.acceptWithin x T init ∧
      Hl M x t ((rfcompile M).initial x.length) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hs : ∀ b, rstep M x b ((rfcompile M).initial x.length) = enc (.run ⟨0, hwf.1⟩) init :=
    fun b => rstep_init hwf.1 b
  obtain ⟨h1, h2⟩ := sim hwf hfc T init hwf.1 (Nat.zero_le _) hT t (by omega)
  exact ⟨by rw [P_det hs]; exact h1, Hl_det hs h2⟩

/-- **Exact acceptance probability**: if every host run on `x` has at most `T` steps, then after
any `t ≥ 2 T + 2` steps the compiled machine accepts with probability exactly
`M.acceptWithin x T init`. -/
theorem rcompile_acceptanceProbability {T : ℕ} (hT : M.RunsWithin x T) (t : ℕ)
    (ht : 2 * T + 2 ≤ t) :
    (rcompile M).acceptanceProbability x t = M.acceptWithin x T init := by
  rw [ExactDerandomization.Machine.acceptanceProbability_eq_probFrom]
  exact (sim_init hwf hfc hT t ht).1

/-- **Halting**: under the same hypothesis the compiled machine has an output after `t` steps on
every coin sequence. -/
theorem rcompile_haltsBy {T : ℕ} (hT : M.RunsWithin x T) (t : ℕ) (ht : 2 * T + 2 ≤ t) :
    (rcompile M).HaltsBy x t := by
  intro coins
  rw [ExactDerandomization.Machine.run_eq_runFrom]
  exact (sim_init hwf hfc hT t ht).2 coins

end Sim

end RandToLogspace

end Complexity.Space
