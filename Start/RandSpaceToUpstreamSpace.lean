import Start.RandSpaceToUpstreamSim

/-!
# Host fair-coin machines into upstream machines: space, and the class inclusions

This library's own module (task `M27-HOST-RANDOMIZED-SPACE`).

* `RandToLogspace.rcompile_spaceThrough` — if the host machine uses at most `s |x|` cells on every
  reachable configuration, every run of `rcompile M` (every coin sequence, every time) has
  `spaceThrough ≤ 2 s |x|`;
* `RandToLogspace.hostRL_subset_RL`, `RandToLogspace.hostBPL_subset_BPL` — host `RL` and `BPL`
  are contained in upstream `RL` and `BPL`, with the explicit clock
  `polynomialClock (2 a + 2) k n = (2 a + 2) (n + 2) ^ k` for a host time bound
  `T n ≤ a (n + 1) ^ k`, and the `LogSpace` constant `2 a' + 1` for a host space bound
  `a' (log₂ (n + 1) + 1)`.
-/

set_option autoImplicit false

namespace Complexity.Space

namespace RandToLogspace

open ExactDerandomization (Word InputSymbol Direction FMachine FAction FConfig readInput CoinTape)
open ToLogspace (inPos succCfg moveInput_inPos)

variable {M : Machine} {x : Word}

/-- The phase condition of a reachable configuration of the compiled machine. -/
def PhaseOK (p : RPh M.states) (c : Config) (i₀ : Fin (x.length + 2)) : Prop :=
  match p with
  | .init => False
  | .run q => q.val = c.state ∧ i₀ = inPos x.length c.inHead
  | .fix q => q.val = c.state ∧
      (i₀ = inPos x.length c.inHead ∨ (c.inHead = 0 ∧ i₀ = ⟨0, by omega⟩))
  | .acc => True
  | .rej => True

variable (M x) in
/-- Reachable configurations of the compiled machine: the initial one, or the encoding of a
reachable host configuration. -/
def RInv (u : FConfig (RPh M.states) 2 1 x.length) : Prop :=
  u = (rfcompile M).initial x.length ∨
    ∃ (m : ℕ) (c : Config) (p : RPh M.states) (i₀ : Fin (x.length + 2)),
      Reach.steps (M.Step x) m init c ∧ u = encR p c i₀ ∧ PhaseOK p c i₀

theorem rInv_step (hwf : M.WellFormed) {u : FConfig (RPh M.states) 2 1 x.length}
    (hu : RInv M x u) (b : Bool) : RInv M x (rstep M x b u) := by
  rcases hu with rfl | ⟨m, c, p, i₀, hm, rfl, hp⟩
  · right
    exact ⟨0, init, .run ⟨0, hwf.1⟩, _, rfl, rstep_init hwf.1 b, rfl, rfl⟩
  · cases p with
    | init => exact hp.elim
    | acc => exact Or.inr ⟨m, c, .acc, i₀, hm, rstep_out rfl b, trivial⟩
    | rej => exact Or.inr ⟨m, c, .rej, i₀, hm, rstep_out rfl b, trivial⟩
    | fix q =>
        right
        refine ⟨m, c, .run q, _, hm, rstep_fix b hp.2, hp.1, rfl⟩
    | run q =>
        obtain ⟨hq, rfl⟩ := hp
        obtain ⟨qv, hqv⟩ := q
        simp only at hq
        subst hq
        have hi := Machine.inHead_le_of_steps hm
        by_cases hacc : M.accept c.state = true
        · exact Or.inr ⟨m, c, .acc, _, hm, rstep_run_acc hacc b, trivial⟩
        · have hacc' : M.accept c.state = false := by simpa using hacc
          rcases hch : choose b (M.delta c.state x[c.inHead]? (c.tape.getD c.wHead false)) with
            _ | ⟨q', bw, dI, dW⟩
          · exact Or.inr ⟨m, c, .rej, _, hm,
              rstep_run_halt hi hacc' (choose_eq_none.mp hch), trivial⟩
          · have hin := choose_mem hch
            have hq' : q' < M.states := hwf.2 _ _ _ _ hin
            right
            refine ⟨m + 1, succCfg x.length c q' bw dI dW, .fix ⟨q', hq'⟩, _, ⟨c, hm, ?_⟩,
              rstep_run hi hacc' hch hq', rfl, moveInput_inPos hi dI⟩
            show _ ∈ M.stepList x c
            rw [stepList_eq]
            exact List.mem_map_of_mem hin

theorem rInv_run (hwf : M.WellFormed) (coins : CoinTape) :
    ∀ t, RInv M x ((rfcompile M).run x coins t)
  | 0 => Or.inl rfl
  | t + 1 => rInv_step hwf (rInv_run hwf coins t) (coins t)

/-- Every reachable configuration of the compiled machine keeps its work heads in `[0, s)`. -/
theorem rInv_inBound {s : ℕ} (hsp : M.SpaceBoundedOn x s)
    {u : FConfig (RPh M.states) 2 1 x.length} (hu : RInv M x u) (k : Fin 2) :
    0 ≤ u.workPos k ∧ u.workPos k < s := by
  rcases hu with rfl | ⟨m, c, p, i₀, hm, rfl, -⟩
  · have := hsp 0 init rfl
    simp only [FMachine.initial, Config.space, init] at this ⊢
    omega
  · have := hsp m c hm
    simp only [encR, Config.space] at this ⊢
    omega

/-- **Space**: every run of the compiled machine has `spaceThrough ≤ 2 s`. -/
theorem rcompile_spaceThrough (hwf : M.WellFormed) {s : ℕ} (hsp : M.SpaceBoundedOn x s)
    (coins : CoinTape) (t : ℕ) : (rcompile M).spaceThrough x coins t ≤ 2 * s := by
  rw [rcompile, FMachine.toMachine_spaceThrough]
  have hcard : ∀ k : Fin 2, ((Finset.range (t + 1)).image
      (fun i => ((rfcompile M).run x coins i).workPos k)).card ≤ s := by
    intro k
    calc _ ≤ ((Finset.range s).image (fun j : ℕ => (j : ℤ))).card := by
          apply Finset.card_le_card
          intro z hz
          simp only [Finset.mem_image, Finset.mem_range] at hz ⊢
          obtain ⟨i, -, rfl⟩ := hz
          obtain ⟨h0, h1⟩ := rInv_inBound hsp (rInv_run hwf coins i) k
          exact ⟨(((rfcompile M).run x coins i).workPos k).toNat, by omega, by omega⟩
      _ ≤ (Finset.range s).card := Finset.card_image_le
      _ = s := Finset.card_range _
  calc _ ≤ ∑ _k : Fin 2, s := Finset.sum_le_sum fun k _ => hcard k
    _ = 2 * s := by simp

/-- **The upstream `LogSpace` bound** for a host space bound `a (log₂ (n + 1) + 1)`, with constant
`2 a + 1`. -/
theorem rcompile_logSpace (hwf : M.WellFormed) {a : ℕ}
    (hsp : M.SpaceBounded (fun n => a * (Nat.log 2 (n + 1) + 1))) :
    ∀ (x : Word) (coins : CoinTape) (t : ℕ),
      (rcompile M).spaceThrough x coins t ≤ (2 * a + 1) * Nat.clog 2 (x.length + 2) := by
  intro x coins t
  have h1 := rcompile_spaceThrough hwf (M.spaceBoundedOn_of_spaceBounded hsp x) coins t
  have h2 := ToLogspace.log_succ_le_clog x.length
  calc _ ≤ 2 * (a * (Nat.log 2 (x.length + 1) + 1)) := h1
    _ ≤ 2 * (a * Nat.clog 2 (x.length + 2)) := by gcongr
    _ ≤ (2 * a + 1) * Nat.clog 2 (x.length + 2) := by nlinarith

/-- The upstream clock dominates the doubled host time bound. -/
theorem clock_ge {T : ℕ → ℕ} {a k : ℕ} (hT : ∀ n, T n ≤ a * (n + 1) ^ k) (n : ℕ) :
    2 * T n + 2 ≤ ExactDerandomization.polynomialClock (2 * a + 2) k n := by
  unfold ExactDerandomization.polynomialClock
  have h1 : (n + 1) ^ k ≤ (n + 2) ^ k := Nat.pow_le_pow_left (by omega) k
  have h2 : 1 ≤ (n + 2) ^ k := Nat.one_le_pow _ _ (by omega)
  have := hT n
  nlinarith

/-- **Host `RL` is contained in upstream `RL`.** -/
theorem hostRL_subset_RL {A : Language} (h : HostRL A) :
    {x | A x} ∈ ExactDerandomization.RL := by
  obtain ⟨M, a', T, hwf, hfc, ⟨a, k, hT⟩, hsp, hA⟩ := h
  refine ⟨_, 2, 1, rcompile M, ⟨2 * a' + 1, by omega, rcompile_logSpace hwf hsp⟩,
    2 * a + 2, k, by omega, fun x => ?_⟩
  obtain ⟨hrun, hin, hout⟩ := hA x
  have hc := clock_ge hT x.length
  rw [rcompile_acceptanceProbability hwf hfc hrun _ hc]
  exact ⟨rcompile_haltsBy hwf hfc hrun _ hc, hin, hout⟩

/-- **Host `BPL` is contained in upstream `BPL`.** -/
theorem hostBPL_subset_BPL {A : Language} (h : HostBPL A) :
    {x | A x} ∈ ExactDerandomization.BPL := by
  obtain ⟨M, a', T, hwf, hfc, ⟨a, k, hT⟩, hsp, hA⟩ := h
  refine ⟨_, 2, 1, rcompile M, ⟨2 * a' + 1, by omega, rcompile_logSpace hwf hsp⟩,
    2 * a + 2, k, by omega, fun x => ?_⟩
  obtain ⟨hrun, hin, hout⟩ := hA x
  have hc := clock_ge hT x.length
  rw [rcompile_acceptanceProbability hwf hfc hrun _ hc]
  exact ⟨rcompile_haltsBy hwf hfc hrun _ hc, hin, hout⟩

end RandToLogspace

end Complexity.Space
