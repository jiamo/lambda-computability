import Start.RandUpstreamToSpaceSim
import Start.RandSpaceToUpstreamSpace

/-!
# Upstream probabilistic machines into fair-coin host machines: time, space and the classes

This library's own module (task `M27-HOST-RANDOMIZED-SPACE`).  For an upstream machine `M` with
`q + 1` states, `w` work tapes and `h` input heads, using at most `c₀ ⌈log₂ (n + 2)⌉` cells on
every coin sequence, and having an output after `t₀` steps on every coin sequence on `x`:

* `RandFromLogspace.rcompile_acceptWithin` — **exact acceptance probability**:
  `(rcompile M c₀).acceptWithin x (timeB M c₀ |x|) init = M.acceptanceProbability x t₀`;
* every run of the host on `x` has at most `timeB M c₀ |x|` steps, where
  `timeB M c₀ n = (n + 2) ^ clockLen Q a` with `Q` the number of host states,
  `a = (2 c₀ + q + 7) (2 (7 + h + 2 w) + 1)` and `clockLen Q a = Q (a + 1)² 2^a + a + 3`
  (`Start/SpaceToLogspaceTransfer.lean`);
* every reachable host configuration uses at most `a (log₂ (n + 1) + 1)` cells;
* `RandFromLogspace.RL_subset_hostRL`, `RandFromLogspace.BPL_subset_hostBPL` — upstream `RL` and
  `BPL` are contained in host `RL` and `BPL`.

The bound on the run length comes from counting configurations: every run ends (the simulation
of one upstream step is a finite deterministic segment, and the upstream machine halts on every
coin sequence), every reachable configuration fits in the space bound, so a run longer than the
number `cfgBound` of such configurations would repeat one and give runs of every length.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace RandFromLogspace

open Tracks Prog FromLogspace Machine
open ExactDerandomization (Word InputSymbol Direction Configuration readInput CoinTape)

variable {q w h : ℕ} (M : ExactDerandomization.Machine q w h) (c₀ : ℕ)

/-- The host space constant. -/
def spaceA (q w h c₀ : ℕ) : ℕ := (2 * c₀ + q + 7) * (2 * (7 + h + 2 * w) + 1)

/-- The explicit host time bound. -/
def timeB (n : ℕ) : ℕ :=
  (n + 2) ^ ToLogspace.clockLen (rcompile M c₀).states (spaceA q w h c₀)

theorem timeB_polyBound : Complexity.PolyBound (timeB M c₀) := by
  refine ⟨2 ^ ToLogspace.clockLen (rcompile M c₀).states (spaceA q w h c₀),
    ToLogspace.clockLen (rcompile M c₀).states (spaceA q w h c₀), fun n => ?_⟩
  unfold timeB
  rw [← mul_pow]
  exact Nat.pow_le_pow_left (by omega) _

/-- **The simulation of the upstream machine on `x`**: exact acceptance probability at the clock
`timeB`, every run within `timeB` steps, every reachable configuration within the space bound. -/
theorem rcompile_acceptWithin {x : Word}
    (hLS : ∀ coins t, M.spaceThrough x coins t ≤ c₀ * Nat.clog 2 (x.length + 2))
    {t₀ : ℕ} (hhalt : M.HaltsBy x t₀) :
    (rcompile M c₀).acceptWithin x (timeB M c₀ x.length) init = M.acceptanceProbability x t₀ ∧
      (rcompile M c₀).RunsWithin x (timeB M c₀ x.length) ∧
      (rcompile M c₀).SpaceBoundedOn x (spaceA q w h c₀ * (Nat.log 2 (x.length + 1) + 1)) := by
  obtain ⟨N, hN, hval, hR⟩ := init_claim (M := M) (c₀ := c₀) hLS hhalt
  have hsp : (rcompile M c₀).SpaceBoundedOn x (spaceB q w h c₀ x.length) :=
    fun n d hd => hR n d hd
  have hsp' : (rcompile M c₀).SpaceBoundedOn x (spaceA q w h c₀ * (Nat.log 2 (x.length + 1) + 1)) :=
    fun n d hd => (hsp n d hd).trans (spaceB_le_log q w h c₀ x.length)
  have hrun : (rcompile M c₀).RunsWithin x (timeB M c₀ x.length) := by
    have h1 := runsWithin_cfgBound (rcompile_wellFormed M c₀) hsp' (N := N) hN
    have h2 := ToLogspace.cfgBound_le_clock (rcompile M c₀) (spaceA q w h c₀) x
    exact Ends.mono h1 h2
  refine ⟨?_, hrun, hsp'⟩
  have e1 := acceptWithin_stable _ _ hrun (max N (timeB M c₀ x.length)) (le_max_right _ _)
  have e2 := acceptWithin_stable _ _ hN (max N (timeB M c₀ x.length)) (le_max_left _ _)
  rw [← e1, e2, hval]

/-- **Upstream `RL` is contained in host `RL`.** -/
theorem RL_subset_hostRL {A : Language} (hA : {x | A x} ∈ ExactDerandomization.RL) :
    HostRL A := by
  obtain ⟨q, w, h, M, ⟨c₀, -, hLS⟩, c, k, -, hM⟩ := hA
  refine ⟨rcompile M c₀, spaceA q w h c₀, timeB M c₀, rcompile_wellFormed M c₀,
    rcompile_fairCoin M c₀, timeB_polyBound M c₀, ?_, fun x => ?_⟩
  · intro x n d hd
    obtain ⟨hhalt, -, -⟩ := hM x
    exact (rcompile_acceptWithin M c₀ (hLS x) hhalt).2.2 n d hd
  · obtain ⟨hhalt, hin, hout⟩ := hM x
    obtain ⟨hv, hrun, -⟩ := rcompile_acceptWithin M c₀ (hLS x) hhalt
    refine ⟨hrun, fun hx => ?_, fun hx => ?_⟩
    · rw [hv]; exact hin hx
    · rw [hv]; exact hout hx

/-- **Upstream `BPL` is contained in host `BPL`.** -/
theorem BPL_subset_hostBPL {A : Language} (hA : {x | A x} ∈ ExactDerandomization.BPL) :
    HostBPL A := by
  obtain ⟨q, w, h, M, ⟨c₀, -, hLS⟩, c, k, -, hM⟩ := hA
  refine ⟨rcompile M c₀, spaceA q w h c₀, timeB M c₀, rcompile_wellFormed M c₀,
    rcompile_fairCoin M c₀, timeB_polyBound M c₀, ?_, fun x => ?_⟩
  · intro x n d hd
    obtain ⟨hhalt, -, -⟩ := hM x
    exact (rcompile_acceptWithin M c₀ (hLS x) hhalt).2.2 n d hd
  · obtain ⟨hhalt, hin, hout⟩ := hM x
    obtain ⟨hv, hrun, -⟩ := rcompile_acceptWithin M c₀ (hLS x) hhalt
    refine ⟨hrun, fun hx => ?_, fun hx => ?_⟩
    · rw [hv]; exact hin hx
    · rw [hv]; exact hout hx

end RandFromLogspace

/-- **Host `RL` is upstream `RL`**, by the two explicit simulations
(`Start/RandSpaceToUpstream*.lean`, `Start/RandUpstreamToSpace*.lean`). -/
theorem hostRL_iff (A : Language) : HostRL A ↔ {x | A x} ∈ ExactDerandomization.RL :=
  ⟨RandToLogspace.hostRL_subset_RL, RandFromLogspace.RL_subset_hostRL⟩

/-- **Host `BPL` is upstream `BPL`**, by the two explicit simulations. -/
theorem hostBPL_iff (A : Language) : HostBPL A ↔ {x | A x} ∈ ExactDerandomization.BPL :=
  ⟨RandToLogspace.hostBPL_subset_BPL, RandFromLogspace.BPL_subset_hostBPL⟩

end Complexity.Space
