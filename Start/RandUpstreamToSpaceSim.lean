import Start.RandUpstreamToSpaceSeg
import Start.RandSpaceUpstreamProb

/-!
# Upstream probabilistic machines into fair-coin host machines: exact acceptance probability

This library's own module (task `M27-HOST-RANDOMIZED-SPACE`).  For the host machine
`RandFromLogspace.rcompile M c₀` of `Start/RandUpstreamToSpace.lean`:

* `RandFromLogspace.iter_claim` — from the loop head on the register file of a reachable
  configuration `c` of `M` all of whose coin sequences give an output within `r` steps, every host
  run ends, every reachable host configuration fits in `spaceB` cells, and once the runs have
  ended the host has accepted with probability exactly `M.probFrom x r c`;
* `RandFromLogspace.init_claim` — the same from the host's initial configuration, for the initial
  configuration of `M`.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace RandFromLogspace

open Tracks Prog FromLogspace Machine
open ExactDerandomization (Word InputSymbol Direction Configuration readInput CoinTape)

variable {q w h : ℕ} (M : ExactDerandomization.Machine q w h) (c₀ : ℕ) {x : Word}

/-- Every coin sequence gives `M` an output within `r` steps from `c`. -/
def HaltsFrom (x : Word) (r : ℕ) (c : Configuration q w h x.length) : Prop :=
  ∀ coins : CoinTape, ∃ v, M.output (M.runFrom x c coins r).state = some v

theorem probFrom_out {c : Configuration q w h x.length} {v : Bool}
    (hv : M.output c.state = some v) : ∀ r, M.probFrom x r c = if v = true then 1 else 0
  | 0 => by cases v <;> simp [ExactDerandomization.Machine.probFrom, hv]
  | r + 1 => by
      have hs : ∀ b, M.step x b c = c := fun b => by
        simp only [ExactDerandomization.Machine.step, hv]
      rw [ExactDerandomization.Machine.probFrom, hs, hs, probFrom_out hv r]; ring

theorem haltsFrom_step {r : ℕ} {c : Configuration q w h x.length} (hH : HaltsFrom M x (r + 1) c)
    (b : Bool) : HaltsFrom M x r (M.step x b c) := by
  intro coins
  obtain ⟨v, hv⟩ := hH (fun i => if i = 0 then b else coins (i - 1))
  exact ⟨v, by simpa [ExactDerandomization.Machine.runFrom] using hv⟩

theorem output_some_of_haltsFrom_zero {c : Configuration q w h x.length}
    (hH : HaltsFrom M x 0 c) : ∃ v, M.output c.state = some v := by
  obtain ⟨v, hv⟩ := hH (fun _ => false)
  exact ⟨v, hv⟩

theorem run_update_succ (coins : CoinTape) (t : ℕ) (b : Bool) :
    M.run x (Function.update coins t b) (t + 1) = M.step x b (M.run x coins t) := by
  rw [ExactDerandomization.Machine.run_succ, Function.update_self,
    M.run_eq_of_prefix x (fun s hs => Function.update_of_ne (by omega) _ _)]

/-- The host side condition. -/
abbrev Sp (x : Word) (d : Config) : Prop := d.space ≤ spaceB q w h c₀ x.length

theorem space_at (d : Config) (s : ℕ) : (d.at s).space = d.space := rfl

theorem allReach_halt {N : Machine} {P : Config → Prop} {d : Config} (hl : N.stepList x d = [])
    (hd : P d) : N.AllReach x P d :=
  allReach_of_succs hd fun e he => by
    have : e ∈ N.stepList x d := he
    rw [hl] at this; simp at this

theorem step_of_single {N : Machine} {c d : Config} (hl : N.stepList x c = [d]) :
    N.Step x c d := by
  show d ∈ N.stepList x c
  rw [hl]; simp

theorem single_succ {N : Machine} {c d e : Config} (hl : N.stepList x c = [d])
    (he : N.Step x c e) : e = d := by
  have : e ∈ N.stepList x c := he
  rw [hl] at this; simpa using this

variable {M c₀}

/-- The loop-head step. -/
theorem stepList_stL {H : Config} (hH : H.state = stL M c₀) :
    (rcompile M c₀).stepList x H =
      [(touch x H).at (if runTest (rdIn x H) (rdW H) then stL M c₀ + 1 else stAcc M c₀)] := by
  rw [stepList_of_delta (i := (_, rdW H, .stay, .stay)) (by rw [hH]; exact delta_stL M c₀ _ _)]
  rfl

theorem detOK_stL {H : Config} (hH : H.state = stL M c₀)
    (hsp : H.space ≤ spaceB q w h c₀ x.length) :
    (rcompile M c₀).DetOK x (SpOK (q := q) (w := w) (h := h) c₀ x) H :=
  detOK_of_range M c₀ hsp (by rw [hH]; exact stL_ne_flip M c₀)
    (by rw [hH, stAcc, mainProg_size]; have := stL_ne_halt M c₀;
        have := stFlip_lt_stHalt M c₀; simp only [stFlip, stF] at *; omega)

theorem rdW_of_abs {H : Config} {s : TState} (h : H.abs = s) : rdW H = s.view s.head := by
  rw [rdW_eq_view, h]

/-- The loop head of a configuration with output `true`. -/
theorem case_true {H : Config} {c : Configuration q w h x.length} (hH : H.state = stL M c₀)
    (habs : H.abs = encTS M c₀ x c) (hsp : H.space ≤ spaceB q w h c₀ x.length)
    (hout : M.output c.state = some true) :
    ∃ N, (rcompile M c₀).Ends x H N ∧ (rcompile M c₀).acceptWithin x N H = 1 ∧
      (rcompile M c₀).AllReach x (Sp (q := q) (w := w) (h := h) c₀ x) H := by
  have hv : rdW H = true := by rw [rdW_of_abs habs]; simp [encTS, view_res, hout]
  have hl := stepList_stL (x := x) hH
  simp only [hv, runTest, Bool.not_true, Bool.false_eq_true, if_false] at hl
  set A := (touch x H).at (stAcc M c₀)
  have hlA : (rcompile M c₀).stepList x A = [] :=
    stepList_of_delta_nil (delta_stAcc M c₀ _ _)
  have haccA : (rcompile M c₀).accept A.state = true := by simp [A, rcompile_accept]
  have hD := detOK_stL hH hsp
  refine ⟨1, ends_of_succs fun d hd => ?_, ?_, ?_⟩
  · rw [single_succ hl hd]; exact ends_halt hlA
  · rw [acceptWithin_single hl hD.2.1, acceptWithin_accept haccA]
  · refine allReach_of_succs hsp fun d hd => ?_
    rw [single_succ hl hd]
    exact allReach_halt hlA (by simpa [A, space_at, space_touch] using hsp)

/-- From the loop head of a configuration without output `true`, to the running-flag test. -/
theorem to_flagTest {H : Config} {c : Configuration q w h x.length} (hH : H.state = stL M c₀)
    (habs : H.abs = encTS M c₀ x c) (hsp : H.space ≤ spaceB q w h c₀ x.length)
    (hout : M.output c.state ≠ some true) :
    ∃ d : Config, d.abs = ⟨lay (regK h w) (encC M (winR c₀ x.length : ℤ) c), 1, 0⟩ ∧
      d.space ≤ spaceB q w h c₀ x.length ∧
      (rcompile M c₀).Path x ((rcompile M c₀).DetOK x (SpOK (q := q) (w := w) (h := h) c₀ x))
        H (d.at (stF M c₀)) := by
  have hv : rdW H = false := by rw [rdW_of_abs habs]; simp [encTS, view_res, hout]
  have hl := stepList_stL (x := x) hH
  simp only [hv, runTest, Bool.not_false, if_true] at hl
  obtain ⟨d, hds, hdB, -, hp⟩ := path_of_runs M c₀ (rhosts_mvL2 M c₀) (range_mvL2 M c₀)
    ((runs_mvL 2 _ 3 0).of_eq rfl rfl) (c := touch x H) (by rw [abs_touch, habs]; rfl)
    (by rw [space_touch]; exact hsp)
  exact ⟨d, hds, hdB, .head (detOK_stL hH hsp) (step_of_single hl) hp⟩

/-- The loop head of a configuration with output `false`: the host halts without accepting. -/
theorem case_false {H : Config} {c : Configuration q w h x.length} (hH : H.state = stL M c₀)
    (habs : H.abs = encTS M c₀ x c) (hsp : H.space ≤ spaceB q w h c₀ x.length)
    (hout : M.output c.state = some false) :
    ∃ N, (rcompile M c₀).Ends x H N ∧ (rcompile M c₀).acceptWithin x N H = 0 ∧
      (rcompile M c₀).AllReach x (Sp (q := q) (w := w) (h := h) c₀ x) H := by
  obtain ⟨d, hds, hdB, hp⟩ := to_flagTest hH habs hsp (by rw [hout]; simp)
  have hv : rdW (d.at (stF M c₀)) = false := by
    rw [rdW_at, rdW_of_abs hds]; simp [view_run, hout]
  have hl : (rcompile M c₀).stepList x (d.at (stF M c₀)) =
      [(touch x (d.at (stF M c₀))).at (stHalt M c₀)] := by
    rw [stepList_of_delta (i := (stHalt M c₀, rdW (d.at (stF M c₀)), .stay, .stay))
      (by rw [Config.at_state, delta_stF, hv]; rfl)]
    rfl
  set Hh := (touch x (d.at (stF M c₀))).at (stHalt M c₀)
  have hlH : (rcompile M c₀).stepList x Hh = [] := stepList_of_delta_nil (delta_stHalt M c₀ _ _)
  have haccH : (rcompile M c₀).accept Hh.state = false := by
    simp [Hh, rcompile_accept, (stAcc_ne_halt M c₀).symm]
  have hDF : (rcompile M c₀).DetOK x (SpOK (q := q) (w := w) (h := h) c₀ x) (d.at (stF M c₀)) :=
    detOK_of_range M c₀ hdB (by simpa using stF_ne_flip M c₀)
      (by have := stF_ne_halt M c₀; have := stFlip_lt_stHalt M c₀
          simp only [Config.at_state, stAcc, mainProg_size]; simp only [stFlip] at *; omega)
  have hpath := hp.trans (.single hDF (step_of_single hl))
  obtain ⟨m, hm, hval, hR⟩ := path_transport hpath 0 (ends_halt hlH)
    (allReach_halt hlH (by simpa [Hh, space_at, space_touch] using hdB))
  refine ⟨m, by simpa using hm, ?_, hR⟩
  have := hval 0
  rw [Nat.zero_add] at this
  rw [this, acceptWithin_halt hlH haccH]

/-- The loop head of a running configuration: one fair branching, then one simulated step with
each coin. -/
theorem case_run {H : Config} {c : Configuration q w h x.length} (hH : H.state = stL M c₀)
    (habs : H.abs = encTS M c₀ x c) (hsp : H.space ≤ spaceB q w h c₀ x.length)
    (hout : M.output c.state = none) (hwin : ∀ b, WinOK c₀ x c ∧ WinOK c₀ x (M.step x b c))
    {v : Bool → ℚ}
    (hnext : ∀ (b : Bool) (H' : Config), H'.state = stL M c₀ →
      H'.abs = encTS M c₀ x (M.step x b c) → H'.space ≤ spaceB q w h c₀ x.length →
      ∃ N, (rcompile M c₀).Ends x H' N ∧ (rcompile M c₀).acceptWithin x N H' = v b ∧
        (rcompile M c₀).AllReach x (Sp (q := q) (w := w) (h := h) c₀ x) H') :
    ∃ N, (rcompile M c₀).Ends x H N ∧
      (rcompile M c₀).acceptWithin x N H = (v false + v true) / 2 ∧
      (rcompile M c₀).AllReach x (Sp (q := q) (w := w) (h := h) c₀ x) H := by
  obtain ⟨d, hds, hdB, hp⟩ := to_flagTest hH habs hsp (by rw [hout]; simp)
  have hv : rdW (d.at (stF M c₀)) = true := by
    rw [rdW_at, rdW_of_abs hds]; simp [view_run, hout]
  have hl : (rcompile M c₀).stepList x (d.at (stF M c₀)) =
      [(touch x (d.at (stF M c₀))).at (stF M c₀ + 1)] := by
    rw [stepList_of_delta (i := (stF M c₀ + 1, rdW (d.at (stF M c₀)), .stay, .stay))
      (by rw [Config.at_state, delta_stF, hv]; rfl)]
    rfl
  have hDF : (rcompile M c₀).DetOK x (SpOK (q := q) (w := w) (h := h) c₀ x) (d.at (stF M c₀)) :=
    detOK_of_range M c₀ hdB (by simpa using stF_ne_flip M c₀)
      (by have := stF_ne_halt M c₀; have := stFlip_lt_stHalt M c₀
          simp only [Config.at_state, stAcc, mainProg_size]; simp only [stFlip] at *; omega)
  have h3B := three_lt_spaceB (q := q) (w := w) (h := h) c₀ (x := x)
  obtain ⟨d2, hd2s, hd2B, -, hp2⟩ := path_of_runs M c₀ (rhosts_mvR2 M c₀) (range_mvR2 M c₀)
    ((runs_mvR 2 _ 1 0 (by omega)).of_eq rfl rfl) (c := touch x (d.at (stF M c₀)))
    (by rw [abs_touch]; exact hds) (by rw [space_touch]; exact hdB)
  set F := d2.at (stFlip M c₀) with hFdef
  have hFabs : F.abs = ⟨lay (regK h w) (encC M (winR c₀ x.length : ℤ) c), 3, 0⟩ := hd2s
  have hFB : F.space ≤ spaceB q w h c₀ x.length := hd2B
  set s : Bool → Config := fun b => (eff x F (b, .stay, .stay)).at (stFlip M c₀ + 1) with hsdef
  have hlF : (rcompile M c₀).stepList x F = [s false, s true] := by
    rw [stepList_of_delta_pair (i := (stFlip M c₀ + 1, false, .stay, .stay))
      (j := (stFlip M c₀ + 1, true, .stay, .stay)) (by rw [Config.at_state, delta_stFlip])]
  have haccF : (rcompile M c₀).accept F.state = false := by
    rw [rcompile_accept, hFdef, Config.at_state, decide_eq_false_iff_not]
    exact fun h => stAcc_ne_flip M c₀ h.symm
  -- the two branches
  have hbr : ∀ b, ∃ k, (rcompile M c₀).Ends x (s b) k ∧
      (rcompile M c₀).acceptWithin x k (s b) = v b ∧
      (rcompile M c₀).AllReach x (Sp (q := q) (w := w) (h := h) c₀ x) (s b) := by
    intro b
    have hview : F.view = lay (regK h w) (encC M (winR c₀ x.length : ℤ) c) :=
      congrArg TState.view hFabs
    have hhead : F.wHead = 3 := congrArg TState.head hFabs
    have hin : F.inHead = 0 := congrArg TState.inHead hFabs
    obtain ⟨e, hes, heB, -, hpe⟩ := path_of_runs M c₀ (rhosts_coinTest M c₀) (range_coinTest M c₀)
      (runs_coinTest M c₀ b c hout (hwin b).1 (hwin b).2) (c := eff x F (b, .stay, .stay))
      (by rw [abs_eff, hview, hhead, hin]; rfl)
      (space_eff_le x F b .stay .stay hFB (Or.inl (by simp [moveWork])))
    obtain ⟨Nb, hNb, hvb, hRb⟩ := hnext b (e.at (stL M c₀)) rfl hes heB
    obtain ⟨mb, hmb, hvalb, hRb'⟩ := path_transport hpe Nb hNb hRb
    refine ⟨mb + Nb, hmb, ?_, hRb'⟩
    rw [Nat.add_comm, hvalb, hvb]
  obtain ⟨k₀, hk₀, hv₀, hR₀⟩ := hbr false
  obtain ⟨k₁, hk₁, hv₁, hR₁⟩ := hbr true
  set K := max k₀ k₁
  have hEF : (rcompile M c₀).Ends x F (K + 1) := by
    refine ends_of_succs fun e he => ?_
    have : e ∈ (rcompile M c₀).stepList x F := he
    rw [hlF] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl
    · exact hk₀.mono (le_max_left _ _)
    · exact hk₁.mono (le_max_right _ _)
  have hvF : (rcompile M c₀).acceptWithin x (K + 1) F = (v false + v true) / 2 := by
    rw [acceptWithin_pair hlF haccF,
      acceptWithin_stable k₀ _ hk₀ K (le_max_left _ _), hv₀,
      acceptWithin_stable k₁ _ hk₁ K (le_max_right _ _), hv₁]
  have hRF : (rcompile M c₀).AllReach x (Sp (q := q) (w := w) (h := h) c₀ x) F := by
    refine allReach_of_succs hFB fun e he => ?_
    have : e ∈ (rcompile M c₀).stepList x F := he
    rw [hlF] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl
    · exact hR₀
    · exact hR₁
  have hpath := hp.trans (.head hDF (step_of_single hl) hp2)
  obtain ⟨m, hm, hval, hR⟩ := path_transport hpath (K + 1) hEF hRF
  refine ⟨K + 1 + m, by rw [Nat.add_comm]; exact hm, ?_, hR⟩
  rw [hval, hvF]

/-- **The iteration claim.** -/
theorem iter_claim (hLS : ∀ coins t, M.spaceThrough x coins t ≤ c₀ * Nat.clog 2 (x.length + 2)) :
    ∀ (r : ℕ) (coins : CoinTape) (t : ℕ) (H : Config), H.state = stL M c₀ →
      H.abs = encTS M c₀ x (M.run x coins t) → H.space ≤ spaceB q w h c₀ x.length →
      HaltsFrom M x r (M.run x coins t) →
      ∃ N, (rcompile M c₀).Ends x H N ∧
        (rcompile M c₀).acceptWithin x N H = M.probFrom x r (M.run x coins t) ∧
        (rcompile M c₀).AllReach x (Sp (q := q) (w := w) (h := h) c₀ x) H := by
  intro r
  induction r with
  | zero =>
      intro coins t H hH habs hsp hhalt
      obtain ⟨v, hv⟩ := output_some_of_haltsFrom_zero M hhalt
      rw [probFrom_out M hv]
      cases v with
      | true => simpa using case_true hH habs hsp hv
      | false => simpa using case_false hH habs hsp hv
  | succ r ih =>
      intro coins t H hH habs hsp hhalt
      rcases hv : M.output (M.run x coins t).state with _ | v
      · obtain ⟨N, hN, hval, hR⟩ := case_run (v := fun b => M.probFrom x r (M.step x b
            (M.run x coins t))) hH habs hsp hv
          (fun b => ⟨winOK_run M c₀ hLS coins t, by
            rw [← run_update_succ]; exact winOK_run M c₀ hLS _ _⟩)
          (fun b H' hH' habs' hsp' => by
            have := ih (Function.update coins t b) (t + 1) H' hH'
              (by rw [run_update_succ]; exact habs') hsp'
              (by rw [run_update_succ]; exact haltsFrom_step M hhalt b)
            rwa [run_update_succ] at this)
        exact ⟨N, hN, by rw [hval]; rfl, hR⟩
      · rw [probFrom_out M hv]
        cases v with
        | true => simpa using case_true hH habs hsp hv
        | false => simpa using case_false hH habs hsp hv

/-- **From the initial configuration**: if `M` has an output after `t₀` steps on every coin
sequence, every host run on `x` ends, every reachable host configuration fits in `spaceB` cells,
and once the runs have ended the host has accepted with probability exactly
`M.acceptanceProbability x t₀`. -/
theorem init_claim (hLS : ∀ coins t, M.spaceThrough x coins t ≤ c₀ * Nat.clog 2 (x.length + 2))
    {t₀ : ℕ} (hhalt : M.HaltsBy x t₀) :
    ∃ N, (rcompile M c₀).Ends x init N ∧
      (rcompile M c₀).acceptWithin x N init = M.acceptanceProbability x t₀ ∧
      (rcompile M c₀).AllReach x (Sp (q := q) (w := w) (h := h) c₀ x) init := by
  obtain ⟨d, hds, hdB, -, hp⟩ := path_of_runs M c₀ (rhosts_initPart M c₀) (range_initPart M c₀)
    (runs_initPart M c₀) (c := init) init_abs (init_space_le c₀ x)
  have hH : HaltsFrom M x t₀ (M.run x (fun _ => false) 0) := by
    intro coins
    obtain ⟨b, hb⟩ := hhalt coins
    exact ⟨b, by rw [ExactDerandomization.Machine.run_eq_runFrom] at hb; exact hb⟩
  obtain ⟨N, hN, hval, hR⟩ := iter_claim hLS t₀ (fun _ => false) 0 (d.at (stL M c₀)) rfl hds hdB hH
  obtain ⟨m, hm, hval', hR'⟩ := path_transport hp N hN hR
  have hi : init.at 0 = init := rfl
  rw [hi] at hm hval' hR'
  refine ⟨N + m, by rw [Nat.add_comm]; exact hm, ?_, hR'⟩
  rw [hval', hval, ExactDerandomization.Machine.acceptanceProbability_eq_probFrom]
  rfl

end RandFromLogspace

end Complexity.Space
