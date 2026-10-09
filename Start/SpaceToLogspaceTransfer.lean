import Start.SpaceToLogspaceRun

/-!
# Host `LOGSPACE` languages are in `ExactDerandomization.L`

This module is this library's own (tasks `M27-SPACE-MODEL-COMPILE`, `M27-SPACE-MODEL-TOTALIZE`,
first half of `M27-LOGSPACE-TRANSFER`).

* `outcome` — on every input, the compiled machine reaches an output configuration whose output
  is the host's acceptance, and every configuration on the way keeps both work heads inside the
  host's space bound.  Two cases: the host accepts or halts before the clock expires, or the clock
  expires; in the latter case the host cannot accept, because an accepting run can be shortened
  below `cfgBound` (`Complexity.Space.exists_short_accepting_run`) and the clock counts at least
  that far.
* `compile_decides`, `compile_spaceThrough` — the machine-level witnesses: the compiled machine
  decides the host language, halts on every input, and uses at most `2 s(|x|)` work cells.
* `cfgBound_le_clock` — the explicit clock length `k = Q (a+1)² 2^a + a + 3` suffices for space
  bound `a (log₂ (n+1) + 1)`.
* `logspace_subset_L` — **every host `LOGSPACE` language is in `ExactDerandomization.L`**, with
  the explicit machine `compile M k` and space constant `2a + 1`.
-/

set_option autoImplicit false

namespace Complexity.Space

namespace ToLogspace

open ExactDerandomization (Word InputSymbol Direction FMachine FAction FConfig readInput)

variable {M : Machine} {k : ℕ} {x : Word}

/-- The work heads stay among the first `s` cells. -/
def InBound (s : ℕ) (u : FConfig (Ph M.states k) 2 (k + 1) x.length) : Prop :=
  ∀ t, 0 ≤ u.workPos t ∧ u.workPos t < s

theorem inBound_encR {s : ℕ} {c : Config} (hc : c.space ≤ s) (p : Ph M.states k)
    (i₀ : Fin (x.length + 2)) (D : Fin k → Fin (x.length + 2)) :
    InBound s (encR M k p c i₀ D) := by
  intro t
  simp only [encR, Config.space] at hc ⊢
  omega

theorem hrun_none_after {t u : ℕ} (h : hrun M x t = none) (htu : t ≤ u) :
    hrun M x u = none := by
  induction htu with
  | refl => exact h
  | step _ ih => simp [hrun, ih]

theorem reach_inBound (hdet : M.Deterministic) {s : ℕ} (hsp : M.SpaceBoundedOn x s) {t : ℕ}
    {c : Config} (h : hrun M x t = some c) (p : Ph M.states k)
    (i₀ : Fin (x.length + 2)) (D : Fin k → Fin (x.length + 2)) :
    InBound s (encR M k p c i₀ D) :=
  inBound_encR (hsp t c (hrun_reach hdet h)) p i₀ D

theorem initial_inBound {s : ℕ} (hsp : M.SpaceBoundedOn x s) :
    InBound (k := k) (x := x) s ((fcompile M k).initial x.length) := by
  have := hsp 0 init rfl
  intro t
  simp only [FMachine.initial, Config.space, init] at this ⊢
  omega

section Simulation

variable (hwf : M.WellFormed) (hdet : M.Deterministic) {s : ℕ} (hsp : M.SpaceBoundedOn x s)
  (hk : 0 < k)
include hwf hdet hsp hk

/-- **Simulation**: the compiled machine reaches the encoding of the `t`-th host configuration,
with clock value `t`, as long as the clock has not expired and the host has neither accepted nor
halted before time `t`. -/
theorem simulate : ∀ t : ℕ, t < (x.length + 2) ^ k →
    (∀ t' < t, ∃ c, hrun M x t' = some c ∧ M.accept c.state = false ∧ (hnext M x c).isSome) →
    ∃ (c : Config) (D : Fin k → Fin (x.length + 2)) (hq : c.state < M.states),
      hrun M x t = some c ∧ clockVal D = t ∧
      ReachesVia M k x (InBound s) ((fcompile M k).initial x.length)
        (enc M k (.run ⟨c.state, hq⟩) c D) := by
  intro t
  induction t with
  | zero =>
      intro _ _
      refine ⟨init, fun _ => ⟨0, by omega⟩, hwf.1, rfl, by simp [clockVal], ?_⟩
      exact .step (initial_inBound hsp)
        (reach_inBound hdet hsp (t := 0) rfl _ _ _) (stp_init hwf.1)
  | succ t ih =>
      intro ht hprev
      obtain ⟨c, D, hq, hc, hv, hR⟩ := ih (by omega) fun t' h => hprev t' (by omega)
      obtain ⟨c₀, hc₀, hacc, hnx⟩ := hprev t (by omega)
      rw [hc] at hc₀
      cases hc₀
      obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hnx
      have hi : c.inHead ≤ x.length := Machine.inHead_le_of_steps (hrun_reach hdet hc)
      obtain ⟨hq', hgo, -⟩ := macro_step (P := InBound s) (D := D) hwf hk hi hq hacc hc'
        (reach_inBound hdet hsp hc)
        (reach_inBound hdet hsp (t := t + 1) (by simp [hrun, hc, hc']))
      have hex : ∃ i : Fin k, (D i).val < x.length + 1 := by
        by_contra hno
        push Not at hno
        have hall : ∀ i : Fin k, (D i).val = x.length + 1 := fun i => by
          have := (D i).isLt; have := hno i; omega
        have hsum : clockVal D = ∑ j : Fin k, (x.length + 1) * (x.length + 2) ^ j.val :=
          Finset.sum_congr rfl fun j _ => by rw [hall j]
        have := clockVal_max (n := x.length) k
        omega
      obtain ⟨D', hR', hv'⟩ := hgo hex
      exact ⟨c', D', hq', by simp [hrun, hc, hc'], by omega, hR.trans hR'⟩

/-- **Outcome**: the compiled machine reaches an output configuration giving the host's verdict,
with every configuration on the way inside the space bound. -/
theorem outcome (hcfg : cfgBound M x s ≤ (x.length + 2) ^ k) :
    ∃ (m : ℕ) (b : Bool), out M k ((stp M k x)^[m] ((fcompile M k).initial x.length)).state =
        some b ∧ (b = true ↔ M.Accepts x) ∧
      ∀ i ≤ m, InBound s ((stp M k x)^[i] ((fcompile M k).initial x.length)) := by
  classical
  set u₀ := (fcompile M k).initial x.length
  -- `Stop t`: at time `t` the host accepts or halts.
  let Stop : ℕ → Prop := fun t =>
    ∃ c, hrun M x t = some c ∧ (M.accept c.state = true ∨ hnext M x c = none)
  have hpos : 0 < (x.length + 2) ^ k := by positivity
  -- Before the first stop, the host runs on without accepting.
  have hbefore : ∀ t, (∀ t' < t, ¬ Stop t') →
      ∀ t' < t, ∃ c, hrun M x t' = some c ∧ M.accept c.state = false ∧ (hnext M x c).isSome := by
    intro t hns t' ht'
    induction t' with
    | zero =>
        refine ⟨init, rfl, ?_⟩
        have := hns 0 ht'
        simp only [Stop, not_exists, not_and, not_or] at this
        obtain ⟨h1, h2⟩ := this init rfl
        exact ⟨by simpa using h1, Option.isSome_iff_ne_none.mpr h2⟩
    | succ t' ih =>
        obtain ⟨c, hc, -, hnx⟩ := ih (by omega)
        obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hnx
        have hrun' : hrun M x (t' + 1) = some c' := by simp [hrun, hc, hc']
        refine ⟨c', hrun', ?_⟩
        have := hns (t' + 1) ht'
        simp only [Stop, not_exists, not_and, not_or] at this
        obtain ⟨h1, h2⟩ := this c' hrun'
        exact ⟨by simpa using h1, Option.isSome_iff_ne_none.mpr h2⟩
  by_cases hstop : ∃ t, t < (x.length + 2) ^ k ∧ Stop t
  · -- The host accepts or halts before the clock expires.
    let t₀ := Nat.find hstop
    have ht₀ : t₀ < (x.length + 2) ^ k ∧ Stop t₀ := Nat.find_spec hstop
    have hmin : ∀ t' < t₀, ¬ Stop t' := fun t' h hs =>
      Nat.find_min hstop h ⟨by have := ht₀.1; omega, hs⟩
    obtain ⟨c, D, hq, hc, -, ⟨m, hm, hmP⟩⟩ :=
      simulate hwf hdet hsp hk t₀ ht₀.1 (hbefore t₀ hmin)
    obtain ⟨c₁, hc₁, hstp⟩ := ht₀.2
    rw [hc] at hc₁; cases hc₁
    have hinc := reach_inBound (k := k) hdet hsp hc
    rcases hacc : M.accept c.state with _ | _
    · -- The host halts in a rejecting state.
      have hnone : hnext M x c = none := by simpa [hacc] using hstp
      have hi : c.inHead ≤ x.length := Machine.inHead_le_of_steps (hrun_reach hdet hc)
      have hrej := stp_run_halt (k := k) (q := ⟨c.state, hq⟩) (D := D) hi hacc (hnext_none hnone)
      refine ⟨m + 1, false, ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', hm, hrej]; rfl
      · simp only [Bool.false_eq_true, false_iff]
        rintro ⟨n', c', hc', hacc'⟩
        rw [steps_iff_hrun hdet] at hc'
        rcases lt_trichotomy n' t₀ with hlt | heq | hgt
        · obtain ⟨c'', hc'', hacc'', -⟩ := hbefore t₀ hmin n' hlt
          rw [hc'] at hc''; cases hc''
          rw [hacc''] at hacc'; exact absurd hacc' (by simp)
        · subst heq; rw [hc] at hc'; cases hc'; rw [hacc] at hacc'; exact absurd hacc' (by simp)
        · have : hrun M x (t₀ + 1) = none := by simp [hrun, hc, hnone]
          rw [hrun_none_after this hgt] at hc'; cases hc'
      · intro i hi
        rcases Nat.lt_or_ge i (m + 1) with h | h
        · exact hmP i (by omega)
        · have : i = m + 1 := by omega
          subst this
          rw [Function.iterate_succ_apply', hm, hrej]
          exact hinc _ _ _
    · -- The host accepts.
      have hacc' := stp_run_acc (k := k) (x := x) (q := ⟨c.state, hq⟩) (c := c)
        (i₀ := inPos x.length c.inHead) (D := D) hacc
      refine ⟨m + 1, true, ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', hm]
        simp only [enc] at hacc' ⊢
        rw [hacc']; rfl
      · simp only [true_iff]
        exact ⟨t₀, c, hrun_reach hdet hc, hacc⟩
      · intro i hi
        rcases Nat.lt_or_ge i (m + 1) with h | h
        · exact hmP i (by omega)
        · have : i = m + 1 := by omega
          subst this
          rw [Function.iterate_succ_apply', hm]
          simp only [enc] at hacc' ⊢
          rw [hacc']
          exact hinc _ _ _
  · -- The clock expires.
    push Not at hstop
    set T := (x.length + 2) ^ k - 1
    have hns : ∀ t' < T, ¬ Stop t' := fun t' h hs => hstop t' (by omega) hs
    obtain ⟨c, D, hq, hc, hv, ⟨m, hm, hmP⟩⟩ :=
      simulate hwf hdet hsp hk T (by omega) (hbefore T hns)
    have hall : ∀ i : Fin k, (D i).val = x.length + 1 :=
      clockVal_eq_max D (by omega)
    have hnT := hstop T (by omega)
    simp only [Stop, not_exists, not_and, not_or] at hnT
    obtain ⟨hacc, hnx⟩ := hnT c hc
    obtain ⟨c', hc'⟩ := Option.ne_none_iff_exists'.mp hnx
    have hi : c.inHead ≤ x.length := Machine.inHead_le_of_steps (hrun_reach hdet hc)
    obtain ⟨hq', -, hover⟩ := macro_step (P := InBound s) (D := D) hwf hk hi hq
      (by simpa using hacc) hc'
      (reach_inBound hdet hsp hc)
      (reach_inBound hdet hsp (t := T + 1) (by simp [hrun, hc, hc']))
    obtain ⟨i₀, D', ⟨m', hm', hmP'⟩⟩ := hover hall
    refine ⟨m' + m, false, ?_, ?_, ?_⟩
    · rw [Function.iterate_add_apply, hm, hm']; rfl
    · simp only [Bool.false_eq_true, false_iff]
      intro hA
      obtain ⟨n', c'', hlt, hc'', hacc''⟩ := exists_short_accepting_run hwf hsp hA
      rw [steps_iff_hrun hdet] at hc''
      have := hstop n' (by omega)
      exact this ⟨c'', hc'', .inl hacc''⟩
    · intro i hi
      by_cases him : i ≤ m
      · exact hmP i him
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le him)
        have := hmP' d (by omega)
        rwa [← hm, ← Function.iterate_add_apply, Nat.add_comm d m] at this

end Simulation

/-! ### Machine-level witnesses -/

theorem iterate_out {u : FConfig (Ph M.states k) 2 (k + 1) x.length} {b : Bool}
    (h : out M k u.state = some b) : ∀ d, (stp M k x)^[d] u = u := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply', ih, stp_out h]

/-- **The compiled machine decides the host language and halts on every input**, provided the
clock is long enough. -/
theorem compile_decides (hwf : M.WellFormed) (hdet : M.Deterministic) (hk : 0 < k)
    (s : ℕ → ℕ) (hsp : M.SpaceBounded s)
    (hcfg : ∀ x : Word, cfgBound M x (s x.length) ≤ (x.length + 2) ^ k) :
    (compile M k).Decides {x | M.Accepts x} := by
  intro x
  obtain ⟨m, b, hout, hb, -⟩ :=
    outcome hwf hdet (M.spaceBoundedOn_of_spaceBounded hsp x) hk (hcfg x)
  refine ⟨m, b, hb, fun coins => ?_⟩
  rw [compile, FMachine.toMachine_output_run, run_eq]
  exact hout

/-- **Every configuration of the compiled machine keeps its two work heads among the first
`s |x|` cells**, so the space it uses is at most `2 s |x|`. -/
theorem compile_spaceThrough (hwf : M.WellFormed) (hdet : M.Deterministic) (hk : 0 < k)
    (s : ℕ → ℕ) (hsp : M.SpaceBounded s)
    (hcfg : ∀ x : Word, cfgBound M x (s x.length) ≤ (x.length + 2) ^ k)
    (x : Word) (coins : ExactDerandomization.CoinTape) (t : ℕ) :
    (compile M k).spaceThrough x coins t ≤ 2 * s x.length := by
  obtain ⟨m, b, hout, -, hP⟩ :=
    outcome hwf hdet (M.spaceBoundedOn_of_spaceBounded hsp x) hk (hcfg x)
  have hall : ∀ i, InBound (s x.length) ((stp M k x)^[i] ((fcompile M k).initial x.length)) := by
    intro i
    by_cases hi : i ≤ m
    · exact hP i hi
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le hi)
      rw [Nat.add_comm m d, Function.iterate_add_apply, iterate_out hout]
      exact hP m le_rfl
  rw [compile, FMachine.toMachine_spaceThrough]
  have hcard : ∀ w : Fin 2, ((Finset.range (t + 1)).image
      (fun i => ((fcompile M k).run x coins i).workPos w)).card ≤ s x.length := by
    intro w
    calc _ ≤ ((Finset.range (s x.length)).image (fun j : ℕ => (j : ℤ))).card := by
          apply Finset.card_le_card
          intro z hz
          simp only [Finset.mem_image, Finset.mem_range] at hz ⊢
          obtain ⟨i, -, rfl⟩ := hz
          rw [run_eq]
          obtain ⟨h0, h1⟩ := hall i w
          exact ⟨((stp M k x)^[i] ((fcompile M k).initial x.length)).workPos w |>.toNat,
            by omega, by omega⟩
      _ ≤ (Finset.range (s x.length)).card := Finset.card_image_le
      _ = s x.length := Finset.card_range _
  calc _ ≤ ∑ _w : Fin 2, s x.length := Finset.sum_le_sum fun w _ => hcard w
    _ = 2 * s x.length := by simp

/-! ### The explicit clock and the class inclusion -/

/-- The clock length used for space bound `a (log₂ (n+1) + 1)` and `Q` host states. -/
def clockLen (Q a : ℕ) : ℕ := Q * (a + 1) ^ 2 * 2 ^ a + a + 3

/-- **The clock is long enough**: `cfgBound ≤ (n+2)^(Q (a+1)² 2^a + a + 3)`. -/
theorem cfgBound_le_clock (M : Machine) (a : ℕ) (x : Word) :
    cfgBound M x (a * (Nat.log 2 (x.length + 1) + 1)) ≤
      (x.length + 2) ^ clockLen M.states a := by
  set n := x.length
  set L := Nat.log 2 (n + 1)
  set Q := M.states
  have h2L : 2 ^ L ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
  have hLn : L ≤ n := by
    have := Nat.lt_two_pow_self (n := L)
    omega
  have hs1 : a * (L + 1) + 1 ≤ (a + 1) * (n + 1) := by nlinarith
  have h2s : 2 ^ (a * (L + 1)) ≤ 2 ^ a * (n + 1) ^ a := by
    rw [mul_comm a, pow_mul, pow_succ, mul_pow, mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2L a)
  set K := Q * (a + 1) ^ 2 * 2 ^ a
  have hK : K ≤ (n + 2) ^ K :=
    le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left (by omega) K)
  calc cfgBound M x (a * (L + 1))
      = Q * (n + 1) * (a * (L + 1) + 1) * 2 ^ (a * (L + 1)) * (a * (L + 1) + 1) := rfl
    _ ≤ Q * (n + 1) * ((a + 1) * (n + 1)) * (2 ^ a * (n + 1) ^ a) * ((a + 1) * (n + 1)) := by
        gcongr
    _ = K * (n + 1) ^ (a + 3) := by simp only [K]; ring
    _ ≤ (n + 2) ^ K * (n + 2) ^ (a + 3) := by
        gcongr
        omega
    _ = (n + 2) ^ clockLen Q a := by rw [← pow_add]; simp only [clockLen, K]; ring_nf

theorem clockLen_pos (Q a : ℕ) : 0 < clockLen Q a := by simp [clockLen]

theorem log_succ_le_clog (n : ℕ) : Nat.log 2 (n + 1) + 1 ≤ Nat.clog 2 (n + 2) := by
  have h1 : 2 ^ Nat.log 2 (n + 1) ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
  have h2 : n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) := Nat.le_pow_clog (by omega) _
  have : 2 ^ Nat.log 2 (n + 1) < 2 ^ Nat.clog 2 (n + 2) := by omega
  have := (Nat.pow_lt_pow_iff_right (by omega)).mp this
  omega

/-- **Host logarithmic space is contained in the upstream class `L`**: every host `LOGSPACE`
language is decided by the explicit machine `compile M (clockLen M.states a)` — deterministic,
halting on every input, and using at most `(2a + 1) ⌈log₂ (n+2)⌉` work cells. -/
theorem logspace_subset_L {A : Language} (h : LOGSPACE A) :
    {x | A x} ∈ ExactDerandomization.L := by
  obtain ⟨a, M, hwf, hdet, hsp, hA⟩ := h
  have hcfg : ∀ x : Word, cfgBound M x (a * (Nat.log 2 (x.length + 1) + 1)) ≤
      (x.length + 2) ^ clockLen M.states a := cfgBound_le_clock M a
  refine ⟨_, 2, clockLen M.states a + 1, compile M (clockLen M.states a),
    compile_deterministic M _, ⟨2 * a + 1, by omega, fun x coins t => ?_⟩, ?_⟩
  · have h1 := compile_spaceThrough hwf hdet (clockLen_pos _ _) _ hsp hcfg x coins t
    have h2 := log_succ_le_clog x.length
    calc _ ≤ 2 * (a * (Nat.log 2 (x.length + 1) + 1)) := h1
      _ ≤ 2 * (a * Nat.clog 2 (x.length + 2)) := by gcongr
      _ ≤ (2 * a + 1) * Nat.clog 2 (x.length + 2) := by nlinarith
  · have hd := compile_decides hwf hdet (clockLen_pos _ _) _ hsp hcfg
    intro x
    obtain ⟨t, b, hb, hout⟩ := hd x
    refine ⟨t, b, ?_, hout⟩
    rw [hb]
    simp only [Set.mem_ofPred_eq]
    exact (hA x).symm

end ToLogspace

end Complexity.Space
