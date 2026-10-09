import Start.SpaceToLogspaceStep

/-!
# The compiled machine: the clock and the simulation of host runs

This module is this library's own (tasks `M27-SPACE-MODEL-COMPILE`, `M27-SPACE-MODEL-TOTALIZE`).

* `ReachesVia P u v` — the compiled machine runs from `u` to `v`, every configuration on the way
  (both ends included) satisfying `P`;
* `clockVal` — the number shown by the clock digits, in base `n + 2`;
* `sweep_reach`, `tick_reach` — **the odometer**: a tick from digit `j` adds `(n+2)^j` when some
  higher digit is not maximal, and rejects otherwise;
* `macro_step` — one host step costs a bounded segment of target steps: `run`, `fix`, then a
  tick;
* `simulate` — the target machine reaches the encoding of the `t`-th host configuration, with
  clock value `t`, for every `t` below `(n+2)^k` such that the host has neither accepted nor
  halted earlier.
-/

set_option autoImplicit false

namespace Complexity.Space

namespace ToLogspace

open ExactDerandomization (Word InputSymbol Direction FMachine FAction FConfig readInput)

variable {M : Machine} {k : ℕ} {x : Word}

variable (M k x) in
/-- A run segment of the compiled machine, every configuration of which satisfies `P`. -/
def ReachesVia (P : FConfig (Ph M.states k) 2 (k + 1) x.length → Prop)
    (u v : FConfig (Ph M.states k) 2 (k + 1) x.length) : Prop :=
  ∃ m, (stp M k x)^[m] u = v ∧ ∀ i ≤ m, P ((stp M k x)^[i] u)

namespace ReachesVia

variable {P : FConfig (Ph M.states k) 2 (k + 1) x.length → Prop}
  {u v w : FConfig (Ph M.states k) 2 (k + 1) x.length}

theorem refl (hu : P u) : ReachesVia M k x P u u :=
  ⟨0, rfl, fun i hi => by rwa [Nat.le_zero.mp hi]⟩

theorem trans (h₁ : ReachesVia M k x P u v) (h₂ : ReachesVia M k x P v w) :
    ReachesVia M k x P u w := by
  obtain ⟨m₁, e₁, p₁⟩ := h₁
  obtain ⟨m₂, e₂, p₂⟩ := h₂
  refine ⟨m₂ + m₁, by rw [Function.iterate_add_apply, e₁, e₂], fun i hi => ?_⟩
  by_cases hi₁ : i ≤ m₁
  · exact p₁ i hi₁
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le hi₁)
    have := p₂ d (by omega)
    rwa [← e₁, ← Function.iterate_add_apply, Nat.add_comm d m₁] at this

theorem step (hu : P u) (hv : P v) (h : stp M k x u = v) : ReachesVia M k x P u v := by
  refine ⟨1, h, fun i hi => ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
  · exact hu
  · simpa [h] using hv

theorem step_trans (hu : P u) (h : stp M k x u = v) (h₂ : ReachesVia M k x P v w) :
    ReachesVia M k x P u w := by
  obtain ⟨m, e, p⟩ := h₂
  exact (step hu (p 0 (Nat.zero_le _)) h).trans ⟨m, e, p⟩

end ReachesVia

/-! ### The clock -/

/-- The value of the clock digits `D` in base `n + 2`. -/
def clockVal {n : ℕ} (D : Fin k → Fin (n + 2)) : ℕ := ∑ j : Fin k, (D j).val * (n + 2) ^ j.val

theorem clockVal_update {n : ℕ} (D : Fin k → Fin (n + 2)) (j : Fin k) (v : Fin (n + 2)) :
    clockVal (Function.update D j v) + (D j).val * (n + 2) ^ j.val =
      clockVal D + v.val * (n + 2) ^ j.val := by
  unfold clockVal
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have : ∑ i ∈ Finset.univ.erase j, ((Function.update D j v) i).val * (n + 2) ^ i.val =
      ∑ i ∈ Finset.univ.erase j, (D i).val * (n + 2) ^ i.val :=
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [this, Function.update_self]
  ring

theorem clockVal_max {n : ℕ} : ∀ k : ℕ, ∑ j : Fin k, (n + 1) * (n + 2) ^ j.val + 1 = (n + 2) ^ k
  | 0 => by simp
  | k + 1 => by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have := clockVal_max (n := n) k
      rw [pow_succ]
      nlinarith

theorem clockVal_le {n : ℕ} (D : Fin k → Fin (n + 2)) : clockVal D + 1 ≤ (n + 2) ^ k := by
  rw [← clockVal_max k]
  have : clockVal D ≤ ∑ j : Fin k, (n + 1) * (n + 2) ^ j.val :=
    Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (by omega)
  omega

/-- When the clock shows its largest value, every digit is maximal. -/
theorem clockVal_eq_max {n : ℕ} (D : Fin k → Fin (n + 2)) (h : clockVal D + 1 = (n + 2) ^ k)
    (j : Fin k) : (D j).val = n + 1 := by
  by_contra hj
  have hlt : clockVal D < ∑ j : Fin k, (n + 1) * (n + 2) ^ j.val := by
    apply Finset.sum_lt_sum
    · intro i _; exact Nat.mul_le_mul_right _ (by omega)
    · exact ⟨j, Finset.mem_univ _, Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)⟩
  have := clockVal_max (n := n) k
  omega

variable {P : FConfig (Ph M.states k) 2 (k + 1) x.length → Prop}

/-- A carry: digit `j` is swept back to the left end marker. -/
theorem sweep_reach (q : Fin M.states) (c : Config) (i₀ : Fin (x.length + 2))
    (hP : ∀ p D, P (encR M k p c i₀ D)) (j : Fin k) :
    ∀ (v : ℕ) (D : Fin k → Fin (x.length + 2)), (D j).val = v →
      ReachesVia M k x P (encR M k (.sweep q j) c i₀ D)
        (encR M k (.sweep q j) c i₀ (Function.update D j ⟨0, by omega⟩)) := by
  intro v
  induction v with
  | zero =>
      intro D hD
      have : Function.update D j ⟨0, by omega⟩ = D := by
        rw [Function.update_eq_self_iff]; ext; exact hD.symm
      rw [this]
      exact .refl (hP _ _)
  | succ v ih =>
      intro D hD
      refine ReachesVia.step_trans (hP _ _) (stp_sweep_move (by omega)) ?_
      have := ih (Function.update D j ⟨(D j).val - 1, by omega⟩) (by simp; omega)
      rwa [Function.update_idem] at this

/-- **The odometer.**  A tick from digit `j` either adds `(n+2)^j` to the clock value and resumes
the simulation, or — when all digits from `j` on are maximal — rejects. -/
theorem tick_reach (q : Fin M.states) (c : Config) (i₀ : Fin (x.length + 2))
    (hP : ∀ p D, P (encR M k p c i₀ D)) :
    ∀ (r j : ℕ) (hj : j < k) (D : Fin k → Fin (x.length + 2)), k - j = r + 1 →
      ((∃ i : Fin k, j ≤ i.val ∧ (D i).val < x.length + 1) →
        ∃ D', ReachesVia M k x P (encR M k (.tick q ⟨j, hj⟩) c i₀ D) (encR M k (.run q) c i₀ D') ∧
          clockVal D' = clockVal D + (x.length + 2) ^ j) ∧
      ((∀ i : Fin k, j ≤ i.val → (D i).val = x.length + 1) →
        ∃ D', ReachesVia M k x P (encR M k (.tick q ⟨j, hj⟩) c i₀ D) (encR M k .rej c i₀ D')) := by
  intro r
  induction r with
  | zero =>
      intro j hj D hr
      have hjk : ¬ j + 1 < k := by omega
      by_cases hD : (D ⟨j, hj⟩).val < x.length + 1
      · refine ⟨fun _ => ⟨_, .step (hP _ _) (hP _ _) (stp_tick_inc hD), ?_⟩, fun h => ?_⟩
        · have := clockVal_update D ⟨j, hj⟩ ⟨(D ⟨j, hj⟩).val + 1, by omega⟩
          simp only at this
          nlinarith
        · exact absurd (h ⟨j, hj⟩ le_rfl) (by omega)
      · have hD' : (D ⟨j, hj⟩).val = x.length + 1 := by have := (D ⟨j, hj⟩).isLt; omega
        refine ⟨fun ⟨i, hi, hlt⟩ => ?_, fun _ => ⟨D, .step (hP _ _) (hP _ _) (stp_tick_over hD' hjk)⟩⟩
        have : i = ⟨j, hj⟩ := by ext; simp only; have := i.isLt; omega
        subst this
        omega
  | succ r ih =>
      intro j hj D hr
      have hjk : j + 1 < k := by omega
      by_cases hD : (D ⟨j, hj⟩).val < x.length + 1
      · refine ⟨fun _ => ⟨_, .step (hP _ _) (hP _ _) (stp_tick_inc hD), ?_⟩, fun h => ?_⟩
        · have := clockVal_update D ⟨j, hj⟩ ⟨(D ⟨j, hj⟩).val + 1, by omega⟩
          simp only at this
          nlinarith
        · exact absurd (h ⟨j, hj⟩ le_rfl) (by omega)
      · have hD' : (D ⟨j, hj⟩).val = x.length + 1 := by have := (D ⟨j, hj⟩).isLt; omega
        set D₁ := Function.update D ⟨j, hj⟩ ⟨0, by omega⟩ with hD₁
        have hseg : ReachesVia M k x P (encR M k (.tick q ⟨j, hj⟩) c i₀ D)
            (encR M k (.tick q ⟨j + 1, hjk⟩) c i₀ D₁) := by
          refine ReachesVia.step_trans (hP _ _) (stp_tick_carry hD' hjk) ?_
          refine (sweep_reach q c i₀ hP ⟨j, hj⟩ _ D rfl).trans ?_
          exact .step (hP _ _) (hP _ _) (stp_sweep_done (by simp) hjk)
        have hD₁i : ∀ i : Fin k, j + 1 ≤ i.val → D₁ i = D i := fun i hi =>
          Function.update_of_ne (fun e => by rw [e] at hi; simp at hi) _ _
        obtain ⟨ih₁, ih₂⟩ := ih (j + 1) hjk D₁ (by omega)
        refine ⟨fun ⟨i, hi, hlt⟩ => ?_, fun h => ?_⟩
        · have hij : j + 1 ≤ i.val := by
            rcases Nat.lt_or_eq_of_le hi with h' | h'
            · omega
            · exfalso
              have : i = ⟨j, hj⟩ := by ext; exact h'.symm
              subst this; omega
          obtain ⟨D', hR, hv⟩ := ih₁ ⟨i, hij, by rw [hD₁i i hij]; exact hlt⟩
          refine ⟨D', hseg.trans hR, ?_⟩
          have hu := clockVal_update D ⟨j, hj⟩ ⟨0, by omega⟩
          simp only [zero_mul, add_zero, hD'] at hu
          rw [hv, ← hD₁] at *
          rw [pow_succ]
          nlinarith
        · obtain ⟨D', hR⟩ := ih₂ fun i hi => by rw [hD₁i i hi]; exact h i (by omega)
          exact ⟨D', hseg.trans hR⟩

/-! ### Host runs -/

variable (M x) in
/-- The successor of a host configuration (the first instruction, for a deterministic host). -/
def hnext (c : Config) : Option Config := (M.stepList x c).head?

variable (M x) in
/-- The run of the host. -/
def hrun : ℕ → Option Config
  | 0 => some init
  | t + 1 => (hrun t).bind (hnext M x)

theorem step_iff_hnext (hdet : M.Deterministic) {c c' : Config} :
    M.Step x c c' ↔ hnext M x c = some c' := by
  unfold Machine.Step hnext
  have hl : (M.stepList x c).length ≤ 1 := by
    simp only [Machine.stepList, List.length_map]; exact hdet _ _ _
  constructor
  · intro h
    rcases hs : M.stepList x c with _ | ⟨d, _ | ⟨e, l⟩⟩
    · simp [hs] at h
    · simp only [hs, List.mem_singleton] at h; simp [h]
    · simp [hs] at hl
  · intro h
    exact List.mem_of_mem_head? h

theorem steps_iff_hrun (hdet : M.Deterministic) :
    ∀ (t : ℕ) (c : Config), Reach.steps (M.Step x) t init c ↔ hrun M x t = some c := by
  intro t
  induction t with
  | zero => intro c; simp [hrun, eq_comm]
  | succ t ih =>
      intro c
      simp only [Reach.steps_succ, hrun, Option.bind_eq_some_iff, ih, step_iff_hnext hdet]

theorem hrun_reach {t : ℕ} {c : Config} (hdet : M.Deterministic) (h : hrun M x t = some c) :
    Reach.steps (M.Step x) t init c := (steps_iff_hrun hdet t c).2 h

/-- The shape of a successful host step. -/
theorem hnext_eq {c c' : Config} (h : hnext M x c = some c') :
    ∃ b dI dW rest, M.delta c.state x[c.inHead]? (c.tape.getD c.wHead false) =
      (c'.state, b, dI, dW) :: rest ∧ c' = succCfg x.length c c'.state b dI dW := by
  rcases hd : M.delta c.state x[c.inHead]? (c.tape.getD c.wHead false) with
    _ | ⟨⟨q', b, dI, dW⟩, rest⟩
  · simp only [hnext, Machine.stepList, hd, List.map_nil, List.head?_nil, reduceCtorEq] at h
  · simp only [hnext, Machine.stepList, hd, List.map_cons, List.head?_cons,
      Option.some.injEq] at h
    subst h
    exact ⟨b, dI, dW, rest, rfl, rfl⟩

theorem hnext_none {c : Config} (h : hnext M x c = none) :
    M.delta c.state x[c.inHead]? (c.tape.getD c.wHead false) = [] := by
  unfold hnext Machine.stepList at h
  simpa using h

theorem moveInput_inPos {n i : ℕ} (hi : i ≤ n) (d : Dir) :
    (dirIn d).moveInput (inPos n i) = inPos n (moveIn n i d) ∨
      (moveIn n i d = 0 ∧ (dirIn d).moveInput (inPos n i) = ⟨0, by omega⟩) := by
  cases d with
  | left =>
      by_cases h0 : i = 0
      · subst h0; right; simp [dirIn, Direction.moveInput, inPos, moveIn]
      · left; ext; simp [dirIn, Direction.moveInput, inPos, moveIn]; omega
  | right => left; ext; simp [dirIn, Direction.moveInput, inPos, moveIn]; omega
  | stay => left; rfl

/-- **One host step** as a target segment `run → fix → tick`. -/
theorem macro_step (hwf : M.WellFormed) (hk : 0 < k) {c c' : Config}
    {D : Fin k → Fin (x.length + 2)} (hi : c.inHead ≤ x.length) (hq : c.state < M.states)
    (hacc : M.accept c.state = false) (hn : hnext M x c = some c')
    (hP : ∀ p i₀ D, P (encR M k p c i₀ D)) (hP' : ∀ p i₀ D, P (encR M k p c' i₀ D)) :
    ∃ hq' : c'.state < M.states,
      ((∃ i : Fin k, (D i).val < x.length + 1) →
        ∃ D', ReachesVia M k x P (enc M k (.run ⟨c.state, hq⟩) c D)
          (enc M k (.run ⟨c'.state, hq'⟩) c' D') ∧ clockVal D' = clockVal D + 1) ∧
      ((∀ i : Fin k, (D i).val = x.length + 1) →
        ∃ i₀ D', ReachesVia M k x P (enc M k (.run ⟨c.state, hq⟩) c D) (encR M k .rej c' i₀ D')) := by
  obtain ⟨b, dI, dW, rest, hd, hc'⟩ := hnext_eq hn
  have hq' : c'.state < M.states := hwf.2 _ _ _ _ (by rw [hd]; exact List.mem_cons_self)
  refine ⟨hq', ?_⟩
  have hrun := stp_run (k := k) (q := ⟨c.state, hq⟩) (D := D) hi hacc hd hq'
  rw [← hc'] at hrun
  have hin : c'.inHead = moveIn x.length c.inHead dI := by rw [hc']; rfl
  have hfix := stp_fix (M := M) (q := ⟨_, hq'⟩) (D := D) hk (c := c')
    (i₀ := (dirIn dI).moveInput (inPos x.length c.inHead)) (by rw [hin]; exact moveInput_inPos hi dI)
  have hseg : ReachesVia M k x P (enc M k (.run ⟨c.state, hq⟩) c D)
      (enc M k (.tick ⟨_, hq'⟩ ⟨0, hk⟩) c' D) :=
    ReachesVia.step_trans (hP _ _ _) hrun (.step (hP' _ _ _) (hP' _ _ _) hfix)
  obtain ⟨t₁, t₂⟩ := tick_reach (P := P) ⟨_, hq'⟩ c' _
    (fun p D => hP' p _ D) (k - 1) 0 hk D (by omega)
  refine ⟨fun ⟨i, hlt⟩ => ?_, fun h => ?_⟩
  · obtain ⟨D', hR, hv⟩ := t₁ ⟨i, Nat.zero_le _, hlt⟩
    exact ⟨D', hseg.trans hR, by simpa using hv⟩
  · obtain ⟨D', hR⟩ := t₂ fun i _ => h i
    exact ⟨_, D', hseg.trans hR⟩

end ToLogspace

end Complexity.Space
