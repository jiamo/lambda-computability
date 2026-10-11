import Start.SpaceRandomized
import Start.SpaceConfigCount
import Start.SpaceCompile

/-!
# Runs of fair-coin host machines: termination, stability and pumping

This library's own module (task `M27-HOST-RANDOMIZED-SPACE`).  Generic facts about the host
machines of `Start/SpaceMachine.lean` and the probability `Machine.acceptWithin` of
`Start/SpaceRandomized.lean`:

* `Machine.Ends M x c N` — every run from `c` has at most `N` steps;
* `Machine.acceptWithin_stable` — once every run from `c` has ended, a longer clock does not
  change `acceptWithin`;
* `Machine.ends_of_path`, `Machine.acceptWithin_path` — along a run segment through
  configurations with a single successor, termination and `acceptWithin` are transported;
* `Machine.runsWithin_cfgBound` — **pumping**: if every run on `x` ends and every reachable
  configuration fits in `s` cells, every run has at most `cfgBound M x s` steps.
-/

set_option autoImplicit false

namespace Complexity.Space

namespace Machine

variable {M : Machine} {x : List Bool}

/-- Every run from `c` has at most `N` steps. -/
def Ends (M : Machine) (x : List Bool) (c : Config) (N : ℕ) : Prop :=
  ∀ d, ¬ Reach.steps (M.Step x) (N + 1) c d

/-- Every configuration reachable from `c` satisfies `P`. -/
def AllReach (M : Machine) (x : List Bool) (P : Config → Prop) (c : Config) : Prop :=
  ∀ n d, Reach.steps (M.Step x) n c d → P d

theorem steps_succ_first {n : ℕ} {a b : Config} :
    Reach.steps (M.Step x) (n + 1) a b ↔ ∃ m, M.Step x a m ∧ Reach.steps (M.Step x) n m b := by
  rw [Nat.add_comm, Reach.steps_add]
  simp only [Reach.steps_one]

theorem Ends.mono {c : Config} {N N' : ℕ} (h : M.Ends x c N) (hN : N ≤ N') : M.Ends x c N' := by
  intro d hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [show N + k + 1 = (N + 1) + k by omega, Reach.steps_add] at hd
  obtain ⟨m, hm, -⟩ := hd
  exact h m hm

theorem Ends.succ {c d : Config} {N : ℕ} (h : M.Ends x c (N + 1)) (hs : M.Step x c d) :
    M.Ends x d N := fun e he => h e (steps_succ_first.2 ⟨d, hs, he⟩)

theorem Ends.zero_stepList {c : Config} (h : M.Ends x c 0) : M.stepList x c = [] := by
  rcases hl : M.stepList x c with _ | ⟨d, l⟩
  · rfl
  · exact absurd ((Reach.steps_one _ _ _).2 (show d ∈ M.stepList x c by rw [hl]; simp))
      (h d)

theorem ends_of_succs {c : Config} {N : ℕ} (h : ∀ d, M.Step x c d → M.Ends x d N) :
    M.Ends x c (N + 1) := by
  intro e he
  obtain ⟨m, hm, he'⟩ := steps_succ_first.1 he
  exact h m hm e he'

theorem AllReach.self {P : Config → Prop} {c : Config} (h : M.AllReach x P c) : P c :=
  h 0 c rfl

theorem allReach_of_succs {P : Config → Prop} {c : Config} (hc : P c)
    (h : ∀ d, M.Step x c d → M.AllReach x P d) : M.AllReach x P c := by
  intro n e he
  cases n with
  | zero => cases he; exact hc
  | succ n =>
      obtain ⟨m, hm, he'⟩ := steps_succ_first.1 he
      exact h m hm n e he'

/-- **Stability**: once every run from `c` has ended, the clock no longer matters. -/
theorem acceptWithin_stable : ∀ (N : ℕ) (c : Config), M.Ends x c N →
    ∀ T, N ≤ T → M.acceptWithin x T c = M.acceptWithin x N c := by
  intro N
  induction N with
  | zero =>
      intro c hc T _
      have hl := hc.zero_stepList
      cases T with
      | zero => rfl
      | succ T => simp only [acceptWithin, hl]
  | succ N ih =>
      intro c hc T hT
      obtain ⟨T, rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
      have hs : ∀ d ∈ M.stepList x c, M.acceptWithin x T d = M.acceptWithin x N d :=
        fun d hd => ih d (hc.succ hd) T (by omega)
      simp only [acceptWithin]
      split
      · rfl
      · rcases hl : M.stepList x c with _ | ⟨d, _ | ⟨d₂, l⟩⟩
        · rfl
        · simp only
          exact hs d (by rw [hl]; simp)
        · simp only
          rw [hs d (by rw [hl]; simp), hs d₂ (by rw [hl]; simp)]

/-- One step to the only successor. -/
theorem acceptWithin_single {c d : Config} (hl : M.stepList x c = [d])
    (hacc : M.accept c.state = false) (T : ℕ) :
    M.acceptWithin x (T + 1) c = M.acceptWithin x T d := by
  simp only [acceptWithin, hl, hacc, Bool.false_eq_true, if_false]

/-- One branching between two successors. -/
theorem acceptWithin_pair {c d₀ d₁ : Config} (hl : M.stepList x c = [d₀, d₁])
    (hacc : M.accept c.state = false) (T : ℕ) :
    M.acceptWithin x (T + 1) c = (M.acceptWithin x T d₀ + M.acceptWithin x T d₁) / 2 := by
  simp only [acceptWithin, hl, hacc, Bool.false_eq_true, if_false]

/-- A halting non-accepting configuration has probability `0`. -/
theorem acceptWithin_halt {c : Config} (hl : M.stepList x c = [])
    (hacc : M.accept c.state = false) (T : ℕ) : M.acceptWithin x T c = 0 := by
  cases T <;> simp [acceptWithin, hl, hacc]

/-- An accepting configuration has probability `1`. -/
theorem acceptWithin_accept {c : Config} (hacc : M.accept c.state = true) (T : ℕ) :
    M.acceptWithin x T c = 1 := by
  cases T <;> simp [acceptWithin, hacc]

theorem ends_halt {c : Config} (hl : M.stepList x c = []) : M.Ends x c 0 := by
  intro d hd
  have : d ∈ M.stepList x c := (Reach.steps_one _ _ _).1 hd
  rw [hl] at this
  simp at this

/-- The side condition of a deterministic segment. -/
def DetOK (M : Machine) (x : List Bool) (P : Config → Prop) (c : Config) : Prop :=
  (M.stepList x c).length ≤ 1 ∧ M.accept c.state = false ∧ P c

theorem stepList_eq_single {c d : Config} (hl : (M.stepList x c).length ≤ 1)
    (hs : M.Step x c d) : M.stepList x c = [d] := by
  unfold Step at hs
  rcases h : M.stepList x c with _ | ⟨e, _ | ⟨e₂, l⟩⟩
  · rw [h] at hs; simp at hs
  · rw [h] at hs; simp only [List.mem_singleton] at hs; rw [hs]
  · rw [h] at hl; simp at hl

/-- **Deterministic segments**: along a run segment whose configurations have a single successor,
are not accepting and satisfy `P`, termination, the probability and the side condition are
transported from the end to the start. -/
theorem path_transport {P : Config → Prop} {a b : Config} (hp : M.Path x (M.DetOK x P) a b) :
    ∀ N, M.Ends x b N → M.AllReach x P b →
      ∃ m, M.Ends x a (m + N) ∧ (∀ T, M.acceptWithin x (T + m) a = M.acceptWithin x T b) ∧
        M.AllReach x P a := by
  induction hp with
  | refl c => intro N hN hR; exact ⟨0, by simpa using hN, fun T => rfl, hR⟩
  | @head c d e hc hs _ ih =>
      intro N hN hR
      obtain ⟨m, hm, hv, hR'⟩ := ih N hN hR
      have hl := stepList_eq_single hc.1 hs
      refine ⟨m + 1, ?_, fun T => ?_, ?_⟩
      · rw [show m + 1 + N = (m + N) + 1 by omega]
        refine ends_of_succs fun d' hd' => ?_
        have : d' ∈ M.stepList x c := hd'
        rw [hl, List.mem_singleton] at this
        subst this; exact hm
      · rw [← Nat.add_assoc, acceptWithin_single hl hc.2.1, hv]
      · refine allReach_of_succs hc.2.2 fun d' hd' => ?_
        have : d' ∈ M.stepList x c := hd'
        rw [hl, List.mem_singleton] at this
        subst this; exact hR'

/-! ### Pumping -/

/-- A walk of length at least the number of bounded configurations repeats a configuration, so
there are walks of every length. -/
theorem runsWithin_cfgBound (hwf : M.WellFormed) {s : ℕ} (hsp : M.SpaceBoundedOn x s) {N : ℕ}
    (hN : M.RunsWithin x N) : M.RunsWithin x (cfgBound M x s) := by
  classical
  intro d hd
  set K := cfgBound M x s
  obtain ⟨f, hf0, hfK, hstep⟩ := Reach.exists_isWalk hd
  -- every prefix of the walk is a run from `init`
  have hpre : ∀ i, i ≤ K + 1 → Reach.steps (M.Step x) i init (f i) := by
    intro i hi
    rw [← hf0]
    exact Reach.steps_of_chain f i fun j hj => hstep j (by omega)
  let g : Fin (K + 1) → BoundedCfg M x s := fun i =>
    ⟨f i, mem_boundedCfg_of_steps hwf hsp (hpre i (by omega))⟩
  have hcard : Fintype.card (BoundedCfg M x s) < Fintype.card (Fin (K + 1)) := by
    rw [Fintype.card_fin]; exact Nat.lt_succ_of_le (card_boundedCfg_le M x s)
  obtain ⟨i, j, hij, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
  have hfij : f i = f j := congrArg Subtype.val hg
  obtain ⟨a, ha, b, hb, hab, hfab⟩ : ∃ a, a ≤ K ∧ ∃ b, b ≤ K ∧ a < b ∧ f a = f b := by
    have hi := i.isLt; have hj := j.isLt
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact ⟨i, by omega, j, by omega, h, hfij⟩
    · exact ⟨j, by omega, i, by omega, h, hfij.symm⟩
  clear hfij hg hij i j g hcard
  -- the cycle from `f a` back to itself
  have hcyc : Reach.steps (M.Step x) (b - a) (f a) (f a) := by
    have := Reach.steps_of_chain (fun k => f (a + k)) (b - a) fun k hk =>
      hstep (a + k) (by omega)
    simp only [Nat.add_zero] at this
    rwa [show a + (b - a) = b by omega, ← hfab] at this
  have hpump : ∀ r, Reach.steps (M.Step x) (a + r * (b - a)) init (f a) := by
    intro r
    induction r with
    | zero => simpa using hpre a (by omega)
    | succ r ih =>
        rw [show a + (r + 1) * (b - a) = (a + r * (b - a)) + (b - a) by ring]
        exact (Reach.steps_add _ _ _ _ _).2 ⟨f a, ih, hcyc⟩
  have hlen : N + 1 ≤ a + (N + 1) * (b - a) := by
    have : 1 ≤ b - a := by omega
    nlinarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hlen
  have := hpump (N + 1)
  rw [hk, Reach.steps_add] at this
  obtain ⟨m, hm, -⟩ := this
  exact hN m hm

end Machine

end Complexity.Space
