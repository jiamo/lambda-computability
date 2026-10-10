import Start.LogspaceToSpaceInit

/-!
# The upstream-to-host compiler: `ExactDerandomization.Machine` into `Complexity.Space.Machine`

This library's own module (task `M27-SPACE-MODEL-COMPILE`).  For a machine `M` of
`Start/LogspaceDeterministic.lean` (`q + 1` states, `w` two-sided work tapes, `h` input heads) and a
constant `c₀`, `FromLogspace.compile M c₀` is the host machine of `Start/SpaceMachine.lean` given by
the tape program

  `loop runTest (mvL 3; (if ruler then stepProg M else initProg M c₀); mvR 3)`,

compiled by `Complexity.Space.Prog.machine`.  Between iterations the work tape holds the register
file `encC M W c` of the simulated configuration `c` (window radius `W = winR c₀ n`) with the work
head on the presence cell of the result register; the loop leaves when that register is non-empty,
i.e. when the simulated machine has accepted.  On the blank initial tape the ruler is missing, so
the first iteration runs `initProg`.  A rejecting run of `M` halts in a state with output `false`,
on which `stepProg` does nothing; the host machine then loops forever in the same configuration,
without accepting.

The simulation runs `M` on the coin sequence `fun _ => false`; a deterministic decider is
independent of its coins.

Main results (all with the hypothesis that `M` uses at most `c₀ ⌈log₂ (n + 2)⌉` work cells, the
`LogSpace` bound, on the all-`false` coins):

* `FromLogspace.compile_wellFormed`, `FromLogspace.compile_deterministic`;
* `FromLogspace.compile_accepts_iff` — if `M` decides `A`, the host machine accepts exactly `A`;
* `FromLogspace.compile_spaceBoundedOn` — **every** configuration reachable by the host machine on
  `x` (including those inside the initialization, the counters, the input seeks, the dispatch and
  the window registers) uses at most `spaceB q w h c₀ |x|` cells;
* `FromLogspace.spaceB_le` — `spaceB q w h c₀ n ≤ C_M · (c₀ ⌈log₂ (n + 2)⌉ + log₂ (n + 2) + 1)`
  with `C_M = 2 (q + 6) (2 (7 + h + 2 w) + 1)`;
* `FromLogspace.spaceB_le_log` — `spaceB q w h c₀ n ≤ a (log₂ (n + 1) + 1)` with
  `a = (2 c₀ + q + 7) (2 (7 + h + 2 w) + 1)`;
* `FromLogspace.logspace_of_L` — `{x | A x} ∈ ExactDerandomization.L → LOGSPACE A`.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace FromLogspace

open Tracks Prog
open ExactDerandomization (Word InputSymbol Direction Configuration readInput CoinTape)

variable {q w h : ℕ} (M : ExactDerandomization.Machine q w h)

/-! ### Head positions stay inside the window -/

theorem workPos_step_close {x : Word} (b : Bool) (c : Configuration q w h x.length) (k : Fin w) :
    (M.step x b c).workPos k = c.workPos k ∨ (M.step x b c).workPos k = c.workPos k + 1 ∨
      (M.step x b c).workPos k = c.workPos k - 1 := by
  unfold ExactDerandomization.Machine.step
  split
  · left; rfl
  · dsimp only
    generalize (M.transition c.state (fun j => readInput x (c.inputPos j))
      (fun k => c.work k (c.workPos k)) b).workMove k = d
    cases d <;> simp [Direction.move]

theorem Icc_subset_visited (x : Word) (coins : CoinTape) (k : Fin w) (t : ℕ) :
    Finset.Icc (min 0 ((M.run x coins t).workPos k)) (max 0 ((M.run x coins t).workPos k)) ⊆
      (Finset.range (t + 1)).image (fun s => (M.run x coins s).workPos k) := by
  induction t with
  | zero =>
      intro z hz
      simp only [ExactDerandomization.Machine.run_zero, ExactDerandomization.Machine.initial,
        min_self, max_self, Finset.Icc_self, Finset.mem_singleton] at hz
      exact Finset.mem_image.2 ⟨0, by simp, by simp [hz, ExactDerandomization.Machine.initial]⟩
  | succ t ih =>
      intro z hz
      by_cases hz' : z ∈ Finset.Icc (min 0 ((M.run x coins t).workPos k))
          (max 0 ((M.run x coins t).workPos k))
      · exact Finset.image_subset_image (Finset.range_mono (by omega)) (ih hz')
      · have hz2 : z = (M.run x coins (t + 1)).workPos k := by
          rw [Finset.mem_Icc] at hz hz'
          rw [ExactDerandomization.Machine.run_succ] at hz ⊢
          rcases workPos_step_close M (coins t) (M.run x coins t) k with e | e | e <;>
            rw [e] at hz ⊢ <;> omega
        exact Finset.mem_image.2 ⟨t + 1, by simp, hz2.symm⟩

/-- A head position is bounded by the number of cells visited so far. -/
theorem workPos_lt_of_spaceThrough (x : Word) (coins : CoinTape) {S : ℕ}
    (hS : ∀ t, M.spaceThrough x coins t ≤ S) (t : ℕ) (k : Fin w) :
    -(S : ℤ) < (M.run x coins t).workPos k ∧ (M.run x coins t).workPos k < S := by
  have h1 := Finset.card_le_card (Icc_subset_visited M x coins k t)
  have h2 : ((Finset.range (t + 1)).image (fun s => (M.run x coins s).workPos k)).card ≤
      M.spaceThrough x coins t := by
    unfold ExactDerandomization.Machine.spaceThrough
    exact Finset.single_le_sum (f := fun k : Fin w => ((Finset.range (t + 1)).image
      (fun s => (M.run x coins s).workPos k)).card) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
  have h3 := hS t
  rw [Int.card_Icc] at h1
  omega

theorem clog_le_succ_length_bnum (n : ℕ) : Nat.clog 2 (n + 2) ≤ (bnum n).length + 1 :=
  Nat.clog_le_of_le_pow (lt_two_pow_length_bnum n)

theorem succ_length_bnum_le_clog (n : ℕ) : (bnum n).length + 1 ≤ Nat.clog 2 (n + 2) := by
  have h := two_pow_length_le (bnum n)
  rw [bval_bnum] at h
  exact (Nat.lt_clog_iff_pow_lt (by norm_num)).2 (by omega)

/-- The window radius is exactly the `LogSpace` bound `c₀ ⌈log₂ (n + 2)⌉`. -/
theorem winR_eq_clog (c₀ n : ℕ) : winR c₀ n = c₀ * Nat.clog 2 (n + 2) := by
  unfold winR
  rw [le_antisymm (succ_length_bnum_le_clog n) (clog_le_succ_length_bnum n)]

/-! ### The host program -/

/-- The all-`false` coin sequence. -/
def zeroCoins : CoinTape := fun _ => false

/-- The run of `M` on the all-`false` coins. -/
abbrev run0 (x : Word) (t : ℕ) : Configuration q w h x.length := M.run x zeroCoins t

/-- The register bound `N`: windows `2 W + 1`, unary state `q`, counters `log₂ (n + 2) + 1`. -/
def nBound (q c₀ n : ℕ) : ℕ := 2 * winR c₀ n + q + Nat.log 2 (n + 2) + 3

/-- The space bound of the host machine on inputs of length `n`. -/
def spaceB (q w h c₀ n : ℕ) : ℕ := (nBound q c₀ n + 3) * wd (regK h w)

/-- The observable state of the host between two simulated steps. -/
def encTS (c₀ : ℕ) (x : Word) (c : Configuration q w h x.length) : TState :=
  ⟨lay (regK h w) (encC M (winR c₀ x.length : ℤ) c), 3, 0⟩

/-- The loop body: initialize if the ruler is missing, otherwise simulate one transition. -/
def body (c₀ : ℕ) : Prog :=
  .seq (mvL 3) (.seq (.ite (fun _ w => w) (stepProg M) (initProg M c₀)) (mvR 3))

/-- The loop test: continue while the result register is empty. -/
def runTest : Test := fun _ w => !w

/-- **The compiled host machine.** -/
def compile (c₀ : ℕ) : Machine := (Prog.loop runTest (body M c₀)).machine

theorem compile_wellFormed (c₀ : ℕ) : (compile M c₀).WellFormed := machine_wellFormed _

theorem compile_deterministic (c₀ : ℕ) : (compile M c₀).Deterministic :=
  machine_deterministic _

section run

variable (c₀ : ℕ)

theorem toNat_window (n : ℕ) : (2 * (winR c₀ n : ℤ) + 1).toNat = 2 * winR c₀ n + 1 := by
  omega

theorem runs_body_init (x : Word) :
    Runs x (spaceB q w h c₀ x.length) (body M c₀) ⟨fun _ => false, 0, 0⟩
      (encTS M c₀ x (M.initial x.length)) := by
  have hB : (nBound q c₀ x.length + 3) * wd (regK h w) ≤ spaceB q w h c₀ x.length := le_rfl
  have hwB := wd_lt_of_hB hB
  have h3B : 3 < spaceB q w h c₀ x.length := by
    have := Nat.mul_le_mul_right (wd (regK h w)) (show 3 ≤ nBound q c₀ x.length + 3 by omega)
    have : 7 ≤ regK h w := by unfold regK; omega
    unfold wd at *; omega
  unfold body encTS
  refine ((runs_mvL 3 _ 0 0).of_eq rfl (by rfl : _ = (⟨fun _ => false, 0, 0⟩ : TState))).seq
    (Runs.seq (t := ⟨lay (regK h w) (encC M (winR c₀ x.length : ℤ) (M.initial x.length)), 0, 0⟩)
      ?_ ?_)
  · exact Runs.iteF (by rfl) (runs_initProg M c₀ _ hB (by unfold nBound; omega)
      (by unfold nBound; omega) (by unfold nBound; omega))
  · exact (runs_mvR 3 _ 0 0 (by omega)).of_eq rfl rfl

theorem runs_body_step (x : Word)
    (hLS : ∀ t, M.spaceThrough x zeroCoins t ≤ c₀ * Nat.clog 2 (x.length + 2)) (t : ℕ) :
    Runs x (spaceB q w h c₀ x.length) (body M c₀) (encTS M c₀ x (run0 M x t))
      (encTS M c₀ x (run0 M x (t + 1))) := by
  have hB : (nBound q c₀ x.length + 3) * wd (regK h w) ≤ spaceB q w h c₀ x.length := le_rfl
  have hwB := wd_lt_of_hB hB
  have hW := winR_eq_clog c₀ x.length
  have hwin : ∀ k : Fin w, -(winR c₀ x.length : ℤ) ≤ (run0 M x t).workPos k ∧
      (run0 M x t).workPos k ≤ winR c₀ x.length ∧
      -(winR c₀ x.length : ℤ) ≤ (M.step x false (run0 M x t)).workPos k ∧
      (M.step x false (run0 M x t)).workPos k ≤ winR c₀ x.length := by
    intro k
    rw [hW]
    have a1 := workPos_lt_of_spaceThrough M x zeroCoins hLS t k
    have a2 := workPos_lt_of_spaceThrough M x zeroCoins hLS (t + 1) k
    rw [ExactDerandomization.Machine.run_succ] at a2
    have e : zeroCoins t = false := rfl
    rw [e] at a2
    push_cast at a1 a2 ⊢
    refine ⟨by linarith [a1.1], by linarith [a1.2], by linarith [a2.1], by linarith [a2.2]⟩
  have hstep := runs_stepProg (x := x) (B := spaceB q w h c₀ x.length) M
    (winR c₀ x.length : ℤ) (run0 M x t) (nBound q c₀ x.length) hB
    (by rw [toNat_window]; unfold nBound; omega) (by unfold nBound; omega)
    (by unfold nBound; omega) hwin
  have hrun : run0 M x (t + 1) = M.step x false (run0 M x t) := rfl
  have h3B : 3 < spaceB q w h c₀ x.length := by
    have := Nat.mul_le_mul_right (wd (regK h w)) (show 3 ≤ nBound q c₀ x.length + 3 by omega)
    have : 7 ≤ regK h w := by unfold regK; omega
    unfold wd at *; omega
  unfold body encTS
  rw [hrun]
  refine ((runs_mvL 3 _ 3 0).of_eq rfl (by rfl : _ = (⟨lay (regK h w)
    (encC M (winR c₀ x.length : ℤ) (run0 M x t)), 0, 0⟩ : TState))).seq
    (Runs.seq (t := ⟨lay (regK h w) (encC M (winR c₀ x.length : ℤ)
      (M.step x false (run0 M x t))), 0, 0⟩) ?_ ?_)
  · refine Runs.iteT ?_ hstep
    have := mk_ruler (regK h w) (fun j b => decide (b < (encC M (winR c₀ x.length : ℤ)
      (run0 M x t) j).length)) (fun j b => (encC M (winR c₀ x.length : ℤ) (run0 M x t) j).getD b
        false) 0
    simpa [lay] using this
  · exact (runs_mvR 3 _ 0 0 (by omega)).of_eq rfl rfl

/-! ### The abstract machine of the simulation -/

open Classical in
/-- The host configuration after one more loop iteration, chosen among those the body reaches. -/
noncomputable def nxt (x : Word) (i : ℕ) (H : Config) : Config :=
  if hd : ∃ d, Exec x (fun c => c.space ≤ spaceB q w h c₀ x.length) (body M c₀) (touch x H) d ∧
      d.abs = encTS M c₀ x (run0 M x i) ∧ d.space ≤ spaceB q w h c₀ x.length
  then Classical.choose hd else H

/-- Accepting index: the simulated machine has output `true` at time `i - 1`. -/
def acc (x : Word) (i : ℕ) : Prop := i ≠ 0 ∧ M.output (run0 M x (i - 1)).state = some true

instance (x : Word) (i : ℕ) : Decidable (acc M x i) := by unfold acc; infer_instance

/-- The abstract machine whose steps are the loop iterations: index `0` is the blank tape, index
`t + 1` is the encoding of the simulated configuration at time `t`. -/
noncomputable def absM : AbsMachine (Word × ℕ × Config) where
  start x := (x, 0, init)
  step s := if acc M s.1 s.2.1 then none else some (s.1, s.2.1 + 1, nxt M c₀ s.1 s.2.1 s.2.2)
  accept s := decide (acc M s.1 s.2.1)

/-- The invariant of reachable abstract states. -/
def Inv (x : Word) (s : Word × ℕ × Config) : Prop :=
  s.1 = x ∧ (s.2.1 = 0 → s.2.2 = init) ∧
    ∀ t, s.2.1 = t + 1 → s.2.2.abs = encTS M c₀ x (run0 M x t) ∧
      s.2.2.space ≤ spaceB q w h c₀ x.length

theorem init_abs : init.abs = ⟨fun _ => false, 0, 0⟩ := by
  show (⟨fun i => ([] : List Bool).getD i false, 0, 0⟩ : TState) = _
  congr 1

theorem init_space_le (x : Word) : init.space ≤ spaceB q w h c₀ x.length := by
  show max 0 (0 + 1) ≤ _
  unfold spaceB
  have : 1 ≤ (nBound q c₀ x.length + 3) * wd (regK h w) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

variable (hLS : ∀ x t, M.spaceThrough x zeroCoins t ≤ c₀ * Nat.clog 2 (x.length + 2))
include hLS

theorem body_exec (x : Word) (i : ℕ) (H : Config) (hI : Inv M c₀ x (x, i, H)) :
    ∃ d, Exec x (fun c => c.space ≤ spaceB q w h c₀ x.length) (body M c₀) (touch x H) d ∧
      d.abs = encTS M c₀ x (run0 M x i) ∧ d.space ≤ spaceB q w h c₀ x.length := by
  rcases i with _ | t
  · have hH : H = init := hI.2.1 rfl
    subst hH
    exact runs_body_init M c₀ x (touch x init) (by rw [abs_touch, init_abs])
      (by rw [space_touch]; exact init_space_le (q := q) (w := w) (h := h) c₀ x)
  · obtain ⟨habs, hsp⟩ := hI.2.2 t rfl
    exact runs_body_step M c₀ x (hLS x) t (touch x H) (by rw [abs_touch, habs])
      (by rw [space_touch]; exact hsp)

theorem nxt_spec (x : Word) (i : ℕ) (H : Config) (hI : Inv M c₀ x (x, i, H)) :
    Exec x (fun c => c.space ≤ spaceB q w h c₀ x.length) (body M c₀) (touch x H)
        (nxt M c₀ x i H) ∧
      (nxt M c₀ x i H).abs = encTS M c₀ x (run0 M x i) ∧
      (nxt M c₀ x i H).space ≤ spaceB q w h c₀ x.length := by
  have hd := body_exec M c₀ hLS x i H hI
  unfold nxt
  rw [dif_pos hd]
  exact Classical.choose_spec hd

theorem reaches_inv {x : Word} {s : Word × ℕ × Config} (hs : (absM M c₀).Reaches x s) :
    Inv M c₀ x s := by
  induction hs with
  | refl => exact ⟨rfl, fun _ => rfl, fun t ht => by simp [absM] at ht⟩
  | @tail s s' _ hst ih =>
      obtain ⟨s1, i, H⟩ := s
      have ih' := ih
      obtain ⟨h1, _, _⟩ := ih'
      try simp only at h1
      subst h1
      change (if acc M s1 i then none else some (s1, i + 1, nxt M c₀ s1 i H)) = some s' at hst
      split at hst
      · exact absurd hst (by simp)
      · obtain rfl := Option.some.inj hst
        obtain ⟨_, h2, h3⟩ := nxt_spec M c₀ hLS s1 i H ih
        refine ⟨rfl, fun h0 => by simp at h0, fun t ht => ?_⟩
        simp only [Nat.add_right_cancel_iff] at ht
        subst ht
        exact ⟨h2, h3⟩

omit hLS in
theorem test_enc (x : Word) (H : Config) (c : Configuration q w h x.length)
    (hH : H.abs = encTS M c₀ x c) :
    runTest (rdIn x H) (rdW H) = !decide (M.output c.state = some true) := by
  have hv := congrArg TState.view hH
  have hw := congrArg TState.head hH
  simp only [Config.abs, encTS] at hv hw
  have hr : rdW H = H.view H.wHead := rfl
  rw [hr, hv, hw]
  have := lay_pres (K := regK h w) (encC M (winR c₀ x.length : ℤ) c) 1 (by unfold regK; omega) 0
  simp only [zero_mul, zero_add] at this
  simp only [runTest]
  rw [this]
  simp only [encC, encR_RES]
  split_ifs with ho <;> simp [ho]

theorem realizes_compile :
    Realizes (compile M c₀) (absM M c₀)
      (fun x (s : Word × ℕ × Config) => if ((absM M c₀).step s).isSome then s.2.2.at 0
        else (touch x s.2.2).at (Prog.loop runTest (body M c₀)).size)
      (fun x => spaceB q w h c₀ x.length) := by
  refine Prog.realizes_loop (enc := fun _ (s : Word × ℕ × Config) => s.2.2) (fun x => rfl) ?_ ?_ ?_ ?_ ?_
  · intro x
    simp [absM, acc]
  · intro x s hs
    obtain ⟨h1, h2, h3⟩ := reaches_inv M c₀ hLS hs
    obtain ⟨s1, i, H⟩ := s
    rcases i with _ | t
    · rw [h2 rfl]; exact init_space_le (q := q) (w := w) (h := h) c₀ x
    · exact (h3 t rfl).2
  · intro x s _
    simp only [absM]
    split_ifs with hc <;> simp [hc]
  · intro x s hs hstop
    obtain ⟨h1, h2, h3⟩ := reaches_inv M c₀ hLS hs
    obtain ⟨s1, i, H⟩ := s
    try simp only at h1
    subst h1
    have hacc : acc M s1 i := by
      by_contra hc
      simp [absM, hc] at hstop
    obtain ⟨hi, ho⟩ := hacc
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    simp only
    rw [test_enc M c₀ s1 H _ (h3 t rfl).1]
    simpa using ho
  · intro x s s' hs hstep
    have hI := reaches_inv M c₀ hLS hs
    obtain ⟨h1, h2, h3⟩ := hI
    obtain ⟨s1, i, H⟩ := s
    try simp only at h1
    subst h1
    change (if acc M s1 i then none else some (s1, i + 1, nxt M c₀ s1 i H)) = some s' at hstep
    split at hstep
    · exact absurd hstep (by simp)
    · rename_i hnacc
      obtain rfl := Option.some.inj hstep
      refine ⟨?_, (nxt_spec M c₀ hLS s1 i H ⟨rfl, h2, h3⟩).1⟩
      rcases i with _ | t
      · rw [h2 rfl]; rfl
      · simp only
        rw [test_enc M c₀ s1 H _ (h3 t rfl).1]
        simp only [acc, ne_eq, Nat.add_one_ne_zero, not_false_eq_true, true_and,
          Nat.add_sub_cancel] at hnacc
        simp [hnacc]

theorem absM_accepts_iff (x : Word) :
    (absM M c₀).Accepts x ↔ ∃ t, M.output (run0 M x t).state = some true := by
  constructor
  · rintro ⟨s, hs, hacc⟩
    obtain ⟨h1, _, _⟩ := reaches_inv M c₀ hLS hs
    obtain ⟨s1, i, H⟩ := s
    try simp only at h1
    subst h1
    simp only [absM, decide_eq_true_eq] at hacc
    exact ⟨i - 1, hacc.2⟩
  · rintro ⟨t, ht⟩
    have key : ∀ i, ∃ s, (absM M c₀).Reaches x s ∧ (s.2.1 = i ∨ (absM M c₀).accept s = true) := by
      intro i
      induction i with
      | zero => exact ⟨_, AbsMachine.Reaches.start x, Or.inl rfl⟩
      | succ i ih =>
          obtain ⟨s, hs, hi⟩ := ih
          rcases hi with hi | hi
          · cases hst : (absM M c₀).step s with
            | none =>
                refine ⟨s, hs, Or.inr ?_⟩
                simp only [absM] at hst ⊢
                split_ifs at hst with hc
                simpa using hc
            | some s' =>
                refine ⟨s', hs.tail hst, Or.inl ?_⟩
                simp only [absM] at hst
                split_ifs at hst
                obtain rfl := Option.some.inj hst
                simp [hi]
          · exact ⟨s, hs, Or.inr hi⟩
    obtain ⟨s, hs, hi⟩ := key (t + 1)
    refine ⟨s, hs, ?_⟩
    rcases hi with hi | hi
    · obtain ⟨h1, _, _⟩ := reaches_inv M c₀ hLS hs
      obtain ⟨s1, i, H⟩ := s
      try simp only at h1 hi
      subst h1 hi
      simp [absM, acc, ht]
    · exact hi

theorem compile_accepts_iff_output (x : Word) :
    (compile M c₀).Accepts x ↔ ∃ t, M.output (run0 M x t).state = some true :=
  ((realizes_compile M c₀ hLS).accepts_iff (compile_deterministic M c₀) x).trans
    (absM_accepts_iff M c₀ hLS x)

/-- **Acceptance**: if `M` decides `A`, the compiled host machine accepts exactly `A`. -/
theorem compile_accepts_iff {A : ExactDerandomization.Language} (hdec : M.Decides A)
    (x : Word) : (compile M c₀).Accepts x ↔ x ∈ A := by
  rw [compile_accepts_iff_output M c₀ hLS]
  obtain ⟨t₀, b, hb, hout⟩ := hdec x
  constructor
  · rintro ⟨t, ht⟩
    have := ExactDerandomization.Machine.halted_outputs_eq (hout zeroCoins) ht
    exact hb.1 this
  · intro hx
    exact ⟨t₀, by rw [hout zeroCoins, hb.2 hx]⟩

/-- **The space bound on every reachable host configuration.** -/
theorem compile_spaceBoundedOn (x : Word) :
    (compile M c₀).SpaceBoundedOn x (spaceB q w h c₀ x.length) :=
  (realizes_compile M c₀ hLS).spaceBoundedOn (compile_deterministic M c₀) x

end run

/-! ### The explicit bound -/

theorem log_two_add_two_le (n : ℕ) : Nat.log 2 (n + 2) ≤ Nat.log 2 (n + 1) + 1 := by
  have : Nat.log 2 ((n + 1) * 2) = Nat.log 2 (n + 1) + 1 := Nat.log_mul_base (by norm_num) (by omega)
  have h2 : Nat.log 2 (n + 2) ≤ Nat.log 2 ((n + 1) * 2) := Nat.log_mono_right (by omega)
  omega

/-- The bound in the form `C_M (s + log₂ (n + 2) + 1)`, with `s = c₀ ⌈log₂ (n + 2)⌉` the upstream
space bound. -/
theorem spaceB_le (q w h c₀ n : ℕ) :
    spaceB q w h c₀ n ≤ 2 * (q + 6) * (2 * (7 + h + 2 * w) + 1) *
      (c₀ * Nat.clog 2 (n + 2) + Nat.log 2 (n + 2) + 1) := by
  unfold spaceB nBound wd regK
  rw [winR_eq_clog]
  set S := c₀ * Nat.clog 2 (n + 2)
  set L := Nat.log 2 (n + 2)
  have h1 : 2 * S + q + L + 3 + 3 ≤ 2 * (q + 6) * (S + L + 1) := by nlinarith
  calc (2 * S + q + L + 3 + 3) * (2 * (7 + h + 2 * w) + 1)
      ≤ 2 * (q + 6) * (S + L + 1) * (2 * (7 + h + 2 * w) + 1) := Nat.mul_le_mul_right _ h1
    _ = _ := by ring

/-- The bound in the form of `LOGSPACE`. -/
theorem spaceB_le_log (q w h c₀ n : ℕ) :
    spaceB q w h c₀ n ≤ (2 * c₀ + q + 7) * (2 * (7 + h + 2 * w) + 1) *
      (Nat.log 2 (n + 1) + 1) := by
  unfold spaceB nBound wd regK winR
  have hl := length_bnum_le n
  have h2 := log_two_add_two_le n
  set u := Nat.log 2 (n + 1)
  set ℓ := (bnum n).length
  set L := Nat.log 2 (n + 2)
  have h1 : 2 * (c₀ * (ℓ + 1)) + q + L + 3 + 3 ≤ (2 * c₀ + q + 7) * (u + 1) := by
    have : c₀ * (ℓ + 1) ≤ c₀ * (u + 1) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  calc (2 * (c₀ * (ℓ + 1)) + q + L + 3 + 3) * (2 * (7 + h + 2 * w) + 1)
      ≤ (2 * c₀ + q + 7) * (u + 1) * (2 * (7 + h + 2 * w) + 1) := Nat.mul_le_mul_right _ h1
    _ = _ := by ring

/-! ### `L ⊆ LOGSPACE` -/

/-- **`ExactDerandomization.L ⊆ LOGSPACE`**, through the concrete compiler. -/
theorem logspace_of_L {A : Language} (hA : {x | A x} ∈ ExactDerandomization.L) : LOGSPACE A := by
  obtain ⟨q, w, h, M, _, ⟨c₀, _, hc₀⟩, hdec⟩ := hA
  have hLS : ∀ x t, M.spaceThrough x zeroCoins t ≤ c₀ * Nat.clog 2 (x.length + 2) :=
    fun x t => hc₀ x zeroCoins t
  refine ⟨(2 * c₀ + q + 7) * (2 * (7 + h + 2 * w) + 1), compile M c₀, compile_wellFormed M c₀,
    compile_deterministic M c₀, ?_, ?_⟩
  · intro x n c hc
    exact (compile_spaceBoundedOn M c₀ hLS x n c hc).trans (spaceB_le_log q w h c₀ x.length)
  · intro x
    exact (compile_accepts_iff M c₀ hLS hdec x).symm

end FromLogspace

end Complexity.Space
