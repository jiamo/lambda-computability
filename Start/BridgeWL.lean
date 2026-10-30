/-
**Bridge: the Weisfeiler–Leman lower bound for the host multi-tape machines** — milestone M31
(`M31-BRIDGE-WL`).

The Weisfeiler–Leman development (`Start/WL*.lean`, absorbed; main theorem
`WLTime.unconditional_time_lower_bound : WLTime.MainClaim`) proves an `n ^ Ω(k)` lower bound on
the time in which a machine of its own models (`WLTime.TM`, multi-tape machines over `ℤ`-indexed
tapes, and word RAMs) decides `k`-dimensional WL equivalence of two encoded graphs.  The host has
its own multi-tape machines, `DepthThreeLowerBound.FiniteMultiTapeMachine`
(`Start/DepthThreeModel.lean`, over Mathlib's `Turing.Tape`, with arbitrary finite tapes,
alphabet and states), whose polynomial-time deciders are polynomial time in Cobham's sense
(`Complexity.MultiTapeCobham.inP_of_multiTapeHaltsIn`).  This module compiles a host machine into
a WL machine, step for step.

* `WLBridge.tm` — the compiled machine: one WL tape per host tape (input tape first), symbols
  numbered with the blank at `0` and the input bits at `1`, `2`, and one WL state per host state,
  plus the halting states `1` (accept) and `2` (reject);
* `WLBridge.rel_run` — **the simulation**: after `t` steps of the host machine, the WL machine
  after `t` steps represents the same configuration;
* `WLBridge.haltsIn_tm` — a host run halting with output `b` within `T` steps gives a WL run
  halting within `T + 1` steps, accepting iff `b`;
* **`WLTime.multiTape_lower_bound`** — **the WL lower bound for host machines**: there are
  `c > 0` and `k₀` such that a host multi-tape machine deciding `k`-WL equivalence (`k ≥ k₀`)
  within time `T n` on graphs with `n` vertices has `n ^ (c k) ≤ T n + 1` for all large `n`;
* **`WLTime.multiTape_not_poly`** — consequently, for `2a < c k`, no host multi-tape machine
  decides `k`-WL equivalence within time `C (|x| + 1) ^ a` in the length of its input `x`.
-/

import Start.WLMain
import Start.DepthThreeMultiTapeMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Classical

namespace WLBridge

open DepthThreeLowerBound

variable (M : FiniteMultiTapeMachine)

/-! ### Numbering tapes, symbols and states -/

theorem card_K_pos : 0 < Fintype.card M.K := Fintype.card_pos_iff.mpr ⟨M.inputTape⟩

/-- A numbering of the tapes with the input tape at `0`. -/
def tapeNum : M.K ≃ Fin (Fintype.card M.K) :=
  (Fintype.equivFin M.K).trans
    (Equiv.swap ((Fintype.equivFin M.K) M.inputTape) ⟨0, card_K_pos M⟩)

theorem tapeNum_input : tapeNum M M.inputTape = ⟨0, card_K_pos M⟩ := by
  simp [tapeNum, Equiv.swap_apply_left]

theorem tapeNum_symm_zero (a : Fin (Fintype.card M.K)) (ha : (a : ℕ) = 0) :
    (tapeNum M).symm a = M.inputTape := by
  rw [Equiv.symm_apply_eq, tapeNum_input]
  exact Fin.ext ha

theorem tapeNum_symm_ne (a : Fin (Fintype.card M.K)) (ha : (a : ℕ) ≠ 0) :
    (tapeNum M).symm a ≠ M.inputTape := by
  intro h
  rw [Equiv.symm_apply_eq, tapeNum_input] at h
  exact ha (by rw [h])

/-- The number of a symbol: the blank is `0`, the input bits `false`, `true` are `1`, `2`. -/
def symCode (g : M.Γ) : ℕ :=
  if g = default then 0 else if g = M.inputSymbol false then 1 else
    if g = M.inputSymbol true then 2 else 3 + Fintype.equivFin M.Γ g

theorem symCode_lt (g : M.Γ) : symCode M g < Fintype.card M.Γ + 3 := by
  have := (Fintype.equivFin M.Γ g).isLt
  unfold symCode
  split_ifs <;> omega

/-- The symbol of a number. -/
def symDec (s : ℕ) : M.Γ :=
  if s = 0 then default else if s = 1 then M.inputSymbol false else
    if s = 2 then M.inputSymbol true else
      if h : s - 3 < Fintype.card M.Γ then (Fintype.equivFin M.Γ).symm ⟨s - 3, h⟩ else default

theorem symDec_code (g : M.Γ) : symDec M (symCode M g) = g := by
  unfold symCode
  split_ifs with h0 h1 h2
  · simp [symDec, h0]
  · simp [symDec, h1]
  · simp [symDec, h2]
  · have hlt := (Fintype.equivFin M.Γ g).isLt
    have hs : 3 + ((Fintype.equivFin M.Γ) g : ℕ) - 3 < Fintype.card M.Γ := by omega
    simp only [symDec, show 3 + ((Fintype.equivFin M.Γ) g : ℕ) ≠ 0 by omega,
      show 3 + ((Fintype.equivFin M.Γ) g : ℕ) ≠ 1 by omega,
      show 3 + ((Fintype.equivFin M.Γ) g : ℕ) ≠ 2 by omega, ite_false, dite_eq_left hs]
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by simp)

theorem symCode_default : symCode M default = 0 := by simp [symCode]

theorem symCode_input (b : Bool) : symCode M (M.inputSymbol b) = if b then 2 else 1 := by
  have h0 := M.input_ne_blank b
  have hft : M.inputSymbol true ≠ M.inputSymbol false := fun h =>
    Bool.noConfusion (M.input_injective h)
  cases b with
  | false => simp [symCode, h0]
  | true => simp [symCode, h0, hft]

/-- A symbol as a WL symbol. -/
def encSym (g : M.Γ) : Fin (Fintype.card M.Γ + 3) := ⟨symCode M g, symCode_lt M g⟩

/-- The number of a host state, above the three reserved WL states. -/
def stCode (q : M.Q) : ℕ := 3 + Fintype.equivFin M.Q q

theorem stCode_lt (q : M.Q) : stCode M q < Fintype.card M.Q + 3 := by
  have := (Fintype.equivFin M.Q q).isLt
  unfold stCode
  omega

/-- The host state of a WL state; the initial WL state `0` is the initial host state. -/
def stDec (s : ℕ) : M.Q :=
  if h : 3 ≤ s ∧ s - 3 < Fintype.card M.Q then (Fintype.equivFin M.Q).symm ⟨s - 3, h.2⟩
  else M.initialState

theorem stDec_code (q : M.Q) : stDec M (stCode M q) = q := by
  have hlt := (Fintype.equivFin M.Q q).isLt
  have h : 3 ≤ stCode M q ∧ stCode M q - 3 < Fintype.card M.Q := by
    unfold stCode
    omega
  rw [stDec, dite_eq_left h, Equiv.symm_apply_eq]
  exact Fin.ext (by simp [stCode])

theorem stDec_zero : stDec M 0 = M.initialState := by simp [stDec]

/-- A host head move as a WL head move. -/
def moveOf : HeadMove → WLTime.Move
  | .left => .left
  | .stay => .stay
  | .right => .right

theorem apply_nth {Γ : Type} [Inhabited Γ] (m : HeadMove) (T : Turing.Tape Γ) (i : ℤ) :
    (m.apply T).nth (i - (moveOf m).displacement) = T.nth i := by
  cases m with
  | left =>
      simp only [HeadMove.apply_left, Turing.Tape.move_left_nth, moveOf, WLTime.Move.displacement]
      congr 1
      ring
  | stay => simp [moveOf, WLTime.Move.displacement]
  | right =>
      simp only [HeadMove.apply_right, Turing.Tape.move_right_nth, moveOf,
        WLTime.Move.displacement]
      congr 1
      ring

theorem mk₁_nth {Γ : Type} [Inhabited Γ] (l : List Γ) (z : ℤ) :
    (Turing.Tape.mk₁ l).nth z = if 0 ≤ z then l.getI z.toNat else default := by
  cases z with
  | ofNat n =>
      simp only [Int.ofNat_eq_natCast, Int.natCast_nonneg, ite_true, Int.toNat_natCast]
      exact Turing.Tape.mk'_nth_nat _ _ n
  | negSucc n =>
      simp only [Int.negSucc_not_nonneg, ite_false]
      rfl

/-! ### The compiled machine -/

/-- The transition of the compiled machine.  A state decodes to a host state; if the host machine
halts there, the WL machine moves to `1` or `2` according to the output, else it performs the
host step. -/
def trans (s : Fin (Fintype.card M.Q + 3))
    (r : Fin (Fintype.card M.K) → Fin (Fintype.card M.Γ + 3)) :
    Fin (Fintype.card M.Q + 3) × (Fin (Fintype.card M.K) → Fin (Fintype.card M.Γ + 3)) ×
      (Fin (Fintype.card M.K) → WLTime.Move) :=
  match M.code (stDec M s) (fun k => symDec M (r (tapeNum M k))) with
  | none => (if M.accept (stDec M s) then ⟨1, by omega⟩ else ⟨2, by omega⟩, r, fun _ => .stay)
  | some out => (⟨stCode M out.1, stCode_lt M out.1⟩,
      fun a => encSym M (out.2.1 ((tapeNum M).symm a)),
      fun a => moveOf (out.2.2 ((tapeNum M).symm a)))

theorem trans_none {s : Fin (Fintype.card M.Q + 3)}
    {r : Fin (Fintype.card M.K) → Fin (Fintype.card M.Γ + 3)}
    (h : M.code (stDec M s) (fun k => symDec M (r (tapeNum M k))) = none) :
    trans M s r =
      (if M.accept (stDec M s) then ⟨1, by omega⟩ else ⟨2, by omega⟩, r, fun _ => .stay) := by
  simp only [trans, h]

theorem trans_some {s : Fin (Fintype.card M.Q + 3)}
    {r : Fin (Fintype.card M.K) → Fin (Fintype.card M.Γ + 3)}
    {out : M.Q × (M.K → M.Γ) × (M.K → HeadMove)}
    (h : M.code (stDec M s) (fun k => symDec M (r (tapeNum M k))) = some out) :
    trans M s r = (⟨stCode M out.1, stCode_lt M out.1⟩,
      fun a => encSym M (out.2.1 ((tapeNum M).symm a)),
      fun a => moveOf (out.2.2 ((tapeNum M).symm a))) := by
  simp only [trans, h]

/-- **The WL machine of a host multi-tape machine.** -/
abbrev tm : WLTime.TM where
  tapes := Fintype.card M.K
  states := Fintype.card M.Q + 3
  symbols := Fintype.card M.Γ + 3
  tapes_pos := card_K_pos M
  states_ge := by omega
  symbols_ge := by omega
  transition := trans M

theorem tm_transition : (tm M).transition = trans M := rfl

/-! ### The simulation -/

/-- A WL configuration represents a host configuration: the state decodes to the host state and
is not a halting state, and every tape agrees with the host tape relative to the head. -/
structure Rel (C : (tm M).Config) (c : M.Cfg) : Prop where
  state : stDec M C.state = c.q
  live : ¬ (tm M).halted C
  tape : ∀ (a : Fin (Fintype.card M.K)) (z : ℤ),
    (C.tape a z : ℕ) = symCode M ((c.tapes ((tapeNum M).symm a)).nth (z - C.head a))

theorem step_live {T : WLTime.TM} {C : T.Config} (h : ¬ T.halted C) :
    T.step C = { state := (T.transition C.state (fun a => C.tape a (C.head a))).1
                 head := fun a => C.head a +
                   ((T.transition C.state (fun a => C.tape a (C.head a))).2.2 a).displacement
                 tape := fun a z => if z = C.head a then
                   (T.transition C.state (fun a => C.tape a (C.head a))).2.1 a else C.tape a z } := by
  simp only [WLTime.TM.step, ite_eq_right h]

theorem step_halted {T : WLTime.TM} {C : T.Config} (h : T.halted C) : T.step C = C := by
  simp only [WLTime.TM.step, ite_eq_left h]

theorem read_eq {C : (tm M).Config} {c : M.Cfg} (hR : Rel M C c) :
    (fun k => symDec M (((fun a => C.tape a (C.head a)) (tapeNum M k) : Fin _) : ℕ)) =
      fun k => (c.tapes k).head := by
  funext k
  have h := hR.tape (tapeNum M k) (C.head (tapeNum M k))
  rw [sub_self, Turing.Tape.nth_zero, Equiv.symm_apply_apply] at h
  simp only
  rw [h, symDec_code]

theorem init_rel (w : List Bool) : Rel M ((tm M).initial w) (M.init w) := by
  refine ⟨?_, ?_, ?_⟩
  · show stDec M 0 = M.initialState
    exact stDec_zero M
  · simp [WLTime.TM.halted, WLTime.TM.initial]
  · intro a z
    simp only [WLTime.TM.initial, sub_zero]
    by_cases ha : (a : ℕ) = 0
    · rw [tapeNum_symm_zero M a ha, FiniteMultiTapeMachine.init_inputTape, mk₁_nth]
      by_cases hz : 0 ≤ z ∧ z.toNat < w.length
      · rw [ite_eq_left ⟨ha, hz⟩, ite_eq_left hz.1, List.getI_eq_getElem _ (by simpa using hz.2),
          List.getElem_map, symCode_input, WLTime.TM.symbol, List.getD_eq_getElem _ _ hz.2]
        split <;> rfl
      · rw [ite_eq_right (fun h => hz h.2)]
        by_cases hz0 : 0 ≤ z
        · rw [ite_eq_left hz0, List.getI_eq_default _ (by simp; omega), symCode_default]
        · rw [ite_eq_right hz0, symCode_default]
    · rw [ite_eq_right (fun h => ha h.1), FiniteMultiTapeMachine.init_otherTape M w _
        (tapeNum_symm_ne M a ha), mk₁_nth]
      split
      · rw [List.getI_nil, symCode_default]
      · rw [symCode_default]

theorem rel_step {C : (tm M).Config} {c c' : M.Cfg} (hR : Rel M C c) (h : M.step c = some c') :
    Rel M ((tm M).step C) c' := by
  simp only [FiniteMultiTapeMachine.step, multiTapeStep, Option.map_eq_some_iff] at h
  obtain ⟨out, hout, rfl⟩ := h
  have hcode : M.code (stDec M C.state)
      (fun k => symDec M (((fun a => C.tape a (C.head a)) (tapeNum M k) : Fin _) : ℕ)) =
        some out := by
    rw [read_eq M hR, hR.state]
    exact hout
  have htr : (tm M).transition C.state (fun a => C.tape a (C.head a)) =
      (⟨stCode M out.1, stCode_lt M out.1⟩,
        fun a => encSym M (out.2.1 ((tapeNum M).symm a)),
        fun a => moveOf (out.2.2 ((tapeNum M).symm a))) :=
    trans_some M (s := C.state) (r := fun a => C.tape a (C.head a)) hcode
  rw [step_live hR.live, htr]
  refine ⟨?_, ?_, ?_⟩
  · exact stDec_code M out.1
  · show ¬ ((stCode M out.1 = 1) ∨ (stCode M out.1 = 2))
    unfold stCode
    omega
  · intro a z
    simp only [multiTapeUpdate]
    rw [sub_add_eq_sub_sub, apply_nth, Turing.Tape.write_nth]
    by_cases hz : z = C.head a
    · subst hz
      simp [encSym]
    · rw [ite_eq_right hz, ite_eq_right (sub_ne_zero.mpr hz)]
      exact hR.tape a z

theorem state_halt {C : (tm M).Config} {c : M.Cfg} (hR : Rel M C c) (h : M.step c = none) :
    (((tm M).step C).state : ℕ) = if M.accept c.q then 1 else 2 := by
  have h' := (multiTapeStep_eq_none_iff M.code c).mp h
  have hcode : M.code (stDec M C.state)
      (fun k => symDec M (((fun a => C.tape a (C.head a)) (tapeNum M k) : Fin _) : ℕ)) = none := by
    rw [read_eq M hR, hR.state]
    exact h'
  have htr := trans_none M (s := C.state) (r := fun a => C.tape a (C.head a)) hcode
  rw [step_live hR.live]
  show (((tm M).transition C.state (fun a => C.tape a (C.head a))).1 : ℕ) = _
  rw [tm_transition, htr, hR.state]
  split <;> rfl

theorem runSteps_succ {S : Type} (step : S → Option S) (n : ℕ) (x : Option S) :
    runSteps step (n + 1) x = (runSteps step n x).bind step := by
  simp only [runSteps, Function.iterate_succ_apply']

theorem runSteps_none {S : Type} (step : S → Option S) (n : ℕ) : runSteps step n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runSteps_succ, ih]; rfl

theorem runSteps_add {S : Type} (step : S → Option S) (m n : ℕ) (x : Option S) :
    runSteps step (m + n) x = runSteps step n (runSteps step m x) := by
  simp only [runSteps]
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem runSteps_prefix {S : Type} {step : S → Option S} {x : Option S} {k t : ℕ} {c : S}
    (h : runSteps step k x = some c) (ht : t ≤ k) : ∃ d, runSteps step t x = some d := by
  rcases hd : runSteps step t x with _ | d
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [runSteps_add, hd, runSteps_none] at h
    cases h
  · exact ⟨d, rfl⟩

theorem run_succ (w : List Bool) (t : ℕ) : (tm M).run w (t + 1) = (tm M).step ((tm M).run w t) := by
  simp only [WLTime.TM.run, Function.iterate_succ_apply']

/-- **The simulation**: the WL machine follows the host machine step by step. -/
theorem rel_run (w : List Bool) :
    ∀ (t : ℕ) (c : M.Cfg), runSteps M.step t (some (M.init w)) = some c →
      Rel M ((tm M).run w t) c := by
  intro t
  induction t with
  | zero =>
      intro c hc
      cases hc
      exact init_rel M w
  | succ t ih =>
      intro c hc
      rw [runSteps_succ] at hc
      rcases hd : runSteps M.step t (some (M.init w)) with _ | d
      · rw [hd] at hc
        cases hc
      · rw [hd] at hc
        rw [run_succ]
        exact rel_step M (ih d hd) hc

theorem run_stays (w : List Bool) {s : ℕ} (h : (tm M).halted ((tm M).run w s)) :
    ∀ m, (tm M).run w (s + m) = (tm M).run w s := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [← Nat.add_assoc, run_succ, ih, step_halted h]

/-- **A halting host run gives a halting WL run, one step longer, with the same answer.** -/
theorem haltsIn_tm {w : List Bool} {b : Bool} {T : ℕ} (h : MultiTapeHaltsIn M w b T) :
    (tm M).halts w ∧ (tm M).time w ≤ T + 1 ∧ ((tm M).accepts w ↔ b = true) := by
  obtain ⟨k, hk, c, hrun, hhalt, hout⟩ := h
  have hR := rel_run M w k c hrun
  have hst : (((tm M).run w (k + 1)).state : ℕ) = if M.accept c.q then 1 else 2 := by
    rw [run_succ]
    exact state_halt M hR hhalt
  have hhalted : (tm M).halted ((tm M).run w (k + 1)) := by
    show (((tm M).run w (k + 1)).state : ℕ) = 1 ∨ (((tm M).run w (k + 1)).state : ℕ) = 2
    rw [hst]
    split <;> simp
  have hhalts : (tm M).halts w := ⟨k + 1, hhalted⟩
  refine ⟨hhalts, ?_, ?_⟩
  · simp only [WLTime.TM.time, dite_eq_left hhalts]
    exact (Nat.find_min' hhalts hhalted).trans (by omega)
  · constructor
    · rintro ⟨t, ht⟩
      rcases Nat.lt_or_ge t (k + 1) with hlt | hge
      · obtain ⟨d, hd⟩ := runSteps_prefix hrun (show t ≤ k by omega)
        exact absurd (Or.inl ht) (rel_run M w t d hd).live
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hge
        rw [run_stays M w hhalted m, hst] at ht
        rw [← hout]
        split at ht
        · assumption
        · cases ht
    · intro hb
      refine ⟨k + 1, ?_⟩
      rw [hst, hout, ite_eq_left hb]

/-! ### The lower bound for host machines -/

/-- A host multi-tape machine decides `k`-WL equivalence on the inputs of `p` within time
`T n` on graphs with `n` vertices. -/
def MultiTapeDecides (M : FiniteMultiTapeMachine) (conv : WLTime.Convention) (k : ℕ)
    (p : WLTime.InputClass) (T : ℕ → ℕ) : Prop :=
  ∀ n (G H : WLTime.Graph n), p.contains G H →
    ∃ b, MultiTapeHaltsIn M (WLTime.encodePair G H) b (T n) ∧
      (b = true ↔ WLTime.Equivalent conv k G H)

theorem decides_tm {conv : WLTime.Convention} {k : ℕ} {p : WLTime.InputClass} {T : ℕ → ℕ}
    (h : MultiTapeDecides M conv k p T) : WLTime.Decides (.turing (tm M)) conv k p := by
  intro n G H hp
  obtain ⟨b, hb, hiff⟩ := h n G H hp
  obtain ⟨hh, -, hacc⟩ := haltsIn_tm M hb
  exact ⟨hh, hacc.trans hiff⟩

theorem worstTime_le {conv : WLTime.Convention} {k : ℕ} {p : WLTime.InputClass} {T : ℕ → ℕ}
    (h : MultiTapeDecides M conv k p T) (n : ℕ) :
    WLTime.worstTime (.turing (tm M)) p n ≤ T n + 1 := by
  unfold WLTime.worstTime
  refine Finset.sup_le fun pair _ => ?_
  split
  · next hp =>
      obtain ⟨b, hb, -⟩ := h n pair.1 pair.2 hp
      exact (haltsIn_tm M hb).2.1
  · exact Nat.zero_le _

theorem encodePair_length_succ_le {n : ℕ} (G H : WLTime.Graph n) :
    (WLTime.encodePair G H).length + 1 ≤ 3 * (n + 1) ^ 2 := by
  have hd : (Nat.digits 2 n).length ≤ n :=
    (Nat.digits_length_le_iff (by decide) n).mpr n.lt_two_pow_self
  have hbits {v : ℕ} (G : WLTime.Graph v) : (WLTime.matrixBits G).length = v ^ 2 := by
    simp [WLTime.matrixBits, List.length_flatten, Function.comp_def, pow_two]
  simp only [WLTime.encodePair, WLTime.encodeNat, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil, List.length_map, hbits]
  nlinarith

end WLBridge

open WLBridge

/-- **The Weisfeiler–Leman lower bound for host multi-tape machines.** -/
theorem WLTime.multiTape_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ (conv : WLTime.Convention) (p : WLTime.InputClass)
        (M : DepthThreeLowerBound.FiniteMultiTapeMachine) (T : ℕ → ℕ),
        MultiTapeDecides M conv k p T → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          (n : ℝ) ^ (c * (k : ℝ)) ≤ (T n : ℝ) + 1 := by
  obtain ⟨c, hc, k₀, hk⟩ := WLTime.unconditional_time_lower_bound
  refine ⟨c, hc, k₀, fun k hk' conv p M T hM => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hk k hk' conv p (.turing (tm M)) (decides_tm M hM)
  refine ⟨n₀, fun n hn => (hn₀ n hn).trans ?_⟩
  exact_mod_cast worstTime_le M hM n

/-- **No polynomial bound of fixed degree for all `k`**: with `c` and `k₀` as in the lower bound,
once `2a < c k`, no host multi-tape machine decides `k`-WL equivalence within time
`C (|x| + 1) ^ a` in the length of its input `x`. -/
theorem WLTime.multiTape_not_poly :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ (conv : WLTime.Convention) (p : WLTime.InputClass)
        (M : DepthThreeLowerBound.FiniteMultiTapeMachine) (C a : ℕ), (2 * a : ℝ) < c * k →
        ¬ ∀ n (G H : WLTime.Graph n), p.contains G H →
          ∃ b, DepthThreeLowerBound.MultiTapeHaltsIn M (WLTime.encodePair G H) b
              (C * ((WLTime.encodePair G H).length + 1) ^ a) ∧
            (b = true ↔ WLTime.Equivalent conv k G H) := by
  obtain ⟨c, hc, k₀, hk⟩ := WLTime.multiTape_lower_bound
  refine ⟨c, hc, k₀, fun k hk' conv p M C a hlt hdec => ?_⟩
  have hM : MultiTapeDecides M conv k p (fun n => C * (3 * (n + 1) ^ 2) ^ a) := by
    intro n G H hp
    obtain ⟨b, hb, hiff⟩ := hdec n G H hp
    exact ⟨b, DepthThreeLowerBound.MultiTapeHaltsIn.mono hb
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (encodePair_length_succ_le G H) a)), hiff⟩
  obtain ⟨n₀, hn₀⟩ := hk k hk' conv p M _ hM
  -- `n ^ (c k) ≤ C 3^a (n+1)^(2a) + 1 ≤ D n ^ (2a)` with `D = C 12^a + 1`, which fails for large `n`.
  set ε : ℝ := c * k - 2 * a with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set D : ℝ := (C : ℝ) * 12 ^ a + 1 with hD
  have hDpos : 0 < D := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (D ^ (1 / ε))
  set n := max (max n₀ N) 1 with hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_max_right _ _
  have hnpos : (0 : ℝ) < n := by linarith
  have hbound := hn₀ n (le_trans (le_max_left _ _) (le_max_left _ _))
  have hupper : ((C * (3 * (n + 1) ^ 2) ^ a : ℕ) : ℝ) + 1 ≤ D * (n : ℝ) ^ (2 * a) := by
    have h2n : ((n : ℝ) + 1) ≤ 2 * n := by linarith
    have hp : ((n : ℝ) + 1) ^ (2 * a) ≤ (2 * (n : ℝ)) ^ (2 * a) :=
      pow_le_pow_left₀ (by positivity) h2n _
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (2 * a) := one_le_pow₀ hn1
    have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    push_cast
    calc (C : ℝ) * (3 * ((n : ℝ) + 1) ^ 2) ^ a + 1
        = (C : ℝ) * 3 ^ a * ((n : ℝ) + 1) ^ (2 * a) + 1 := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ (C : ℝ) * 3 ^ a * (2 * (n : ℝ)) ^ (2 * a) + (n : ℝ) ^ (2 * a) := by gcongr
      _ = ((C : ℝ) * 12 ^ a + 1) * (n : ℝ) ^ (2 * a) := by
          rw [mul_pow, pow_mul, show ((2 : ℝ) ^ 2) = 4 by norm_num,
            show (12 : ℝ) ^ a = 3 ^ a * 4 ^ a by rw [← mul_pow]; norm_num]
          ring
  have hsplit : (n : ℝ) ^ (c * (k : ℝ)) = (n : ℝ) ^ ε * (n : ℝ) ^ (2 * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]
    congr 1
    rw [hε]
    push_cast
    ring
  have hlarge : D < (n : ℝ) ^ ε := by
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) (le_max_left _ _)
    have h1 : D = (D ^ (1 / ε)) ^ ε := by
      rw [← Real.rpow_mul hDpos.le, one_div_mul_cancel hεpos.ne', Real.rpow_one]
    rw [h1]
    exact Real.rpow_lt_rpow (by positivity) (lt_of_lt_of_le hN hNn) hεpos
  have hpow : (0 : ℝ) < (n : ℝ) ^ (2 * a) := by positivity
  have := hbound.trans hupper
  rw [hsplit] at this
  nlinarith
