/-
**Bridge: solenoidal machines and recorders are host multi-tape machines** — milestone M31
(`M31-BRIDGE-SOLENOIDAL`).

`Start/Solenoidal*.lean` (absorbed) work with single-tape machines `Solenoidal.Machine` over
`ℤ`-indexed tapes and build a reversible *recorder* whose terminal configurations are reached
exactly when the machine halts (`Solenoidal.Recorder.halting_iff`).  The host has multi-tape
machines over Mathlib's `Turing.Tape` (`DepthThreeLowerBound.FiniteMultiTapeMachine`), whose
polynomial-time deciders are in Cobham's class (`Complexity.MultiTapeCobham.inP_of_multiTapeHaltsIn`)
and which run the WL lower bound (`WLTime.multiTape_lower_bound`).  This module compiles a
solenoidal machine, with two non-blank symbols chosen for the input bits, into a one-tape host
machine, step for step.

* `Solenoidal.Machine.toHost` — the host machine: one tape, the same symbols (the blank exchanged
  with the host's default symbol by `swapBlank`), the same states, halting exactly at the halting
  states;
* `Solenoidal.Machine.rel_run` — **the simulation**: until the machine halts, the host run after
  `t` steps represents the configuration after `t` steps;
* **`Solenoidal.Machine.halts_iff_host`** — the machine halts on the encoding of a bit string
  iff the host machine halts on it, within the same number of steps;
* **`Solenoidal.Recorder.terminal_iff_host`** — hence the recorder reaches a terminal
  configuration iff the host machine halts.
-/

import Start.SolenoidalHalting
import Start.DepthThreeMultiTapeMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Solenoidal

open DepthThreeLowerBound

/-- Two distinct non-blank symbols, for the input bits. -/
structure BitSymbols (M : Machine) where
  s₀ : M.Symbol
  s₁ : M.Symbol
  ne : s₀ ≠ s₁
  ne₀ : s₀ ≠ M.blank
  ne₁ : s₁ ≠ M.blank

namespace BitSymbols

variable {M : Machine} (S : BitSymbols M)

/-- The symbol of a bit. -/
def sym (b : Bool) : M.Symbol := if b then S.s₁ else S.s₀

theorem sym_injective : Function.Injective S.sym := by
  intro a b h
  cases a <;> cases b <;> simp [sym] at h ⊢
  · exact S.ne h
  · exact S.ne h.symm

theorem sym_ne_blank (b : Bool) : S.sym b ≠ M.blank := by
  cases b
  · exact S.ne₀
  · exact S.ne₁

end BitSymbols

namespace Machine

variable (M : Machine) (S : BitSymbols M)

/-- A solenoidal move as a host head move. -/
def headMove : Move → HeadMove
  | .left => .left
  | .stay => .stay
  | .right => .right

/-- The host's default symbol is `0`; this involution exchanges it with the blank. -/
def swapBlank : M.Symbol ≃ M.Symbol := Equiv.swap default M.blank

theorem swapBlank_blank : swapBlank M M.blank = default := Equiv.swap_apply_right _ _

theorem swapBlank_symm_default : (swapBlank M).symm default = M.blank := by
  simp [swapBlank, Equiv.swap_apply_left]

/-- **The host machine of a solenoidal machine**; a symbol `s` is written as `swapBlank s`. -/
abbrev toHost : FiniteMultiTapeMachine where
  K := Unit
  inputTape := ()
  Γ := M.Symbol
  Q := M.State
  initialState := M.initial
  inputSymbol := fun b => swapBlank M (S.sym b)
  input_injective := (swapBlank M).injective.comp S.sym_injective
  input_ne_blank := fun b h => S.sym_ne_blank b (by
    have := congrArg (swapBlank M).symm h
    rwa [Equiv.symm_apply_apply, swapBlank_symm_default] at this)
  code := fun q r => if M.halt q then none else
    some ((M.table q ((swapBlank M).symm (r ()))).1,
      fun _ => swapBlank M (M.table q ((swapBlank M).symm (r ()))).2.1,
      fun _ => headMove (M.table q ((swapBlank M).symm (r ()))).2.2)
  accept := M.halt

theorem apply_nth {Γ : Type} [Inhabited Γ] (m : Move) (T : Turing.Tape Γ) (i : ℤ) :
    ((headMove m).apply T).nth (i - m.displacement) = T.nth i := by
  cases m with
  | left =>
      simp only [headMove, HeadMove.apply_left, Turing.Tape.move_left_nth, Move.displacement]
      congr 1
      ring
  | stay => simp [headMove]
  | right =>
      simp only [headMove, HeadMove.apply_right, Turing.Tape.move_right_nth, Move.displacement]
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

theorem getI_eq {Γ : Type} [Inhabited Γ] : ∀ (l : List Γ) (n : ℕ), l.getI n = l[n]?.getD default
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | _ :: l, n + 1 => by simp [getI_eq l n]

/-- A solenoidal configuration represents a host configuration: same state, and the host tape
read relative to its head is the solenoidal tape relative to the head position. -/
def Rel (C : M.Config) (c : (toHost M S).Cfg) : Prop :=
  c.q = C.state ∧ ∀ z : ℤ, (c.tapes ()).nth (z - C.head) = swapBlank M (C.tape z)

theorem init_rel (w : List Bool) : Rel M S (M.initialConfig (w.map S.sym)) ((toHost M S).init w) := by
  refine ⟨rfl, fun z => ?_⟩
  rw [FiniteMultiTapeMachine.init_inputTape]
  simp only [initialConfig, inputTape, sub_zero]
  rw [mk₁_nth, getI_eq]
  split
  · rw [List.getElem?_map, List.getElem?_map]
    cases (w[z.toNat]?) with
    | none => exact (swapBlank_blank M).symm
    | some b => rfl
  · exact (swapBlank_blank M).symm

theorem rel_step {C : M.Config} {c : (toHost M S).Cfg} (hR : Rel M S C c)
    (hh : M.halt C.state = false) :
    ∃ c', (toHost M S).step c = some c' ∧ Rel M S (M.step C) c' := by
  have hhead : (c.tapes ()).head = swapBlank M (C.tape C.head) := by
    have := hR.2 C.head
    rwa [sub_self, Turing.Tape.nth_zero] at this
  have hcode : (toHost M S).code c.q (fun k => (c.tapes k).head) =
      some ((M.table C.state (C.tape C.head)).1,
        fun _ => swapBlank M (M.table C.state (C.tape C.head)).2.1,
        fun _ => headMove (M.table C.state (C.tape C.head)).2.2) := by
    simp only [toHost, hR.1, hh, hhead, Bool.false_eq_true, ↓reduceIte, Equiv.symm_apply_apply]
  refine ⟨_, multiTapeStep_eq_some hcode, ?_⟩
  simp only [step, hh, Bool.false_eq_true, ite_false]
  refine ⟨rfl, fun z => ?_⟩
  simp only [multiTapeUpdate]
  rw [sub_add_eq_sub_sub, apply_nth, Turing.Tape.write_nth]
  by_cases hz : z = C.head
  · subst hz
    simp
  · rw [ite_eq_right (sub_ne_zero.mpr hz), Function.update_of_ne hz]
    exact hR.2 z

theorem runSteps_succ {σ : Type} (step : σ → Option σ) (n : ℕ) (x : Option σ) :
    runSteps step (n + 1) x = (runSteps step n x).bind step := by
  simp only [runSteps, Function.iterate_succ_apply']

/-- **The simulation**: as long as the solenoidal machine has not halted, the host run follows
it step for step. -/
theorem rel_run (w : List Bool) :
    ∀ t, (∀ s < t, M.halt (M.run (w.map S.sym) s).state = false) →
      ∃ c, runSteps (toHost M S).step t (some ((toHost M S).init w)) = some c ∧
        Rel M S (M.run (w.map S.sym) t) c := by
  intro t
  induction t with
  | zero => intro _; exact ⟨_, rfl, init_rel M S w⟩
  | succ t ih =>
      intro hbefore
      obtain ⟨c, hc, hR⟩ := ih fun s hs => hbefore s (by omega)
      obtain ⟨c', hc', hR'⟩ := rel_step M S hR (hbefore t (by omega))
      refine ⟨c', ?_, ?_⟩
      · rw [runSteps_succ, hc]
        exact hc'
      · rw [run_succ]
        exact hR'

theorem step_none_iff {C : M.Config} {c : (toHost M S).Cfg} (hR : Rel M S C c) :
    (toHost M S).step c = none ↔ M.halt C.state = true := by
  rw [multiTapeStep_eq_none_iff]
  simp only [toHost, hR.1]
  cases M.halt C.state <;> simp

/-- **A solenoidal machine halts on the encoding of a bit string iff its host machine halts on
the string**, within the same number of steps and accepting. -/
theorem halts_iff_host (w : List Bool) :
    M.Halts (w.map S.sym) ↔ ∃ T, MultiTapeHaltsIn (toHost M S) w true T := by
  classical
  constructor
  · intro h
    let n := Nat.find h
    have hbefore : ∀ s < n, M.halt (M.run (w.map S.sym) s).state = false := by
      intro s hs
      cases heq : M.halt (M.run (w.map S.sym) s).state with
      | false => rfl
      | true => exact absurd heq (Nat.find_min h hs)
    obtain ⟨c, hc, hR⟩ := rel_run M S w n hbefore
    have hn : M.halt (M.run (w.map S.sym) n).state = true := Nat.find_spec h
    refine ⟨n, n, le_rfl, c, hc, (step_none_iff M S hR).2 hn, ?_⟩
    show M.halt c.q = true
    rw [hR.1]
    exact hn
  · rintro ⟨T, k, -, c, hc, hnone, -⟩
    by_contra hn
    have hall : ∀ s, M.halt (M.run (w.map S.sym) s).state = false := by
      intro s
      cases heq : M.halt (M.run (w.map S.sym) s).state with
      | false => rfl
      | true => exact absurd ⟨s, heq⟩ hn
    obtain ⟨c', hc', hR⟩ := rel_run M S w k fun s _ => hall s
    rw [hc] at hc'
    cases hc'
    have := (step_none_iff M S hR).1 hnone
    rw [hall k] at this
    cases this

end Machine

namespace Recorder

/-- **The recorder of a solenoidal machine reaches a terminal configuration iff the host
machine halts.** -/
theorem terminal_iff_host (M : Machine) (S : BitSymbols M) (w : List Bool) (r₀ : ℤ)
    (hr₀ : 2 ≤ r₀) :
    (∃ (N : ℕ) (c : Config M), Steps N (initial (w.map S.sym) r₀) c ∧ Terminal c) ↔
      ∃ T, MultiTapeHaltsIn (Machine.toHost M S) w true T :=
  (halting_iff (w.map S.sym) r₀ hr₀).trans (Machine.halts_iff_host M S w)

end Recorder

end Solenoidal
