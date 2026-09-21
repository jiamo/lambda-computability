/-
**Configurations of a space-bounded machine, padded to a fixed width.**

The configurations of `Start/SpaceMachine.lean` carry a work tape of *variable* length: the tape
grows as the machine writes, so two configurations with the same contents but tapes of different
lengths are different configurations.  That is convenient for the machine, and inconvenient for
anything that wants to write a configuration as a word of a *fixed* number of bits — which is
exactly what a reduction to a Boolean formula has to do.

This module normalises the tape.  For a machine that runs in space `s` on the input `x`, a
configuration is padded to the width `s` (`Complexity.Space.pad`), the padded configurations
inside the bound are the ones that `Complexity.Space.Fits` recognises, and
`Complexity.Space.padStep` is the one-step relation restricted to them.  Padding is a
bisimulation: a run of the machine is a walk of `padStep` and conversely, so acceptance is
reachability in the padded graph — and, because the padded graph is finite, reachability within
`2 ^ savitchDepth` steps.

Main definitions:

* `Complexity.Space.padTape`, `Complexity.Space.pad` — the first `s` cells of a tape, and a
  configuration with its tape padded to that width;
* `Complexity.Space.Fits` — a configuration of width exactly `s` inside the bound;
* `Complexity.Space.padStep` — the one-step relation between such configurations.

Main results:

* `Complexity.Space.padTape_writeAt` — padding commutes with writing inside the bound;
* `Complexity.Space.padStep_pad`, `Complexity.Space.exists_step_of_padStep` — padding is a
  bisimulation;
* `Complexity.Space.accepts_iff_padStep` — acceptance is reachability in the padded graph;
* `Complexity.Space.accepts_iff_reachLe_padStep` — and reachability there within
  `2 ^ savitchDepth M x s` steps, which is the form the midpoint recursion needs.
-/

import Mathlib
import Start.SavitchSpace

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

open Complexity.Reach

variable {M : Machine} {x : List Bool} {s : ℕ}

/-! ### Padding a work tape -/

/-- The first `s` cells of a work tape, blanks beyond its used part. -/
def padTape (s : ℕ) (l : List Bool) : List Bool := (List.range s).map fun i => l.getD i false

@[simp] theorem padTape_length (s : ℕ) (l : List Bool) : (padTape s l).length = s := by
  simp [padTape]

theorem getD_padTape (s : ℕ) (l : List Bool) {i : ℕ} (hi : i < s) :
    (padTape s l).getD i false = l.getD i false := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [padTape]

theorem padTape_eq_self {s : ℕ} {l : List Bool} (h : l.length = s) : padTape s l = l := by
  refine List.ext_getElem (by simp [h]) ?_
  intro i h₁ h₂
  have hi : i < s := by simpa [padTape] using h₁
  have := getD_padTape s l hi
  rwa [List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂] at this

/-- Writing at a position other than the one read leaves that cell alone. -/
theorem getD_writeAt_of_ne (l : List Bool) (i j : ℕ) (b : Bool) (h : j ≠ i) :
    (writeAt l i b).getD j false = l.getD j false := by
  induction l generalizing i j with
  | nil =>
      induction i generalizing j with
      | zero =>
          cases j with
          | zero => exact absurd rfl h
          | succ j => simp [writeAt]
      | succ i ih =>
          cases j with
          | zero => simp [writeAt]
          | succ j =>
              have := ih (j := j) (by omega)
              simpa [writeAt] using this
  | cons a t ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exact absurd rfl h
          | succ j => simp [writeAt]
      | succ i =>
          cases j with
          | zero => simp [writeAt]
          | succ j =>
              have := ih (i := i) (j := j) (by omega)
              simpa [writeAt] using this

/-- Padding commutes with writing, as long as the cell written is inside the width. -/
theorem padTape_writeAt (s : ℕ) (l : List Bool) (i : ℕ) (b : Bool) (hi : i < s) :
    padTape s (writeAt l i b) = writeAt (padTape s l) i b := by
  have hlen : (writeAt (padTape s l) i b).length = s := by
    simp only [writeAt_length, padTape_length]
    omega
  refine List.ext_getElem (by simp [hlen]) ?_
  intro j h₁ h₂
  have hj : j < s := by simpa [padTape] using h₁
  have hl : (padTape s (writeAt l i b)).getD j false
      = (writeAt (padTape s l) i b).getD j false := by
    rcases eq_or_ne j i with rfl | hne
    · rw [getD_padTape s _ hj, getD_writeAt_self, getD_writeAt_self]
    · rw [getD_padTape s _ hj, getD_writeAt_of_ne _ _ _ _ hne, getD_writeAt_of_ne _ _ _ _ hne,
        getD_padTape s l hj]
  rwa [List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂] at hl

/-! ### Padded configurations -/

/-- A configuration with its work tape padded to the width `s`. -/
def pad (s : ℕ) (c : Config) : Config := { c with tape := padTape s c.tape }

@[simp] theorem pad_state (s : ℕ) (c : Config) : (pad s c).state = c.state := rfl
@[simp] theorem pad_inHead (s : ℕ) (c : Config) : (pad s c).inHead = c.inHead := rfl
@[simp] theorem pad_wHead (s : ℕ) (c : Config) : (pad s c).wHead = c.wHead := rfl
@[simp] theorem pad_tape (s : ℕ) (c : Config) : (pad s c).tape = padTape s c.tape := rfl

/-- A configuration of a machine `M` on the input `x` written at the exact width `s`: the state is
one of the machine's, the input head is on the input or the end marker, the work tape has exactly
`s` cells and the work head stands on one of them. -/
structure Fits (M : Machine) (x : List Bool) (s : ℕ) (c : Config) : Prop where
  /-- The control state is one of the machine's. -/
  state : c.state < M.states
  /-- The input head is on the input or on its end marker. -/
  inHead : c.inHead ≤ x.length
  /-- The work tape has exactly `s` cells. -/
  tape : c.tape.length = s
  /-- The work head stands on one of them. -/
  wHead : c.wHead < s

theorem Fits.space {c : Config} (h : Fits M x s c) : c.space ≤ s := by
  have h₁ := h.tape
  have h₂ := h.wHead
  simp only [Config.space]
  omega

/-- A configuration inside the bound, padded, fits. -/
theorem fits_pad {c : Config} (hst : c.state < M.states)
    (hin : c.inHead ≤ x.length) (hsp : c.space ≤ s) : Fits M x s (pad s c) := by
  refine ⟨hst, hin, by simp, ?_⟩
  have : c.wHead + 1 ≤ s := le_trans (le_max_right _ _) hsp
  simpa using (by omega : c.wHead < s)

/-- The head of a padded configuration reads the same bit as the original one. -/
theorem pad_read {c : Config} (hw : c.wHead < s) :
    (pad s c).tape.getD (pad s c).wHead false = c.tape.getD c.wHead false :=
  getD_padTape s c.tape hw

/-- The one-step relation between configurations of width `s` inside the bound. -/
def padStep (M : Machine) (x : List Bool) (s : ℕ) (c c' : Config) : Prop :=
  Fits M x s c ∧ Fits M x s c' ∧ M.Step x c c'

/-! ### Padding is a bisimulation -/

/-- A step of the machine between configurations inside the bound is a step of the padded
graph. -/
theorem padStep_pad {c d : Config}
    (hcs : c.state < M.states) (hci : c.inHead ≤ x.length) (hcp : c.space ≤ s)
    (hds : d.state < M.states) (hdi : d.inHead ≤ x.length) (hdp : d.space ≤ s)
    (h : M.Step x c d) : padStep M x s (pad s c) (pad s d) := by
  refine ⟨fits_pad hcs hci hcp, fits_pad hds hdi hdp, ?_⟩
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  have hw : c.wHead < s := by
    have : c.wHead + 1 ≤ s := le_trans (le_max_right _ _) hcp
    omega
  refine List.mem_map.2 ⟨t, ?_, ?_⟩
  · rw [pad_state, pad_inHead, pad_read hw]
    exact ht
  · simp only [pad, Config.mk.injEq, true_and]
    exact ⟨(padTape_writeAt s c.tape c.wHead t.2.1 hw).symm, trivial⟩

/-- Conversely a step out of a padded configuration comes from a step of the machine. -/
theorem exists_step_of_padStep {c : Config} {e : Config} (hcw : c.wHead < s)
    (h : M.Step x (pad s c) e) :
    ∃ d : Config, M.Step x c d ∧ pad s d = e := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  rw [pad_state, pad_inHead, pad_read hcw] at ht
  refine ⟨{ state := t.1
            inHead := moveIn x.length c.inHead t.2.2.1
            tape := writeAt c.tape c.wHead t.2.1
            wHead := moveWork c.wHead t.2.2.2 }, List.mem_map.2 ⟨t, ht, rfl⟩, ?_⟩
  simp only [pad, Config.mk.injEq, true_and]
  exact ⟨padTape_writeAt s c.tape c.wHead t.2.1 hcw, trivial⟩

/-! ### Runs -/

/-- A run of the machine is a walk in the padded graph. -/
theorem steps_padStep_of_steps (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s) :
    ∀ (n : ℕ) (c : Config), Reach.steps (M.Step x) n init c →
      Reach.steps (padStep M x s) n (pad s init) (pad s c) := by
  intro n
  induction n with
  | zero => rintro c rfl; rfl
  | succ n ih =>
      rintro c ⟨d, hd, hstep⟩
      have hc : Reach.steps (M.Step x) (n + 1) init c := ⟨d, hd, hstep⟩
      refine ⟨pad s d, ih d hd, ?_⟩
      exact padStep_pad (Machine.state_lt_of_steps hwf hd) (Machine.inHead_le_of_steps hd)
        (hsp n d hd) (Machine.state_lt_of_steps hwf hc)
        (Machine.inHead_le_of_steps hc) (hsp (n + 1) c hc) hstep

/-- Conversely a walk in the padded graph out of the padded initial configuration is a run of the
machine. -/
theorem exists_steps_of_steps_padStep :
    ∀ (n : ℕ) (e : Config), Reach.steps (padStep M x s) n (pad s init) e →
      ∃ c : Config, Reach.steps (M.Step x) n init c ∧ pad s c = e := by
  intro n
  induction n with
  | zero => rintro e rfl; exact ⟨init, rfl, rfl⟩
  | succ n ih =>
      rintro e ⟨d, hd, hstep⟩
      obtain ⟨c, hc, rfl⟩ := ih d hd
      obtain ⟨c', hc', rfl⟩ :=
        exists_step_of_padStep (M := M) (x := x) (s := s) (c := c) (e := e)
          (hstep.1).wHead hstep.2.2
      exact ⟨c', ⟨c, hc, hc'⟩, rfl⟩

/-- Every configuration a walk of the padded graph reaches fits. -/
theorem fits_of_steps_padStep {c e : Config} (hc : Fits M x s c) :
    ∀ (n : ℕ), Reach.steps (padStep M x s) n c e → Fits M x s e := by
  intro n
  induction n generalizing e with
  | zero => rintro rfl; exact hc
  | succ n ih =>
      rintro ⟨d, -, hstep⟩
      exact hstep.2.1

/-- **Acceptance is reachability in the padded graph.** -/
theorem accepts_iff_padStep (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s) :
    M.Accepts x ↔ ∃ (n : ℕ) (e : Config), Reach.steps (padStep M x s) n (pad s init) e ∧
      M.accept e.state = true := by
  constructor
  · rintro ⟨n, c, hc, hacc⟩
    exact ⟨n, pad s c, steps_padStep_of_steps hwf hsp n c hc, hacc⟩
  · rintro ⟨n, e, he, hacc⟩
    obtain ⟨c, hc, rfl⟩ := exists_steps_of_steps_padStep (M := M) (x := x) (s := s) n e he
    exact ⟨n, c, hc, hacc⟩

/-- **Acceptance is reachability in the padded graph within `2 ^ savitchDepth` steps**: the padded
graph is finite, so an accepting walk can be taken shorter than the number of configurations. -/
theorem accepts_iff_reachLe_padStep (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s) :
    M.Accepts x ↔ ∃ e : Config, M.accept e.state = true ∧
      Reach.reachLe (padStep M x s) (savitchDepth M x s) (pad s init) e := by
  constructor
  · intro h
    obtain ⟨n, c, hn, hc, hacc⟩ := exists_short_accepting_run hwf hsp h
    refine ⟨pad s c, hacc, n, ?_, steps_padStep_of_steps hwf hsp n c hc⟩
    exact le_trans (le_of_lt hn) (Nat.le_pow_clog (by norm_num) _)
  · rintro ⟨e, hacc, n, -, hn⟩
    exact (accepts_iff_padStep hwf hsp).2 ⟨n, e, hn, hacc⟩

end Complexity.Space
