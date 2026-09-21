/-
**Configurations of a space-bounded machine as words of a fixed width.**

`Start/QbfReach.lean` turns bounded reachability in a graph whose vertices are `m`-bit words into
a quantified Boolean formula, provided the edge relation of the graph is expressed by formulas on
blocks of variables.  To apply it to a machine one first has to *write a configuration as a word*.

This module does that, for the padded configurations of `Start/SpacePadded.lean`.  The width is
`cfgWidth M x s = q + (n + 1) + s + s`, and the word is read in four blocks: the control state and
the two head positions in unary, the work tape bit by bit.  Unary positions keep every constraint
of a transition local — a head moves by shifting a single `true` — which is what makes the step
formula of `Start/QbfMachine.lean` small; the width stays polynomial because a machine running in
polynomial space has `q`, `n` and `s` polynomial in the input.

Main definitions:

* `Complexity.Qbf.cfgWidth`, `Complexity.Qbf.cfgBit`, `Complexity.Qbf.cfgWord` — the width of a
  configuration word, its bits, and the word itself;
* `Complexity.Qbf.tapeOf` — the tape block of a block of an assignment;
* `Complexity.Qbf.WordStep` — the one-step relation of the machine, read on words.

Main results:

* `Complexity.Qbf.blockVal_eq_cfgWord_iff` — a block of an assignment carries the word of a
  configuration exactly when it carries its bits;
* `Complexity.Qbf.cfgWord_injective` — the encoding is faithful on configurations of width `s`;
* `Complexity.Qbf.wordStep_length` — a step of the word relation stays inside the width;
* `Complexity.Qbf.reachLe_wordStep_iff` — bounded reachability of words is bounded reachability
  of configurations.
-/

import Mathlib
import Start.SpacePadded
import Start.QbfReach

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

open Complexity.Space Complexity.Reach

variable {M : Machine} {x : List Bool} {s : ℕ}

/-! ### The encoding -/

/-- The width of the word encoding one configuration: the control state and the two head
positions in unary, and the work tape bit by bit. -/
def cfgWidth (M : Machine) (x : List Bool) (s : ℕ) : ℕ :=
  M.states + (x.length + 1) + s + s

/-- The bit at position `l` of the word of a configuration. -/
def cfgBit (M : Machine) (x : List Bool) (s : ℕ) (c : Config) (l : ℕ) : Bool :=
  if l < M.states then decide (l = c.state)
  else if l < M.states + (x.length + 1) then decide (l - M.states = c.inHead)
  else if l < M.states + (x.length + 1) + s then
    c.tape.getD (l - (M.states + (x.length + 1))) false
  else decide (l - (M.states + (x.length + 1) + s) = c.wHead)

/-- The word of a configuration. -/
def cfgWord (M : Machine) (x : List Bool) (s : ℕ) (c : Config) : List Bool :=
  (List.range (cfgWidth M x s)).map (cfgBit M x s c)

@[simp] theorem cfgWord_length (M : Machine) (x : List Bool) (s : ℕ) (c : Config) :
    (cfgWord M x s c).length = cfgWidth M x s := by simp [cfgWord]

theorem getD_cfgWord (M : Machine) (x : List Bool) (s : ℕ) (c : Config) {l : ℕ}
    (hl : l < cfgWidth M x s) : (cfgWord M x s c).getD l false = cfgBit M x s c l := by
  rw [List.getD_eq_getElem _ _ (by simpa using hl)]
  simp [cfgWord]

/-- A block of an assignment carries the word of a configuration exactly when it carries its
bits. -/
theorem blockVal_eq_cfgWord_iff (M : Machine) (x : List Bool) (s : ℕ) (c : Config)
    (σ : ℕ → Bool) (a : ℕ) :
    blockVal (cfgWidth M x s) σ a = cfgWord M x s c ↔
      ∀ l < cfgWidth M x s, σ (a * cfgWidth M x s + l) = cfgBit M x s c l := by
  constructor
  · intro h l hl
    have := congrArg (fun w : List Bool => w.getD l false) h
    rwa [blockVal_getD _ _ _ _ hl, getD_cfgWord M x s c hl] at this
  · intro h
    refine List.ext_getElem (by simp) ?_
    intro l h₁ h₂
    have hl : l < cfgWidth M x s := by simpa using h₁
    have := h l hl
    rwa [← blockVal_getD (cfgWidth M x s) σ a l hl, ← getD_cfgWord M x s c hl,
      List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂] at this

/-- The tape block of a block of an assignment: the `s` bits that a configuration word holds as
its work tape. -/
def tapeOf (M : Machine) (x : List Bool) (s : ℕ) (σ : ℕ → Bool) (a : ℕ) : List Bool :=
  (List.range s).map fun l => σ (a * cfgWidth M x s + (M.states + (x.length + 1) + l))

@[simp] theorem tapeOf_length (M : Machine) (x : List Bool) (s : ℕ) (σ : ℕ → Bool) (a : ℕ) :
    (tapeOf M x s σ a).length = s := by simp [tapeOf]

theorem getD_tapeOf (M : Machine) (x : List Bool) (s : ℕ) (σ : ℕ → Bool) (a : ℕ) {l : ℕ}
    (hl : l < s) :
    (tapeOf M x s σ a).getD l false =
      σ (a * cfgWidth M x s + (M.states + (x.length + 1) + l)) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hl)]
  simp [tapeOf]

/-- If a block carries the word of a configuration, its tape block is that configuration's
tape. -/
theorem tapeOf_eq_tape {c : Config} {σ : ℕ → Bool} {a : ℕ}
    (h : blockVal (cfgWidth M x s) σ a = cfgWord M x s c) (hc : c.tape.length = s) :
    tapeOf M x s σ a = c.tape := by
  have hpt := (blockVal_eq_cfgWord_iff M x s c σ a).1 h
  refine List.ext_getElem (by simp [hc]) ?_
  intro i h₁ h₂
  have hi : i < s := by simpa using h₁
  have hlt : M.states + (x.length + 1) + i < cfgWidth M x s := by
    simp only [cfgWidth]; omega
  have hn1 : ¬ (M.states + (x.length + 1) + i < M.states) := by omega
  have hn2 : ¬ (M.states + (x.length + 1) + i < M.states + (x.length + 1)) := by omega
  have hlt3 : M.states + (x.length + 1) + i < M.states + (x.length + 1) + s := by omega
  have hbit : cfgBit M x s c (M.states + (x.length + 1) + i) = c.tape.getD i false := by
    simp [cfgBit, hn1, hn2, hlt3]
  have hval := hpt _ hlt
  rw [hbit] at hval
  rw [← getD_tapeOf M x s σ a hi] at hval
  rwa [List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂] at hval

/-! ### The encoding is faithful -/

/-- The encoding is injective on configurations of width `s` inside the bound. -/
theorem cfgWord_injective {c c' : Config} (hc : Fits M x s c) (hc' : Fits M x s c')
    (h : cfgWord M x s c = cfgWord M x s c') : c = c' := by
  have hbit : ∀ l < cfgWidth M x s, cfgBit M x s c l = cfgBit M x s c' l := by
    intro l hl
    rw [← getD_cfgWord M x s c hl, ← getD_cfgWord M x s c' hl, h]
  have hstate : c.state = c'.state := by
    have h₁ := hbit c.state (by have := hc.state; simp [cfgWidth]; omega)
    have h₂ : cfgBit M x s c c.state = true := by simp [cfgBit, hc.state]
    rw [h₂] at h₁
    have h₃ : cfgBit M x s c' c.state = decide (c.state = c'.state) := by
      simp [cfgBit, hc.state]
    rw [h₃] at h₁
    simpa using h₁.symm
  have hin : c.inHead = c'.inHead := by
    have hlt : M.states + c.inHead < cfgWidth M x s := by
      have := hc.inHead; have := hc.wHead; simp [cfgWidth]; omega
    have h₁ := hbit (M.states + c.inHead) hlt
    have hnot : ¬ (M.states + c.inHead < M.states) := by omega
    have hlt2 : M.states + c.inHead < M.states + (x.length + 1) := by
      have := hc.inHead; omega
    have h₂ : cfgBit M x s c (M.states + c.inHead) = true := by
      simp [cfgBit, hnot, hlt2]
    have h₃ : cfgBit M x s c' (M.states + c.inHead) = decide (c.inHead = c'.inHead) := by
      simp [cfgBit, hnot, hlt2]
    rw [h₂, h₃] at h₁
    simpa using h₁.symm
  have hhead : c.wHead = c'.wHead := by
    have hlt : M.states + (x.length + 1) + s + c.wHead < cfgWidth M x s := by
      have := hc.wHead; simp [cfgWidth]; omega
    have h₁ := hbit _ hlt
    have hn1 : ¬ (M.states + (x.length + 1) + s + c.wHead < M.states) := by omega
    have hn2 : ¬ (M.states + (x.length + 1) + s + c.wHead < M.states + (x.length + 1)) := by omega
    have hn3 : ¬ (M.states + (x.length + 1) + s + c.wHead <
        M.states + (x.length + 1) + s) := by omega
    have h₂ : cfgBit M x s c (M.states + (x.length + 1) + s + c.wHead) = true := by
      simp [cfgBit, hn1, hn2, hn3]
    have h₃ : cfgBit M x s c' (M.states + (x.length + 1) + s + c.wHead) =
        decide (c.wHead = c'.wHead) := by
      simp [cfgBit, hn1, hn2, hn3]
    rw [h₂, h₃] at h₁
    simpa using h₁.symm
  have htape : c.tape = c'.tape := by
    refine List.ext_getElem (by rw [hc.tape, hc'.tape]) ?_
    intro i h₁ h₂
    have hi : i < s := by rw [hc.tape] at h₁; exact h₁
    have hlt : M.states + (x.length + 1) + i < cfgWidth M x s := by simp [cfgWidth]; omega
    have hne := hbit _ hlt
    have hn1 : ¬ (M.states + (x.length + 1) + i < M.states) := by omega
    have hn2 : ¬ (M.states + (x.length + 1) + i < M.states + (x.length + 1)) := by omega
    have hlt3 : M.states + (x.length + 1) + i < M.states + (x.length + 1) + s := by omega
    have e₁ : cfgBit M x s c (M.states + (x.length + 1) + i) = c.tape.getD i false := by
      simp [cfgBit, hn1, hn2, hlt3]
    have e₂ : cfgBit M x s c' (M.states + (x.length + 1) + i) = c'.tape.getD i false := by
      simp [cfgBit, hn1, hn2, hlt3]
    rw [e₁, e₂] at hne
    rwa [List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂] at hne
  cases c; cases c'
  simp_all

/-! ### The step relation on words -/

/-- The one-step relation of the machine, read on configuration words. -/
def WordStep (M : Machine) (x : List Bool) (s : ℕ) (u v : List Bool) : Prop :=
  ∃ c c' : Config, u = cfgWord M x s c ∧ v = cfgWord M x s c' ∧ padStep M x s c c'

theorem wordStep_length {u v : List Bool} (h : WordStep M x s u v) :
    u.length = cfgWidth M x s ∧ v.length = cfgWidth M x s := by
  obtain ⟨c, c', rfl, rfl, -⟩ := h
  exact ⟨cfgWord_length _ _ _ _, cfgWord_length _ _ _ _⟩

/-- A step of the word relation between words of configurations is a step of the padded graph. -/
theorem padStep_of_wordStep {c c' : Config} (hc : Fits M x s c) (hc' : Fits M x s c')
    (h : WordStep M x s (cfgWord M x s c) (cfgWord M x s c')) : padStep M x s c c' := by
  obtain ⟨d, d', hd, hd', hstep⟩ := h
  have h₁ : c = d := cfgWord_injective hc hstep.1 hd
  have h₂ : c' = d' := cfgWord_injective hc' hstep.2.1 hd'
  subst h₁; subst h₂
  exact hstep

/-- Walks of the word relation out of the word of a configuration are walks of the padded
graph. -/
theorem steps_wordStep_iff {c : Config} (hc : Fits M x s c) :
    ∀ (n : ℕ) (c' : Config), Fits M x s c' →
      (Reach.steps (WordStep M x s) n (cfgWord M x s c) (cfgWord M x s c') ↔
        Reach.steps (padStep M x s) n c c') := by
  intro n
  induction n with
  | zero =>
      intro c' hc'
      constructor
      · intro h
        exact cfgWord_injective hc hc' h
      · rintro rfl; rfl
  | succ n ih =>
      intro c' hc'
      constructor
      · rintro ⟨w, hw, hstep⟩
        obtain ⟨d, d', hd, hd', hd''⟩ := hstep
        have hdw : w = cfgWord M x s d := hd
        subst hdw
        have h₁ : c' = d' := cfgWord_injective hc' hd''.2.1 hd'
        subst h₁
        exact ⟨d, (ih d hd''.1).1 hw, hd''⟩
      · rintro ⟨d, hd, hstep⟩
        exact ⟨cfgWord M x s d, (ih d hstep.1).2 hd, ⟨d, c', rfl, rfl, hstep⟩⟩

/-- Bounded reachability of words is bounded reachability of configurations. -/
theorem reachLe_wordStep_iff {c c' : Config} (hc : Fits M x s c) (hc' : Fits M x s c') (k : ℕ) :
    Reach.reachLe (WordStep M x s) k (cfgWord M x s c) (cfgWord M x s c') ↔
      Reach.reachLe (padStep M x s) k c c' := by
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, (steps_wordStep_iff hc n c' hc').1 h⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, (steps_wordStep_iff hc n c' hc').2 h⟩

end Complexity.Qbf
