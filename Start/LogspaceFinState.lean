import Start.LogspaceDeterministic

/-!
# Machines of `ExactDerandomization` with control states in an arbitrary finite type

This module is this library's own (task `M27-SPACE-MODEL-COMPILE`).  The machines of
`Start/LogspaceDeterministic.lean` (absorbed from github.com/openai/math, see `NOTICE`) number
their control states `Fin (q + 1)`.  Compilers are much easier to write with structured control
states, so this module defines machines whose control states form an arbitrary finite type `σ`
with a distinguished initial state, and transports them along `Fintype.equivFin`:

* `ExactDerandomization.FMachine σ w h` and its configurations, step and run;
* `ExactDerandomization.FMachine.toMachine` — the numbered machine;
* `toMachine_run` — runs correspond, configuration by configuration (only the name of the
  control state changes);
* `toMachine_spaceThrough`, `toMachine_deterministic`, `toMachine_output_run` — space, determinism
  and outputs are preserved.
-/

set_option autoImplicit false

namespace ExactDerandomization

/-- An action of a machine with control states in `σ`. -/
structure FAction (σ : Type) (w h : ℕ) where
  nextState : σ
  write : Fin w → Bool
  workMove : Fin w → Direction
  inputMove : Fin h → Direction

/-- A machine with `w` two-sided work tapes, `h` read-only input heads and control states in `σ`. -/
structure FMachine (σ : Type) (w h : ℕ) where
  initialState : σ
  output : σ → Option Bool
  transition : σ → (Fin h → InputSymbol) → (Fin w → Bool) → Bool → FAction σ w h

/-- A configuration of an `FMachine`. -/
structure FConfig (σ : Type) (w h n : ℕ) where
  state : σ
  inputPos : Fin h → Fin (n + 2)
  workPos : Fin w → ℤ
  work : Fin w → ℤ → Bool

namespace FMachine

variable {σ : Type} {w h : ℕ}

def initial (M : FMachine σ w h) (n : ℕ) : FConfig σ w h n where
  state := M.initialState
  inputPos := fun _ => ⟨0, by omega⟩
  workPos := fun _ => 0
  work := fun _ _ => false

def step (M : FMachine σ w h) (x : Word) (b : Bool)
    (c : FConfig σ w h x.length) : FConfig σ w h x.length :=
  match M.output c.state with
  | some _ => c
  | none =>
    let a := M.transition c.state (fun j => readInput x (c.inputPos j))
      (fun k => c.work k (c.workPos k)) b
    { state := a.nextState
      inputPos := fun j => (a.inputMove j).moveInput (c.inputPos j)
      workPos := fun k => (a.workMove k).move (c.workPos k)
      work := fun k => Function.update (c.work k) (c.workPos k) (a.write k) }

def run (M : FMachine σ w h) (x : Word) (coins : CoinTape) : ℕ → FConfig σ w h x.length
  | 0 => M.initial x.length
  | t + 1 => M.step x (coins t) (M.run x coins t)

def Deterministic (M : FMachine σ w h) : Prop :=
  ∀ s i v, M.transition s i v false = M.transition s i v true

variable [Fintype σ] [DecidableEq σ]

/-- The numbering of the control states. -/
noncomputable def numbering (σ : Type) [Fintype σ] [DecidableEq σ] [Inhabited σ] :
    σ ≃ Fin (Fintype.card σ - 1 + 1) :=
  (Fintype.equivFin σ).trans (finCongr (by
    have : 0 < Fintype.card σ := Fintype.card_pos
    omega))

variable [Inhabited σ]

/-- The numbered machine. -/
noncomputable def toMachine (M : FMachine σ w h) : Machine (Fintype.card σ - 1) w h where
  initialState := numbering σ M.initialState
  output := fun s => M.output ((numbering σ).symm s)
  transition := fun s i v b =>
    let a := M.transition ((numbering σ).symm s) i v b
    { nextState := numbering σ a.nextState
      write := a.write
      workMove := a.workMove
      inputMove := a.inputMove }

/-- Renaming the control state of a configuration. -/
noncomputable def cfgMap {n : ℕ} (c : FConfig σ w h n) :
    Configuration (Fintype.card σ - 1) w h n where
  state := numbering σ c.state
  inputPos := c.inputPos
  workPos := c.workPos
  work := c.work

theorem toMachine_step (M : FMachine σ w h) (x : Word) (b : Bool)
    (c : FConfig σ w h x.length) :
    M.toMachine.step x b (cfgMap c) = cfgMap (M.step x b c) := by
  unfold Machine.step step
  simp only [toMachine, cfgMap, Equiv.symm_apply_apply]
  cases M.output c.state <;> rfl

/-- **Runs correspond**: the numbered machine runs through the renamed configurations. -/
theorem toMachine_run (M : FMachine σ w h) (x : Word) (coins : CoinTape) (t : ℕ) :
    M.toMachine.run x coins t = cfgMap (M.run x coins t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Machine.run_succ, ih, toMachine_step]; rfl

theorem toMachine_deterministic {M : FMachine σ w h} (hM : M.Deterministic) :
    M.toMachine.Deterministic := by
  intro s i v
  simp only [toMachine]
  rw [hM]

theorem toMachine_output_run (M : FMachine σ w h) (x : Word) (coins : CoinTape) (t : ℕ) :
    M.toMachine.output (M.toMachine.run x coins t).state = M.output (M.run x coins t).state := by
  rw [toMachine_run]
  simp [toMachine, cfgMap]

theorem toMachine_spaceThrough (M : FMachine σ w h) (x : Word) (coins : CoinTape) (t : ℕ) :
    M.toMachine.spaceThrough x coins t =
      ∑ k : Fin w, ((Finset.range (t + 1)).image (fun s => (M.run x coins s).workPos k)).card := by
  simp only [Machine.spaceThrough, toMachine_run]
  rfl

end FMachine

end ExactDerandomization
