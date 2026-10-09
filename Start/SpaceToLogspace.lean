import Start.LogspaceFinState
import Start.SpaceConfigCount

/-!
# Compiling host offline machines into `ExactDerandomization` deciders

This module is this library's own (tasks `M27-SPACE-MODEL-COMPILE` and
`M27-SPACE-MODEL-TOTALIZE`).  It compiles a deterministic, well-formed offline machine `M` of
`Start/SpaceMachine.lean` (one read-only input head without a left end marker, one one-sided
binary work tape, acceptance by *passing through* an accepting state, possibly looping) into a
machine of `Start/LogspaceDeterministic.lean` (absorbed from openai/math; several two-sided work
tapes, several input heads, both end markers, output states) that **always halts**.

The compiled machine `compile M k` has

* work tape `0`: the host work tape, cell for cell;
* work tape `1`: an origin marker (`true` exactly on cell `0`, written by the initialisation
  step), moved in lockstep with tape `0`, which lets the finite control clamp the host's left
  moves at the origin;
* input head `0`: the host input head, shifted by one cell because of the left end marker; a host
  left move from the first cell lands on the marker and is undone by a `fix` step;
* input heads `1, …, k`: an **odometer clock** — their positions are the digits of a number in
  base `n + 2`; after every simulated host step the clock ticks (a carry sweeps a head back to
  the left marker), and when all `k` digits are maximal the machine rejects.  The clock uses **no
  work-tape cells at all**.

The control states (`Ph`) are the initialisation state, the host state in four phases
(`run`, `fix`, `tick j`, `sweep j`) and the two output states.  One host step is carried out by a
fixed finite table: the target transition reads the same input symbol and work bit as the host
and applies the host's (finite) instruction table; carries cost additional target steps.
-/

set_option autoImplicit false

namespace Complexity.Space

namespace ToLogspace

open ExactDerandomization (Word InputSymbol Direction FMachine FAction FConfig readInput)

/-- Control states of the compiled machine, for `Q` host states and `k` clock digits. -/
inductive Ph (Q k : ℕ) where
  | init
  | run (q : Fin Q)
  | fix (q : Fin Q)
  | tick (q : Fin Q) (j : Fin k)
  | sweep (q : Fin Q) (j : Fin k)
  | acc
  | rej
  deriving DecidableEq, Fintype

instance (Q k : ℕ) : Inhabited (Ph Q k) := ⟨.init⟩

/-- The host's view of an input symbol: a bit, or the end marker (`none`). -/
def hostSym : InputSymbol → Option Bool
  | .bit b => some b
  | _ => none

/-- Host input moves. -/
def dirIn : Dir → Direction
  | .left => .left
  | .right => .right
  | .stay => .stay

/-- Host work moves, clamped at the origin (`atOrigin` is the bit under the marker head). -/
def dirW (atOrigin : Bool) : Dir → Direction
  | .left => if atOrigin then .stay else .left
  | .right => .right
  | .stay => .stay

/-- The action that changes nothing but the control state. -/
def idle {Q k : ℕ} (p : Ph Q k) (wk : Fin 2 → Bool) : FAction (Ph Q k) 2 (k + 1) where
  nextState := p
  write := wk
  workMove := fun _ => .stay
  inputMove := fun _ => .stay

/-- The action that changes the control state and moves one input head. -/
def moveHead {Q k : ℕ} (p : Ph Q k) (wk : Fin 2 → Bool) (i : Fin (k + 1)) (d : Direction) :
    FAction (Ph Q k) 2 (k + 1) where
  nextState := p
  write := wk
  workMove := fun _ => .stay
  inputMove := fun j => if j = i then d else .stay

variable (M : Machine) (k : ℕ)

/-- The finite transition table of the compiled machine. -/
def trans : Ph M.states k → (Fin (k + 1) → InputSymbol) → (Fin 2 → Bool) →
    FAction (Ph M.states k) 2 (k + 1)
  | .init, _, wk =>
      { nextState := if h : 0 < M.states then .run ⟨0, h⟩ else .rej
        write := ![wk 0, true]
        workMove := fun _ => .stay
        inputMove := fun j => if j = 0 then .right else .stay }
  | .run q, inp, wk =>
      if M.accept q then idle .acc wk else
      match M.delta q (hostSym (inp 0)) (wk 0) with
      | [] => idle .rej wk
      | (q', b, dI, dW) :: _ =>
          { nextState := if h : q' < M.states then .fix ⟨q', h⟩ else .rej
            write := ![b, wk 1]
            workMove := fun _ => dirW (wk 1) dW
            inputMove := fun j => if j = 0 then dirIn dI else .stay }
  | .fix q, inp, wk =>
      let next : Ph M.states k := if h : 0 < k then .tick q ⟨0, h⟩ else .rej
      if inp 0 = .leftMarker then moveHead next wk 0 .right else idle next wk
  | .tick q j, inp, wk =>
      if inp j.succ = .rightMarker then
        idle (if j.val + 1 < k then .sweep q j else .rej) wk
      else moveHead (.run q) wk j.succ .right
  | .sweep q j, inp, wk =>
      if inp j.succ = .leftMarker then
        idle (if h : j.val + 1 < k then .tick q ⟨j.val + 1, h⟩ else .rej) wk
      else moveHead (.sweep q j) wk j.succ .left
  | .acc, _, wk => idle .acc wk
  | .rej, _, wk => idle .rej wk

/-- Output states. -/
def out : Ph M.states k → Option Bool
  | .acc => some true
  | .rej => some false
  | _ => none

/-- **The compiled machine**, with control states `Ph M.states k`. -/
def fcompile : FMachine (Ph M.states k) 2 (k + 1) where
  initialState := .init
  output := out M k
  transition := fun p inp wk _ => trans M k p inp wk

/-- **The compiled machine**, numbered as an `ExactDerandomization.Machine`. -/
noncomputable def compile : ExactDerandomization.Machine (Fintype.card (Ph M.states k) - 1) 2 (k + 1) :=
  (fcompile M k).toMachine

theorem fcompile_deterministic : (fcompile M k).Deterministic := fun _ _ _ => rfl

theorem compile_deterministic : (compile M k).Deterministic :=
  FMachine.toMachine_deterministic (fcompile_deterministic M k)

end ToLogspace

end Complexity.Space
