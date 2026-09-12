/-
Space-bounded computation: offline Turing machines with a read-only input tape and one binary
work tape, and the classes `DSPACE`, `NSPACE`, `L`, `PSPACE`, `NPSPACE`.

Time and space are measured on different models in this library: polynomial *time* is Cobham's
class (`Start/ComplexityClasses.lean`), where closure under composition is a constructor rather
than a theorem, while space has to be measured on a machine, because the whole point of a space
bound is that the storage used by a computation is much smaller than the computation itself.
The model here is the standard one for sublinear space: the input sits on a separate read-only
tape which does not count towards the space bound, the head on it is clamped to the input (the
position `|x|` is the end marker), and the machine has one work tape of binary cells whose used
length is what the bound constrains.  Nondeterminism is built in — the transition function
returns the *list* of possible instructions — and determinism is the property of that list
having at most one entry.

Main definitions:

* `Complexity.Space.Config` — a configuration: control state, input head, work tape, work head;
* `Complexity.Space.Machine` — an offline machine, `Machine.Step` its one-step relation;
* `Complexity.Space.Machine.Accepts` — acceptance by some finite run;
* `Complexity.Space.Machine.SpaceBounded` — every reachable configuration fits in the bound;
* `Complexity.Space.NSPACE`, `DSPACE`, `LOGSPACE`, `PSPACE`, `NPSPACE` — the classes.

Main results:

* `Complexity.Space.writeAt_length`, `Complexity.Space.getD_writeAt_self` — the work tape;
* `Complexity.Space.Machine.step_state_lt`, `.step_inHead_le` — the invariants of a run;
* `Complexity.Space.nspace_of_dspace`, `Complexity.Space.npspace_of_pspace` — determinism is a
  special case of nondeterminism;
* `Complexity.Space.DSPACE.mono`, `Complexity.Space.NSPACE.mono` — monotonicity in the bound;
* `Complexity.Space.pspace_of_logspace` — `L ⊆ PSPACE`;
* `Complexity.Space.dspace_const_decidable` — a machine that reads nothing and answers at once,
  witnessing that the classes are non-empty.
-/

import Mathlib
import Start.ComplexityClasses
import Start.SavitchReach

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

open Complexity (PolyBound)

/-! ### Configurations -/

/-- The direction of a head move. -/
inductive Dir
  | left
  | right
  | stay
  deriving DecidableEq, Repr, Inhabited

/-- A configuration of an offline machine: the control state, the position of the read-only input
head, the contents of the work tape, and the position of the work head. -/
structure Config where
  /-- The control state. -/
  state : ℕ
  /-- The position of the read-only input head. -/
  inHead : ℕ
  /-- The used part of the work tape. -/
  tape : List Bool
  /-- The position of the work head. -/
  wHead : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The space a configuration occupies: the part of the work tape that has been written or
visited. -/
def Config.space (c : Config) : ℕ := max c.tape.length (c.wHead + 1)

/-- Writing a bit at a position of the work tape, extending it with blanks when the position is
beyond the used part. -/
def writeAt : List Bool → ℕ → Bool → List Bool
  | [], 0, b => [b]
  | [], i + 1, b => false :: writeAt [] i b
  | _ :: t, 0, b => b :: t
  | a :: t, i + 1, b => a :: writeAt t i b

@[simp] theorem writeAt_length (l : List Bool) (i : ℕ) (b : Bool) :
    (writeAt l i b).length = max l.length (i + 1) := by
  induction l generalizing i with
  | nil =>
      induction i with
      | zero => simp [writeAt]
      | succ i ih => simp [writeAt] at ih ⊢; omega
  | cons a t ih =>
      cases i with
      | zero => simp [writeAt]
      | succ i => simp [writeAt, ih]

@[simp] theorem getD_writeAt_self (l : List Bool) (i : ℕ) (b : Bool) :
    (writeAt l i b).getD i false = b := by
  induction l generalizing i with
  | nil =>
      induction i with
      | zero => simp [writeAt]
      | succ i ih => simpa [writeAt] using ih
  | cons a t ih =>
      cases i with
      | zero => simp [writeAt]
      | succ i => simpa [writeAt] using ih i

/-- Moving the work head; it cannot move left of the origin. -/
def moveWork (i : ℕ) : Dir → ℕ
  | .left => i - 1
  | .right => i + 1
  | .stay => i

/-- Moving the read-only input head; it stays inside `0, …, n`, where the position `n` is the end
marker of an input of length `n`. -/
def moveIn (n i : ℕ) : Dir → ℕ
  | .left => i - 1
  | .right => min (i + 1) n
  | .stay => i

theorem moveIn_le (n i : ℕ) (d : Dir) (h : i ≤ n) : moveIn n i d ≤ n := by
  cases d <;> simp [moveIn] <;> omega

theorem moveWork_le (i s : ℕ) (d : Dir) (h : i + 1 ≤ s) : moveWork i d ≤ s := by
  cases d <;> simp [moveWork] <;> omega

/-! ### Machines -/

/-- An offline machine with a read-only input tape and one binary work tape.  The control states
are `0, …, states - 1` with `0` the initial state; `accept` marks the accepting states; and
`delta q a b` is the list of instructions available in state `q` when the input head reads `a`
(`none` at the end marker) and the work head reads `b`.  An instruction is a new state, the bit
to write, the input move and the work move.  An empty list means that the machine halts. -/
structure Machine where
  /-- The number of control states. -/
  states : ℕ
  /-- The accepting states. -/
  accept : ℕ → Bool
  /-- The transition function; the empty list means halting. -/
  delta : ℕ → Option Bool → Bool → List (ℕ × Bool × Dir × Dir)

namespace Machine

variable (M : Machine)

/-- The machine is deterministic when every situation offers at most one instruction. -/
def Deterministic : Prop := ∀ q a b, (M.delta q a b).length ≤ 1

/-- The machine is well formed when it has an initial state and never leaves its state set. -/
def WellFormed : Prop :=
  0 < M.states ∧ ∀ q a b, ∀ t ∈ M.delta q a b, t.1 < M.states

/-- The successors of a configuration on a given input. -/
def stepList (x : List Bool) (c : Config) : List Config :=
  (M.delta c.state x[c.inHead]? (c.tape.getD c.wHead false)).map fun t =>
    { state := t.1
      inHead := moveIn x.length c.inHead t.2.2.1
      tape := writeAt c.tape c.wHead t.2.1
      wHead := moveWork c.wHead t.2.2.2 }

/-- The one-step relation of the machine on a given input. -/
def Step (x : List Bool) (c c' : Config) : Prop := c' ∈ M.stepList x c

instance (x : List Bool) : DecidablePred fun p : Config × Config => M.Step x p.1 p.2 :=
  fun p => inferInstanceAs (Decidable (p.2 ∈ M.stepList x p.1))

end Machine

/-- The initial configuration: state `0`, both heads at the origin, empty work tape. -/
def init : Config := ⟨0, 0, [], 0⟩

namespace Machine

variable (M : Machine)

/-- The machine accepts an input when some finite run leads to an accepting state. -/
def Accepts (x : List Bool) : Prop :=
  ∃ (n : ℕ) (c : Config), Reach.steps (M.Step x) n init c ∧ M.accept c.state = true

/-- The machine runs in space `s` on the input `x` when every configuration reachable on that
input uses at most `s` cells of the work tape. -/
def SpaceBoundedOn (x : List Bool) (s : ℕ) : Prop :=
  ∀ (n : ℕ) (c : Config), Reach.steps (M.Step x) n init c → c.space ≤ s

/-- The machine runs in space `s` when every configuration reachable on an input `x` uses at most
`s |x|` cells of the work tape. -/
def SpaceBounded (s : ℕ → ℕ) : Prop :=
  ∀ (x : List Bool) (n : ℕ) (c : Config),
    Reach.steps (M.Step x) n init c → c.space ≤ s x.length

theorem spaceBoundedOn_of_spaceBounded {s : ℕ → ℕ} (h : M.SpaceBounded s) (x : List Bool) :
    M.SpaceBoundedOn x (s x.length) := fun n c hc => h x n c hc

variable {M}

theorem step_state_lt (hwf : M.WellFormed) {x : List Bool} {c c' : Config}
    (h : M.Step x c c') : c'.state < M.states := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  exact hwf.2 _ _ _ t ht

theorem step_inHead_le {x : List Bool} {c c' : Config} (hc : c.inHead ≤ x.length)
    (h : M.Step x c c') : c'.inHead ≤ x.length := by
  obtain ⟨t, _, rfl⟩ := List.mem_map.1 h
  exact moveIn_le _ _ _ hc

theorem init_inHead_le (x : List Bool) : (init).inHead ≤ x.length := Nat.zero_le _

theorem inHead_le_of_steps {x : List Bool} :
    ∀ {n : ℕ} {c : Config}, Reach.steps (M.Step x) n init c → c.inHead ≤ x.length := by
  intro n
  induction n with
  | zero => rintro c rfl; exact Nat.zero_le _
  | succ n ih =>
      rintro c ⟨m, hm, hstep⟩
      exact step_inHead_le (ih hm) hstep

theorem state_lt_of_steps (hwf : M.WellFormed) {x : List Bool} :
    ∀ {n : ℕ} {c : Config}, Reach.steps (M.Step x) n init c → c.state < M.states := by
  intro n
  induction n with
  | zero => rintro c rfl; exact hwf.1
  | succ n ih =>
      rintro c ⟨m, _, hstep⟩
      exact step_state_lt hwf hstep

end Machine

/-! ### The classes -/

/-- A language: a set of binary words. -/
abbrev Language := List Bool → Prop

/-- `NSPACE s`: decided by a well-formed nondeterministic machine running in space `s`. -/
def NSPACE (s : ℕ → ℕ) (L : Language) : Prop :=
  ∃ M : Machine, M.WellFormed ∧ M.SpaceBounded s ∧ ∀ x, L x ↔ M.Accepts x

/-- `DSPACE s`: decided by a well-formed deterministic machine running in space `s`. -/
def DSPACE (s : ℕ → ℕ) (L : Language) : Prop :=
  ∃ M : Machine, M.WellFormed ∧ M.Deterministic ∧ M.SpaceBounded s ∧ ∀ x, L x ↔ M.Accepts x

/-- Logarithmic space. -/
def LOGSPACE (L : Language) : Prop := ∃ a : ℕ, DSPACE (fun n => a * (Nat.log 2 (n + 1) + 1)) L

/-- Polynomial space. -/
def PSPACE (L : Language) : Prop := ∃ s : ℕ → ℕ, PolyBound s ∧ DSPACE s L

/-- Nondeterministic polynomial space. -/
def NPSPACE (L : Language) : Prop := ∃ s : ℕ → ℕ, PolyBound s ∧ NSPACE s L

theorem nspace_of_dspace {s : ℕ → ℕ} {L : Language} (h : DSPACE s L) : NSPACE s L := by
  obtain ⟨M, hwf, _, hsp, hL⟩ := h
  exact ⟨M, hwf, hsp, hL⟩

theorem npspace_of_pspace {L : Language} (h : PSPACE L) : NPSPACE L := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, hs, nspace_of_dspace h⟩

theorem DSPACE.mono {s s' : ℕ → ℕ} {L : Language} (h : DSPACE s L) (hs : ∀ n, s n ≤ s' n) :
    DSPACE s' L := by
  obtain ⟨M, hwf, hdet, hsp, hL⟩ := h
  exact ⟨M, hwf, hdet, fun x n c hc => le_trans (hsp x n c hc) (hs _), hL⟩

theorem NSPACE.mono {s s' : ℕ → ℕ} {L : Language} (h : NSPACE s L) (hs : ∀ n, s n ≤ s' n) :
    NSPACE s' L := by
  obtain ⟨M, hwf, hsp, hL⟩ := h
  exact ⟨M, hwf, fun x n c hc => le_trans (hsp x n c hc) (hs _), hL⟩

/-- Logarithmic space is polynomial space. -/
theorem pspace_of_logspace {L : Language} (h : LOGSPACE L) : PSPACE L := by
  obtain ⟨a, hL⟩ := h
  refine ⟨fun n => a * (n + 1), ⟨a + a, 1, ?_⟩, hL.mono fun n => ?_⟩
  · intro n
    simp only [pow_one]
    exact Nat.mul_le_mul_right (n + 1) (Nat.le_add_right a a)
  · have hlog : Nat.log 2 (n + 1) < n + 1 :=
      Nat.log_lt_of_lt_pow (by omega) (Nat.lt_two_pow_self)
    exact Nat.mul_le_mul_left a (by omega)

/-! ### Non-vacuity -/

/-- The machine with one state that halts at once; it accepts everything or nothing, according to
whether its single state is accepting. -/
def constMachine (b : Bool) : Machine where
  states := 1
  accept := fun _ => b
  delta := fun _ _ _ => []

theorem constMachine_wellFormed (b : Bool) : (constMachine b).WellFormed := by
  refine ⟨Nat.one_pos, ?_⟩
  intro q a c t ht
  simp [constMachine] at ht

theorem constMachine_deterministic (b : Bool) : (constMachine b).Deterministic := by
  intro q a c
  simp [constMachine]

theorem constMachine_steps (b : Bool) (x : List Bool) :
    ∀ (n : ℕ) (c : Config), Reach.steps ((constMachine b).Step x) n init c →
      c = init := by
  intro n
  induction n with
  | zero => rintro c rfl; rfl
  | succ n ih =>
      rintro c ⟨m, hm, hstep⟩
      exact absurd hstep (by simp [Machine.Step, Machine.stepList, constMachine])

/-- Both the always-accepting and the always-rejecting language are in `DSPACE 1`, so all the
classes above are non-empty.  (One cell is the least a configuration can occupy: the work head
always stands on some cell.) -/
theorem dspace_const_decidable (b : Bool) :
    DSPACE (fun _ => 1) (fun _ => b = true) := by
  refine ⟨constMachine b, constMachine_wellFormed b, constMachine_deterministic b, ?_, ?_⟩
  · intro x n c hc
    rw [constMachine_steps b x n c hc]
    simp [Config.space, init]
  · intro x
    constructor
    · intro hb
      exact ⟨0, init, rfl, by simpa [constMachine] using hb⟩
    · rintro ⟨n, c, hc, hacc⟩
      simpa [constMachine] using hacc

end Complexity.Space
