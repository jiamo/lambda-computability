/-
**Space-bounded computation with an oracle: `DSPACE^A`, `NSPACE^A`, `PSPACE^A`.**

The model is the offline machine of `Start/SpaceMachine.lean` with one further tape: a query
tape, which the machine writes on and which it may hand to the oracle in a *query state*.  The
oracle answers in one step, the query tape is erased, and the machine continues in one of two
states according to the answer.  The query tape counts towards the space bound, which is the
standard convention (the *oracle space* convention); with it, `PSPACE^A` contains `PSPACE` for
every oracle, which is the inclusion this file proves.

Main definitions:

* `Complexity.Space.OConfig`, `Complexity.Space.OMachine` — configurations and machines;
* `Complexity.Space.OMachine.Accepts`, `.SpaceBounded` — acceptance and the space bound;
* `Complexity.Space.ODSPACE`, `.ONSPACE`, `.InPSPACE_rel`, `.InNPSPACE_rel` — the classes.

Main results:

* `Complexity.Space.onspace_of_odspace`, `Complexity.Space.ODSPACE.mono`,
  `Complexity.Space.ONSPACE.mono` — the elementary structure of the classes;
* `Complexity.Space.ofMachine_accepts_iff`, `Complexity.Space.ofMachine_spaceBounded` — an
  ordinary offline machine is an oracle machine that never queries, with the same runs;
* `Complexity.Space.odspace_of_dspace`, `Complexity.Space.inPSPACE_rel_of_pspace` —
  `DSPACE s ⊆ DSPACE^A s` and `PSPACE ⊆ PSPACE^A`, for every oracle `A`;
* `Complexity.Space.inPSPACE_rel_oracle_free` — the empty oracle adds nothing to a machine that
  does not query, so the unrelativized class is recovered on that part of the model.
-/

import Mathlib
import Start.SpaceMachine
import Start.OracleCob

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

open Complexity (PolyBound Oracle Word)

/-! ### Configurations -/

/-- A configuration of an offline machine with a query tape. -/
structure OConfig where
  /-- The control state. -/
  state : ℕ
  /-- The position of the read-only input head. -/
  inHead : ℕ
  /-- The used part of the work tape. -/
  tape : List Bool
  /-- The position of the work head. -/
  wHead : ℕ
  /-- The contents of the query tape. -/
  qtape : List Bool
  deriving DecidableEq, Repr, Inhabited

/-- The space a configuration occupies: the work tape and the query tape together. -/
def OConfig.space (c : OConfig) : ℕ := max (max c.tape.length (c.wHead + 1)) c.qtape.length

/-- The initial configuration. -/
def oinit : OConfig := ⟨0, 0, [], 0, []⟩

/-! ### Machines -/

/-- An offline machine with a read-only input tape, a binary work tape and a query tape.  In a
state `q` with `query q = some (qyes, qno)` the machine asks the oracle about the contents of its
query tape, erases the tape and continues in `qyes` or `qno` according to the answer.  In any
other state it behaves like the machine of `Start/SpaceMachine.lean`, with the extra option of
appending a bit to the query tape. -/
structure OMachine where
  /-- The number of control states. -/
  states : ℕ
  /-- The accepting states. -/
  accept : ℕ → Bool
  /-- The query states, with the two continuations. -/
  query : ℕ → Option (ℕ × ℕ)
  /-- The transition function; the empty list means halting.  An instruction is a new state, the
  bit to write on the work tape, an optional bit to append to the query tape, the input move and
  the work move. -/
  delta : ℕ → Option Bool → Bool → List (ℕ × Bool × Option Bool × Dir × Dir)

namespace OMachine

variable (M : OMachine)

/-- The machine is deterministic when every situation offers at most one instruction. -/
def Deterministic : Prop := ∀ q a b, (M.delta q a b).length ≤ 1

/-- The machine is well formed when it has an initial state and never leaves its state set. -/
def WellFormed : Prop :=
  0 < M.states ∧ (∀ q a b, ∀ t ∈ M.delta q a b, t.1 < M.states) ∧
    ∀ q p, M.query q = some p → p.1 < M.states ∧ p.2 < M.states

/-- The successors of a configuration on a given input, with the oracle `A`. -/
def stepList (A : Oracle) (x : List Bool) (c : OConfig) : List OConfig :=
  match M.query c.state with
  | some (qyes, qno) =>
      [{ c with state := if A c.qtape then qyes else qno, qtape := [] }]
  | none =>
      (M.delta c.state x[c.inHead]? (c.tape.getD c.wHead false)).map fun t =>
        { state := t.1
          inHead := moveIn x.length c.inHead t.2.2.2.1
          tape := writeAt c.tape c.wHead t.2.1
          wHead := moveWork c.wHead t.2.2.2.2
          qtape := match t.2.2.1 with
            | none => c.qtape
            | some b => c.qtape ++ [b] }

/-- The one-step relation of the machine on a given input, with the oracle `A`. -/
def Step (A : Oracle) (x : List Bool) (c c' : OConfig) : Prop := c' ∈ M.stepList A x c

/-- The machine accepts an input when some finite run leads to an accepting state. -/
def Accepts (A : Oracle) (x : List Bool) : Prop :=
  ∃ (n : ℕ) (c : OConfig), Reach.steps (M.Step A x) n oinit c ∧ M.accept c.state = true

/-- The machine runs in space `s` when every configuration reachable on an input `x` uses at most
`s |x|` cells, counting the work tape and the query tape. -/
def SpaceBounded (A : Oracle) (s : ℕ → ℕ) : Prop :=
  ∀ (x : List Bool) (n : ℕ) (c : OConfig),
    Reach.steps (M.Step A x) n oinit c → c.space ≤ s x.length

end OMachine

/-! ### The classes -/

/-- `NSPACE^A s`: decided by a well-formed nondeterministic oracle machine running in space
`s`. -/
def ONSPACE (A : Oracle) (s : ℕ → ℕ) (L : Language) : Prop :=
  ∃ M : OMachine, M.WellFormed ∧ M.SpaceBounded A s ∧ ∀ x, L x ↔ M.Accepts A x

/-- `DSPACE^A s`: decided by a well-formed deterministic oracle machine running in space `s`. -/
def ODSPACE (A : Oracle) (s : ℕ → ℕ) (L : Language) : Prop :=
  ∃ M : OMachine, M.WellFormed ∧ M.Deterministic ∧ M.SpaceBounded A s ∧ ∀ x, L x ↔ M.Accepts A x

/-- `PSPACE^A`. -/
def InPSPACE_rel (A : Oracle) (L : Language) : Prop :=
  ∃ s : ℕ → ℕ, PolyBound s ∧ ODSPACE A s L

/-- `NPSPACE^A`. -/
def InNPSPACE_rel (A : Oracle) (L : Language) : Prop :=
  ∃ s : ℕ → ℕ, PolyBound s ∧ ONSPACE A s L

theorem onspace_of_odspace {A : Oracle} {s : ℕ → ℕ} {L : Language} (h : ODSPACE A s L) :
    ONSPACE A s L := by
  obtain ⟨M, hwf, _, hsp, hL⟩ := h
  exact ⟨M, hwf, hsp, hL⟩

theorem inNPSPACE_rel_of_inPSPACE_rel {A : Oracle} {L : Language} (h : InPSPACE_rel A L) :
    InNPSPACE_rel A L := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, hs, onspace_of_odspace h⟩

theorem ODSPACE.mono {A : Oracle} {s s' : ℕ → ℕ} {L : Language} (h : ODSPACE A s L)
    (hs : ∀ n, s n ≤ s' n) : ODSPACE A s' L := by
  obtain ⟨M, hwf, hdet, hsp, hL⟩ := h
  exact ⟨M, hwf, hdet, fun x n c hc => le_trans (hsp x n c hc) (hs _), hL⟩

theorem ONSPACE.mono {A : Oracle} {s s' : ℕ → ℕ} {L : Language} (h : ONSPACE A s L)
    (hs : ∀ n, s n ≤ s' n) : ONSPACE A s' L := by
  obtain ⟨M, hwf, hsp, hL⟩ := h
  exact ⟨M, hwf, fun x n c hc => le_trans (hsp x n c hc) (hs _), hL⟩

/-! ### An ordinary machine is an oracle machine that never queries -/

/-- The oracle machine attached to an ordinary offline machine: it has no query state and never
writes on the query tape. -/
def ofMachine (M : Machine) : OMachine where
  states := M.states
  accept := M.accept
  query := fun _ => none
  delta := fun q a b => (M.delta q a b).map fun t => (t.1, t.2.1, none, t.2.2.1, t.2.2.2)

/-- The configuration of the oracle machine attached to a configuration of an ordinary one. -/
def ofConfig (c : Config) : OConfig := ⟨c.state, c.inHead, c.tape, c.wHead, []⟩

@[simp] theorem ofConfig_space (c : Config) : (ofConfig c).space = c.space := by
  simp [ofConfig, OConfig.space, Config.space]

@[simp] theorem ofConfig_init : ofConfig init = oinit := rfl

theorem ofMachine_stepList (M : Machine) (A : Oracle) (x : List Bool) (c : Config) :
    (ofMachine M).stepList A x (ofConfig c) = (M.stepList x c).map ofConfig := by
  simp [OMachine.stepList, ofMachine, ofConfig, Machine.stepList, List.map_map,
    Function.comp_def]

theorem ofMachine_step_iff (M : Machine) (A : Oracle) (x : List Bool) (c : Config)
    (d : OConfig) :
    (ofMachine M).Step A x (ofConfig c) d ↔ ∃ c', M.Step x c c' ∧ d = ofConfig c' := by
  rw [OMachine.Step, ofMachine_stepList]
  constructor
  · intro h
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 h
    exact ⟨c', hc', rfl⟩
  · rintro ⟨c', hc', rfl⟩
    exact List.mem_map_of_mem hc'

/-- The runs of the oracle machine attached to `M` are exactly the runs of `M`. -/
theorem ofMachine_steps_iff (M : Machine) (A : Oracle) (x : List Bool) :
    ∀ (n : ℕ) (d : OConfig),
      Reach.steps ((ofMachine M).Step A x) n oinit d ↔
        ∃ c, Reach.steps (M.Step x) n init c ∧ d = ofConfig c := by
  intro n
  induction n with
  | zero =>
      intro d
      constructor
      · intro h
        exact ⟨init, rfl, by rw [← h]; rfl⟩
      · rintro ⟨c, hc, rfl⟩
        rw [Reach.steps_zero] at hc
        rw [← hc]
        rfl
  | succ n ih =>
      intro d
      constructor
      · rintro ⟨m, hm, hstep⟩
        obtain ⟨c, hc, rfl⟩ := (ih m).1 hm
        obtain ⟨c', hc', rfl⟩ := (ofMachine_step_iff M A x c d).1 hstep
        exact ⟨c', ⟨c, hc, hc'⟩, rfl⟩
      · rintro ⟨c, ⟨m, hm, hstep⟩, rfl⟩
        exact ⟨ofConfig m, (ih _).2 ⟨m, hm, rfl⟩,
          (ofMachine_step_iff M A x m (ofConfig c)).2 ⟨c, hstep, rfl⟩⟩

theorem ofMachine_accepts_iff (M : Machine) (A : Oracle) (x : List Bool) :
    (ofMachine M).Accepts A x ↔ M.Accepts x := by
  constructor
  · rintro ⟨n, d, hd, hacc⟩
    obtain ⟨c, hc, rfl⟩ := (ofMachine_steps_iff M A x n d).1 hd
    exact ⟨n, c, hc, by simpa [ofConfig, ofMachine] using hacc⟩
  · rintro ⟨n, c, hc, hacc⟩
    exact ⟨n, ofConfig c, (ofMachine_steps_iff M A x n _).2 ⟨c, hc, rfl⟩,
      by simpa [ofConfig, ofMachine] using hacc⟩

theorem ofMachine_spaceBounded {M : Machine} {s : ℕ → ℕ} (A : Oracle) (h : M.SpaceBounded s) :
    (ofMachine M).SpaceBounded A s := by
  intro x n d hd
  obtain ⟨c, hc, rfl⟩ := (ofMachine_steps_iff M A x n d).1 hd
  rw [ofConfig_space]
  exact h x n c hc

theorem ofMachine_wellFormed {M : Machine} (h : M.WellFormed) : (ofMachine M).WellFormed := by
  refine ⟨h.1, ?_, ?_⟩
  · intro q a b t ht
    simp only [ofMachine, List.mem_map] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    exact h.2 q a b t' ht'
  · intro q p hp
    simp [ofMachine] at hp

theorem ofMachine_deterministic {M : Machine} (h : M.Deterministic) :
    (ofMachine M).Deterministic := by
  intro q a b
  simpa [ofMachine] using h q a b

/-- **`DSPACE s ⊆ DSPACE^A s` for every oracle.** -/
theorem odspace_of_dspace {s : ℕ → ℕ} {L : Language} (A : Oracle) (h : DSPACE s L) :
    ODSPACE A s L := by
  obtain ⟨M, hwf, hdet, hsp, hL⟩ := h
  exact ⟨ofMachine M, ofMachine_wellFormed hwf, ofMachine_deterministic hdet,
    ofMachine_spaceBounded A hsp, fun x => (hL x).trans (ofMachine_accepts_iff M A x).symm⟩

/-- **`PSPACE ⊆ PSPACE^A` for every oracle.** -/
theorem inPSPACE_rel_of_pspace {L : Language} (A : Oracle) (h : PSPACE L) :
    InPSPACE_rel A L := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, hs, odspace_of_dspace A h⟩

/-- On the query-free part of the model the oracle is irrelevant: the machine attached to an
ordinary one accepts the same inputs whatever the oracle is. -/
theorem inPSPACE_rel_oracle_free {M : Machine} (A B : Oracle) (x : List Bool) :
    (ofMachine M).Accepts A x ↔ (ofMachine M).Accepts B x := by
  rw [ofMachine_accepts_iff, ofMachine_accepts_iff]

end Complexity.Space
