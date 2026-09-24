/-
**From a bounded-memory abstract machine to an offline machine: the bridge, proved once.**

Several parts of the library have a special-purpose abstract machine with its own memory bound —
the stack machine that evaluates quantified Boolean formulas (`Start/Qbf.lean`, `2n² + 3n` bits),
the Krivine machine with a shared heap (`Start/KrivineSpaceConfig.lean`, `O(s log s)` bits),
Savitch's recursion (`Start/SavitchVM.lean`) — and in each case what is missing to turn the memory
bound into a statement about `Complexity.Space.DSPACE` is the same thing: an offline machine of
`Start/SpaceMachine.lean` that runs the abstract machine.

That task has two halves of very different nature.

* A *step-level* half: one step of the abstract machine has to be carried out by the finite
  control of an offline machine on the binary encoding of the abstract state.  This is genuinely
  specific to each abstract machine — it is where a stack of records is laid out on a tape and
  pushed and popped bit by bit — and no general theorem can supply it: the finite control of an
  offline machine cannot compute an arbitrary transition function.
* A *run-level* half: given the step-level simulation, the offline machine accepts exactly the
  inputs the abstract machine accepts, and every configuration it ever reaches — not only the
  encodings of abstract states but every intermediate configuration of every simulated step —
  fits in the memory bound.  This is the same argument every time: it needs determinism of the
  offline machine to know that its unique run is the concatenation of the step segments, and an
  induction over that run.

This module proves the run-level half once, in the pattern of `Start/Rewriting.lean`: the
client supplies a single bridge statement, `Complexity.Space.Realizes`, which says that each
abstract step is carried out by a *segment* of the offline machine (`Complexity.Space.Machine.Seg`)
between the encodings of the two abstract states, that halting abstract states are encoded by
halting configurations, and that the encoding respects acceptance and the bound.  Everything
else — acceptance, the space bound on all reachable configurations, membership in `DSPACE` and
`PSPACE` — follows from `Complexity.Space.Realizes.accepts_iff`,
`Complexity.Space.Realizes.spaceBoundedOn`, `Complexity.Space.Realizes.dspace` and
`Complexity.Space.Realizes.pspace`.

Main definitions:

* `Complexity.Space.AbsMachine` — a deterministic abstract machine on binary inputs: an initial
  state for each input, a partial step function, and an acceptance test;
  `AbsMachine.Reaches` and `AbsMachine.Accepts` are its reachability and acceptance;
* `Complexity.Space.Machine.Path`, `Complexity.Space.Machine.Seg` — a run of the offline machine
  whose intermediate configurations satisfy a side condition (for `Seg`: at most `B` cells and a
  non-accepting control state), with composition lemmas for building segments piecewise;
* `Complexity.Space.Realizes` — the bridge: an offline machine realizes an abstract machine
  under an encoding of its states into configurations, within a bound `B x` for each input.

Main results:

* `Complexity.Space.Machine.steps_det` — a deterministic machine has at most one configuration at
  each distance from a given one;
* `Complexity.Space.Realizes.reach_code` — every reachable abstract state is simulated;
* `Complexity.Space.Realizes.onRun` — every reachable configuration of the offline machine is the
  encoding of a reachable abstract state or lies inside the segment of one of its steps;
* `Complexity.Space.Realizes.accepts_iff` — the offline machine accepts exactly the inputs the
  abstract machine accepts;
* `Complexity.Space.Realizes.spaceBoundedOn` — and it runs within the bound on every input;
* `Complexity.Space.Realizes.dspace`, `Complexity.Space.Realizes.pspace` — hence the language of
  the abstract machine lies in `DSPACE s` (resp. `PSPACE`) as soon as the bound is `s |x|`
  (resp. polynomial);
* `Complexity.Space.realizes_self` — a deterministic offline machine realizes itself, viewed as an
  abstract machine, so the interface loses nothing: `DSPACE` is exactly the class of languages of
  realized abstract machines (`Complexity.Space.dspace_iff_realizes`).
-/

import Mathlib
import Start.SpaceMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

open Complexity.Reach

/-! ### Abstract machines -/

/-- A deterministic abstract machine on binary inputs, with states of an arbitrary type: the state
it starts in on each input, a partial step function (`none` means that the machine has halted),
and an acceptance test on states. -/
structure AbsMachine (σ : Type*) where
  /-- The initial state on an input. -/
  start : List Bool → σ
  /-- One step; `none` means halting. -/
  step : σ → Option σ
  /-- The accepting states. -/
  accept : σ → Bool

namespace AbsMachine

variable {σ : Type*} (A : AbsMachine σ)

/-- The one-step relation of an abstract machine. -/
def StepRel (s t : σ) : Prop := A.step s = some t

/-- The states reachable on an input. -/
def Reaches (x : List Bool) (s : σ) : Prop := Relation.ReflTransGen A.StepRel (A.start x) s

/-- The abstract machine accepts an input when an accepting state is reachable on it. -/
def Accepts (x : List Bool) : Prop := ∃ s, A.Reaches x s ∧ A.accept s = true

variable {A}

theorem Reaches.start (x : List Bool) : A.Reaches x (A.start x) := Relation.ReflTransGen.refl

theorem Reaches.tail {x : List Bool} {s t : σ} (hs : A.Reaches x s) (h : A.step s = some t) :
    A.Reaches x t := Relation.ReflTransGen.tail hs h

end AbsMachine

/-! ### Runs with a side condition, and determinism -/

namespace Machine

variable (M : Machine) (x : List Bool)

/-- `M.Path x P c c'`: the machine runs from `c` to `c'` on the input `x`, and every configuration
of the run *before* `c'` satisfies `P` (the last one need not). -/
inductive Path (P : Config → Prop) : Config → Config → Prop
  /-- The empty run. -/
  | refl (c : Config) : Path P c c
  /-- One step from a configuration satisfying `P`, then a run. -/
  | head {c d e : Config} (hc : P c) (hs : M.Step x c d) (hr : Path P d e) : Path P c e

/-- The side condition of a segment: at most `B` cells, and a non-accepting control state. -/
def Quiet (B : ℕ) (c : Config) : Prop := c.space ≤ B ∧ M.accept c.state = false

/-- `M.Seg x B c c'`: a segment of a run — at least one step from `c` to `c'` on the input `x`,
every configuration strictly between the two ends fits in `B` cells and has a non-accepting
control state.  (The ends themselves are constrained separately by `Realizes`.) -/
def Seg (B : ℕ) (c c' : Config) : Prop := ∃ d, M.Step x c d ∧ M.Path x (M.Quiet B) d c'

variable {M x}

namespace Path

variable {P : Config → Prop}

theorem trans {a b c : Config} (h₁ : M.Path x P a b) (h₂ : M.Path x P b c) : M.Path x P a c := by
  induction h₁ with
  | refl => exact h₂
  | head hc hs _ ih => exact .head hc hs (ih h₂)

theorem single {a b : Config} (ha : P a) (h : M.Step x a b) : M.Path x P a b :=
  .head ha h (.refl b)

theorem mono {Q : Config → Prop} (hPQ : ∀ c, P c → Q c) {a b : Config} (h : M.Path x P a b) :
    M.Path x Q a b := by
  induction h with
  | refl => exact .refl _
  | head hc hs _ ih => exact .head (hPQ _ hc) hs ih

/-- A path is a walk of some length. -/
theorem exists_steps {a b : Config} (h : M.Path x P a b) : ∃ n, steps (M.Step x) n a b := by
  induction h with
  | refl c => exact ⟨0, rfl⟩
  | @head c d e _ hs _ ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨1 + n, (steps_add _ 1 n c e).2 ⟨d, (steps_one _ _ _).2 hs, hn⟩⟩

end Path

namespace Seg

variable {B : ℕ}

/-- Segments compose through a quiet configuration. -/
theorem trans {a b c : Config} (h₁ : M.Seg x B a b) (hb : M.Quiet B b) (h₂ : M.Seg x B b c) :
    M.Seg x B a c := by
  obtain ⟨d, hd, hp⟩ := h₁
  obtain ⟨e, he, hq⟩ := h₂
  exact ⟨d, hd, hp.trans (.head hb he hq)⟩

/-- One step is a segment. -/
theorem single {a b : Config} (h : M.Step x a b) : M.Seg x B a b := ⟨b, h, .refl b⟩

theorem mono {B' : ℕ} (hB : B ≤ B') {a b : Config} (h : M.Seg x B a b) : M.Seg x B' a b := by
  obtain ⟨d, hd, hp⟩ := h
  exact ⟨d, hd, hp.mono fun c hc => ⟨le_trans hc.1 hB, hc.2⟩⟩

end Seg

/-- A deterministic machine has at most one successor. -/
theorem step_det (hdet : M.Deterministic) {c d d' : Config} (h : M.Step x c d)
    (h' : M.Step x c d') : d = d' := by
  unfold Step stepList at h h'
  have hlen := hdet c.state x[c.inHead]? (c.tape.getD c.wHead false)
  generalize M.delta c.state x[c.inHead]? (c.tape.getD c.wHead false) = l at h h' hlen
  match l, hlen with
  | [], _ => simp at h
  | [t], _ =>
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at h h'
      rw [h, h']
  | _ :: _ :: _, hlen => simp at hlen

/-- A deterministic machine has at most one configuration at each distance from a given one. -/
theorem steps_det (hdet : M.Deterministic) {a : Config} :
    ∀ {n : ℕ} {b b' : Config}, steps (M.Step x) n a b → steps (M.Step x) n a b' → b = b' := by
  intro n
  induction n with
  | zero => rintro b b' rfl rfl; rfl
  | succ n ih =>
      rintro b b' ⟨m, hm, hb⟩ ⟨m', hm', hb'⟩
      obtain rfl := ih hm hm'
      exact step_det hdet hb hb'

/-- For a deterministic machine a longer run extends a shorter one from the same start. -/
theorem steps_prefix (hdet : M.Deterministic) {a b c : Config} {i j : ℕ}
    (hb : steps (M.Step x) i a b) (hc : steps (M.Step x) (i + j) a c) :
    steps (M.Step x) j b c := by
  obtain ⟨m, hm, hmc⟩ := (steps_add _ i j a c).1 hc
  obtain rfl := steps_det hdet hb hm
  exact hmc

end Machine

/-! ### The bridge -/

variable {σ : Type*}

/-- **The bridge statement.**  The offline machine `M` realizes the abstract machine `A` under the
encoding `code` of abstract states into configurations, within the bound `B x` on the input `x`,
when on every input:

* the encoding of the initial abstract state is the initial configuration;
* the encoding of a reachable abstract state fits in `B x` cells and has an accepting control
  state exactly when the abstract state is accepting;
* a reachable halting abstract state is encoded by a halting configuration;
* each step `s ↦ s'` from a reachable abstract state is carried out by a segment of `M` from the
  encoding of `s` to that of `s'`, all of whose intermediate configurations fit in `B x` cells and
  are non-accepting.

This is the only obligation of a client: it is the analogue, for space-bounded simulation, of the
bridge `Red t u ↔ Star Step t u` of `Start/Rewriting.lean`. -/
structure Realizes (M : Machine) (A : AbsMachine σ) (code : List Bool → σ → Config)
    (B : List Bool → ℕ) : Prop where
  /-- The initial abstract state is encoded by the initial configuration. -/
  start : ∀ x, code x (A.start x) = init
  /-- The encoding respects acceptance. -/
  accept : ∀ x s, A.Reaches x s → M.accept (code x s).state = A.accept s
  /-- The encoding respects the bound. -/
  space : ∀ x s, A.Reaches x s → (code x s).space ≤ B x
  /-- Halting abstract states are encoded by halting configurations. -/
  halt : ∀ x s, A.Reaches x s → A.step s = none → M.stepList x (code x s) = []
  /-- Each abstract step is carried out by a segment. -/
  step : ∀ x s s', A.Reaches x s → A.step s = some s' → M.Seg x (B x) (code x s) (code x s')

namespace Realizes

variable {M : Machine} {A : AbsMachine σ} {code : List Bool → σ → Config} {B : List Bool → ℕ}

/-- Every reachable abstract state is simulated: its encoding is reachable. -/
theorem reach_code (hR : Realizes M A code B) {x : List Bool} {s : σ} (hs : A.Reaches x s) :
    ∃ n, steps (M.Step x) n init (code x s) := by
  induction hs with
  | refl => exact ⟨0, (hR.start x).symm⟩
  | @tail t u ht htu ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨d, hd, hp⟩ := hR.step x t u ht htu
      obtain ⟨m, hm⟩ := hp.exists_steps
      refine ⟨n + (1 + m), (steps_add _ n (1 + m) _ _).2 ⟨code x t, hn, ?_⟩⟩
      exact (steps_add _ 1 m _ _).2 ⟨d, (steps_one _ _ _).2 hd, hm⟩

/-- **The run invariant.**  Every configuration the (deterministic) offline machine reaches is the
encoding of a reachable abstract state, or lies strictly inside the segment of a step taken from
one — in which case it is quiet. -/
theorem onRun (hR : Realizes M A code B) (hdet : M.Deterministic) {x : List Bool} :
    ∀ {n : ℕ} {c : Config}, steps (M.Step x) n init c →
      (∃ s, A.Reaches x s ∧ c = code x s) ∨ M.Quiet (B x) c := by
  -- the stronger invariant: an encoding, or a quiet configuration on a path to an encoding
  suffices H : ∀ {n : ℕ} {c : Config}, steps (M.Step x) n init c →
      (∃ s, A.Reaches x s ∧ c = code x s) ∨
        (M.Quiet (B x) c ∧ ∃ s', A.Reaches x s' ∧ M.Path x (M.Quiet (B x)) c (code x s')) by
    intro n c hc
    rcases H hc with h | ⟨hq, _⟩
    · exact Or.inl h
    · exact Or.inr hq
  -- entering a path towards `code x s'` at its first configuration `d`
  have enter : ∀ {d : Config} {s' : σ}, A.Reaches x s' →
      M.Path x (M.Quiet (B x)) d (code x s') →
      (∃ s, A.Reaches x s ∧ d = code x s) ∨
        (M.Quiet (B x) d ∧ ∃ s', A.Reaches x s' ∧ M.Path x (M.Quiet (B x)) d (code x s')) := by
    intro d s' hs' hp
    cases hp with
    | refl => exact Or.inl ⟨s', hs', rfl⟩
    | head hq hst hr => exact Or.inr ⟨hq, s', hs', .head hq hst hr⟩
  intro n
  induction n with
  | zero =>
      rintro c rfl
      exact Or.inl ⟨A.start x, AbsMachine.Reaches.start x, (hR.start x).symm⟩
  | succ n ih =>
      rintro c' ⟨c, hc, hstep⟩
      have encCase : ∀ s, A.Reaches x s → M.Step x (code x s) c' →
          (∃ s, A.Reaches x s ∧ c' = code x s) ∨
            (M.Quiet (B x) c' ∧
              ∃ s', A.Reaches x s' ∧ M.Path x (M.Quiet (B x)) c' (code x s')) := by
        intro s hs hst
        cases hA : A.step s with
        | none =>
            have hh := hR.halt x s hs hA
            simp [Machine.Step, hh] at hst
        | some s' =>
            obtain ⟨d, hd, hp⟩ := hR.step x s s' hs hA
            obtain rfl := Machine.step_det hdet hst hd
            exact enter (hs.tail hA) hp
      rcases ih hc with ⟨s, hs, rfl⟩ | ⟨_, s', hs', hp⟩
      · exact encCase s hs hstep
      · cases hp with
        | refl => exact encCase s' hs' hstep
        | head _ hst hr =>
            obtain rfl := Machine.step_det hdet hstep hst
            exact enter hs' hr

/-- **Acceptance is preserved**: the offline machine accepts exactly the inputs the abstract
machine accepts. -/
theorem accepts_iff (hR : Realizes M A code B) (hdet : M.Deterministic) (x : List Bool) :
    M.Accepts x ↔ A.Accepts x := by
  constructor
  · rintro ⟨n, c, hc, hacc⟩
    rcases hR.onRun hdet hc with ⟨s, hs, rfl⟩ | hq
    · exact ⟨s, hs, by rw [← hR.accept x s hs]; exact hacc⟩
    · rw [hq.2] at hacc
      exact absurd hacc (by simp)
  · rintro ⟨s, hs, hacc⟩
    obtain ⟨n, hn⟩ := hR.reach_code hs
    exact ⟨n, code x s, hn, by rw [hR.accept x s hs]; exact hacc⟩

/-- **The space bound**: on every input the offline machine stays within the bound. -/
theorem spaceBoundedOn (hR : Realizes M A code B) (hdet : M.Deterministic) (x : List Bool) :
    M.SpaceBoundedOn x (B x) := by
  intro n c hc
  rcases hR.onRun hdet hc with ⟨s, hs, rfl⟩ | hq
  · exact hR.space x s hs
  · exact hq.1

/-- **Membership in `DSPACE`**: when the offline machine is well formed and deterministic and the
bound depends only on the length of the input through `s`, the language of the abstract machine is
in `DSPACE s`. -/
theorem dspace (hR : Realizes M A code B) (hwf : M.WellFormed) (hdet : M.Deterministic)
    {s : ℕ → ℕ} (hB : ∀ x, B x ≤ s x.length) : DSPACE s A.Accepts :=
  ⟨M, hwf, hdet, fun x n c hc => le_trans (hR.spaceBoundedOn hdet x n c hc) (hB x),
    fun x => (hR.accepts_iff hdet x).symm⟩

/-- **Membership in `PSPACE`**: the same, with a polynomial bound. -/
theorem pspace (hR : Realizes M A code B) (hwf : M.WellFormed) (hdet : M.Deterministic)
    {s : ℕ → ℕ} (hs : PolyBound s) (hB : ∀ x, B x ≤ s x.length) : PSPACE A.Accepts :=
  ⟨s, hs, hR.dspace hwf hdet hB⟩

end Realizes

/-! ### The interface loses nothing -/

/-- A machine viewed as an abstract machine on its own configurations: its step is the unique
successor, if any. -/
def Machine.toAbs (M : Machine) : AbsMachine (List Bool × Config) where
  start x := (x, init)
  step p := ((M.stepList p.1 p.2).head?).map fun c => (p.1, c)
  accept p := M.accept p.2.state

/-- A machine running in space `s` realizes itself, viewed as an abstract machine,
under the identity encoding. -/
theorem realizes_self {M : Machine} {s : ℕ → ℕ} (hsp : M.SpaceBounded s) :
    Realizes M M.toAbs (fun _ p => p.2) (fun x => s x.length) := by
  have hreach : ∀ {x : List Bool} {p : List Bool × Config}, M.toAbs.Reaches x p →
      p.1 = x ∧ ∃ n, steps (M.Step x) n init p.2 := by
    intro x p hp
    induction hp with
    | refl => exact ⟨rfl, 0, rfl⟩
    | @tail q r _ hqr ih =>
        obtain ⟨hq1, n, hn⟩ := ih
        simp only [AbsMachine.StepRel, Machine.toAbs, Option.map_eq_some_iff] at hqr
        obtain ⟨c, hc, rfl⟩ := hqr
        refine ⟨hq1, n + 1, q.2, hn, ?_⟩
        rw [← hq1]
        exact List.mem_of_mem_head? hc
  refine ⟨fun _ => rfl, fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro x p hp
    obtain ⟨_, n, hn⟩ := hreach hp
    exact hsp x n p.2 hn
  · intro x p hp hstop
    obtain ⟨h1, -⟩ := hreach hp
    simp only [Machine.toAbs, Option.map_eq_none_iff, List.head?_eq_none_iff] at hstop
    rw [← h1]
    exact hstop
  · intro x p p' hp hpp'
    obtain ⟨h1, -⟩ := hreach hp
    simp only [Machine.toAbs, Option.map_eq_some_iff] at hpp'
    obtain ⟨c, hc, rfl⟩ := hpp'
    refine Machine.Seg.single ?_
    rw [← h1]
    exact List.mem_of_mem_head? hc

/-- `DSPACE` is exactly the class of languages of abstract machines realized, within the bound, by
a well-formed deterministic offline machine. -/
theorem dspace_iff_realizes (s : ℕ → ℕ) (L : Language) :
    DSPACE s L ↔ ∃ (σ : Type) (A : AbsMachine σ) (M : Machine) (code : List Bool → σ → Config),
      M.WellFormed ∧ M.Deterministic ∧ Realizes M A code (fun x => s x.length) ∧
        ∀ x, L x ↔ A.Accepts x := by
  constructor
  · rintro ⟨M, hwf, hdet, hsp, hL⟩
    have hR := realizes_self hsp
    exact ⟨_, M.toAbs, M, _, hwf, hdet, hR, fun x => (hL x).trans (hR.accepts_iff hdet x)⟩
  · rintro ⟨σ, A, M, code, hwf, hdet, hR, hL⟩
    obtain ⟨M', hwf', hdet', hsp', hL'⟩ := hR.dspace hwf hdet (s := s) fun _ => le_rfl
    exact ⟨M', hwf', hdet', hsp', fun x => (hL x).trans (hL' x)⟩

end Complexity.Space
