/-
**Space invariance of a run: the machine runs in the space of its live data.**

`Start/KrivineSpace.lean` measures the space of a state as the number of cells reachable from its
roots, and shows that the other cells can be removed without changing the run
(`Krivine.Impl.gcState`).  `Start/KrivineSpaceLog.lean` writes a collected state in binary, with
only a logarithmic overhead.  This module runs the machine *with a collection at every
transition* and puts the two together.

The point is that the heap of `Krivine.Impl.hrun` is a time measure: `Krivine.Impl.hstep` appends
a cell at every administrative transition and never frees one, so after `n` transitions it holds
`n` cells, most of them garbage.  The machine of this module, `Krivine.Impl.gstep`, holds exactly
its live data at every step, performs the same run, and is written in
`O((live cells + stack) · log)` bits.

Main definitions:

* `Krivine.Impl.gstep`, `Krivine.Impl.grun` — a transition followed by a collection, and the run;
* `Krivine.Impl.gpeak` — the peak memory of a collected run.

Main results:

* `Krivine.Impl.gstep_trans`, `Krivine.Impl.gstep_valid`, `Krivine.Impl.gstep_isNone_iff` — the
  collected machine **performs the same transitions**, keeps the invariant, and is stuck exactly
  when the machine is;
* `Krivine.Impl.gstep_heap_length` — after a transition the heap holds **exactly the live cells**
  of the state the transition produced;
* `Krivine.Impl.exists_grun_of_run` — every run of the abstract machine is performed by the
  collected implementation;
* `Krivine.Impl.gpeak_le`, `Krivine.Impl.heap_length_le_gpeak_of_grun` — the memory of every
  state of a run is bounded by the peak, itself at most the initial memory plus the number of
  transitions;
* `Krivine.Impl.encStateBin_length_le'` — a state occupies at most
  `(4 + |stack| + 3 · |heap|) · (w + 1)` bits;
* `Krivine.Impl.eval_impl_space` — **the space bound for an evaluation**, in the shape of the
  time bound `Krivine.Impl.eval_impl_cost`.

## Boundary

The peak is bounded here by the number of transitions.  Bounding it instead by a *space* cost
model of the λ-calculus — the Accattoli–Dal Lago–Vanoni programme, where the space of the
calculus is compared with the space of a Turing machine up to a logarithmic factor — needs a
space measure on the λ-terms themselves, which this library does not define.  What is proved
here is the machine half: the implementation keeps only live data, and pays only a logarithmic
factor to write it down.
-/

import Start.KrivineHeapCost
import Start.KrivineSpaceLog

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Krivine

namespace Impl

/-! ### The collected machine -/

/-- **One transition, followed by a collection.** -/
def gstep (tab : Tab) (s : HState) : Option (Label × HState) :=
  (hstep tab s).map fun ls => (ls.1, gcState ls.2)

/-- Running the collected implementation for `n` transitions. -/
def grun (tab : Tab) : ℕ → HState → Option HState
  | 0, s => some s
  | n + 1, s =>
      match gstep tab s with
      | none => none
      | some (_, s') => grun tab n s'

/-- The peak memory of a collected run. -/
def gpeak (tab : Tab) : ℕ → HState → ℕ
  | 0, s => s.heap.length
  | n + 1, s =>
      match gstep tab s with
      | none => s.heap.length
      | some (_, s') => max s.heap.length (gpeak tab n s')

theorem gstep_eq_some {tab : Tab} {s : HState} {l : Label} {s' : HState}
    (h : hstep tab s = some (l, s')) : gstep tab s = some (l, gcState s') := by
  simp [gstep, h]

theorem gstep_eq_none {tab : Tab} {s : HState} (h : hstep tab s = none) :
    gstep tab s = none := by
  simp [gstep, h]

theorem gstep_cases {tab : Tab} {s : HState} {l : Label} {s' : HState}
    (h : gstep tab s = some (l, s')) : ∃ u, hstep tab s = some (l, u) ∧ s' = gcState u := by
  rcases hcase : hstep tab s with _ | ⟨l', u⟩
  · rw [gstep_eq_none hcase] at h; exact absurd h (by simp)
  · rw [gstep_eq_some hcase] at h
    simp only [Option.some_inj, Prod.mk.injEq] at h
    obtain ⟨rfl, hs⟩ := h
    exact ⟨u, rfl, hs.symm⟩

/-- **The collected machine is stuck exactly when the machine is.** -/
theorem gstep_isNone_iff {tab : Tab} {s : HState} (hv : Valid tab s) :
    gstep tab s = none ↔ IsFinal (decState tab s) := by
  rw [← hstep_isNone_iff hv]
  constructor
  · intro h
    rcases hcase : hstep tab s with _ | ⟨l, u⟩
    · rfl
    · rw [gstep_eq_some hcase] at h; exact absurd h (by simp)
  · intro h
    exact gstep_eq_none h

/-- **The collected machine performs the transitions of the Krivine machine.** -/
theorem gstep_trans {tab : Tab} {s : HState} (hv : Valid tab s) {l : Label} {s' : HState}
    (h : gstep tab s = some (l, s')) : Trans l (decState tab s) (decState tab s') := by
  obtain ⟨u, hu, rfl⟩ := gstep_cases h
  rw [gcState_dec (hv.hstep hu)]
  exact hstep_trans hv hu

/-- The invariant survives a transition and the collection that follows it. -/
theorem gstep_valid {tab : Tab} {s : HState} (hv : Valid tab s) {l : Label} {s' : HState}
    (h : gstep tab s = some (l, s')) : Valid tab s' := by
  obtain ⟨u, hu, rfl⟩ := gstep_cases h
  exact gcState_valid (hv.hstep hu)

/-- **After a transition the heap holds exactly the live cells.** -/
theorem gstep_heap_length {tab : Tab} {s : HState} {l : Label} {s' : HState}
    (h : gstep tab s = some (l, s')) : ∃ u, hstep tab s = some (l, u) ∧ s'.heap.length = space u :=
  match gstep_cases h with
  | ⟨u, hu, hs⟩ => ⟨u, hu, by rw [hs, gcState_heap_length]⟩

/-- A transition of the collected machine adds at most one cell to the memory. -/
theorem gstep_heap_length_le {tab : Tab} {s : HState} (hv : Valid tab s) {l : Label}
    {s' : HState} (h : gstep tab s = some (l, s')) : s'.heap.length ≤ s.heap.length + 1 := by
  obtain ⟨u, hu, hlen⟩ := gstep_heap_length h
  have h1 : space u ≤ space s + 1 := space_hstep_le hv hu
  have h2 : space s ≤ s.heap.length := space_le_heap_length s
  omega

/-- A state is **collected** when its heap holds exactly the cells that are live: no garbage. -/
def Collected (s : HState) : Prop := s.heap.length = space s

/-- The initial state is collected: its heap is empty. -/
theorem collected_initState (t : Lambda) : Collected (initState t) := by
  rw [Collected, space_initState]
  simp [initState]

/-- **A transition of the collected machine produces a state with no garbage.** -/
theorem gstep_collected {tab : Tab} {s : HState} (hv : Valid tab s) {l : Label} {s' : HState}
    (h : gstep tab s = some (l, s')) : Collected s' := by
  obtain ⟨u, hu, rfl⟩ := gstep_cases h
  have hvu : Valid tab u := hv.hstep hu
  change (gcState u).heap.length = space (gcState u)
  rw [gcState_heap_length, space_gcState hvu]

/-! ### The run -/

/-- **Every run of the abstract machine is performed by the collected implementation.** -/
theorem exists_grun_of_run {tab : Tab} {s : HState} (hv : Valid tab s) :
    ∀ {n b : ℕ} {u : State}, Run n b (decState tab s) u →
      ∃ s₁, grun tab n s = some s₁ ∧ decState tab s₁ = u ∧ Valid tab s₁ := by
  intro n
  induction n generalizing s with
  | zero =>
      intro b u h
      cases h with
      | refl _ => exact ⟨s, rfl, rfl, hv⟩
  | succ n ih =>
      intro b u h
      cases h with
      | cons hstep0 hrest =>
          have hnotfinal : ¬ IsFinal (decState tab s) := fun hfin =>
            hfin _ (Step.of_trans hstep0)
          obtain ⟨⟨l', s'⟩, hcase⟩ : ∃ ls, gstep tab s = some ls := by
            cases hg : gstep tab s with
            | none => exact absurd ((gstep_isNone_iff hv).1 hg) hnotfinal
            | some ls => exact ⟨ls, rfl⟩
          have htr : Trans l' (decState tab s) (decState tab s') := gstep_trans hv hcase
          obtain ⟨-, hss⟩ := Trans.deterministic htr hstep0
          rw [← hss] at hrest
          have hv' : Valid tab s' := gstep_valid hv hcase
          obtain ⟨s₂, hrun', hdec', hv''⟩ := ih hv' hrest
          exact ⟨s₂, by simp [grun, hcase, hrun'], hdec', hv''⟩

/-- The peak of a run is at most the initial memory plus the number of transitions. -/
theorem gpeak_le {tab : Tab} : ∀ (n : ℕ) (s : HState), Valid tab s →
    gpeak tab n s ≤ s.heap.length + n := by
  intro n
  induction n with
  | zero => intro s _; simp [gpeak]
  | succ n ih =>
      intro s hv
      cases hcase : gstep tab s with
      | none => simp [gpeak, hcase]
      | some ls =>
          obtain ⟨l, s'⟩ := ls
          have hv' : Valid tab s' := gstep_valid hv hcase
          have hlen : s'.heap.length ≤ s.heap.length + 1 := gstep_heap_length_le hv hcase
          have := ih s' hv'
          simp only [gpeak, hcase]
          omega

/-- Every state of a run is bounded in memory by the peak of that run. -/
theorem heap_length_le_gpeak_of_grun {tab : Tab} : ∀ (n : ℕ) (s s₁ : HState),
    grun tab n s = some s₁ → s₁.heap.length ≤ gpeak tab n s := by
  intro n
  induction n with
  | zero =>
      intro s s₁ h
      simp only [grun, Option.some_inj] at h
      simp [gpeak, h]
  | succ n ih =>
      intro s s₁ h
      cases hcase : gstep tab s with
      | none => rw [grun, hcase] at h; exact absurd h (by simp)
      | some ls =>
          obtain ⟨l, s'⟩ := ls
          rw [grun, hcase] at h
          have := ih s' s₁ h
          simp only [gpeak, hcase]
          omega

/-- **Every state of a collected run holds exactly its live data.** -/
theorem grun_collected {tab : Tab} : ∀ (n : ℕ) (s s₁ : HState), Valid tab s → Collected s →
    grun tab n s = some s₁ → Collected s₁ := by
  intro n
  induction n with
  | zero =>
      intro s s₁ _ hc h
      simp only [grun, Option.some_inj] at h
      rwa [← h]
  | succ n ih =>
      intro s s₁ hv _ h
      cases hcase : gstep tab s with
      | none => rw [grun, hcase] at h; exact absurd h (by simp)
      | some ls =>
          obtain ⟨l, s'⟩ := ls
          rw [grun, hcase] at h
          exact ih s' s₁ (gstep_valid hv hcase) (gstep_collected hv hcase) h

/-! ### The memory of a state, in bits -/

/-- A state occupies at most `(4 + |stack| + 3 · |heap|) · (w + 1)` bits. -/
theorem encStateBin_length_le' (w : ℕ) (s : HState) :
    (encStateBin w s).length ≤ (4 + s.stack.length + 3 * s.heap.length) * (w + 1) := by
  rw [encStateBin_length]
  have key : (4 + s.stack.length + 3 * s.heap.length) * (w + 1)
      = (4 * w + 1 + s.stack.length * w + s.heap.length * (2 * w + 2))
        + (3 + s.stack.length + s.heap.length * w + s.heap.length) := by
    ring
  rw [key]
  exact Nat.le_add_right _ _

/-- **The space of an evaluation.**  If the weak head strategy normalises `t` in `k` steps then
the implementation collected at every transition, started on the encoding of `t`, runs to a stuck
state in `n` transitions, reaching the weak head normal form of `t`; at every point of that run
its heap holds exactly the cells that are live, its memory is bounded by the peak of the run,
which is at most the number of transitions, and writing the state down costs
`(4 + |stack| + 3 · |heap|) · (w + 1)` bits with `w` the number of bits of an address — the
logarithmic overhead. -/
theorem eval_impl_space {t : Lambda} {k : ℕ} (h : Lambda.WHNIn k t) :
    ∃ (n b : ℕ) (s : HState),
      grun (tabOf t) n (initState t) = some s ∧
      gstep (tabOf t) s = none ∧
      b ≤ k ∧ n ≤ b + Lambda.size t * (1 + b * (b + 1)) ∧
      Lambda.reducesIn b t (decState (tabOf t) s).decode ∧
      Lambda.IsWhnf (decState (tabOf t) s).decode ∧
      s.heap.length = space s ∧
      s.heap.length ≤ gpeak (tabOf t) n (initState t) ∧
      gpeak (tabOf t) n (initState t) ≤ n ∧
      (encStateBin (widthOf (tabOf t) s) s).length
        ≤ (4 + s.stack.length + 3 * s.heap.length) * (widthOf (tabOf t) s + 1) := by
  obtain ⟨n, b, u, hrunA, hfin, hbk, hnle, hred, hwhnf⟩ := eval_cost h
  have hv0 : Valid (tabOf t) (initState t) := valid_initState t
  have hdec0 : decState (tabOf t) (initState t) = State.init t := decState_initState t
  have hrunA' : Run n b (decState (tabOf t) (initState t)) u := by rw [hdec0]; exact hrunA
  obtain ⟨s, hrunI, hdec, hvs⟩ := exists_grun_of_run hv0 hrunA'
  have hpeak : gpeak (tabOf t) n (initState t) ≤ n := by
    have := gpeak_le n (initState t) hv0
    simpa [initState] using this
  refine ⟨n, b, s, hrunI, ?_, hbk, hnle, ?_, ?_,
    grun_collected n (initState t) s hv0 (collected_initState t) hrunI, ?_, hpeak,
    encStateBin_length_le' _ _⟩
  · rw [gstep_isNone_iff hvs, hdec]
    exact hfin
  · rw [hdec]; exact hred
  · rw [hdec]; exact hwhnf
  · exact heap_length_le_gpeak_of_grun n (initState t) s hrunI

end Impl

end Krivine
