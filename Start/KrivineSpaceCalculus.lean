/-
**A space measure on the states of the calculus, and the machine runs inside it.**

`Start/KrivineSpace.lean` measures the space of an implementation state as the number of heap
cells reachable from its roots, and `Start/KrivineSpaceRun.lean` runs the machine with a
collection at every transition, so that its heap holds exactly those cells.  What was missing was
a measure on the *calculus* side to compare that number with: the states of
`Start/Krivine.lean` are trees of closures, with no heap and no sharing, and nothing counted
their size.

This module supplies it and proves the comparison.  The space of a closure is the number of
nodes of the tree that writes it down — one for the closure itself, one for each cons of its
environment, recursively — and the space of a state is the space of its environment plus the
space of the closures on its stack.  The comparison is that **the implementation never holds
more cells than the state it represents has nodes**: sharing can only save.

Main definitions:

* `Krivine.Clos.cells`, `Krivine.envCells`, `Krivine.State.cells` — the space of a closure, of an
  environment and of a state of the calculus.

Main results:

* `Krivine.Impl.reach_length_le_cells` — the addresses reachable from a closure pointer are at
  most the nodes of the closure it decodes to, and likewise for environment pointers;
* `Krivine.Impl.space_le_cells_decState` — **the live cells of an implementation state are at
  most the nodes of the state it represents**;
* `Krivine.Impl.heap_length_le_cells_of_collected` — a collected state, which holds exactly its
  live cells, is bounded in the same way;
* `Krivine.Impl.gpeak_le_of_cells_le` — **the peak of a collected run is bounded by any bound on
  the space of the states of the calculus that the run passes through**;
* `Krivine.Impl.eval_impl_space_calculus` — the space bound for an evaluation, in the shape of
  `Krivine.Impl.eval_impl_space` but with the peak bounded by the calculus measure and the
  logarithmic factor for writing a state down.
-/

import Start.KrivineSpaceRun

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Krivine

/-! ### The space of a closure, of an environment, of a state -/

mutual

/-- The **space of a closure**: one node for the closure, and the space of its environment. -/
def Clos.cells : Clos → ℕ
  | Clos.mk _ e => 1 + envCells e

/-- The **space of an environment**: one node per cons, and the space of each closure in it. -/
def envCells : Env → ℕ
  | [] => 0
  | c :: e => 1 + Clos.cells c + envCells e

end

@[simp] theorem Clos.cells_mk (t : Lambda) (e : Env) : (Clos.mk t e).cells = 1 + envCells e := rfl
@[simp] theorem envCells_nil : envCells [] = 0 := rfl
@[simp] theorem envCells_cons (c : Clos) (e : Env) :
    envCells (c :: e) = 1 + c.cells + envCells e := rfl

/-- The **space of a state of the calculus**: its environment and the closures of its stack.
The code is not counted: it is a pointer into the program, not data the run builds. -/
def State.cells (s : State) : ℕ := envCells s.env + (s.stack.map Clos.cells).sum

@[simp] theorem State.cells_mk (t : Lambda) (e : Env) (π : List Clos) :
    State.cells ⟨t, e, π⟩ = envCells e + (π.map Clos.cells).sum := rfl

namespace Impl

/-! ### The reachable addresses are bounded by the nodes of the decoded data -/

/-- The joint bound for the two decoders, by strong induction on the address: what is reachable
from a closure pointer is bounded by the nodes of the closure it decodes to, and what is
reachable from a cons pointer by the nodes of the environment it decodes to. -/
private theorem reach_le_aux {tab : Tab} {hp : Heap} (hwf : HeapWF hp) (hty : HeapTyped tab hp) :
    ∀ p, p < hp.length → ∀ f, p < f →
      ((∃ c e, hp[p]? = some (Cell.clos c e)) →
        (reachF hp f p).length ≤ (decClF tab hp f p).cells) ∧
      ((∃ a t, hp[p]? = some (Cell.cons a t)) →
        (reachF hp f p).length ≤ envCells (decEnvF tab hp f (some p))) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hplt f hf
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
    have hcell : hp[p]? = some (hp[p]'hplt) := List.getElem?_eq_getElem hplt
    have hrefs : (hp[p]'hplt).refsLt p := hwf p hplt
    have htyp : CellTyped tab hp (hp[p]'hplt) := hty p hplt
    cases hcase : hp[p]'hplt with
    | clos c e =>
        rw [hcase] at hcell hrefs htyp
        refine ⟨fun _ => ?_, fun hcons => ?_⟩
        · rw [reachF_succ_eq hcell, decClF_clos_eq hcell]
          cases e with
          | none => simp [Cell.refs]
          | some j =>
              have hj : j < p := hrefs j rfl
              obtain ⟨a, t, hat⟩ := htyp.2 j rfl
              have hle := (ih j hj (lt_trans hj hplt) k (by omega)).2 ⟨a, t, hat⟩
              simp only [Cell.refs, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.length_cons, Clos.cells_mk]
              omega
        · obtain ⟨a, t, hat⟩ := hcons
          rw [hcell] at hat
          exact absurd hat (by simp)
    | cons a t =>
        rw [hcase] at hcell hrefs htyp
        obtain ⟨ha, ht⟩ := hrefs
        obtain ⟨ca, ea, hca⟩ := htyp.1
        have hlea := (ih a ha (lt_trans ha hplt) k (by omega)).1 ⟨ca, ea, hca⟩
        refine ⟨fun hclos => ?_, fun _ => ?_⟩
        · obtain ⟨c, e, hce⟩ := hclos
          rw [hcell] at hce
          exact absurd hce (by simp)
        · rw [reachF_succ_eq hcell, decEnvF_cons_eq hcell]
          cases t with
          | none =>
              simp only [Cell.refs, Option.toList_none, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.length_cons, envCells_cons, decEnvF_none, envCells_nil]
              omega
          | some j =>
              have hj : j < p := ht j rfl
              obtain ⟨b, u, hbu⟩ := htyp.2 j rfl
              have hlet := (ih j hj (lt_trans hj hplt) k (by omega)).2 ⟨b, u, hbu⟩
              simp only [Cell.refs, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.length_cons, List.length_append, envCells_cons]
              omega

/-- **What is reachable from a closure pointer is bounded by the nodes of its closure.** -/
theorem reach_length_le_cells {tab : Tab} {hp : Heap} (hwf : HeapWF hp) (hty : HeapTyped tab hp)
    {p : ℕ} (hcl : IsClosPtr hp p) : (reach hp p).length ≤ (decClos tab hp p).cells := by
  obtain ⟨c, e, hce⟩ := hcl
  have hplt : p < hp.length := lt_length_of_getElem? hce
  exact (reach_le_aux hwf hty p hplt hp.length hplt).1 ⟨c, e, hce⟩

/-- **What is reachable from an environment pointer is bounded by the nodes of its
environment.** -/
theorem reach_length_le_envCells {tab : Tab} {hp : Heap} (hwf : HeapWF hp)
    (hty : HeapTyped tab hp) {p : ℕ} (hcons : ∃ a t, hp[p]? = some (Cell.cons a t)) :
    (reach hp p).length ≤ envCells (decEnvP tab hp (some p)) := by
  obtain ⟨a, t, hat⟩ := hcons
  have hplt : p < hp.length := lt_length_of_getElem? hat
  exact (reach_le_aux hwf hty p hplt hp.length hplt).2 ⟨a, t, hat⟩

/-! ### The live cells of a state are bounded by the nodes of the state it represents -/

/-- **The live cells of an implementation state are at most the nodes of the state of the
calculus it represents**: sharing can only save. -/
theorem space_le_cells_decState {tab : Tab} {s : HState} (hv : Valid tab s) :
    space s ≤ State.cells (decState tab s) := by
  have hnodup : (liveList s).Nodup := (List.nodup_range).filter _
  have hsub : liveList s ⊆ reachRoots s := by
    intro a ha
    have h1 : a ∈ (List.range s.heap.length).filter (IsLive s) := ha
    have h2 : IsLive s a := (List.mem_filter.1 h1).2
    simpa [IsLive] using h2
  have hlen : space s ≤ (reachRoots s).length :=
    (List.subperm_of_subset hnodup hsub).length_le
  have hstack : ((s.stack.map (fun p => (reach s.heap p).length)).sum)
      ≤ ((s.stack.map (fun p => (decClos tab s.heap p).cells)).sum) := by
    refine List.sum_le_sum ?_
    intro p hp
    exact reach_length_le_cells hv.heapWF hv.heapTyped (hv.stack_ty p hp)
  have henv : ((s.env.toList.flatMap (reach s.heap)).length)
      ≤ envCells (decEnvP tab s.heap s.env) := by
    cases hcase : s.env with
    | none => simp
    | some j =>
        have hj : IsEnvPtr s.heap (some j) := by rw [← hcase]; exact hv.env_ty
        obtain ⟨a, t, hat⟩ := hj j rfl
        simpa using reach_length_le_envCells hv.heapWF hv.heapTyped ⟨a, t, hat⟩
  have hsplit : (reachRoots s).length
      = (s.env.toList.flatMap (reach s.heap)).length
        + ((s.stack.map (fun p => (reach s.heap p).length)).sum) := by
    simp [reachRoots, roots, List.flatMap_append, List.length_flatMap]
  have hcells : State.cells (decState tab s)
      = envCells (decEnvP tab s.heap s.env)
        + ((s.stack.map (fun p => (decClos tab s.heap p).cells)).sum) := by
    simp [State.cells, decState, List.map_map, Function.comp_def]
  omega

/-- A collected state holds exactly its live cells, so its heap is bounded by the nodes of the
state it represents. -/
theorem heap_length_le_cells_of_collected {tab : Tab} {s : HState} (hv : Valid tab s)
    (hc : Collected s) : s.heap.length ≤ State.cells (decState tab s) := by
  rw [hc]
  exact space_le_cells_decState hv

/-! ### The peak of a collected run -/

/-- **The peak of a collected run is bounded by any bound on the space of the states of the
calculus it passes through.** -/
theorem gpeak_le_of_cells_le {tab : Tab} : ∀ (n : ℕ) (s : HState), Valid tab s → Collected s →
    ∀ m : ℕ, (∀ (i : ℕ) (u : HState), i ≤ n → grun tab i s = some u →
      State.cells (decState tab u) ≤ m) → gpeak tab n s ≤ m := by
  intro n
  induction n with
  | zero =>
      intro s hv hc m hm
      have := hm 0 s (le_refl 0) rfl
      simpa [gpeak] using le_trans (heap_length_le_cells_of_collected hv hc) this
  | succ n ih =>
      intro s hv hc m hm
      have h0 : s.heap.length ≤ m :=
        le_trans (heap_length_le_cells_of_collected hv hc) (hm 0 s (Nat.zero_le _) rfl)
      cases hstep : gstep tab s with
      | none => simpa [gpeak, hstep] using h0
      | some ls =>
          obtain ⟨l, s'⟩ := ls
          have hv' : Valid tab s' := gstep_valid hv hstep
          have hc' : Collected s' := gstep_collected hv hstep
          have hrest : ∀ (i : ℕ) (u : HState), i ≤ n → grun tab i s' = some u →
              State.cells (decState tab u) ≤ m := by
            intro i u hi hu
            exact hm (i + 1) u (by omega) (by simp [grun, hstep, hu])
          have := ih s' hv' hc' m hrest
          simp only [gpeak, hstep]
          omega

/-! ### The space of an evaluation, measured on the calculus -/

/-- **The space of an evaluation, measured on the calculus.**  If the weak head strategy
normalises `t` in `k` steps then the implementation collected at every transition runs to a
stuck state in `n` transitions, reaching the weak head normal form of `t`; at every point its
heap holds exactly the cells that are live, its memory is at most the number of nodes of the
state of the calculus it represents, the peak of the run is bounded by any bound on those
numbers along the run, and writing a state down costs
`(4 + |stack| + 3 · |heap|) · (w + 1)` bits — the logarithmic overhead. -/
theorem eval_impl_space_calculus {t : Lambda} {k : ℕ} (h : Lambda.WHNIn k t) :
    ∃ (n b : ℕ) (s : HState),
      grun (tabOf t) n (initState t) = some s ∧
      gstep (tabOf t) s = none ∧
      b ≤ k ∧ n ≤ b + Lambda.size t * (1 + b * (b + 1)) ∧
      Lambda.reducesIn b t (decState (tabOf t) s).decode ∧
      Lambda.IsWhnf (decState (tabOf t) s).decode ∧
      s.heap.length = space s ∧
      s.heap.length ≤ State.cells (decState (tabOf t) s) ∧
      (∀ m : ℕ, (∀ (i : ℕ) (u : HState), i ≤ n → grun (tabOf t) i (initState t) = some u →
          State.cells (decState (tabOf t) u) ≤ m) → gpeak (tabOf t) n (initState t) ≤ m) ∧
      (encStateBin (widthOf (tabOf t) s) s).length
        ≤ (4 + s.stack.length + 3 * s.heap.length) * (widthOf (tabOf t) s + 1) := by
  obtain ⟨n, b, u, hrunA, hfin, hbk, hnle, hred, hwhnf⟩ := eval_cost h
  have hv0 : Valid (tabOf t) (initState t) := valid_initState t
  have hdec0 : decState (tabOf t) (initState t) = State.init t := decState_initState t
  have hrunA' : Run n b (decState (tabOf t) (initState t)) u := by rw [hdec0]; exact hrunA
  obtain ⟨s, hrunI, hdec, hvs⟩ := exists_grun_of_run hv0 hrunA'
  have hcoll : Collected s :=
    grun_collected n (initState t) s hv0 (collected_initState t) hrunI
  refine ⟨n, b, s, hrunI, ?_, hbk, hnle, ?_, ?_, hcoll, ?_, ?_,
    encStateBin_length_le' _ _⟩
  · rw [gstep_isNone_iff hvs, hdec]
    exact hfin
  · rw [hdec]; exact hred
  · rw [hdec]; exact hwhnf
  · exact heap_length_le_cells_of_collected hvs hcoll
  · exact fun m hm => gpeak_le_of_cells_le n (initState t) hv0 (collected_initState t) m hm

end Impl

end Krivine
