/-
**Garbage collection for the shared implementation of the Krivine machine.**

`Start/KrivineSpace.lean` measures the space of a state as the number of cells reachable from its
roots, and proves that nothing else is ever read.  This module removes the other cells.

Collection keeps the live cells in their original order and renames every reference to the
**rank** of the address it points at (`Krivine.Impl.rankIn`), so that the heap of the collected
state has exactly one cell per live address.

Main definitions:

* `Krivine.Impl.Cell.reloc`, `Krivine.Impl.Closed`, `Krivine.Impl.gcHeap` — renaming a cell, a
  selection of addresses closed under references, and the collected heap;
* `Krivine.Impl.gcState` — the collected state.

Main results:

* `Krivine.Impl.gcHeap_wf`, `Krivine.Impl.gcHeap_typed` — the collected heap is again an acyclic,
  well-typed graph;
* `Krivine.Impl.decClos_gcHeap`, `Krivine.Impl.decEnvP_gcHeap`, `Krivine.Impl.gcState_dec` —
  **collection preserves what the heap says**, hence the state the implementation represents;
* `Krivine.Impl.gcState_valid` — it preserves the invariant;
* `Krivine.Impl.gcState_heap_length` — the collected heap has exactly `Krivine.Impl.space` cells;
* `Krivine.Impl.mem_reach_gcHeap`, `Krivine.Impl.space_gcState` — **collection loses nothing**:
  reachability survives the renaming, so the collected state has the same space.
-/

import Start.KrivineSpace

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Krivine

namespace Impl

/-! ### Garbage collection -/

/-- Renaming the references of a cell. -/
def Cell.reloc (f : ℕ → ℕ) : Cell → Cell
  | Cell.clos c e => Cell.clos c (e.map f)
  | Cell.cons a t => Cell.cons (f a) (t.map f)

@[simp] theorem Cell.reloc_clos (f : ℕ → ℕ) (c : ℕ) (e : Option ℕ) :
    Cell.reloc f (Cell.clos c e) = Cell.clos c (e.map f) := rfl

@[simp] theorem Cell.reloc_cons (f : ℕ → ℕ) (a : ℕ) (t : Option ℕ) :
    Cell.reloc f (Cell.cons a t) = Cell.cons (f a) (t.map f) := rfl

/-- The references of a cell bound its `Krivine.Impl.Cell.refsLt`. -/
theorem Cell.refsLt_of_refs {c : Cell} {k : ℕ} (h : ∀ b ∈ c.refs, b < k) : c.refsLt k := by
  cases c with
  | clos c e => intro j hj; exact h j (by simpa using hj)
  | cons a t => exact ⟨h a (by simp), fun j hj =>
      h j (List.mem_cons_of_mem _ (Option.mem_toList.2 hj))⟩

@[simp] theorem Cell.refs_reloc (f : ℕ → ℕ) (c : Cell) :
    (Cell.reloc f c).refs = c.refs.map f := by
  cases c with
  | clos c e => cases e <;> simp
  | cons a t => cases t <;> simp

/-- **The collected heap**: the selected cells, in their original order, with every reference
renamed to the rank of the address it points at. -/
def gcHeap (P : ℕ → Bool) (hp : Heap) : Heap :=
  (upto P hp.length).map fun a => Cell.reloc (rankIn P) ((hp[a]?).getD (Cell.clos 0 none))

@[simp] theorem gcHeap_length (P : ℕ → Bool) (hp : Heap) :
    (gcHeap P hp).length = (upto P hp.length).length := by
  simp [gcHeap]

/-- A selected cell is found in the collected heap at its rank. -/
theorem getElem?_gcHeap {P : ℕ → Bool} {hp : Heap} {a : ℕ} {c : Cell} (hPa : P a)
    (hc : hp[a]? = some c) :
    (gcHeap P hp)[rankIn P a]? = some (Cell.reloc (rankIn P) c) := by
  have ha : a < hp.length := lt_length_of_getElem? hc
  rw [gcHeap, List.getElem?_map, getElem?_upto_rankIn ha hPa]
  simp [hc]

/-- Every cell of the collected heap comes from a selected cell of the original one. -/
theorem getElem?_gcHeap_eq {P : ℕ → Bool} {hp : Heap} {k : ℕ} {d : Cell}
    (h : (gcHeap P hp)[k]? = some d) :
    ∃ a c, P a ∧ hp[a]? = some c ∧ rankIn P a = k ∧ d = Cell.reloc (rankIn P) c := by
  rw [gcHeap, List.getElem?_map] at h
  obtain ⟨a, ha, hd⟩ := Option.map_eq_some_iff.1 h
  have hmem : a ∈ upto P hp.length := List.mem_of_getElem? ha
  rw [mem_upto] at hmem
  obtain ⟨halt, hPa⟩ := hmem
  refine ⟨a, hp[a]'halt, hPa, List.getElem?_eq_getElem halt, rankIn_of_getElem? ha, ?_⟩
  rw [← hd, List.getElem?_eq_getElem halt]
  rfl

/-- The collected heap is acyclic. -/
theorem gcHeap_wf {P : ℕ → Bool} {hp : Heap} (hwf : HeapWF hp) (hcl : Closed P hp) :
    HeapWF (gcHeap P hp) := by
  intro k hk
  obtain ⟨a, c, hPa, hc, hrank, hd⟩ :=
    getElem?_gcHeap_eq (P := P) (hp := hp) (k := k) (List.getElem?_eq_getElem hk)
  have halt : a < hp.length := lt_length_of_getElem? hc
  have hcase : (hp[a]'halt) = c := by
    have := List.getElem?_eq_getElem halt
    rw [this] at hc
    exact Option.some_inj.1 hc
  have hrefs : c.refsLt a := by
    have := hwf a halt
    rwa [hcase] at this
  rw [hd]
  refine Cell.refsLt_of_refs ?_
  intro b hb
  rw [Cell.refs_reloc] at hb
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  have hblt : b' < a := Cell.refs_lt hrefs b' hb'
  have hPb : P b' := hcl a c halt hPa hc b' hb'
  rw [← hrank]
  exact rankIn_lt_rankIn hPb hblt

/-- The collected heap is well typed. -/
theorem gcHeap_typed {tab : Tab} {P : ℕ → Bool} {hp : Heap} (hty : HeapTyped tab hp)
    (hcl : Closed P hp) : HeapTyped tab (gcHeap P hp) := by
  intro k hk
  obtain ⟨a, c, hPa, hc, hrank, hd⟩ :=
    getElem?_gcHeap_eq (P := P) (hp := hp) (k := k) (List.getElem?_eq_getElem hk)
  have halt : a < hp.length := lt_length_of_getElem? hc
  have hcase : (hp[a]'halt) = c := by
    have := List.getElem?_eq_getElem halt
    rw [this] at hc
    exact Option.some_inj.1 hc
  have hcty : CellTyped tab hp c := by
    have := hty a halt
    rwa [hcase] at this
  -- a selected pointer of `c` keeps its kind in the collected heap
  have henv : ∀ e : Option ℕ, (∀ j ∈ e, j ∈ c.refs) → IsEnvPtr hp e →
      IsEnvPtr (gcHeap P hp) (e.map (rankIn P)) := by
    intro e hmem hety j hj
    obtain ⟨j', hj', rfl⟩ : ∃ j', j' ∈ e ∧ rankIn P j' = j := by
      cases e with
      | none => simp at hj
      | some i => exact ⟨i, rfl, by simpa using hj⟩
    obtain ⟨x, t, hx⟩ := hety j' hj'
    have hPj : P j' := hcl a c halt hPa hc j' (hmem j' hj')
    exact ⟨rankIn P x, t.map (rankIn P), by rw [getElem?_gcHeap hPj hx]; rfl⟩
  have hclos : ∀ x : ℕ, x ∈ c.refs → IsClosPtr hp x →
      IsClosPtr (gcHeap P hp) (rankIn P x) := by
    intro x hx hcty'
    obtain ⟨code, e, hcell⟩ := hcty'
    have hPx : P x := hcl a c halt hPa hc x hx
    exact ⟨code, e.map (rankIn P), by rw [getElem?_gcHeap hPx hcell]; rfl⟩
  rw [hd]
  cases c with
  | clos code e =>
      exact ⟨hcty.1, henv e (fun j hj => by simpa using hj) hcty.2⟩
  | cons x t =>
      exact ⟨hclos x (by simp) hcty.1,
        henv t (fun j hj => List.mem_cons_of_mem _ (Option.mem_toList.2 hj)) hcty.2⟩

/-- The joint statement: collection preserves what the heap says. -/
private theorem dec_gc_aux {tab : Tab} {P : ℕ → Bool} {hp : Heap} (hwf : HeapWF hp)
    (hcl : Closed P hp) :
    ∀ a, P a → ∀ c, hp[a]? = some c →
      decClos tab (gcHeap P hp) (rankIn P a) = decClos tab hp a ∧
        decEnvP tab (gcHeap P hp) (some (rankIn P a)) = decEnvP tab hp (some a) := by
  have hgcwf : HeapWF (gcHeap P hp) := gcHeap_wf hwf hcl
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro hPa c hc
    have halt : a < hp.length := lt_length_of_getElem? hc
    have hcase : (hp[a]'halt) = c := by
      have := List.getElem?_eq_getElem halt
      rw [this] at hc
      exact Option.some_inj.1 hc
    have hrefs : c.refsLt a := by
      have := hwf a halt
      rwa [hcase] at this
    have hgc : (gcHeap P hp)[rankIn P a]? = some (Cell.reloc (rankIn P) c) :=
      getElem?_gcHeap hPa hc
    -- the recursive call, on a reference of the cell
    have hrec : ∀ b ∈ c.refs,
        decClos tab (gcHeap P hp) (rankIn P b) = decClos tab hp b ∧
          decEnvP tab (gcHeap P hp) (some (rankIn P b)) = decEnvP tab hp (some b) := by
      intro b hb
      have hblt : b < a := Cell.refs_lt hrefs b hb
      have hPb : P b := hcl a c halt hPa hc b hb
      exact ih b hblt hPb _ (List.getElem?_eq_getElem (lt_trans hblt halt))
    cases c with
    | clos code e =>
        have henv : decEnvP tab (gcHeap P hp) (e.map (rankIn P)) = decEnvP tab hp e := by
          cases e with
          | none => simp
          | some j => exact (hrec j (by simp)).2
        refine ⟨?_, ?_⟩
        · rw [decClos_clos hgcwf (by simpa using hgc), decClos_clos hwf hc, henv]
        · rw [decEnvP_of_clos (by simpa using hgc), decEnvP_of_clos hc]
    | cons x t =>
        have hx : decClos tab (gcHeap P hp) (rankIn P x) = decClos tab hp x :=
          (hrec x (by simp)).1
        have ht : decEnvP tab (gcHeap P hp) (t.map (rankIn P)) = decEnvP tab hp t := by
          cases t with
          | none => simp
          | some j => exact (hrec j (by simp)).2
        refine ⟨?_, ?_⟩
        · rw [decClos_of_cons (by simpa using hgc), decClos_of_cons hc]
        · rw [decEnvP_cons hgcwf (by simpa using hgc), decEnvP_cons hwf hc, hx, ht]

/-- **Collection preserves the closure at a selected address.** -/
theorem decClos_gcHeap {tab : Tab} {P : ℕ → Bool} {hp : Heap} (hwf : HeapWF hp)
    (hcl : Closed P hp) {a : ℕ} {c : Cell} (hPa : P a) (hc : hp[a]? = some c) :
    decClos tab (gcHeap P hp) (rankIn P a) = decClos tab hp a :=
  (dec_gc_aux hwf hcl a hPa c hc).1

/-- **Collection preserves the environment at a selected address.** -/
theorem decEnvP_gcHeap {tab : Tab} {P : ℕ → Bool} {hp : Heap} (hwf : HeapWF hp)
    (hcl : Closed P hp) {a : ℕ} {c : Cell} (hPa : P a) (hc : hp[a]? = some c) :
    decEnvP tab (gcHeap P hp) (some (rankIn P a)) = decEnvP tab hp (some a) :=
  (dec_gc_aux hwf hcl a hPa c hc).2

/-! ### Collecting a state -/

/-- **The collected state**: the same code, the pointers renamed to the ranks of the addresses
they point at, and the heap reduced to its live cells. -/
def gcState (s : HState) : HState :=
  ⟨s.code, s.env.map (rankIn (IsLive s)), s.stack.map (rankIn (IsLive s)),
    gcHeap (IsLive s) s.heap⟩

@[simp] theorem gcState_code (s : HState) : (gcState s).code = s.code := rfl

@[simp] theorem gcState_env (s : HState) :
    (gcState s).env = s.env.map (rankIn (IsLive s)) := rfl

@[simp] theorem gcState_stack (s : HState) :
    (gcState s).stack = s.stack.map (rankIn (IsLive s)) := rfl

@[simp] theorem gcState_heap (s : HState) :
    (gcState s).heap = gcHeap (IsLive s) s.heap := rfl

/-- **The collected heap has exactly one cell per live address.** -/
@[simp] theorem gcState_heap_length (s : HState) : (gcState s).heap.length = space s := by
  simp [space, liveList]

/-- A pointer of the collected state is the rank of a pointer of the original one. -/
theorem mem_gcState_env {s : HState} {j : ℕ} (hj : j ∈ (gcState s).env) :
    ∃ i ∈ s.env, rankIn (IsLive s) i = j := by
  cases henv : s.env with
  | none => rw [gcState_env, henv] at hj; simp at hj
  | some i =>
      refine ⟨i, rfl, ?_⟩
      rw [gcState_env, henv] at hj
      simpa using hj

/-- **Collection does not change the state the implementation represents.** -/
theorem gcState_dec {tab : Tab} {s : HState} (hv : Valid tab s) :
    decState tab (gcState s) = decState tab s := by
  have hcl : Closed (IsLive s) s.heap := isLive_closed hv.heapWF
  have henv : decEnvP tab (gcHeap (IsLive s) s.heap) (s.env.map (rankIn (IsLive s)))
      = decEnvP tab s.heap s.env := by
    cases he : s.env with
    | none => simp
    | some j =>
        obtain ⟨x, t, hx⟩ := hv.env_ty j (by rw [he]; rfl)
        have hlive : IsLive s j := isLive_root (mem_roots_env (s := s) he) hx
        simpa using decEnvP_gcHeap hv.heapWF hcl hlive hx
  have hstack : (s.stack.map (rankIn (IsLive s))).map (decClos tab (gcHeap (IsLive s) s.heap))
      = s.stack.map (decClos tab s.heap) := by
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro p hp
    obtain ⟨code, e, hcell⟩ := hv.stack_ty p hp
    have hlive : IsLive s p := isLive_root (mem_roots_stack hp) hcell
    exact decClos_gcHeap hv.heapWF hcl hlive hcell
  simp only [decState, gcState_code, gcState_env, gcState_stack, gcState_heap, henv, hstack]

/-- **Collection preserves the invariant.** -/
theorem gcState_valid {tab : Tab} {s : HState} (hv : Valid tab s) : Valid tab (gcState s) := by
  have hcl : Closed (IsLive s) s.heap := isLive_closed hv.heapWF
  have henv : ∀ j ∈ (gcState s).env, ∃ i x t, i ∈ s.env ∧ rankIn (IsLive s) i = j ∧
      IsLive s i ∧ s.heap[i]? = some (Cell.cons x t) := by
    intro j hj
    obtain ⟨i, hi, hrank⟩ := mem_gcState_env hj
    obtain ⟨x, t, hx⟩ := hv.env_ty i hi
    exact ⟨i, x, t, hi, hrank, isLive_root (mem_roots_env (s := s) hi) hx, hx⟩
  have hstack : ∀ j ∈ (gcState s).stack, ∃ i code e, i ∈ s.stack ∧ rankIn (IsLive s) i = j ∧
      IsLive s i ∧ s.heap[i]? = some (Cell.clos code e) := by
    intro j hj
    obtain ⟨i, hi, hrank⟩ := List.mem_map.1 hj
    obtain ⟨code, e, hcell⟩ := hv.stack_ty i hi
    exact ⟨i, code, e, hi, hrank, isLive_root (mem_roots_stack hi) hcell, hcell⟩
  refine ⟨hv.tabWF, hv.code_lt, gcHeap_wf hv.heapWF hcl, gcHeap_typed hv.heapTyped hcl, ?_, ?_,
    ?_, ?_⟩
  · intro j hj
    obtain ⟨i, x, t, _, hrank, hlive, _⟩ := henv j hj
    rw [gcState_heap_length, ← hrank]
    exact rankIn_lt_space hlive
  · intro j hj
    obtain ⟨i, x, t, _, hrank, hlive, hx⟩ := henv j hj
    refine ⟨rankIn (IsLive s) x, t.map (rankIn (IsLive s)), ?_⟩
    rw [gcState_heap, ← hrank, getElem?_gcHeap hlive hx]
    rfl
  · intro j hj
    obtain ⟨i, code, e, _, hrank, hlive, _⟩ := hstack j hj
    rw [gcState_heap_length, ← hrank]
    exact rankIn_lt_space hlive
  · intro j hj
    obtain ⟨i, code, e, _, hrank, hlive, hcell⟩ := hstack j hj
    refine ⟨code, e.map (rankIn (IsLive s)), ?_⟩
    rw [gcState_heap, ← hrank, getElem?_gcHeap hlive hcell]
    rfl

/-- Collection does not increase the space: the collected heap holds exactly the live cells. -/
theorem space_gcState_le {s : HState} : space (gcState s) ≤ space s := by
  have h := space_le_heap_length (gcState s)
  rwa [gcState_heap_length] at h

/-! ### Collection does not lose live cells -/

/-- **Collection preserves reachability**, through the renaming of the addresses. -/
theorem mem_reach_gcHeap {P : ℕ → Bool} {hp : Heap} (hwf : HeapWF hp) (hcl : Closed P hp) :
    ∀ p, P p → ∀ b ∈ reach hp p, rankIn P b ∈ reach (gcHeap P hp) (rankIn P p) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hPp b hb
    cases hc : hp[p]? with
    | none => rw [reach_eq_nil hc] at hb; simp at hb
    | some c =>
        have halt : p < hp.length := lt_length_of_getElem? hc
        have hcase : (hp[p]'halt) = c := by
          have := List.getElem?_eq_getElem halt
          rw [this] at hc
          exact Option.some_inj.1 hc
        have hrefs : c.refsLt p := by
          have := hwf p halt
          rwa [hcase] at this
        have hgc : (gcHeap P hp)[rankIn P p]? = some (Cell.reloc (rankIn P) c) :=
          getElem?_gcHeap hPp hc
        rw [reach_eq hwf hc] at hb
        rw [reach_eq (gcHeap_wf hwf hcl) hgc]
        rcases List.mem_cons.1 hb with rfl | hb
        · exact List.mem_cons_self ..
        · obtain ⟨x, hx, hbx⟩ := List.mem_flatMap.1 hb
          have hxlt : x < p := Cell.refs_lt hrefs x hx
          have hPx : P x := hcl p c halt hPp hc x hx
          refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨rankIn P x, ?_, ih x hxlt hPx b hbx⟩)
          rw [Cell.refs_reloc]
          exact List.mem_map_of_mem hx

/-- A root of a valid state is live. -/
theorem isLive_of_mem_roots {tab : Tab} {s : HState} (hv : Valid tab s) {p : ℕ}
    (hp : p ∈ roots s) : IsLive s p := by
  rcases List.mem_append.1 hp with hpe | hps
  · obtain ⟨x, t, hx⟩ := hv.env_ty p (Option.mem_toList.1 hpe)
    exact isLive_root hp hx
  · obtain ⟨code, e, hcell⟩ := hv.stack_ty p hps
    exact isLive_root hp hcell

/-- The rank of a root is a root of the collected state. -/
theorem mem_roots_gcState {s : HState} {p : ℕ} (hp : p ∈ roots s) :
    rankIn (IsLive s) p ∈ roots (gcState s) := by
  rcases List.mem_append.1 hp with hpe | hps
  · refine mem_roots_env (s := gcState s) ?_
    rw [gcState_env]
    exact Option.mem_map_of_mem _ (Option.mem_toList.1 hpe)
  · exact mem_roots_stack (by rw [gcState_stack]; exact List.mem_map_of_mem hps)

/-- **Collection loses nothing**: the collected state has exactly as many live cells. -/
theorem space_gcState {tab : Tab} {s : HState} (hv : Valid tab s) :
    space (gcState s) = space s := by
  refine le_antisymm space_gcState_le ?_
  have hcl : Closed (IsLive s) s.heap := isLive_closed hv.heapWF
  have hmap : ∀ a ∈ liveList s, rankIn (IsLive s) a ∈ liveList (gcState s) := by
    intro a ha
    rw [liveList, mem_upto] at ha
    obtain ⟨-, hlive⟩ := ha
    obtain ⟨p, hp, hap⟩ := isLive_iff.1 hlive
    rw [liveList, mem_upto]
    refine ⟨by rw [gcState_heap_length]; exact rankIn_lt_space hlive, ?_⟩
    exact isLive_iff.2 ⟨rankIn (IsLive s) p, mem_roots_gcState hp,
      mem_reach_gcHeap hv.heapWF hcl p (isLive_of_mem_roots hv hp) a hap⟩
  have hinj : ∀ x ∈ liveList s, ∀ y ∈ liveList s,
      rankIn (IsLive s) x = rankIn (IsLive s) y → x = y := by
    intro x hx y hy hxy
    rw [liveList, mem_upto] at hx hy
    by_contra hne
    rcases Nat.lt_or_ge x y with hlt | hge
    · have := rankIn_lt_rankIn (P := IsLive s) hx.2 hlt
      omega
    · have hlt : y < x := by omega
      have := rankIn_lt_rankIn (P := IsLive s) hy.2 hlt
      omega
  have hnd : ((liveList s).map (rankIn (IsLive s))).Nodup :=
    (List.nodup_range.filter _).map_on hinj
  have hsub : (liveList s).map (rankIn (IsLive s)) ⊆ liveList (gcState s) := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hj
    exact hmap a ha
  have hlen := hnd.length_le_of_subset hsub
  simpa [space] using hlen

end Impl

end Krivine
