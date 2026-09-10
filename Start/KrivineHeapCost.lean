/-
**The cost of running the shared implementation of the Krivine machine.**

`Start/KrivineHeap.lean` implements the machine on a code table and a heap, and proves that the
implementation simulates `Krivine.Trans` step for step.  This module writes the implementation
states as **words** and measures what a transition costs.

The cost model is the number of *sequential passes* over the encoded state, each pass costing the
length of that encoding: an administrative transition is one pass (read the state, write the
successor, with one cell appended), and a variable lookup adds one pass per cons cell visited.
Every reasonable sequential device — a Turing machine included — performs a pass in time linear
in the length of the word, so a polynomial bound in this model is a polynomial bound in time up
to the polynomial overhead of the device.

Main definitions:

* `Krivine.Impl.encState` — the encoding of a state as a word: unary addresses, self-delimiting
  cells, the heap written once;
* `Krivine.Impl.encBound` — the polynomial bounding the length of that word;
* `Krivine.Impl.hstepPasses`, `Krivine.Impl.hstepCost` — the passes and the cost of one
  transition;
* `Krivine.Impl.hrun`, `Krivine.Impl.hrunCost` — running the implementation and the cost of a
  run.

Main results:

* `Krivine.Impl.encState_inj` — **the encoding is faithful**: a state is determined by its word;
* `Krivine.Impl.encState_length_le` — **the encoded state stays small**: its length is bounded by
  a polynomial in the size of the table and the size of the heap;
* `Krivine.Impl.hstep_heap_length` — a transition allocates at most one cell, so after `n`
  transitions the heap has at most `n` cells;
* `Krivine.Impl.hstepCost_le` — **one transition costs a polynomial in the length of the
  encoding**;
* `Krivine.Impl.exists_hrun_of_run` — every run of the abstract machine is performed by the
  implementation;
* `Krivine.Impl.eval_impl_cost` — **the missing half of invariance**: a term the weak head
  strategy normalises in `k` steps is evaluated by the implementation, from the encoded initial
  state to a stuck state, at a total cost polynomial in the size of the term and in the number of
  β-steps.

## Boundary

The cost is counted in passes over the encoded state, not in the steps of one of the machine
models of the library (`Turing.FinTM2` in `Start/TM2PolyTime.lean`, `Complexity.TuringMachine` in
`Start/UniformTM.lean`).  Compiling a pass into either of those models — a routine but long
piece of machine programming — is what would remove the last gap.
-/

import Start.KrivineBound
import Start.KrivineHeap

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Krivine

namespace Impl

/-! ### States as words -/

/-- A natural number in unary, terminated by `false`: this keeps the encoding self-delimiting
and the arithmetic of the bounds elementary.  A binary encoding would only be shorter. -/
def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]

@[simp] theorem unary_length (n : ℕ) : (unary n).length = n + 1 := by
  simp [unary]

/-- A pointer: `false` for the empty environment, `true` followed by the address otherwise. -/
def encPtr : Option ℕ → List Bool
  | none => [false]
  | some p => true :: unary p

theorem encPtr_length_le {e : Option ℕ} {m : ℕ} (h : ∀ p ∈ e, p < m) :
    (encPtr e).length ≤ m + 2 := by
  cases e with
  | none => simp [encPtr]
  | some p =>
      have := h p rfl
      simp only [encPtr, List.length_cons, unary_length]
      omega

/-- A cell: a tag bit, the address it holds, and its pointer. -/
def encCell : Cell → List Bool
  | Cell.clos c e => false :: (unary c ++ encPtr e)
  | Cell.cons a t => true :: (unary a ++ encPtr t)

/-- The heap, cell after cell. -/
def encHeap (hp : Heap) : List Bool := (hp.map encCell).flatten

/-- **The encoding of an implementation state as a word.**  The code is an address in the table,
which is written once and separately; the environments are the heap, written once, with sharing.
-/
def encState (s : HState) : List Bool :=
  unary s.code ++ encPtr s.env ++ unary s.stack.length ++ (s.stack.map unary).flatten ++
    encHeap s.heap

/-! ### The encoding is faithful -/

@[simp] theorem unary_zero : unary 0 = [false] := rfl

theorem unary_succ (n : ℕ) : unary (n + 1) = true :: unary n := by
  simp [unary, List.replicate_succ]

/-- Unary numbers are self-delimiting. -/
theorem unary_append_inj : ∀ {a b : ℕ} {x y : List Bool},
    unary a ++ x = unary b ++ y → a = b ∧ x = y := by
  intro a
  induction a with
  | zero =>
      intro b x y h
      cases b with
      | zero => exact ⟨rfl, by simpa using h⟩
      | succ b =>
          rw [unary_zero, unary_succ] at h
          simp at h
  | succ a ih =>
      intro b x y h
      cases b with
      | zero =>
          rw [unary_zero, unary_succ] at h
          simp at h
      | succ b =>
          rw [unary_succ, unary_succ] at h
          simp only [List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨hab, hxy⟩ := ih h
          exact ⟨by omega, hxy⟩

/-- Pointers are self-delimiting. -/
theorem encPtr_append_inj {e₁ e₂ : Option ℕ} {x y : List Bool}
    (h : encPtr e₁ ++ x = encPtr e₂ ++ y) : e₁ = e₂ ∧ x = y := by
  cases e₁ with
  | none =>
      cases e₂ with
      | none => exact ⟨rfl, by simpa [encPtr] using h⟩
      | some q => simp [encPtr] at h
  | some p =>
      cases e₂ with
      | none => simp [encPtr] at h
      | some q =>
          simp only [encPtr, List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨hpq, hxy⟩ := unary_append_inj h
          exact ⟨by rw [hpq], hxy⟩

/-- Cells are self-delimiting. -/
theorem encCell_append_inj {c d : Cell} {x y : List Bool}
    (h : encCell c ++ x = encCell d ++ y) : c = d ∧ x = y := by
  cases c with
  | clos c₁ e₁ =>
      cases d with
      | clos c₂ e₂ =>
          simp only [encCell, List.cons_append, List.append_assoc, List.cons.injEq,
            true_and] at h
          obtain ⟨hc, hrest⟩ := unary_append_inj h
          obtain ⟨he, hxy⟩ := encPtr_append_inj hrest
          exact ⟨by rw [hc, he], hxy⟩
      | cons a₂ t₂ => simp [encCell] at h
  | cons a₁ t₁ =>
      cases d with
      | clos c₂ e₂ => simp [encCell] at h
      | cons a₂ t₂ =>
          simp only [encCell, List.cons_append, List.append_assoc, List.cons.injEq,
            true_and] at h
          obtain ⟨ha, hrest⟩ := unary_append_inj h
          obtain ⟨ht, hxy⟩ := encPtr_append_inj hrest
          exact ⟨by rw [ha, ht], hxy⟩

theorem encCell_ne_nil (c : Cell) : encCell c ≠ [] := by
  cases c <;> simp [encCell]

/-- **The heap is determined by its encoding.** -/
theorem encHeap_inj : ∀ {h₁ h₂ : Heap}, encHeap h₁ = encHeap h₂ → h₁ = h₂ := by
  intro h₁
  induction h₁ with
  | nil =>
      intro h₂ h
      cases h₂ with
      | nil => rfl
      | cons d t₂ =>
          exfalso
          simp only [encHeap, List.map_cons, List.flatten_cons, List.map_nil,
            List.flatten_nil] at h
          exact encCell_ne_nil d (List.append_eq_nil_iff.1 h.symm).1
  | cons c t₁ ih =>
      intro h₂ h
      cases h₂ with
      | nil =>
          exfalso
          simp only [encHeap, List.map_cons, List.flatten_cons, List.map_nil,
            List.flatten_nil] at h
          exact encCell_ne_nil c (List.append_eq_nil_iff.1 h).1
      | cons d t₂ =>
          simp only [encHeap, List.map_cons, List.flatten_cons] at h
          obtain ⟨hcd, hrest⟩ := encCell_append_inj h
          rw [hcd, ih hrest]

/-- Stacks of equal length are determined by their encodings. -/
theorem stackWords_append_inj : ∀ {st₁ st₂ : List ℕ} {x y : List Bool},
    st₁.length = st₂.length →
    (st₁.map unary).flatten ++ x = (st₂.map unary).flatten ++ y → st₁ = st₂ ∧ x = y := by
  intro st₁
  induction st₁ with
  | nil =>
      intro st₂ x y hlen h
      cases st₂ with
      | nil => exact ⟨rfl, by simpa using h⟩
      | cons q t₂ => simp at hlen
  | cons p t₁ ih =>
      intro st₂ x y hlen h
      cases st₂ with
      | nil => simp at hlen
      | cons q t₂ =>
          simp only [List.map_cons, List.flatten_cons, List.append_assoc] at h
          obtain ⟨hpq, hrest⟩ := unary_append_inj h
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          obtain ⟨ht, hxy⟩ := ih hlen hrest
          exact ⟨by rw [hpq, ht], hxy⟩

/-- **The encoding is faithful**: a state is determined by the word that encodes it. -/
theorem encState_inj {s₁ s₂ : HState} (h : encState s₁ = encState s₂) : s₁ = s₂ := by
  obtain ⟨c₁, e₁, st₁, hp₁⟩ := s₁
  obtain ⟨c₂, e₂, st₂, hp₂⟩ := s₂
  simp only [encState, List.append_assoc] at h
  obtain ⟨hc, h⟩ := unary_append_inj h
  obtain ⟨he, h⟩ := encPtr_append_inj h
  obtain ⟨hlen, h⟩ := unary_append_inj h
  obtain ⟨hst, h⟩ := stackWords_append_inj hlen h
  have hheap : hp₁ = hp₂ := encHeap_inj (by simpa using h)
  subst hc
  subst he
  subst hst
  subst hheap
  rfl

/-- The polynomial bounding the length of the encoding of a state whose table has `T` nodes and
whose heap has `m` cells. -/
def encBound (T m : ℕ) : ℕ :=
  (T + 1) + (m + 2) + (m + 1) + m * (m + 1) + m * (2 * T + 2 * m + 4)

theorem encBound_mono {T m m' : ℕ} (h : m ≤ m') : encBound T m ≤ encBound T m' := by
  unfold encBound
  have h1 : m * (m + 1) ≤ m' * (m' + 1) := Nat.mul_le_mul h (by omega)
  have h2 : m * (2 * T + 2 * m + 4) ≤ m' * (2 * T + 2 * m' + 4) :=
    Nat.mul_le_mul h (by omega)
  omega

/-- The stack of a state is no longer than its heap: every push allocates a cell. -/
def Sized (s : HState) : Prop := s.stack.length ≤ s.heap.length

/-- The concatenation of a list of words, each no longer than `n`, is no longer than `n` times
the number of words. -/
theorem length_flatten_le {α : Type _} (l : List (List α)) (n : ℕ)
    (h : ∀ x ∈ l, x.length ≤ n) : l.flatten.length ≤ l.length * n := by
  have hmem : ∀ x ∈ l.map List.length, x ≤ n := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact h w hw
  have hsum := List.sum_le_card_nsmul _ _ hmem
  simp only [List.length_map, smul_eq_mul] at hsum
  simpa only [List.length_flatten] using hsum

/-- A cell of a well-typed heap is short. -/
theorem encCell_length_le {tab : Tab} {hp : Heap} (hwf : HeapWF hp) (hty : HeapTyped tab hp)
    {k : ℕ} (hk : k < hp.length) :
    (encCell (hp[k]'hk)).length ≤ 2 * tab.length + 2 * hp.length + 4 := by
  have hcty := hty k hk
  have hrefs : (hp[k]'hk).refsLt k := hwf k hk
  cases hcase : hp[k]'hk with
  | clos c e =>
      rw [hcase] at hcty hrefs
      have hc : c < tab.length := hcty.1
      have he : (encPtr e).length ≤ hp.length + 2 :=
        encPtr_length_le fun p hp' => lt_trans (hrefs p hp') hk
      simp only [encCell, List.length_cons, List.length_append, unary_length]
      omega
  | cons a t =>
      rw [hcase] at hcty hrefs
      have ha : a < hp.length := lt_trans hrefs.1 hk
      have ht : (encPtr t).length ≤ hp.length + 2 :=
        encPtr_length_le fun p hp' => lt_trans (hrefs.2 p hp') hk
      simp only [encCell, List.length_cons, List.length_append, unary_length]
      omega

theorem encHeap_length_le {tab : Tab} {hp : Heap} (hwf : HeapWF hp) (hty : HeapTyped tab hp) :
    (encHeap hp).length ≤ hp.length * (2 * tab.length + 2 * hp.length + 4) := by
  have hb : ∀ x ∈ hp.map encCell, x.length ≤ 2 * tab.length + 2 * hp.length + 4 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    exact encCell_length_le hwf hty hk
  have h := length_flatten_le (hp.map encCell) (2 * tab.length + 2 * hp.length + 4) hb
  simpa only [encHeap, List.length_map] using h

theorem encStack_length_le {st : List ℕ} {m : ℕ} (h : ∀ p ∈ st, p < m) :
    ((st.map unary).flatten).length ≤ st.length * (m + 1) := by
  have hb : ∀ x ∈ st.map unary, x.length ≤ m + 1 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have := h p hp
    simp only [unary_length]
    omega
  have hle := length_flatten_le (st.map unary) (m + 1) hb
  simpa only [List.length_map] using hle

/-- **The encoded state stays small.** -/
theorem encState_length_le {tab : Tab} {s : HState} (hv : Valid tab s) (hs : Sized s) :
    (encState s).length ≤ encBound tab.length s.heap.length := by
  have h1 : (unary s.code).length ≤ tab.length + 1 := by
    have := hv.code_lt
    simp only [unary_length]
    omega
  have h2 : (encPtr s.env).length ≤ s.heap.length + 2 := encPtr_length_le hv.env_lt
  have h3 : (unary s.stack.length).length ≤ s.heap.length + 1 := by
    have hst : s.stack.length ≤ s.heap.length := hs
    simp only [unary_length]
    omega
  have h4 : ((s.stack.map unary).flatten).length ≤ s.heap.length * (s.heap.length + 1) := by
    refine le_trans (encStack_length_le hv.stack_lt) ?_
    exact Nat.mul_le_mul_right _ hs
  have h5 : (encHeap s.heap).length ≤
      s.heap.length * (2 * tab.length + 2 * s.heap.length + 4) :=
    encHeap_length_le hv.heapWF hv.heapTyped
  have hlen : (encState s).length = (unary s.code).length + (encPtr s.env).length +
      (unary s.stack.length).length + ((s.stack.map unary).flatten).length +
      (encHeap s.heap).length := by
    simp only [encState, List.length_append]
  rw [hlen, encBound]
  omega

/-! ### The cost of one transition -/

/-- The number of cons cells a variable lookup visits. -/
def walkSteps (hp : Heap) : Option ℕ → ℕ → ℕ
  | none, _ => 0
  | some _, 0 => 1
  | some p, n + 1 => match hp[p]? with
      | some (Cell.cons _ t) => walkSteps hp t n + 1
      | _ => 1

/-- A lookup visits at most as many cells as the heap has: the addresses it visits strictly
decrease. -/
theorem walkSteps_le {hp : Heap} (hwf : HeapWF hp) :
    ∀ k n e, (∀ p ∈ e, p < k) → walkSteps hp e n ≤ k := by
  intro k
  induction k with
  | zero =>
      intro n e he
      cases e with
      | none => simp [walkSteps]
      | some p => exact absurd (he p rfl) (by omega)
  | succ k ih =>
      intro n e he
      cases e with
      | none => simp [walkSteps]
      | some p =>
          have hp0 : p < k + 1 := he p rfl
          cases n with
          | zero => simp only [walkSteps]; omega
          | succ n =>
              cases hcell : hp[p]? with
              | none => simp only [walkSteps, hcell]; omega
              | some cl =>
                  cases cl with
                  | clos c e' => simp only [walkSteps, hcell]; omega
                  | cons a t =>
                      have hplt : p < hp.length := lt_length_of_getElem? hcell
                      have hrefs : (hp[p]'hplt).refsLt p := hwf p hplt
                      have hcase : (hp[p]'hplt) = Cell.cons a t := by
                        have := List.getElem?_eq_getElem hplt
                        rw [this] at hcell
                        exact Option.some_inj.1 hcell
                      rw [hcase] at hrefs
                      have htail : ∀ j ∈ t, j < k := by
                        intro j hj
                        have := hrefs.2 j hj
                        omega
                      have := ih n t htail
                      simp only [walkSteps, hcell]
                      omega

/-- The number of sequential passes over the encoded state that one transition performs: one to
read the state and write the successor, and one more per cons cell visited by a lookup. -/
def hstepPasses (tab : Tab) (s : HState) : ℕ :=
  match tab[s.code]? with
  | some (Node.var n) => walkSteps s.heap s.env n + 1
  | _ => 1

theorem hstepPasses_le {tab : Tab} {s : HState} (hv : Valid tab s) :
    hstepPasses tab s ≤ s.heap.length + 1 := by
  unfold hstepPasses
  cases hnd : tab[s.code]? with
  | none => simp
  | some nd =>
      cases nd with
      | var n =>
          have := walkSteps_le hv.heapWF s.heap.length n s.env hv.env_lt
          simp only
          omega
      | app f a => simp
      | lam b => simp

/-- **The cost of one transition**: every pass reads the encoded state and writes at most one
more cell, which is itself no longer than the encoding. -/
def hstepCost (tab : Tab) (s : HState) : ℕ :=
  (hstepPasses tab s + 1) * ((encState s).length + 1)

theorem hstepCost_le {tab : Tab} {s : HState} (hv : Valid tab s) (hs : Sized s) :
    hstepCost tab s ≤ (s.heap.length + 2) * (encBound tab.length s.heap.length + 1) := by
  refine Nat.mul_le_mul ?_ ?_
  · have := hstepPasses_le hv
    omega
  · have := encState_length_le hv hs
    omega

/-! ### Running the implementation -/

/-- Running the implementation for `n` transitions. -/
def hrun (tab : Tab) : ℕ → HState → Option HState
  | 0, s => some s
  | n + 1, s => match hstep tab s with
      | none => none
      | some (_, s') => hrun tab n s'

/-- The total cost of running the implementation for `n` transitions. -/
def hrunCost (tab : Tab) : ℕ → HState → ℕ
  | 0, _ => 0
  | n + 1, s => match hstep tab s with
      | none => 0
      | some (_, s') => hstepCost tab s + hrunCost tab n s'

/-- A transition allocates at most one cell. -/
theorem hstep_heap_length {tab : Tab} {s : HState} {l : Label} {s' : HState}
    (h : hstep tab s = some (l, s')) : s'.heap.length ≤ s.heap.length + 1 := by
  rcases hstep_shape h with ⟨hh, -⟩ | ⟨c, hh, -⟩
  · rw [hh]
    omega
  · rw [hh]
    simp

/-- A transition keeps the stack no longer than the heap. -/
theorem hstep_sized {tab : Tab} {s : HState} (hs : Sized s) {l : Label} {s' : HState}
    (h : hstep tab s = some (l, s')) : Sized s' := by
  have hs' : s.stack.length ≤ s.heap.length := hs
  rcases hstep_shape h with ⟨hh, hst⟩ | ⟨c, hh, hst⟩
  · simp only [Sized, hh, hst]
    exact hs'
  · simp only [Sized, hh, List.length_append, List.length_cons, List.length_nil]
    omega

/-- **The cost of a run** is bounded by the number of transitions times the cost of the largest
state it can reach. -/
theorem hrunCost_le {tab : Tab} : ∀ (n : ℕ) (s : HState), Valid tab s → Sized s →
    hrunCost tab n s ≤
      n * ((s.heap.length + n + 2) * (encBound tab.length (s.heap.length + n) + 1)) := by
  intro n
  induction n with
  | zero => intro s _ _; simp [hrunCost]
  | succ n ih =>
      intro s hv hs
      cases hstep0 : hstep tab s with
      | none => simp [hrunCost, hstep0]
      | some ls =>
          obtain ⟨l, s'⟩ := ls
          have hv' : Valid tab s' := hv.hstep hstep0
          have hs' : Sized s' := hstep_sized hs hstep0
          have hlen : s'.heap.length ≤ s.heap.length + 1 := hstep_heap_length hstep0
          have hcost : hstepCost tab s ≤
              (s.heap.length + (n + 1) + 2) *
                (encBound tab.length (s.heap.length + (n + 1)) + 1) := by
            refine le_trans (hstepCost_le hv hs) (Nat.mul_le_mul (by omega) ?_)
            have := encBound_mono (T := tab.length) (m := s.heap.length)
              (m' := s.heap.length + (n + 1)) (by omega)
            omega
          have hrest : hrunCost tab n s' ≤
              n * ((s.heap.length + (n + 1) + 2) *
                (encBound tab.length (s.heap.length + (n + 1)) + 1)) := by
            refine le_trans (ih s' hv' hs') (Nat.mul_le_mul_left n ?_)
            refine Nat.mul_le_mul (by omega) ?_
            have := encBound_mono (T := tab.length) (m := s'.heap.length + n)
              (m' := s.heap.length + (n + 1)) (by omega)
            omega
          have heq : hrunCost tab (n + 1) s = hstepCost tab s + hrunCost tab n s' := by
            simp [hrunCost, hstep0]
          calc hrunCost tab (n + 1) s = hstepCost tab s + hrunCost tab n s' := heq
            _ ≤ (s.heap.length + (n + 1) + 2) *
                  (encBound tab.length (s.heap.length + (n + 1)) + 1) +
                n * ((s.heap.length + (n + 1) + 2) *
                  (encBound tab.length (s.heap.length + (n + 1)) + 1)) :=
                Nat.add_le_add hcost hrest
            _ = (n + 1) * ((s.heap.length + (n + 1) + 2) *
                  (encBound tab.length (s.heap.length + (n + 1)) + 1)) := by ring

/-- **Every run of the abstract machine is performed by the implementation.** -/
theorem exists_hrun_of_run {tab : Tab} {s : HState} (hv : Valid tab s) {n b : ℕ} {u : State}
    (h : Run n b (decState tab s) u) :
    ∃ s₁, hrun tab n s = some s₁ ∧ decState tab s₁ = u ∧ Valid tab s₁ ∧
      (Sized s → Sized s₁) := by
  induction n generalizing s b u with
  | zero =>
      cases h with
      | refl _ => exact ⟨s, rfl, rfl, hv, fun h => h⟩
  | succ n ih =>
      cases h with
      | cons hstep0 hrest =>
          have hnotfinal : ¬ IsFinal (decState tab s) := fun hfin =>
            hfin _ (Step.of_trans hstep0)
          have hsome : ∃ ls, hstep tab s = some ls := by
            cases hcase : hstep tab s with
            | none => exact absurd ((hstep_isNone_iff hv).1 hcase) hnotfinal
            | some ls => exact ⟨ls, rfl⟩
          obtain ⟨⟨l', s'⟩, hcase⟩ := hsome
          have htr : Trans l' (decState tab s) (decState tab s') := hstep_trans hv hcase
          obtain ⟨-, hss⟩ := Trans.deterministic htr hstep0
          rw [← hss] at hrest
          have hv' : Valid tab s' := hv.hstep hcase
          obtain ⟨s₂', hrun', hdec', hv'', hsz⟩ := ih hv' hrest
          refine ⟨s₂', ?_, hdec', hv'', ?_⟩
          · simp [hrun, hcase, hrun']
          · intro hsized
            exact hsz (hstep_sized hsized hcase)

/-- The initial state has an empty stack and an empty heap. -/
theorem sized_initState (t : Lambda) : Sized (initState t) := by
  simp [Sized, initState]

/-- **The missing half of the invariance statement.**  If the weak head strategy normalises `t`
in `k` steps then the implementation, started on the encoding of `t`, runs to a stuck state in
`n ≤ b + |t| · (1 + b · (b + 1))` transitions with `b ≤ k` β transitions, reaching the weak head
normal form of `t`, and the whole run costs at most
`n · ((n + 2) · (encBound |t| n + 1))` — a polynomial in the size of the term and in the number
of β-steps. -/
theorem eval_impl_cost {t : Lambda} {k : ℕ} (h : Lambda.WHNIn k t) :
    ∃ (n b : ℕ) (s : HState),
      hrun (tabOf t) n (initState t) = some s ∧
      hstep (tabOf t) s = none ∧
      b ≤ k ∧ n ≤ b + Lambda.size t * (1 + b * (b + 1)) ∧
      Lambda.reducesIn b t (decState (tabOf t) s).decode ∧
      Lambda.IsWhnf (decState (tabOf t) s).decode ∧
      hrunCost (tabOf t) n (initState t) ≤
        n * ((n + 2) * (encBound t.nodes n + 1)) := by
  obtain ⟨n, b, u, hrunA, hfin, hbk, hnle, hred, hwhnf⟩ := eval_cost h
  have hv0 : Valid (tabOf t) (initState t) := valid_initState t
  have hdec0 : decState (tabOf t) (initState t) = State.init t := decState_initState t
  have hrunA' : Run n b (decState (tabOf t) (initState t)) u := by rw [hdec0]; exact hrunA
  obtain ⟨s, hrunI, hdec, hvs, hsz⟩ := exists_hrun_of_run hv0 hrunA'
  refine ⟨n, b, s, hrunI, ?_, hbk, hnle, ?_, ?_, ?_⟩
  · rw [hstep_isNone_iff hvs, hdec]
    exact hfin
  · rw [hdec]
    exact hred
  · rw [hdec]
    exact hwhnf
  · have hcost := hrunCost_le n (initState t) hv0 (sized_initState t)
    have hheap : (initState t).heap.length = 0 := by simp [initState]
    rw [hheap] at hcost
    have htab : (tabOf t).length = t.nodes := tabOf_length t
    rw [htab] at hcost
    simpa using hcost

end Impl

end Krivine
