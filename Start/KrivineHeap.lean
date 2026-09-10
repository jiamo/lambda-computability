/-
**A shared implementation of the Krivine machine: code table, heap, and one transition.**

`Start/KrivineBound.lean` bounds the *number* of transitions of the Krivine machine
(`Krivine.eval_cost`).  That is only half of an invariance statement: the other half is that one
transition can be *performed* cheaply on a machine that manipulates words, which is what this
module builds.

The point is sharing.  A `Krivine.State` is a tree: a closure carries an environment, whose
closures carry environments, and so on, so writing a state down naively can cost exponentially
more than the run that produced it.  The implementation here represents a state by

* a **code table**: the initial term, flattened once into a list of nodes
  (`Start/KrivineTable.lean`); every piece of code appearing in the run is an address in that
  table, never a copy;
* a **heap** of cells (`Krivine.Impl.Cell`) in which the environments are linked lists whose
  tails are shared: a transition allocates *one* cell and copies nothing.

Main definitions:

* `Krivine.Impl.Heap`, `Krivine.Impl.decClos`, `Krivine.Impl.decEnvP` — the heap and the decoding
  of a closure and of an environment;
* `Krivine.Impl.HState`, `Krivine.Impl.decState` — an implementation state and the abstract state
  it represents;
* `Krivine.Impl.hstep` — **one transition of the implementation**, and `Krivine.Impl.Valid` the
  invariant it preserves.

Main results:

* `Krivine.Impl.decClF_prefix` — decoding only reads the part of the heap that is already there,
  so allocating cells at the end does not disturb it;
* `Krivine.Impl.hstep_trans` — **the implementation simulates the machine**: a step of `hstep` is
  the transition of `Krivine.Trans` with the same label between the decoded states;
* `Krivine.Impl.hstep_isNone_iff` — and it is stuck exactly when the machine is;
* `Krivine.Impl.Valid.hstep` — the invariant is preserved, so the simulation applies all along a
  run.

`Start/KrivineHeapCost.lean` writes the states as words and measures the cost.
-/

import Start.KrivineTable

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Krivine

namespace Impl

/-! ### The heap -/

/-- A cell of the heap: either a closure — a code address together with a pointer to its
environment — or a cons cell of an environment. -/
inductive Cell where
  /-- A closure: the code at address `code`, in the environment at `env` (`none` is the empty
  environment). -/
  | clos (code : ℕ) (env : Option ℕ)
  /-- A cons cell of an environment: the closure at `hd`, in front of the environment at `tl`. -/
  | cons (hd : ℕ) (tl : Option ℕ)
  deriving DecidableEq, Inhabited

/-- The heap: a list of cells, addressed by their position. -/
abbrev Heap := List Cell

/-- The addresses a cell refers to are below `k`. -/
def Cell.refsLt : Cell → ℕ → Prop
  | Cell.clos _ e, k => ∀ j ∈ e, j < k
  | Cell.cons a t, k => a < k ∧ ∀ j ∈ t, j < k

/-- A heap is **well formed** when every cell refers only to cells below it: the heap is a
directed acyclic graph, which is what makes reading it terminate.  Allocating at the end
preserves this. -/
def HeapWF (hp : Heap) : Prop := ∀ k, ∀ hk : k < hp.length, (hp[k]'hk).refsLt k

/-- Appending a cell that refers only to what is already there preserves well-formedness. -/
theorem heapWF_append {hp : Heap} (hwf : HeapWF hp) {c : Cell} (h : c.refsLt hp.length) :
    HeapWF (hp ++ [c]) := by
  intro k hk
  rcases lt_or_ge k hp.length with hlt | hge
  · rw [List.getElem_append_left hlt]
    exact hwf k hlt
  · have hklen : k = hp.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hk
      omega
    subst hklen
    rw [show (hp ++ [c])[hp.length]'hk = c by simp]
    exact h

/-- The cell at `p` is a closure. -/
def IsClosPtr (hp : Heap) (p : ℕ) : Prop := ∃ c e, hp[p]? = some (Cell.clos c e)

/-- The pointer is empty, or points at a cons cell. -/
def IsEnvPtr (hp : Heap) (e : Option ℕ) : Prop := ∀ p ∈ e, ∃ a t, hp[p]? = some (Cell.cons a t)

/-- A cell is **well typed** when a closure holds a valid code address and an environment
pointer, and a cons cell holds a closure pointer and an environment pointer. -/
def CellTyped (tab : Tab) (hp : Heap) : Cell → Prop
  | Cell.clos c e => c < tab.length ∧ IsEnvPtr hp e
  | Cell.cons a t => IsClosPtr hp a ∧ IsEnvPtr hp t

/-- A heap is **well typed** when all its cells are. -/
def HeapTyped (tab : Tab) (hp : Heap) : Prop :=
  ∀ k, ∀ hk : k < hp.length, CellTyped tab hp (hp[k]'hk)

/-- Reading an old address of a heap that has grown at the end. -/
theorem getElem?_append_lt {hp : Heap} {c : Cell} {p : ℕ} (h : p < hp.length) :
    (hp ++ [c])[p]? = hp[p]? := List.getElem?_append_left h

/-- Being a closure pointer survives an allocation. -/
theorem IsClosPtr.append {hp : Heap} {p : ℕ} (h : IsClosPtr hp p) (c : Cell) :
    IsClosPtr (hp ++ [c]) p := by
  obtain ⟨a, e, ha⟩ := h
  exact ⟨a, e, by rw [getElem?_append_lt (lt_length_of_getElem? ha), ha]⟩

/-- Being an environment pointer survives an allocation. -/
theorem IsEnvPtr.append {hp : Heap} {e : Option ℕ} (h : IsEnvPtr hp e) (c : Cell) :
    IsEnvPtr (hp ++ [c]) e := by
  intro p hpe
  obtain ⟨a, t, ha⟩ := h p hpe
  exact ⟨a, t, by rw [getElem?_append_lt (lt_length_of_getElem? ha), ha]⟩

/-- Being well typed survives an allocation. -/
theorem CellTyped.append {tab : Tab} {hp : Heap} {c : Cell} (h : CellTyped tab hp c) (d : Cell) :
    CellTyped tab (hp ++ [d]) c := by
  cases c with
  | clos c' e => exact ⟨h.1, h.2.append d⟩
  | cons a t => exact ⟨h.1.append d, h.2.append d⟩

/-- Allocating a well-typed cell preserves well-typedness. -/
theorem heapTyped_append {tab : Tab} {hp : Heap} (hty : HeapTyped tab hp) {d : Cell}
    (hd : CellTyped tab hp d) : HeapTyped tab (hp ++ [d]) := by
  intro k hk
  rcases lt_or_ge k hp.length with hlt | hge
  · rw [List.getElem_append_left hlt]
    exact (hty k hlt).append d
  · have hklen : k = hp.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hk
      omega
    subst hklen
    rw [show (hp ++ [d])[hp.length]'hk = d by simp]
    exact hd.append d

mutual

/-- Decoding the closure at heap address `p`, with `fuel` bounding the depth of the walk. -/
def decClF (tab : Tab) (hp : Heap) : ℕ → ℕ → Clos
  | 0, _ => Clos.mk (Lambda.var 0) []
  | fuel + 1, p =>
      match hp[p]? with
      | some (Cell.clos c e) => Clos.mk (decTerm tab c) (decEnvF tab hp fuel e)
      | _ => Clos.mk (Lambda.var 0) []

/-- Decoding the environment at heap pointer `e`, with `fuel` bounding the depth of the walk. -/
def decEnvF (tab : Tab) (hp : Heap) : ℕ → Option ℕ → Env
  | 0, _ => []
  | _ + 1, none => []
  | fuel + 1, some p =>
      match hp[p]? with
      | some (Cell.cons a t) => decClF tab hp fuel a :: decEnvF tab hp fuel t
      | _ => []

end

theorem decClF_clos_eq {tab : Tab} {hp : Heap} {p c fuel : ℕ} {e : Option ℕ}
    (h : hp[p]? = some (Cell.clos c e)) :
    decClF tab hp (fuel + 1) p = Clos.mk (decTerm tab c) (decEnvF tab hp fuel e) := by
  simp only [decClF, h]

theorem decClF_cons_eq {tab : Tab} {hp : Heap} {p a fuel : ℕ} {t : Option ℕ}
    (h : hp[p]? = some (Cell.cons a t)) :
    decClF tab hp (fuel + 1) p = Clos.mk (Lambda.var 0) [] := by
  simp only [decClF, h]

theorem decEnvF_cons_eq {tab : Tab} {hp : Heap} {p a fuel : ℕ} {t : Option ℕ}
    (h : hp[p]? = some (Cell.cons a t)) :
    decEnvF tab hp (fuel + 1) (some p) = decClF tab hp fuel a :: decEnvF tab hp fuel t := by
  simp only [decEnvF, h]

theorem decEnvF_clos_eq {tab : Tab} {hp : Heap} {p c fuel : ℕ} {e : Option ℕ}
    (h : hp[p]? = some (Cell.clos c e)) : decEnvF tab hp (fuel + 1) (some p) = [] := by
  simp only [decEnvF, h]

/-- **The closure at a heap address.** -/
def decClos (tab : Tab) (hp : Heap) (p : ℕ) : Clos := decClF tab hp hp.length p

/-- **The environment at a heap pointer.** -/
def decEnvP (tab : Tab) (hp : Heap) (e : Option ℕ) : Env := decEnvF tab hp hp.length e

@[simp] theorem decEnvF_none (tab : Tab) (hp : Heap) (f : ℕ) : decEnvF tab hp f none = [] := by
  cases f <;> rfl

@[simp] theorem decEnvP_none (tab : Tab) (hp : Heap) : decEnvP tab hp none = [] := by
  simp [decEnvP]

/-- The joint stability statement for the two decoders, proved by strong induction on the
address. -/
private theorem dec_prefix_aux {tab : Tab} {hp hp' : Heap} (hwf : HeapWF hp) (hpre : hp <+: hp') :
    ∀ p, p < hp.length → ∀ f₁ f₂, p < f₁ → p < f₂ →
      decClF tab hp f₁ p = decClF tab hp' f₂ p ∧
        decEnvF tab hp f₁ (some p) = decEnvF tab hp' f₂ (some p) := by
  obtain ⟨r, rfl⟩ := hpre
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hplt f₁ f₂ h₁ h₂
    obtain ⟨k₁, rfl⟩ : ∃ k, f₁ = k + 1 := ⟨f₁ - 1, by omega⟩
    obtain ⟨k₂, rfl⟩ : ∃ k, f₂ = k + 1 := ⟨f₂ - 1, by omega⟩
    have hcell : hp[p]? = some (hp[p]'hplt) := List.getElem?_eq_getElem hplt
    have hcell' : (hp ++ r)[p]? = some (hp[p]'hplt) := by
      rw [List.getElem?_append_left hplt, hcell]
    have hrefs : (hp[p]'hplt).refsLt p := hwf p hplt
    cases hcase : hp[p]'hplt with
    | clos c e =>
        rw [hcase] at hcell hcell' hrefs
        refine ⟨?_, ?_⟩
        · rw [decClF_clos_eq hcell, decClF_clos_eq hcell']
          cases e with
          | none => simp
          | some j =>
              have hj : j < p := hrefs j rfl
              simp only [Clos.mk.injEq, true_and]
              exact (ih j hj (lt_trans hj hplt) k₁ k₂ (by omega) (by omega)).2
        · rw [decEnvF_clos_eq hcell, decEnvF_clos_eq hcell']
    | cons a t =>
        rw [hcase] at hcell hcell' hrefs
        obtain ⟨ha, ht⟩ := hrefs
        have hcl := (ih a ha (lt_trans ha hplt) k₁ k₂ (by omega) (by omega)).1
        refine ⟨?_, ?_⟩
        · rw [decClF_cons_eq hcell, decClF_cons_eq hcell']
        · rw [decEnvF_cons_eq hcell, decEnvF_cons_eq hcell']
          cases t with
          | none => simp [hcl]
          | some j =>
              have hj : j < p := ht j rfl
              have henv := (ih j hj (lt_trans hj hplt) k₁ k₂ (by omega) (by omega)).2
              rw [hcl, henv]

/-- **Reading the heap is stable**: it depends neither on the fuel, as long as there is enough of
it, nor on cells allocated afterwards. -/
theorem decClF_prefix {tab : Tab} {hp hp' : Heap} (hwf : HeapWF hp) (hpre : hp <+: hp')
    {p : ℕ} (hp0 : p < hp.length) {f₁ f₂ : ℕ} (h₁ : p < f₁) (h₂ : p < f₂) :
    decClF tab hp f₁ p = decClF tab hp' f₂ p :=
  (dec_prefix_aux hwf hpre p hp0 f₁ f₂ h₁ h₂).1

/-- The companion of `Krivine.Impl.decClF_prefix` for environments. -/
theorem decEnvF_prefix {tab : Tab} {hp hp' : Heap} (hwf : HeapWF hp) (hpre : hp <+: hp')
    {e : Option ℕ} (he : ∀ p ∈ e, p < hp.length) {f₁ f₂ : ℕ}
    (h₁ : ∀ p ∈ e, p < f₁) (h₂ : ∀ p ∈ e, p < f₂) :
    decEnvF tab hp f₁ e = decEnvF tab hp' f₂ e := by
  cases e with
  | none => simp
  | some p => exact (dec_prefix_aux hwf hpre p (he p rfl) f₁ f₂ (h₁ p rfl) (h₂ p rfl)).2

/-- Reading a closure does not depend on the fuel. -/
theorem decClF_eq_decClos {tab : Tab} {hp : Heap} (hwf : HeapWF hp) {p : ℕ} (hp0 : p < hp.length)
    {f : ℕ} (hf : p < f) : decClF tab hp f p = decClos tab hp p :=
  decClF_prefix hwf (List.prefix_refl hp) hp0 hf hp0

/-- Reading an environment does not depend on the fuel. -/
theorem decEnvF_eq_decEnvP {tab : Tab} {hp : Heap} (hwf : HeapWF hp) {e : Option ℕ}
    (he : ∀ p ∈ e, p < hp.length) {f : ℕ} (hf : ∀ p ∈ e, p < f) :
    decEnvF tab hp f e = decEnvP tab hp e :=
  decEnvF_prefix hwf (List.prefix_refl hp) he hf he

/-- **Allocating a cell does not change what the heap already says.** -/
theorem decClos_append {tab : Tab} {hp : Heap} (hwf : HeapWF hp) (c : Cell) {p : ℕ}
    (hp0 : p < hp.length) : decClos tab (hp ++ [c]) p = decClos tab hp p := by
  refine (decClF_prefix hwf (List.prefix_append hp [c]) hp0 hp0 ?_).symm
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- The companion of `Krivine.Impl.decClos_append` for environments. -/
theorem decEnvP_append {tab : Tab} {hp : Heap} (hwf : HeapWF hp) (c : Cell) {e : Option ℕ}
    (he : ∀ p ∈ e, p < hp.length) : decEnvP tab (hp ++ [c]) e = decEnvP tab hp e := by
  refine (decEnvF_prefix hwf (List.prefix_append hp [c]) he he ?_).symm
  intro p hpe
  have := he p hpe
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- Reading the closure at a closure cell. -/
theorem decClos_clos {tab : Tab} {hp : Heap} (hwf : HeapWF hp) {p c : ℕ} {e : Option ℕ}
    (hcell : hp[p]? = some (Cell.clos c e)) :
    decClos tab hp p = Clos.mk (decTerm tab c) (decEnvP tab hp e) := by
  have hplt : p < hp.length := lt_length_of_getElem? hcell
  have hcase : (hp[p]'hplt) = Cell.clos c e := by
    have := List.getElem?_eq_getElem hplt
    rw [this] at hcell
    exact Option.some_inj.1 hcell
  have hrefs : (hp[p]'hplt).refsLt p := hwf p hplt
  rw [hcase] at hrefs
  obtain ⟨m, hm⟩ : ∃ m, hp.length = m + 1 := ⟨hp.length - 1, by omega⟩
  rw [decClos, hm, decClF_clos_eq hcell]
  have henv : decEnvF tab hp m e = decEnvP tab hp e := by
    refine decEnvF_eq_decEnvP hwf (fun j hj => ?_) (fun j hj => ?_)
    · have := hrefs j hj
      omega
    · have := hrefs j hj
      omega
  rw [henv]

/-- Reading the environment at a cons cell. -/
theorem decEnvP_cons {tab : Tab} {hp : Heap} (hwf : HeapWF hp) {p a : ℕ} {t : Option ℕ}
    (hcell : hp[p]? = some (Cell.cons a t)) :
    decEnvP tab hp (some p) = decClos tab hp a :: decEnvP tab hp t := by
  have hplt : p < hp.length := lt_length_of_getElem? hcell
  have hcase : (hp[p]'hplt) = Cell.cons a t := by
    have := List.getElem?_eq_getElem hplt
    rw [this] at hcell
    exact Option.some_inj.1 hcell
  have hrefs : (hp[p]'hplt).refsLt p := hwf p hplt
  rw [hcase] at hrefs
  obtain ⟨ha, ht⟩ := hrefs
  obtain ⟨m, hm⟩ : ∃ m, hp.length = m + 1 := ⟨hp.length - 1, by omega⟩
  rw [decEnvP, hm, decEnvF_cons_eq hcell]
  have hcl : decClF tab hp m a = decClos tab hp a := by
    refine decClF_eq_decClos hwf (lt_trans ha hplt) ?_
    omega
  have henv : decEnvF tab hp m t = decEnvP tab hp t := by
    refine decEnvF_eq_decEnvP hwf (fun j hj => ?_) (fun j hj => ?_)
    · have := ht j hj
      omega
    · have := ht j hj
      omega
  rw [hcl, henv]

/-! ### Looking a variable up in the heap -/

/-- Walking `n` cons cells down the environment at `e`, returning the closure pointer found. -/
def envNth (hp : Heap) : Option ℕ → ℕ → Option ℕ
  | none, _ => none
  | some p, 0 => match hp[p]? with
      | some (Cell.cons a _) => some a
      | _ => none
  | some p, n + 1 => match hp[p]? with
      | some (Cell.cons _ t) => envNth hp t n
      | _ => none

@[simp] theorem envNth_none (hp : Heap) (n : ℕ) : envNth hp none n = none := by
  cases n <;> rfl

theorem envNth_zero_cons {hp : Heap} {p a : ℕ} {t : Option ℕ}
    (h : hp[p]? = some (Cell.cons a t)) : envNth hp (some p) 0 = some a := by
  simp only [envNth, h]

theorem envNth_succ_cons {hp : Heap} {p a n : ℕ} {t : Option ℕ}
    (h : hp[p]? = some (Cell.cons a t)) : envNth hp (some p) (n + 1) = envNth hp t n := by
  simp only [envNth, h]

/-- **The walk finds what the decoded environment holds.** -/
theorem getElem?_decEnvP {tab : Tab} {hp : Heap} (hwf : HeapWF hp) {e : Option ℕ}
    (he : ∀ p ∈ e, p < hp.length) (hety : IsEnvPtr hp e) (hty : HeapTyped tab hp) (n : ℕ) :
    (decEnvP tab hp e)[n]? = (envNth hp e n).map (decClos tab hp) := by
  induction n generalizing e with
  | zero =>
      cases e with
      | none => simp
      | some p =>
          obtain ⟨a, t, hcell⟩ := hety p rfl
          rw [decEnvP_cons hwf hcell, envNth_zero_cons hcell]
          simp
  | succ n ih =>
      cases e with
      | none => simp
      | some p =>
          obtain ⟨a, t, hcell⟩ := hety p rfl
          have hplt : p < hp.length := he p rfl
          have hcase : (hp[p]'hplt) = Cell.cons a t := by
            have := List.getElem?_eq_getElem hplt
            rw [this] at hcell
            exact Option.some_inj.1 hcell
          have hrefs : (hp[p]'hplt).refsLt p := hwf p hplt
          rw [hcase] at hrefs
          obtain ⟨ha, ht⟩ := hrefs
          have htty : IsEnvPtr hp t := by
            have hcty := hty p hplt
            rw [hcase] at hcty
            exact hcty.2
          rw [decEnvP_cons hwf hcell, envNth_succ_cons hcell, List.getElem?_cons_succ]
          exact ih (fun j hj => lt_trans (ht j hj) hplt) htty

/-- The walk lands on a closure. -/
theorem isClosPtr_envNth {tab : Tab} {hp : Heap} (hwf : HeapWF hp) (hty : HeapTyped tab hp)
    {e : Option ℕ} (he : ∀ p ∈ e, p < hp.length) (hety : IsEnvPtr hp e) {n q : ℕ}
    (h : envNth hp e n = some q) : IsClosPtr hp q := by
  induction n generalizing e with
  | zero =>
      cases e with
      | none => simp at h
      | some p =>
          obtain ⟨a, t, hcell⟩ := hety p rfl
          have hplt : p < hp.length := he p rfl
          have hcase : (hp[p]'hplt) = Cell.cons a t := by
            have := List.getElem?_eq_getElem hplt
            rw [this] at hcell
            exact Option.some_inj.1 hcell
          rw [envNth_zero_cons hcell] at h
          have hq : q = a := (Option.some_inj.1 h).symm
          subst hq
          have hcty := hty p hplt
          rw [hcase] at hcty
          exact hcty.1
  | succ n ih =>
      cases e with
      | none => simp at h
      | some p =>
          obtain ⟨a, t, hcell⟩ := hety p rfl
          have hplt : p < hp.length := he p rfl
          have hcase : (hp[p]'hplt) = Cell.cons a t := by
            have := List.getElem?_eq_getElem hplt
            rw [this] at hcell
            exact Option.some_inj.1 hcell
          have hrefs : (hp[p]'hplt).refsLt p := hwf p hplt
          rw [hcase] at hrefs
          obtain ⟨ha, ht⟩ := hrefs
          have htty : IsEnvPtr hp t := by
            have hcty := hty p hplt
            rw [hcase] at hcty
            exact hcty.2
          rw [envNth_succ_cons hcell] at h
          exact ih (fun j hj => lt_trans (ht j hj) hplt) htty h

/-! ### States of the implementation -/

/-- A state of the implementation: the address of the code, the pointer to its environment, the
stack of argument pointers, and the heap. -/
structure HState where
  /-- The address of the code in the table. -/
  code : ℕ
  /-- The pointer to the environment. -/
  env : Option ℕ
  /-- The stack of pointers to the argument closures. -/
  stack : List ℕ
  /-- The heap. -/
  heap : Heap

/-- **The abstract state an implementation state represents.** -/
def decState (tab : Tab) (s : HState) : State :=
  ⟨decTerm tab s.code, decEnvP tab s.heap s.env, s.stack.map (decClos tab s.heap)⟩

/-- The invariant of the implementation: the table is well formed, the heap is a well-formed and
well-typed acyclic graph, and every pointer of the state is valid. -/
structure Valid (tab : Tab) (s : HState) : Prop where
  /-- The table is well formed. -/
  tabWF : TabWF tab
  /-- The code address is valid. -/
  code_lt : s.code < tab.length
  /-- The heap is acyclic. -/
  heapWF : HeapWF s.heap
  /-- The heap is well typed. -/
  heapTyped : HeapTyped tab s.heap
  /-- The environment pointer is valid. -/
  env_lt : ∀ p ∈ s.env, p < s.heap.length
  /-- The environment pointer points at an environment. -/
  env_ty : IsEnvPtr s.heap s.env
  /-- The stack holds valid pointers. -/
  stack_lt : ∀ p ∈ s.stack, p < s.heap.length
  /-- The stack holds closure pointers. -/
  stack_ty : ∀ p ∈ s.stack, IsClosPtr s.heap p

/-- The invariant, stated field by field, for a state given by its components. -/
theorem valid_mk {tab : Tab} {code : ℕ} {env : Option ℕ} {stack : List ℕ} {heap : Heap}
    (h1 : TabWF tab) (h2 : code < tab.length) (h3 : HeapWF heap) (h4 : HeapTyped tab heap)
    (h5 : ∀ p ∈ env, p < heap.length) (h6 : IsEnvPtr heap env)
    (h7 : ∀ p ∈ stack, p < heap.length) (h8 : ∀ p ∈ stack, IsClosPtr heap p) :
    Valid tab ⟨code, env, stack, heap⟩ := ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- The initial state of the implementation on a term: the root address of its table, no
environment, no arguments, and an empty heap. -/
def initState (t : Lambda) : HState := ⟨rootOf t, none, [], []⟩

/-! ### One transition of the implementation -/

/-- **One transition of the implementation.**  An application allocates the closure of its
argument and pushes it; an abstraction allocates a cons cell in front of its environment and
consumes the top of the stack; a variable walks down the environment.  In every case at most one
cell is allocated, and nothing is copied. -/
def hstep (tab : Tab) (s : HState) : Option (Label × HState) :=
  match tab[s.code]? with
  | some (Node.app f a) =>
      some (Label.app, ⟨f, s.env, s.heap.length :: s.stack, s.heap ++ [Cell.clos a s.env]⟩)
  | some (Node.lam b) =>
      match s.stack with
      | [] => none
      | p :: π => some (Label.beta, ⟨b, some s.heap.length, π, s.heap ++ [Cell.cons p s.env]⟩)
  | some (Node.var n) =>
      match envNth s.heap s.env n with
      | none => none
      | some q =>
          match s.heap[q]? with
          | some (Cell.clos c e) => some (Label.var, ⟨c, e, s.stack, s.heap⟩)
          | _ => none
  | none => none

theorem hstep_app_eq {tab : Tab} {s : HState} {f a : ℕ}
    (hnd : tab[s.code]? = some (Node.app f a)) :
    hstep tab s =
      some (Label.app, ⟨f, s.env, s.heap.length :: s.stack, s.heap ++ [Cell.clos a s.env]⟩) := by
  simp only [hstep, hnd]

theorem hstep_lam_nil_eq {tab : Tab} {s : HState} {b : ℕ}
    (hnd : tab[s.code]? = some (Node.lam b)) (hst : s.stack = []) : hstep tab s = none := by
  simp only [hstep, hnd, hst]

theorem hstep_lam_cons_eq {tab : Tab} {s : HState} {b p : ℕ} {π : List ℕ}
    (hnd : tab[s.code]? = some (Node.lam b)) (hst : s.stack = p :: π) :
    hstep tab s =
      some (Label.beta, ⟨b, some s.heap.length, π, s.heap ++ [Cell.cons p s.env]⟩) := by
  simp only [hstep, hnd, hst]

theorem hstep_var_eq {tab : Tab} {s : HState} {n q c : ℕ} {e : Option ℕ}
    (hnd : tab[s.code]? = some (Node.var n)) (hw : envNth s.heap s.env n = some q)
    (hcell : s.heap[q]? = some (Cell.clos c e)) :
    hstep tab s = some (Label.var, ⟨c, e, s.stack, s.heap⟩) := by
  simp only [hstep, hnd, hw, hcell]

theorem hstep_var_none_eq {tab : Tab} {s : HState} {n : ℕ}
    (hnd : tab[s.code]? = some (Node.var n)) (hw : envNth s.heap s.env n = none) :
    hstep tab s = none := by
  simp only [hstep, hnd, hw]

theorem hstep_var_cell_none_eq {tab : Tab} {s : HState} {n q : ℕ}
    (hnd : tab[s.code]? = some (Node.var n)) (hw : envNth s.heap s.env n = some q)
    (hcell : s.heap[q]? = none) : hstep tab s = none := by
  simp only [hstep, hnd, hw, hcell]

theorem hstep_var_cell_cons_eq {tab : Tab} {s : HState} {n q a : ℕ} {t : Option ℕ}
    (hnd : tab[s.code]? = some (Node.var n)) (hw : envNth s.heap s.env n = some q)
    (hcell : s.heap[q]? = some (Cell.cons a t)) : hstep tab s = none := by
  simp only [hstep, hnd, hw, hcell]

/-- **The shape of a transition**: the state either keeps its heap and its stack, or allocates
one cell and pushes at most one pointer. -/
theorem hstep_shape {tab : Tab} {s : HState} {l : Label} {s' : HState}
    (h : hstep tab s = some (l, s')) :
    (s'.heap = s.heap ∧ s'.stack = s.stack) ∨
      (∃ c, s'.heap = s.heap ++ [c] ∧ s'.stack.length ≤ s.stack.length + 1) := by
  obtain ⟨nd, hnd⟩ : ∃ nd, tab[s.code]? = some nd := by
    cases hnd : tab[s.code]? with
    | none => rw [hstep, hnd] at h; exact absurd h (by simp)
    | some nd => exact ⟨nd, rfl⟩
  cases nd with
  | var n =>
      cases hw : envNth s.heap s.env n with
      | none => rw [hstep_var_none_eq hnd hw] at h; exact absurd h (by simp)
      | some q =>
          cases hcell : s.heap[q]? with
          | none => rw [hstep_var_cell_none_eq hnd hw hcell] at h; exact absurd h (by simp)
          | some cl =>
              cases cl with
              | cons a t =>
                  rw [hstep_var_cell_cons_eq hnd hw hcell] at h
                  exact absurd h (by simp)
              | clos c e =>
                  rw [hstep_var_eq hnd hw hcell] at h
                  simp only [Option.some_inj, Prod.mk.injEq] at h
                  obtain ⟨-, hs⟩ := h
                  subst hs
                  exact Or.inl ⟨rfl, rfl⟩
  | app f a =>
      rw [hstep_app_eq hnd] at h
      simp only [Option.some_inj, Prod.mk.injEq] at h
      obtain ⟨-, hs⟩ := h
      subst hs
      exact Or.inr ⟨Cell.clos a s.env, rfl, by simp⟩
  | lam b =>
      cases hst : s.stack with
      | nil => rw [hstep_lam_nil_eq hnd hst] at h; exact absurd h (by simp)
      | cons p π =>
          rw [hstep_lam_cons_eq hnd hst] at h
          simp only [Option.some_inj, Prod.mk.injEq] at h
          obtain ⟨-, hs⟩ := h
          subst hs
          refine Or.inr ⟨Cell.cons p s.env, rfl, ?_⟩
          simp only [List.length_cons]
          omega

/-- **The implementation simulates the machine**: one step of `hstep` is the transition of the
Krivine machine with the same label, between the states the two encode. -/
theorem hstep_trans {tab : Tab} {s : HState} (hv : Valid tab s) {l : Label} {s' : HState}
    (h : hstep tab s = some (l, s')) : Trans l (decState tab s) (decState tab s') := by
  obtain ⟨nd, hnd⟩ : ∃ nd, tab[s.code]? = some nd :=
    ⟨_, List.getElem?_eq_getElem hv.code_lt⟩
  cases nd with
  | var n =>
      cases hw : envNth s.heap s.env n with
      | none =>
          rw [hstep_var_none_eq hnd hw] at h
          exact absurd h (by simp)
      | some q =>
          obtain ⟨c, e, hcell⟩ :=
            isClosPtr_envNth hv.heapWF hv.heapTyped hv.env_lt hv.env_ty hw
          rw [hstep_var_eq hnd hw hcell] at h
          simp only [Option.some_inj, Prod.mk.injEq] at h
          obtain ⟨hl, hs⟩ := h
          subst hl
          subst hs
          have hE : (decEnvP tab s.heap s.env)[n]? = some (decClos tab s.heap q) := by
            rw [getElem?_decEnvP hv.heapWF hv.env_lt hv.env_ty hv.heapTyped n, hw]
            rfl
          have hcl : decClos tab s.heap q = Clos.mk (decTerm tab c) (decEnvP tab s.heap e) :=
            decClos_clos hv.heapWF hcell
          have htr := Trans.var n (decEnvP tab s.heap s.env) (decClos tab s.heap q)
            (s.stack.map (decClos tab s.heap)) hE
          rw [hcl] at htr
          simpa only [decState, decTerm_var hnd, Clos.code_mk, Clos.env_mk] using htr
  | app f a =>
      rw [hstep_app_eq hnd] at h
      simp only [Option.some_inj, Prod.mk.injEq] at h
      obtain ⟨hl, hs⟩ := h
      subst hl
      subst hs
      have hwf' : HeapWF (s.heap ++ [Cell.clos a s.env]) :=
        heapWF_append hv.heapWF (fun j hj => hv.env_lt j hj)
      have hnew : (s.heap ++ [Cell.clos a s.env])[s.heap.length]? =
          some (Cell.clos a s.env) := by simp
      have hdecnew : decClos tab (s.heap ++ [Cell.clos a s.env]) s.heap.length =
          Clos.mk (decTerm tab a) (decEnvP tab s.heap s.env) := by
        rw [decClos_clos hwf' hnew, decEnvP_append hv.heapWF _ hv.env_lt]
      have hstk : s.stack.map (decClos tab (s.heap ++ [Cell.clos a s.env])) =
          s.stack.map (decClos tab s.heap) :=
        List.map_congr_left fun p hp => decClos_append hv.heapWF _ (hv.stack_lt p hp)
      simp only [decState, decTerm_app hv.tabWF hnd, List.map_cons, hdecnew, hstk,
        decEnvP_append hv.heapWF _ hv.env_lt]
      exact Trans.app (decTerm tab f) (decTerm tab a) (decEnvP tab s.heap s.env)
        (s.stack.map (decClos tab s.heap))
  | lam b =>
      cases hst : s.stack with
      | nil =>
          rw [hstep_lam_nil_eq hnd hst] at h
          exact absurd h (by simp)
      | cons p π =>
          rw [hstep_lam_cons_eq hnd hst] at h
          simp only [Option.some_inj, Prod.mk.injEq] at h
          obtain ⟨hl, hs⟩ := h
          subst hl
          subst hs
          have hplt : p < s.heap.length := hv.stack_lt p (by rw [hst]; simp)
          have hwf' : HeapWF (s.heap ++ [Cell.cons p s.env]) :=
            heapWF_append hv.heapWF ⟨hplt, fun j hj => hv.env_lt j hj⟩
          have hnew : (s.heap ++ [Cell.cons p s.env])[s.heap.length]? =
              some (Cell.cons p s.env) := by simp
          have hdecnew : decEnvP tab (s.heap ++ [Cell.cons p s.env]) (some s.heap.length) =
              decClos tab s.heap p :: decEnvP tab s.heap s.env := by
            rw [decEnvP_cons hwf' hnew, decClos_append hv.heapWF _ hplt,
              decEnvP_append hv.heapWF _ hv.env_lt]
          have hstk : π.map (decClos tab (s.heap ++ [Cell.cons p s.env])) =
              π.map (decClos tab s.heap) := by
            refine List.map_congr_left fun q hq => ?_
            refine decClos_append hv.heapWF _ (hv.stack_lt q ?_)
            rw [hst]
            exact List.mem_cons_of_mem p hq
          simp only [decState, decTerm_lam hv.tabWF hnd, hst, List.map_cons, hdecnew, hstk]
          exact Trans.beta (decTerm tab b) (decEnvP tab s.heap s.env) (decClos tab s.heap p)
            (π.map (decClos tab s.heap))

/-- **The invariant is preserved by a transition.** -/
theorem Valid.hstep {tab : Tab} {s : HState} (hv : Valid tab s) {l : Label} {s' : HState}
    (h : Impl.hstep tab s = some (l, s')) : Valid tab s' := by
  obtain ⟨nd, hnd⟩ : ∃ nd, tab[s.code]? = some nd :=
    ⟨_, List.getElem?_eq_getElem hv.code_lt⟩
  have hcodelt : s.code < tab.length := hv.code_lt
  have hndrefs : nd.refsLt s.code := by
    have hcase : (tab[s.code]'hcodelt) = nd := by
      have := List.getElem?_eq_getElem hcodelt
      rw [this] at hnd
      exact Option.some_inj.1 hnd
    rw [← hcase]
    exact hv.tabWF s.code hcodelt
  cases nd with
  | var n =>
      cases hw : envNth s.heap s.env n with
      | none =>
          rw [hstep_var_none_eq hnd hw] at h
          exact absurd h (by simp)
      | some q =>
          obtain ⟨c, e, hcell⟩ :=
            isClosPtr_envNth hv.heapWF hv.heapTyped hv.env_lt hv.env_ty hw
          rw [hstep_var_eq hnd hw hcell] at h
          simp only [Option.some_inj, Prod.mk.injEq] at h
          obtain ⟨hl, hs⟩ := h
          subst hl
          subst hs
          have hqlt : q < s.heap.length := lt_length_of_getElem? hcell
          have hcase : (s.heap[q]'hqlt) = Cell.clos c e := by
            have := List.getElem?_eq_getElem hqlt
            rw [this] at hcell
            exact Option.some_inj.1 hcell
          have hcty := hv.heapTyped q hqlt
          rw [hcase] at hcty
          have hrefs : (s.heap[q]'hqlt).refsLt q := hv.heapWF q hqlt
          rw [hcase] at hrefs
          exact valid_mk hv.tabWF hcty.1 hv.heapWF hv.heapTyped
            (fun j hj => lt_trans (hrefs j hj) hqlt) hcty.2 hv.stack_lt hv.stack_ty
  | app f a =>
      rw [hstep_app_eq hnd] at h
      simp only [Option.some_inj, Prod.mk.injEq] at h
      obtain ⟨hl, hs⟩ := h
      subst hl
      subst hs
      obtain ⟨hf, ha⟩ := hndrefs
      have hwf' : HeapWF (s.heap ++ [Cell.clos a s.env]) :=
        heapWF_append hv.heapWF (fun j hj => hv.env_lt j hj)
      have hnew : (s.heap ++ [Cell.clos a s.env])[s.heap.length]? =
          some (Cell.clos a s.env) := by simp
      have hlen : (s.heap ++ [Cell.clos a s.env]).length = s.heap.length + 1 := by simp
      have hcd : CellTyped tab s.heap (Cell.clos a s.env) :=
        ⟨lt_trans ha hcodelt, hv.env_ty⟩
      refine valid_mk hv.tabWF (lt_trans hf hcodelt) hwf'
        (heapTyped_append hv.heapTyped hcd) ?_ (hv.env_ty.append _) ?_ ?_
      · intro j hj
        have := hv.env_lt j hj
        omega
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq'
        · omega
        · have := hv.stack_lt q hq'
          omega
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq'
        · exact ⟨a, s.env, hnew⟩
        · exact (hv.stack_ty q hq').append _
  | lam b =>
      cases hst : s.stack with
      | nil =>
          rw [hstep_lam_nil_eq hnd hst] at h
          exact absurd h (by simp)
      | cons p π =>
          rw [hstep_lam_cons_eq hnd hst] at h
          simp only [Option.some_inj, Prod.mk.injEq] at h
          obtain ⟨hl, hs⟩ := h
          subst hl
          subst hs
          have hb : b < s.code := hndrefs
          have hpmem : p ∈ s.stack := by rw [hst]; simp
          have hplt : p < s.heap.length := hv.stack_lt p hpmem
          have hwf' : HeapWF (s.heap ++ [Cell.cons p s.env]) :=
            heapWF_append hv.heapWF ⟨hplt, fun j hj => hv.env_lt j hj⟩
          have hnew : (s.heap ++ [Cell.cons p s.env])[s.heap.length]? =
              some (Cell.cons p s.env) := by simp
          have hlen : (s.heap ++ [Cell.cons p s.env]).length = s.heap.length + 1 := by simp
          have hcd : CellTyped tab s.heap (Cell.cons p s.env) :=
            ⟨hv.stack_ty p hpmem, hv.env_ty⟩
          refine valid_mk hv.tabWF (lt_trans hb hcodelt) hwf'
            (heapTyped_append hv.heapTyped hcd) ?_ ?_ ?_ ?_
          · intro j hj
            have hjeq : j = s.heap.length := by
              rw [Option.mem_def, Option.some_inj] at hj
              exact hj.symm
            omega
          · intro j hj
            have hjeq : j = s.heap.length := by
              rw [Option.mem_def, Option.some_inj] at hj
              exact hj.symm
            subst hjeq
            exact ⟨p, s.env, hnew⟩
          · intro q hq
            have hmem : q ∈ s.stack := by
              rw [hst]
              exact List.mem_cons_of_mem p hq
            have := hv.stack_lt q hmem
            omega
          · intro q hq
            have hmem : q ∈ s.stack := by
              rw [hst]
              exact List.mem_cons_of_mem p hq
            exact (hv.stack_ty q hmem).append _

/-- **The implementation is stuck exactly when the machine is.** -/
theorem hstep_isNone_iff {tab : Tab} {s : HState} (hv : Valid tab s) :
    hstep tab s = none ↔ IsFinal (decState tab s) := by
  obtain ⟨nd, hnd⟩ : ∃ nd, tab[s.code]? = some nd :=
    ⟨_, List.getElem?_eq_getElem hv.code_lt⟩
  rw [isFinal_iff]
  cases nd with
  | var n =>
      have hwalk := getElem?_decEnvP (tab := tab) hv.heapWF hv.env_lt hv.env_ty hv.heapTyped n
      constructor
      · intro hnone
        refine Or.inr ⟨n, by simpa only [decState] using decTerm_var hnd, ?_⟩
        simp only [decState]
        rw [hwalk]
        cases hw : envNth s.heap s.env n with
        | none => simp
        | some q =>
            exfalso
            obtain ⟨c, e, hcell⟩ :=
              isClosPtr_envNth hv.heapWF hv.heapTyped hv.env_lt hv.env_ty hw
            rw [hstep_var_eq hnd hw hcell] at hnone
            exact absurd hnone (by simp)
      · rintro (⟨⟨t', ht⟩, -⟩ | ⟨m, hm, hnone⟩)
        · rw [show (decState tab s).code = decTerm tab s.code from rfl, decTerm_var hnd] at ht
          exact absurd ht (by simp)
        · rw [show (decState tab s).code = decTerm tab s.code from rfl, decTerm_var hnd] at hm
          have hmn : m = n := by simpa using hm.symm
          subst hmn
          rw [show (decState tab s).env = decEnvP tab s.heap s.env from rfl, hwalk] at hnone
          cases hw : envNth s.heap s.env m with
          | none => exact hstep_var_none_eq hnd hw
          | some q =>
              rw [hw] at hnone
              exact absurd hnone (by simp)
  | app f a =>
      constructor
      · intro hnone
        rw [hstep_app_eq hnd] at hnone
        exact absurd hnone (by simp)
      · rintro (⟨⟨t', ht⟩, -⟩ | ⟨m, hm, -⟩)
        · rw [show (decState tab s).code = decTerm tab s.code from rfl,
            decTerm_app hv.tabWF hnd] at ht
          exact absurd ht (by simp)
        · rw [show (decState tab s).code = decTerm tab s.code from rfl,
            decTerm_app hv.tabWF hnd] at hm
          exact absurd hm (by simp)
  | lam b =>
      cases hst : s.stack with
      | nil =>
          constructor
          · intro _
            refine Or.inl ⟨⟨decTerm tab b, ?_⟩, ?_⟩
            · rw [show (decState tab s).code = decTerm tab s.code from rfl,
                decTerm_lam hv.tabWF hnd]
            · rw [show (decState tab s).stack = s.stack.map (decClos tab s.heap) from rfl, hst]
              simp
          · intro _
            exact hstep_lam_nil_eq hnd hst
      | cons p π =>
          constructor
          · intro hnone
            rw [hstep_lam_cons_eq hnd hst] at hnone
            exact absurd hnone (by simp)
          · rintro (⟨-, hnil⟩ | ⟨m, hm, -⟩)
            · rw [show (decState tab s).stack = s.stack.map (decClos tab s.heap) from rfl,
                hst] at hnil
              exact absurd hnil (by simp)
            · rw [show (decState tab s).code = decTerm tab s.code from rfl,
                decTerm_lam hv.tabWF hnd] at hm
              exact absurd hm (by simp)

/-- The initial state of the implementation is valid. -/
theorem valid_initState (t : Lambda) : Valid (tabOf t) (initState t) := by
  refine valid_mk (tabWF_tabOf t) (rootOf_lt t) ?_ ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp at hk
  · intro k hk
    simp at hk
  · intro p hp
    exact absurd hp (by simp)
  · intro p hp
    exact absurd hp (by simp)
  · intro p hp
    exact absurd hp (by simp)
  · intro p hp
    exact absurd hp (by simp)

/-- The initial state of the implementation decodes to the initial state of the machine. -/
theorem decState_initState (t : Lambda) :
    decState (tabOf t) (initState t) = State.init t := by
  simp [decState, initState, State.init, decTerm_tabOf]

end Impl

end Krivine
