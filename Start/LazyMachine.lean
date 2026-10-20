/-
**A call-by-need (lazy) abstract machine, in the style of Sestoft** — task `M25-CBNEED-MACHINE`.

The machine of `Start/Krivine.lean` is call-by-name: an argument is a closure that is copied into
the environment and re-evaluated at every use.  The lazy machine here shares arguments through a
heap:

* a **heap** of cells (`Lazy.Cell`): a `thunk` (an unevaluated closure), a `hole` (a thunk under
  evaluation, Sestoft's black hole), or a `value` (an evaluated closure, whose code is an
  abstraction).  Every cell remembers the closure it was allocated with (`Cell.orig`);
* **environments** map de Bruijn indices to heap addresses;
* the **stack** holds argument addresses (`Frame.arg`) and update markers (`Frame.upd`).

Transitions (`Lazy.LTrans`):

* `app`   — `t u` allocates a thunk for the closure of `u` and pushes its address;
* `beta`  — `λt` pops an argument address into the environment (the only β transition);
* `force` — a variable bound to a thunk: the cell becomes a hole, an update marker is pushed, and
  the thunk's closure is evaluated;
* `fetch` — a variable bound to a value: the value is returned, without re-evaluation;
* `update` — a value meeting an update marker overwrites the marked cell with the value.

Main results:

* `Lazy.LTrans.deterministic` — the machine is deterministic;
* `Lazy.LRun.value_persist` — **once a cell holds a value, it holds that value for ever** (in
  particular it is never a thunk again);
* `Lazy.LRun.forced_nodup` — **in any run, each address is forced from a thunk at most once**.
-/

import Start.KrivineDecode

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lazy

/-- A closure of the lazy machine: code and an environment of heap addresses. -/
structure LClos where
  /-- The code. -/
  code : Lambda
  /-- The environment: heap addresses, one per de Bruijn index. -/
  env : List ℕ

/-- A heap cell. -/
inductive Cell where
  /-- An unevaluated closure. -/
  | thunk (c : LClos)
  /-- A thunk under evaluation (a black hole), remembering its closure. -/
  | hole (c : LClos)
  /-- An evaluated thunk: its original closure `c` and its value `v`. -/
  | value (c : LClos) (v : LClos)

/-- The closure a cell was allocated with. -/
def Cell.orig : Cell → LClos
  | thunk c => c
  | hole c => c
  | value c _ => c

/-- A stack frame. -/
inductive Frame where
  /-- An argument, by address. -/
  | arg (a : ℕ)
  /-- An update marker for the cell at an address. -/
  | upd (a : ℕ)

/-- A state of the lazy machine. -/
structure LState where
  /-- The code. -/
  code : Lambda
  /-- The environment. -/
  env : List ℕ
  /-- The stack. -/
  stack : List Frame
  /-- The heap. -/
  heap : List Cell

/-- The initial state on a term. -/
def LState.init (t : Lambda) : LState := ⟨t, [], [], []⟩

/-- The labels of the transitions; `force` records the address it forces. -/
inductive LLabel where
  | app
  | beta
  | force (a : ℕ)
  | fetch
  | update

/-- The number of β-steps a transition performs. -/
def LLabel.betaCount : LLabel → ℕ
  | beta => 1
  | _ => 0

/-- The addresses a transition forces. -/
def LLabel.forced : LLabel → List ℕ
  | force a => [a]
  | _ => []

/-- **The transitions of the lazy machine.** -/
inductive LTrans : LLabel → LState → LState → Prop
  | app (t u : Lambda) (e : List ℕ) (S : List Frame) (H : List Cell) :
      LTrans .app ⟨.app t u, e, S, H⟩ ⟨t, e, .arg H.length :: S, H ++ [.thunk ⟨u, e⟩]⟩
  | beta (t : Lambda) (e : List ℕ) (a : ℕ) (S : List Frame) (H : List Cell) :
      LTrans .beta ⟨.lam t, e, .arg a :: S, H⟩ ⟨t, a :: e, S, H⟩
  | force (n : ℕ) (e : List ℕ) (S : List Frame) (H : List Cell) (a : ℕ) (c : LClos)
      (he : e[n]? = some a) (hc : H[a]? = some (.thunk c)) :
      LTrans (.force a) ⟨.var n, e, S, H⟩ ⟨c.code, c.env, .upd a :: S, H.set a (.hole c)⟩
  | fetch (n : ℕ) (e : List ℕ) (S : List Frame) (H : List Cell) (a : ℕ) (c v : LClos)
      (he : e[n]? = some a) (hc : H[a]? = some (.value c v)) :
      LTrans .fetch ⟨.var n, e, S, H⟩ ⟨v.code, v.env, S, H⟩
  | update (t : Lambda) (e : List ℕ) (a : ℕ) (S : List Frame) (H : List Cell) (c : LClos)
      (hc : H[a]? = some (.hole c)) :
      LTrans .update ⟨.lam t, e, .upd a :: S, H⟩
        ⟨.lam t, e, S, H.set a (.value c ⟨.lam t, e⟩)⟩

/-- One transition, label forgotten. -/
def LStep (s s' : LState) : Prop := ∃ l, LTrans l s s'

/-- A state is final when no transition applies. -/
def LFinal (s : LState) : Prop := ∀ s', ¬ LStep s s'

/-- A run: `LRun n b fs s s'` — `n` transitions, `b` of them β, forcing the addresses `fs`. -/
inductive LRun : ℕ → ℕ → List ℕ → LState → LState → Prop
  | refl (s : LState) : LRun 0 0 [] s s
  | cons {l : LLabel} {n b : ℕ} {fs : List ℕ} {s₁ s₂ s₃ : LState} :
      LTrans l s₁ s₂ → LRun n b fs s₂ s₃ → LRun (n + 1) (b + l.betaCount) (l.forced ++ fs) s₁ s₃

/-- **The lazy machine is deterministic.** -/
theorem LTrans.deterministic {l l' : LLabel} {s s₁ s₂ : LState} (h₁ : LTrans l s s₁)
    (h₂ : LTrans l' s s₂) : l = l' ∧ s₁ = s₂ := by
  cases h₁ with
  | app => cases h₂; exact ⟨rfl, rfl⟩
  | beta => cases h₂; exact ⟨rfl, rfl⟩
  | force n e S H a c he hc =>
      cases h₂ with
      | force _ _ _ _ a' c' he' hc' =>
          rw [he] at he'; cases he'
          rw [hc] at hc'; cases hc'
          exact ⟨rfl, rfl⟩
      | fetch _ _ _ _ a' c' v' he' hc' =>
          rw [he] at he'; cases he'
          rw [hc] at hc'; cases hc'
  | fetch n e S H a c v he hc =>
      cases h₂ with
      | force _ _ _ _ a' c' he' hc' =>
          rw [he] at he'; cases he'
          rw [hc] at hc'; cases hc'
      | fetch _ _ _ _ a' c' v' he' hc' =>
          rw [he] at he'; cases he'
          rw [hc] at hc'; cases hc'
          exact ⟨rfl, rfl⟩
  | update t e a S H c hc =>
      cases h₂ with
      | update _ _ _ _ _ c' hc' =>
          rw [hc] at hc'; cases hc'
          exact ⟨rfl, rfl⟩

theorem LStep.deterministic {s s₁ s₂ : LState} (h₁ : LStep s s₁) (h₂ : LStep s s₂) : s₁ = s₂ :=
  (LTrans.deterministic h₁.choose_spec h₂.choose_spec).2

/-! ### Sharing -/

theorem LTrans.heap_length_le {l : LLabel} {s s' : LState} (h : LTrans l s s') :
    s.heap.length ≤ s'.heap.length := by
  cases h <;> simp

/-- **A value stays the same value**: one transition never changes a cell holding a value. -/
theorem LTrans.value_persist {l : LLabel} {s s' : LState} (h : LTrans l s s') {a : ℕ}
    {c v : LClos} (ha : s.heap[a]? = some (.value c v)) : s'.heap[a]? = some (.value c v) := by
  cases h with
  | app t u e S H =>
      have hlt : a < H.length := by
        by_contra hge; simp [List.getElem?_eq_none (by omega : H.length ≤ a)] at ha
      simpa [List.getElem?_append_left hlt] using ha
  | beta => exact ha
  | force n e S H a' c' he hc =>
      by_cases hae : a = a'
      · subst hae; simp_all
      · simpa [List.getElem?_set_ne (Ne.symm hae)] using ha
  | fetch => exact ha
  | update t e a' S H c' hc =>
      by_cases hae : a = a'
      · subst hae; simp_all
      · simpa [List.getElem?_set_ne (Ne.symm hae)] using ha

/-- **Once a cell holds a value it holds that value for ever** along any run. -/
theorem LRun.value_persist {n b : ℕ} {fs : List ℕ} {s s' : LState} (h : LRun n b fs s s')
    {a : ℕ} {c v : LClos} (ha : s.heap[a]? = some (.value c v)) :
    s'.heap[a]? = some (.value c v) := by
  induction h with
  | refl => exact ha
  | cons hstep _ ih => exact ih (hstep.value_persist ha)

/-- In particular a cell overwritten by a value is never a thunk again. -/
theorem LRun.value_not_thunk {n b : ℕ} {fs : List ℕ} {s s' : LState} (h : LRun n b fs s s')
    {a : ℕ} {c v : LClos} (ha : s.heap[a]? = some (.value c v)) (c' : LClos) :
    s'.heap[a]? ≠ some (.thunk c') := by
  rw [h.value_persist ha]
  simp

/-- A cell that exists and is not a thunk is never a thunk after one transition. -/
theorem LTrans.not_thunk_persist {l : LLabel} {s s' : LState} (h : LTrans l s s') {a : ℕ}
    (hlt : a < s.heap.length) (hnt : ∀ c, s.heap[a]? ≠ some (.thunk c)) :
    a < s'.heap.length ∧ ∀ c, s'.heap[a]? ≠ some (.thunk c) := by
  refine ⟨lt_of_lt_of_le hlt h.heap_length_le, ?_⟩
  cases h with
  | app t u e S H =>
      intro c
      simpa [List.getElem?_append_left hlt] using hnt c
  | beta => exact hnt
  | force n e S H a' c' he hc =>
      intro c
      by_cases hae : a = a'
      · subst hae; simp [List.getElem?_set_self hlt]
      · simpa [List.getElem?_set_ne (Ne.symm hae)] using hnt c
  | fetch => exact hnt
  | update t e a' S H c' hc =>
      intro c
      by_cases hae : a = a'
      · subst hae; simp [List.getElem?_set_self hlt]
      · simpa [List.getElem?_set_ne (Ne.symm hae)] using hnt c

/-- A forced address held a thunk, and holds a non-thunk afterwards. -/
theorem LTrans.forced_spec {l : LLabel} {s s' : LState} (h : LTrans l s s') {a : ℕ}
    (ha : a ∈ l.forced) :
    (∃ c, s.heap[a]? = some (.thunk c)) ∧ a < s'.heap.length ∧
      ∀ c, s'.heap[a]? ≠ some (.thunk c) := by
  cases h with
  | force n e S H a' c' he hc =>
      simp only [LLabel.forced, List.mem_singleton] at ha
      subst ha
      have hlt : a < H.length := by
        by_contra hge; simp [List.getElem?_eq_none (by omega : H.length ≤ a)] at hc
      exact ⟨⟨c', hc⟩, by simpa using hlt, fun c => by simp [List.getElem?_set_self hlt]⟩
  | _ => simp [LLabel.forced] at ha

theorem LRun.not_forced {n b : ℕ} {fs : List ℕ} {s s' : LState} (h : LRun n b fs s s') {a : ℕ}
    (hlt : a < s.heap.length) (hnt : ∀ c, s.heap[a]? ≠ some (.thunk c)) : a ∉ fs := by
  induction h with
  | refl => simp
  | cons hstep _ ih =>
      simp only [List.mem_append, not_or]
      refine ⟨fun hm => ?_, ?_⟩
      · obtain ⟨⟨c, hc⟩, _⟩ := hstep.forced_spec hm
        exact hnt c hc
      · obtain ⟨hlt', hnt'⟩ := hstep.not_thunk_persist hlt hnt
        exact ih hlt' hnt'

/-- **Sharing: in any run, each address is forced from a thunk at most once.** -/
theorem LRun.forced_nodup {n b : ℕ} {fs : List ℕ} {s s' : LState} (h : LRun n b fs s s') :
    fs.Nodup := by
  induction h with
  | refl => simp
  | @cons l _ _ fs' _ _ _ hstep hrun ih =>
      refine List.nodup_append.2 ⟨?_, ih, ?_⟩
      · cases l <;> simp [LLabel.forced]
      · intro a ha b hb hab
        subst hab
        obtain ⟨_, hlt, hnt⟩ := hstep.forced_spec ha
        exact hrun.not_forced hlt hnt hb

end Lazy
