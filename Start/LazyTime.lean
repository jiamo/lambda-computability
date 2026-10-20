/-
**A linear time bound for the call-by-need machine** — task `M25-CBNEED-TIME`.

The transitions of `Lazy.LTrans` are counted by kind, through one potential

  `Φ(s) = 3·(argument frames) − 2·(thunk cells) − (update markers) + [code is an abstraction]`.

Every transition costs one, and is paid as follows (`Lazy.LTrans.potential`):

* `app` pushes an argument frame (`+3`) and allocates a thunk (`−2`);
* `beta` pops an argument frame (`−3`) and is itself paid five;
* `force` turns a thunk into a hole (`+2`) and pushes an update marker (`−1`);
* `fetch` goes from a variable to the value of a cell, which is an abstraction (`+1`): every value
  cell holds an abstraction (`Lazy.ValOK`, preserved by every transition);
* `update` pops an update marker (`+1`).

This is the counting argument by transition kind: `#app = #β + (arguments left on the stack)`,
`#force ≤ #app` (each force consumes a thunk, and only `app` allocates thunks),
`#update ≤ #force` (each update pops a marker pushed by a force), and `#fetch ≤ #β + 1` (a fetch
ends on an abstraction, and only a β transition leaves one).

* `Lazy.LRun.time_bound`: **a run of `n` transitions with `b` β transitions from the initial state
  ends in a state `s` with `n ≤ 5·b + 3·(argument frames of s) + 1`**; in particular
  `n ≤ 5·b + 3·|stack of s| + 1` (`Lazy.LRun.time_bound_length`).  No dependence on the size of the
  term.
* `Lazy.LRun.time_bound_halt`: a run that ends with an empty stack (in particular a run that ends
  on a value) has `n ≤ 5·b + 1`.
-/

import Start.LazyMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lazy

/-- Thunk cells. -/
def Cell.isThunk : Cell → Bool
  | .thunk _ => true
  | _ => false

/-- Argument frames. -/
def Frame.isArg : Frame → Bool
  | .arg _ => true
  | .upd _ => false

/-- Update markers. -/
def Frame.isUpd : Frame → Bool
  | .arg _ => false
  | .upd _ => true

/-- `1` when the code is an abstraction. -/
def Lambda.isLamN : Lambda → ℕ
  | .lam _ => 1
  | _ => 0

/-- The positive part of the potential: `3·(argument frames) + [code is an abstraction]`. -/
def potPos (s : LState) : ℕ := 3 * s.stack.countP Frame.isArg + Lambda.isLamN s.code

/-- The negative part of the potential: `2·(thunk cells) + (update markers)`. -/
def potNeg (s : LState) : ℕ := 2 * s.heap.countP Cell.isThunk + s.stack.countP Frame.isUpd

/-- Every value cell holds an abstraction. -/
def ValOK (H : List Cell) : Prop :=
  ∀ (a : ℕ) (c v : LClos), H[a]? = some (Cell.value c v) → ∃ t, v.code = Lambda.lam t

theorem countP_set {α : Type} (p : α → Bool) :
    ∀ (H : List α) (a : ℕ) (x y : α), H[a]? = some x →
      (H.set a y).countP p + (if p x then 1 else 0) = H.countP p + (if p y then 1 else 0)
  | [], a, x, y, h => by simp at h
  | z :: H, 0, x, y, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.set_cons_zero, List.countP_cons]
      split_ifs <;> omega
  | z :: H, a + 1, x, y, h => by
      simp only [List.getElem?_cons_succ] at h
      have := countP_set p H a x y h
      simp only [List.set_cons_succ, List.countP_cons]
      omega

theorem ValOK.step {l : LLabel} {s s' : LState} (h : LTrans l s s') (hv : ValOK s.heap) :
    ValOK s'.heap := by
  cases h with
  | app t u e S H =>
      intro a c v ha
      by_cases hlt : a < H.length
      · rw [List.getElem?_append_left hlt] at ha
        exact hv a c v ha
      · rw [List.getElem?_append_right (by omega)] at ha
        cases h' : a - H.length with
        | zero => rw [h'] at ha; simp at ha
        | succ k => rw [h'] at ha; simp at ha
  | beta => exact hv
  | force n e S H a' c' he hc =>
      intro a c v ha
      by_cases hae : a = a'
      · subst hae
        have hlt : a < H.length := by
          by_contra hge; simp [List.getElem?_eq_none (by omega : H.length ≤ a)] at hc
        simp [List.getElem?_set_self hlt] at ha
      · rw [List.getElem?_set_ne (Ne.symm hae)] at ha
        exact hv a c v ha
  | fetch => exact hv
  | update t e a' S H c' hc =>
      intro a c v ha
      by_cases hae : a = a'
      · subst hae
        have hlt : a < H.length := by
          by_contra hge; simp [List.getElem?_eq_none (by omega : H.length ≤ a)] at hc
        simp only [List.getElem?_set_self hlt, Option.some.injEq, Cell.value.injEq] at ha
        obtain ⟨-, rfl⟩ := ha
        exact ⟨t, rfl⟩
      · rw [List.getElem?_set_ne (Ne.symm hae)] at ha
        exact hv a c v ha

/-- **The potential pays for every transition**: a β transition is paid five, every other
transition is paid by the drop of the potential. -/
theorem LTrans.potential {l : LLabel} {s s' : LState} (h : LTrans l s s') (hv : ValOK s.heap) :
    1 + potNeg s' + potPos s ≤ 5 * l.betaCount + potPos s' + potNeg s := by
  cases h with
  | app t u e S H =>
      simp only [potPos, potNeg, List.countP_cons, List.countP_append, Frame.isArg, Frame.isUpd,
        Cell.isThunk, LLabel.betaCount]
      cases t <;> simp [Lambda.isLamN] <;> omega
  | beta t e a S H =>
      simp only [potPos, potNeg, List.countP_cons, Frame.isArg, Frame.isUpd,
        LLabel.betaCount]
      cases t <;> simp [Lambda.isLamN] <;> omega
  | force n e S H a c he hc =>
      have hset := countP_set Cell.isThunk H a _ (.hole c) hc
      simp [Cell.isThunk] at hset
      simp only [potPos, potNeg, List.countP_cons, Frame.isArg, Frame.isUpd,
        LLabel.betaCount]
      cases c.code <;> simp [Lambda.isLamN] <;> omega
  | fetch n e S H a c v he hc =>
      obtain ⟨t, ht⟩ := hv a c v hc
      simp only [potPos, potNeg, LLabel.betaCount, ht, Lambda.isLamN]
      omega
  | update t e a S H c hc =>
      have hset := countP_set Cell.isThunk H a _ (.value c ⟨.lam t, e⟩) hc
      simp [Cell.isThunk] at hset
      simp only [potPos, potNeg, List.countP_cons, Lambda.isLamN, LLabel.betaCount]
      simp only [Frame.isArg, Frame.isUpd, Bool.false_eq_true, ↓reduceIte]
      omega

/-- The potential inequality summed along a run. -/
theorem LRun.potential {n b : ℕ} {fs : List ℕ} {s s' : LState} (h : LRun n b fs s s')
    (hv : ValOK s.heap) : n + potNeg s' + potPos s ≤ 5 * b + potPos s' + potNeg s := by
  induction h with
  | refl => omega
  | cons hstep _ ih =>
      have h1 := hstep.potential hv
      have h2 := ih (ValOK.step hstep hv)
      rw [Nat.mul_add]
      omega

/-- **Linear time bound for call-by-need**: a run of `n` transitions, `b` of them β, from the
initial state on any term ends in a state `s` with `n ≤ 5·b + 3·(argument frames of s) + 1`. -/
theorem LRun.time_bound {n b : ℕ} {fs : List ℕ} {t : Lambda} {s : LState}
    (h : LRun n b fs (LState.init t) s) :
    n ≤ 5 * b + 3 * s.stack.countP Frame.isArg + 1 := by
  have hv : ValOK (LState.init t).heap := fun a c v ha => by simp [LState.init] at ha
  have hp := h.potential hv
  have hl : Lambda.isLamN s.code ≤ 1 := by cases s.code <;> simp [Lambda.isLamN]
  simp only [potPos, potNeg, LState.init, List.countP_nil] at hp
  omega

/-- The time bound with the length of the final stack. -/
theorem LRun.time_bound_length {n b : ℕ} {fs : List ℕ} {t : Lambda} {s : LState}
    (h : LRun n b fs (LState.init t) s) : n ≤ 5 * b + 3 * s.stack.length + 1 := by
  have := h.time_bound
  have := List.countP_le_length (p := Frame.isArg) (l := s.stack)
  omega

/-- **Halting runs**: a run from the initial state that ends with an empty stack makes at most
`5·b + 1` transitions. -/
theorem LRun.time_bound_halt {n b : ℕ} {fs : List ℕ} {t : Lambda} {s : LState}
    (h : LRun n b fs (LState.init t) s) (hs : s.stack = []) : n ≤ 5 * b + 1 := by
  have := h.time_bound
  rw [hs] at this
  simpa using this

end Lazy
