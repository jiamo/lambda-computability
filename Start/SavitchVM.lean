/-
The machine that runs Savitch's recursion, and its memory bound.

Savitch's theorem is not just the midpoint identity of `Start/SavitchReach.lean`: the identity
turns the search for a walk into a recursion, and the theorem is the claim that the recursion can
be *executed* in small memory.  That claim is about an implementation, so this module gives one:
a deterministic stack machine whose only memory is a stack of activation records, each record
holding the two endpoints of a subproblem, its depth, the index of the midpoint currently being
tried — an index into an enumeration of the vertices, not a stored list of them — and one bit
saying which of the two legs is running.

Two things are proved about it, in one induction: it returns the value of the recursion
(`Complexity.Savitch.trace_call`), and *every state it passes through* carries at most `k` records
when it is started on a subproblem of depth `k`.  The memory bound is then a count of bits:
`Complexity.Savitch.memBits_le_of_trace`.  Instantiated at the configuration graph of a
nondeterministic machine running in space `s` (`Start/SavitchSpace.lean`), `k` and the size of a
record are both `O(s)`, which is Savitch's `O(s²)`.

Main definitions:

* `Complexity.Savitch.reachL` — the midpoint recursion with midpoints drawn from a list;
* `Complexity.Savitch.VM`, `Complexity.Savitch.step` — the stack machine;
* `Complexity.Savitch.Trace` — reachability of the machine along states of bounded stack height;
* `Complexity.Savitch.memBits` — the memory of a state, in bits.

Main results:

* `Complexity.Savitch.reachL_eq_reachB` — the recursion with an exhaustive list of midpoints is
  the recursion of `Start/SavitchReach.lean`;
* `Complexity.Savitch.trace_call` — the machine computes it, with at most `k` records alive;
* `Complexity.Savitch.memBits_le_of_trace` — hence in `(k + 1) · (2 w + 2 d + 1)` bits.
-/

import Mathlib
import Start.SavitchReach

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Savitch

open Complexity.Reach

variable {C : Type*}

/-! ### The recursion -/

/-- The midpoint recursion, with the midpoints drawn from the list `cs`. -/
def reachL [DecidableEq C] (r : C → C → Bool) (cs : List C) : ℕ → C → C → Bool
  | 0, a, b => (a == b) || r a b
  | k + 1, a, b => cs.any fun m => reachL r cs k a m && reachL r cs k m b

@[simp] theorem reachL_zero [DecidableEq C] (r : C → C → Bool) (cs : List C) (a b : C) :
    reachL r cs 0 a b = ((a == b) || r a b) := rfl

@[simp] theorem reachL_succ [DecidableEq C] (r : C → C → Bool) (cs : List C) (k : ℕ) (a b : C) :
    reachL r cs (k + 1) a b = cs.any fun m => reachL r cs k a m && reachL r cs k m b := rfl

/-- With an exhaustive list of midpoints the recursion is the one of `Start/SavitchReach.lean`. -/
theorem reachL_eq_reachB [Fintype C] [DecidableEq C] (r : C → C → Bool) (cs : List C)
    (hcs : ∀ c : C, c ∈ cs) :
    ∀ (k : ℕ) (a b : C), reachL r cs k a b = Reach.reachB r k a b := by
  intro k
  induction k with
  | zero => intro a b; rfl
  | succ k ih =>
      intro a b
      refine Bool.eq_iff_iff.2 ?_
      rw [reachL_succ, List.any_eq_true, Reach.reachB_succ]
      constructor
      · rintro ⟨m, -, hm⟩
        rw [Bool.and_eq_true] at hm
        exact ⟨m, by rw [← ih]; exact hm.1, by rw [← ih]; exact hm.2⟩
      · rintro ⟨m, h1, h2⟩
        exact ⟨m, hcs m, by rw [Bool.and_eq_true, ih, ih]; exact ⟨h1, h2⟩⟩

/-! ### The machine -/

/-- An activation record: the subproblem `a → b` at depth `k`, the index of the midpoint being
tried, and which of the two legs is running. -/
structure Frame (C : Type*) where
  /-- The source of the subproblem. -/
  a : C
  /-- The target of the subproblem. -/
  b : C
  /-- The depth of the two sub-calls. -/
  k : ℕ
  /-- The index of the midpoint currently being tried. -/
  idx : ℕ
  /-- Whether the first leg has already succeeded. -/
  second : Bool

/-- What the machine is doing: starting a subproblem, or returning an answer. -/
inductive Phase (C : Type*)
  /-- Decide whether `b` is reachable from `a` within `2 ^ k` steps. -/
  | call (a b : C) (k : ℕ)
  /-- Return the answer `v` to the caller. -/
  | ret (v : Bool)

/-- A state of the machine: what it is doing, and its stack of activation records. -/
structure VM (C : Type*) where
  /-- The current phase. -/
  phase : Phase C
  /-- The activation records, innermost first. -/
  stack : List (Frame C)

/-- Start the subproblem `a → b` at depth `k` with the midpoint of index `i`; if the enumeration
is exhausted, the answer is `false`. -/
def enter (cs : List C) (a b : C) (k i : ℕ) (st : List (Frame C)) : VM C :=
  match cs[i]? with
  | none => ⟨.ret false, st⟩
  | some m => ⟨.call a m k, ⟨a, b, k, i, false⟩ :: st⟩

/-- One step of the machine.  `none` means that it has finished: an answer with an empty stack. -/
def step [DecidableEq C] (r : C → C → Bool) (cs : List C) : VM C → Option (VM C)
  | ⟨.call a b 0, st⟩ => some ⟨.ret ((a == b) || r a b), st⟩
  | ⟨.call a b (k + 1), st⟩ => some (enter cs a b k 0 st)
  | ⟨.ret _, []⟩ => none
  | ⟨.ret v, f :: st⟩ =>
      if f.second then
        if v then some ⟨.ret true, st⟩ else some (enter cs f.a f.b f.k (f.idx + 1) st)
      else
        if v then
          match cs[f.idx]? with
          | none => some ⟨.ret false, st⟩
          | some m => some ⟨.call m f.b f.k, { f with second := true } :: st⟩
        else some (enter cs f.a f.b f.k (f.idx + 1) st)

/-- `Trace r cs B s t`: the machine runs from `s` to `t`, and every state it passes through —
including `s` and `t` — carries at most `B` activation records. -/
inductive Trace [DecidableEq C] (r : C → C → Bool) (cs : List C) (B : ℕ) : VM C → VM C → Prop
  /-- The empty run. -/
  | refl {s : VM C} (h : s.stack.length ≤ B) : Trace r cs B s s
  /-- One step, then a run. -/
  | head {s t u : VM C} (h : s.stack.length ≤ B) (hs : step r cs s = some t)
      (ht : Trace r cs B t u) : Trace r cs B s u

namespace Trace

variable [DecidableEq C] {r : C → C → Bool} {cs : List C} {B B' : ℕ} {s t u : VM C}

theorem stack_le_left (h : Trace r cs B s t) : s.stack.length ≤ B := by
  cases h with
  | refl h => exact h
  | head h _ _ => exact h

theorem stack_le_right (h : Trace r cs B s t) : t.stack.length ≤ B := by
  induction h with
  | refl h => exact h
  | head _ _ _ ih => exact ih

theorem trans (h₁ : Trace r cs B s t) (h₂ : Trace r cs B t u) : Trace r cs B s u := by
  induction h₁ with
  | refl _ => exact h₂
  | head h hs _ ih => exact .head h hs (ih h₂)

theorem mono (h : Trace r cs B s t) (hB : B ≤ B') : Trace r cs B' s t := by
  induction h with
  | refl h => exact .refl (le_trans h hB)
  | head h hs _ ih => exact .head (le_trans h hB) hs ih

theorem single (h : step r cs s = some t) (hs : s.stack.length ≤ B) (ht : t.stack.length ≤ B) :
    Trace r cs B s t :=
  .head hs h (.refl ht)

end Trace

/-! ### The machine computes the recursion -/

variable [DecidableEq C]

/-- The loop over the midpoints: starting the subproblem `a → b` at depth `k` with the midpoint of
index `i`, the machine returns whether some midpoint of index at least `i` splits `a → b`, and it
never holds more than `k + 1` activation records above the stack it started with. -/
theorem trace_enter (r : C → C → Bool) (cs : List C) (k : ℕ)
    (IH : ∀ (a b : C) (st : List (Frame C)),
      Trace r cs (st.length + k) ⟨.call a b k, st⟩ ⟨.ret (reachL r cs k a b), st⟩) :
    ∀ (N i : ℕ), cs.length - i ≤ N → ∀ (a b : C) (st : List (Frame C)),
      Trace r cs (st.length + (k + 1)) (enter cs a b k i st)
        ⟨.ret ((cs.drop i).any fun m => reachL r cs k a m && reachL r cs k m b), st⟩ := by
  intro N
  induction N with
  | zero =>
      intro i hi a b st
      have hlen : cs.length ≤ i := by omega
      have hnone : cs[i]? = none := List.getElem?_eq_none hlen
      have hdrop : cs.drop i = [] := List.drop_eq_nil_of_le hlen
      simp only [enter, hnone, hdrop, List.any_nil]
      exact .refl (by simp)
  | succ N ih =>
      intro i hi a b st
      by_cases hlen : cs.length ≤ i
      · have hnone : cs[i]? = none := List.getElem?_eq_none hlen
        have hdrop : cs.drop i = [] := List.drop_eq_nil_of_le hlen
        simp only [enter, hnone, hdrop, List.any_nil]
        exact .refl (by simp)
      · have hlt : i < cs.length := by omega
        obtain ⟨m, hm⟩ : ∃ m, cs[i]? = some m := ⟨cs[i], List.getElem?_eq_getElem hlt⟩
        have hmval : cs[i] = m := by
          have h := List.getElem?_eq_getElem hlt
          rw [hm] at h
          exact (Option.some.inj h).symm
        have hdrop : cs.drop i = m :: cs.drop (i + 1) := by
          rw [List.drop_eq_getElem_cons hlt, hmval]
        have henter : enter cs a b k i st =
            ⟨.call a m k, (⟨a, b, k, i, false⟩ : Frame C) :: st⟩ := by
          simp [enter, hm]
        rw [henter, hdrop, List.any_cons]
        have h1 : Trace r cs (st.length + (k + 1))
            (⟨.call a m k, (⟨a, b, k, i, false⟩ : Frame C) :: st⟩ : VM C)
            ⟨.ret (reachL r cs k a m), (⟨a, b, k, i, false⟩ : Frame C) :: st⟩ := by
          refine (IH a m ((⟨a, b, k, i, false⟩ : Frame C) :: st)).mono ?_
          simp
          omega
        refine h1.trans ?_
        cases h1v : reachL r cs k a m
        · have hstep : step r cs (⟨.ret false, (⟨a, b, k, i, false⟩ : Frame C) :: st⟩ : VM C)
              = some (enter cs a b k (i + 1) st) := rfl
          have hrec := ih (i + 1) (by omega) a b st
          simp only [Bool.false_and, Bool.false_or]
          exact Trace.head (by simp) hstep hrec
        · have hstep : step r cs (⟨.ret true, (⟨a, b, k, i, false⟩ : Frame C) :: st⟩ : VM C)
              = some ⟨.call m b k, (⟨a, b, k, i, true⟩ : Frame C) :: st⟩ := by
            simp [step, hm]
          have h2 : Trace r cs (st.length + (k + 1))
              (⟨.call m b k, (⟨a, b, k, i, true⟩ : Frame C) :: st⟩ : VM C)
              ⟨.ret (reachL r cs k m b), (⟨a, b, k, i, true⟩ : Frame C) :: st⟩ := by
            refine (IH m b ((⟨a, b, k, i, true⟩ : Frame C) :: st)).mono ?_
            simp
            omega
          simp only [Bool.true_and]
          refine Trace.head (by simp) hstep (h2.trans ?_)
          cases h2v : reachL r cs k m b
          · have hstep2 : step r cs (⟨.ret false, (⟨a, b, k, i, true⟩ : Frame C) :: st⟩ : VM C)
                = some (enter cs a b k (i + 1) st) := rfl
            have hrec := ih (i + 1) (by omega) a b st
            simp only [Bool.false_or]
            exact Trace.head (by simp) hstep2 hrec
          · have hstep2 : step r cs (⟨.ret true, (⟨a, b, k, i, true⟩ : Frame C) :: st⟩ : VM C)
                = some ⟨.ret true, st⟩ := rfl
            simp only [Bool.true_or]
            exact Trace.head (by simp) hstep2 (.refl (by simp))

/-- The machine computes the recursion, and never holds more than `k` activation records. -/
theorem trace_call (r : C → C → Bool) (cs : List C) :
    ∀ (k : ℕ) (a b : C) (st : List (Frame C)),
      Trace r cs (st.length + k) ⟨.call a b k, st⟩ ⟨.ret (reachL r cs k a b), st⟩ := by
  intro k
  induction k with
  | zero =>
      intro a b st
      exact .single rfl (by simp) (by simp)
  | succ k ih =>
      intro a b st
      have hstep : step r cs ⟨.call a b (k + 1), st⟩ = some (enter cs a b k 0 st) := rfl
      have hrun := trace_enter r cs k ih cs.length 0 (by omega) a b st
      refine .head (by simp) hstep ?_
      simpa using hrun

/-! ### The memory bound -/

/-- The memory of a state, in bits, when a vertex takes `w` bits and each counter takes `d` bits:
one record per activation, plus the phase. -/
def memBits (w d : ℕ) (v : VM C) : ℕ := (v.stack.length + 1) * (2 * w + 2 * d + 1)

/-- Along a run with at most `B` records alive, the memory never exceeds `(B + 1)` records. -/
theorem memBits_le_of_trace {r : C → C → Bool} {cs : List C} {B w d : ℕ} {s t : VM C}
    (h : Trace r cs B s t) : memBits w d s ≤ (B + 1) * (2 * w + 2 * d + 1) :=
  Nat.mul_le_mul_right _ (by have := h.stack_le_left; omega)

/-- The same bound for every state the run passes through: a visited state is the endpoint of an
initial segment of the run. -/
theorem memBits_le_of_visited {r : C → C → Bool} {cs : List C} {B w d : ℕ} {s u : VM C}
    (h : Trace r cs B s u) : memBits w d u ≤ (B + 1) * (2 * w + 2 * d + 1) :=
  Nat.mul_le_mul_right _ (by have := h.stack_le_right; omega)

end Complexity.Savitch
