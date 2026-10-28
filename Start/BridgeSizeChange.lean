/-
**Bridge: size-change termination certifies the host's counter machines** — milestone M31
(`M31-BRIDGE-SIZECHANGE`).

`Start/SizeChange.lean` and `Start/SizeChangeCallGraph.lean` prove the size-change principle of
Lee, Jones and Ben-Amram for call graphs labelled by size-change graphs.  The host's two-counter
machines (`FsubGhelli.CM`, `Start/FsubGhelli.lean`) have an undecidable halting problem
(`Minsky.Universal.cm_halts_not_lambdaDecidable`, `Start/BridgeMinsky.lean`).  This module reads a
counter machine as a call graph and shows that size-change termination of that graph is a
sufficient condition for halting on every input.

* `FsubGhelli.CM.callGraph` — the call graph of a machine: one function per label of the program,
  the two counters as parameters, one call per transition into the program, labelled by the
  size-change graph of the transition (an increment drops the arc of its counter, a decrement is
  a strict arc, a zero test keeps both counters);
* `FsubGhelli.CM.callGraph_wf` — the call graph is well formed;
* `FsubGhelli.CM.next`, `FsubGhelli.CM.step_next`, `FsubGhelli.CM.descent` — the transition
  function and the soundness of the graphs: every arc bounds the new value of a counter by the
  old one, strictly for a strict arc;
* **`FsubGhelli.CM.halts_of_sct`** — **a counter machine whose call graph is size-change
  terminating halts on every input**; `FsubGhelli.CM.halts_of_criterion` — the same from the
  closure criterion.
-/

import Start.SizeChangeCallGraph
import Start.BridgeMinsky

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace FsubGhelli

open SizeChange

namespace CM

variable (M : CM)

/-- The arcs keeping the first counter. -/
def keepA : SCG 2 := {((0 : Fin 2), (0 : Fin 2), false)}

/-- The arcs keeping the second counter. -/
def keepB : SCG 2 := {((1 : Fin 2), (1 : Fin 2), false)}

/-- The arcs keeping both counters. -/
def keepAB : SCG 2 := {((0 : Fin 2), (0 : Fin 2), false), ((1 : Fin 2), (1 : Fin 2), false)}

/-- The arcs of a decrement of the first (`true`) or second counter. -/
def decG : Bool → SCG 2
  | true => {((0 : Fin 2), (0 : Fin 2), true), ((1 : Fin 2), (1 : Fin 2), false)}
  | false => {((0 : Fin 2), (0 : Fin 2), false), ((1 : Fin 2), (1 : Fin 2), true)}

/-- A call from `pc` to the label `l`, if `l` is in the program. -/
def callTo (pc : Fin M.length) (l : ℕ) (G : SCG 2) : Finset (Fin M.length × Fin M.length × SCG 2) :=
  if h : l < M.length then {(pc, ⟨l, h⟩, G)} else ∅

/-- The calls of the instruction at `pc`. -/
def instrCalls (pc : Fin M.length) : CMInstr → Finset (Fin M.length × Fin M.length × SCG 2)
  | .inc true l => callTo M pc l keepB
  | .inc false l => callTo M pc l keepA
  | .test r l₁ l₂ => callTo M pc l₁ keepAB ∪ callTo M pc l₂ (decG r)

/-- **The call graph of a counter machine.** -/
def callGraph : CallGraph M.length 2 where
  arity := fun _ => 2
  calls := Finset.univ.biUnion fun pc : Fin M.length => instrCalls M pc (M.get pc)

theorem callGraph_wf : (callGraph M).WF := fun _ _ _ _ x y _ _ => ⟨x.isLt, y.isLt⟩

/-- The value of a counter. -/
def cval (c : CMConf) (x : Fin 2) : ℕ := if x.val = 0 then c.a else c.b

/-- The transition function. -/
def next (c : CMConf) : CMConf :=
  match M[c.pc]? with
  | some (.inc true l) => ⟨l, c.a + 1, c.b⟩
  | some (.inc false l) => ⟨l, c.a, c.b + 1⟩
  | some (.test true l₁ l₂) => if c.a = 0 then ⟨l₁, c.a, c.b⟩ else ⟨l₂, c.a - 1, c.b⟩
  | some (.test false l₁ l₂) => if c.b = 0 then ⟨l₁, c.a, c.b⟩ else ⟨l₂, c.a, c.b - 1⟩
  | none => c

/-- The size-change graph of the transition from a configuration. -/
def graph (c : CMConf) : SCG 2 :=
  match M[c.pc]? with
  | some (.inc true _) => keepB
  | some (.inc false _) => keepA
  | some (.test true _ _) => if c.a = 0 then keepAB else decG true
  | some (.test false _ _) => if c.b = 0 then keepAB else decG false
  | none => ∅

theorem step_next {c : CMConf} (h : c.pc < M.length) : CM.Step M c (next M c) := by
  have hget : M[c.pc]? = some (M.get ⟨c.pc, h⟩) := by simp
  unfold next
  rw [hget]
  rcases hi : M.get ⟨c.pc, h⟩ with (_ | _) | ⟨(_ | _), l₁, l₂⟩
  · rw [hi] at hget; exact .incB hget
  · rw [hi] at hget; exact .incA hget
  · rw [hi] at hget
    simp only
    split
    · next hb => exact .zeroB hget hb
    · next hb =>
        obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hb
        have : c.b - 1 = n := by omega
        rw [this]
        exact .decB hget hn
  · rw [hi] at hget
    simp only
    split
    · next ha => exact .zeroA hget ha
    · next ha =>
        obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero ha
        have : c.a - 1 = n := by omega
        rw [this]
        exact .decA hget hn

theorem call_next {c : CMConf} (h : c.pc < M.length) (h' : (next M c).pc < M.length) :
    ((⟨c.pc, h⟩ : Fin M.length), (⟨(next M c).pc, h'⟩ : Fin M.length), graph M c) ∈
      (callGraph M).calls := by
  have hget : M[c.pc]? = some (M.get ⟨c.pc, h⟩) := by simp
  simp only [callGraph, Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine ⟨⟨c.pc, h⟩, ?_⟩
  revert h'
  unfold next graph
  rw [hget]
  rcases M.get ⟨c.pc, h⟩ with (_ | _) | ⟨(_ | _), l₁, l₂⟩
  · intro h'; simp [instrCalls, callTo, h']
  · intro h'; simp [instrCalls, callTo, h']
  · simp only
    split
    · intro h'; simp [instrCalls, callTo, h']
    · intro h'; simp [instrCalls, callTo, h']
  · simp only
    split
    · intro h'; simp [instrCalls, callTo, h']
    · intro h'; simp [instrCalls, callTo, h']

/-- **The graphs are sound**: along an arc `x → y` of the graph of a transition the new value of
`y` is at most the old value of `x`, and smaller for a strict arc. -/
theorem descent (c : CMConf) {x y : Fin 2} {s : Bool} (hm : (x, y, s) ∈ graph M c) :
    cval (next M c) y ≤ cval c x ∧ (s = true → cval (next M c) y < cval c x) := by
  revert hm
  unfold next graph
  rcases M[c.pc]? with _ | ((_ | _) | ⟨(_ | _), l₁, l₂⟩)
  · simp
  · simp only [keepA, Finset.mem_singleton, Prod.mk.injEq]
    rintro ⟨rfl, rfl, rfl⟩
    simp [cval]
  · simp only [keepB, Finset.mem_singleton, Prod.mk.injEq]
    rintro ⟨rfl, rfl, rfl⟩
    simp [cval]
  · simp only
    split
    · simp only [keepAB, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> simp [cval]
    · next hb =>
        simp only [decG, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
        · simp [cval]
        · simp [cval]; omega
  · simp only
    split
    · simp only [keepAB, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> simp [cval]
    · next ha =>
        simp only [decG, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
        · simp [cval]; omega
        · simp [cval]

/-- No sequence of naturals that never increases along a thread can decrease infinitely often. -/
theorem no_infinite_descent (h : ℕ → ℕ) (i : ℕ) (hmono : ∀ p, i ≤ p → h (p + 1) ≤ h p)
    (l : ℕ → Bool) (hstrict : ∀ p, i ≤ p → l p = true → h (p + 1) < h p)
    (hinf : ∀ N, ∃ p, N ≤ p ∧ i ≤ p ∧ l p = true) : False := by
  have hle : ∀ p, i ≤ p → ∀ k, h (p + k) ≤ h p := by
    intro p hp k
    induction k with
    | zero => rfl
    | succ k ih => exact (hmono (p + k) (by omega)).trans ih
  have key : ∀ N, ∃ p, i ≤ p ∧ h p + N ≤ h i := by
    intro N
    induction N with
    | zero => exact ⟨i, le_rfl, by omega⟩
    | succ N ih =>
        obtain ⟨p, hp, hpN⟩ := ih
        obtain ⟨q, hq, hiq, hl⟩ := hinf p
        have h1 := hstrict q hiq hl
        have h2 : h q ≤ h p := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hq
          exact hle p hp k
        exact ⟨q + 1, by omega, by omega⟩
  obtain ⟨p, -, hp⟩ := key (h i + 1)
  omega

/-- **Size-change termination certifies halting**: a counter machine whose call graph is
size-change terminating halts on every input. -/
theorem halts_of_sct (hsct : (callGraph M).SCT) (a b : ℕ) : CM.Halts M a b := by
  by_contra hn
  let run : ℕ → CMConf := fun k => (next M)^[k] ⟨0, a, b⟩
  have hrun_succ : ∀ k, run (k + 1) = next M (run k) := fun k =>
    Function.iterate_succ_apply' _ _ _
  have hreach : ∀ k, Relation.ReflTransGen (CM.Step M) ⟨0, a, b⟩ (run k) ∧
      (run k).pc < M.length := by
    intro k
    induction k with
    | zero =>
        refine ⟨Relation.ReflTransGen.refl, ?_⟩
        by_contra hge
        exact hn ⟨_, Relation.ReflTransGen.refl, not_lt.mp hge⟩
    | succ k ih =>
        have hr : Relation.ReflTransGen (CM.Step M) ⟨0, a, b⟩ (run (k + 1)) := by
          rw [hrun_succ]
          exact ih.1.tail (step_next M ih.2)
        refine ⟨hr, ?_⟩
        by_contra hge
        exact hn ⟨_, hr, not_lt.mp hge⟩
  let fn : ℕ → Fin M.length := fun k => ⟨(run k).pc, (hreach k).2⟩
  let g : ℕ → SCG 2 := fun k => graph M (run k)
  have hcalls : ∀ k, (fn k, fn (k + 1), g k) ∈ (callGraph M).calls := by
    intro k
    have h' : (next M (run k)).pc < M.length := by
      rw [← hrun_succ]
      exact (hreach (k + 1)).2
    have := call_next M (hreach k).2 h'
    simp only [fn, g]
    convert this using 3
    exact Fin.ext (by simp only [hrun_succ])
  obtain ⟨i, t, l, hthread, hinf⟩ := hsct fn g hcalls
  refine no_infinite_descent (fun p => cval (run p) (t p)) i (fun p hp => ?_) l
    (fun p hp hl => ?_) hinf
  · have := (descent M (run p) (hthread p hp)).1
    simp only [hrun_succ]
    exact this
  · have := (descent M (run p) (hthread p hp)).2 hl
    simp only [hrun_succ]
    exact this

/-- The closure criterion, a decidable condition on the finite call graph, certifies halting on
every input. -/
theorem halts_of_criterion (hc : (callGraph M).Criterion) (a b : ℕ) : CM.Halts M a b :=
  halts_of_sct M (CallGraph.sct_of_criterion hc) a b

end CM

end FsubGhelli
