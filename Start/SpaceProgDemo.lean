/-
**A worked client of the space bridge: "the input contains a `1`" in constant space.**

This module exercises `Start/SpaceCompile.lean` and `Start/SpaceProg.lean` end to end on the
smallest honest example: an abstract machine that scans its input for a `true` bit, a three-line
tape program that performs one of its steps, the single bridge lemma relating the two, and the
resulting membership of the language `{x | true ∈ x}` in `DSPACE 1`.  Nothing here is hard; the
point is that the client supplies only the step-level facts (`Complexity.Space.Demo.exec_step`)
and gets the machine, its determinism, its well-formedness, the acceptance equivalence and the
space bound of every reachable configuration from the general theorems.

Main definitions:

* `Complexity.Space.Demo.scan` — the abstract scanner; its state is the input, the position read
  so far, and the one-cell tape it keeps;
* `Complexity.Space.Demo.body` — the tape program for one scanner step.

Main results:

* `Complexity.Space.Demo.exec_step` — the bridge lemma: the program performs each scanner step on
  the encoding of the state;
* `Complexity.Space.Demo.scan_accepts_iff` — the scanner accepts exactly the words containing
  `true`;
* `Complexity.Space.Demo.dspace_hasTrue` — hence `{x | true ∈ x}` is in `DSPACE 1`.
-/

import Mathlib
import Start.SpaceProg

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space.Demo

open Prog

/-- The state of the scanner: the input, the position of the input head, and the contents of its
one-cell work tape (`[]` before the first step, `[false]` while scanning, `[true]` once a `true`
bit has been found). -/
abbrev St := List Bool × ℕ × List Bool

/-- The scanner: halt (accepting) once the tape says `true`; otherwise read the input — a `true`
bit is recorded on the tape, the end marker makes it loop forever (rejecting), a `false` bit moves
on. -/
def scan : AbsMachine St where
  start x := (x, 0, [])
  step s :=
    if s.2.2 = [true] then none
    else if s.1[s.2.1]? = some true then some (s.1, s.2.1, [true])
    else if s.1[s.2.1]? = none then some (s.1, s.2.1, [false])
    else some (s.1, s.2.1 + 1, [false])
  accept s := decide (s.2.2 = [true])

/-- The encoding of a scanner state as a configuration. -/
def enc (_ : List Bool) (s : St) : Config := ⟨0, s.2.1, s.2.2, 0⟩

/-- The main-loop test: continue while the work bit is `false`. -/
def test : Test := fun _ w => !w

/-- One scanner step as a tape program. -/
def body : Prog :=
  .ite (fun a _ => decide (a = some true)) (write true)
    (.ite (fun a _ => decide (a = none)) skip (imove .right))

/-- The reachable states of the scanner. -/
def Inv (x : List Bool) (s : St) : Prop :=
  s.1 = x ∧ s.2.1 ≤ x.length ∧ (s.2.2 = [] ∨ s.2.2 = [false] ∨ s.2.2 = [true]) ∧
    (s.2.2 = [] → s.2.1 = 0) ∧ (∀ j < s.2.1, x[j]? = some false) ∧
    (s.2.2 = [true] → x[s.2.1]? = some true)

theorem inv_of_reaches {x : List Bool} {s : St} (h : scan.Reaches x s) : Inv x s := by
  induction h with
  | refl =>
      change Inv x (x, 0, [])
      exact ⟨rfl, Nat.zero_le _, Or.inl rfl, fun _ => rfl,
        fun j hj => absurd hj (Nat.not_lt_zero j), fun h => by simp at h⟩
  | @tail s t _ hst ih =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
      obtain ⟨y, i, tp⟩ := s
      simp only at h1 h2 h3 h4 h5 h6
      subst h1
      simp only [AbsMachine.StepRel, scan] at hst
      split_ifs at hst with ha hb hc
      · obtain rfl := Option.some.inj hst.symm
        exact ⟨rfl, h2, Or.inr (Or.inr rfl), by simp, h5, fun _ => hb⟩
      · obtain rfl := Option.some.inj hst.symm
        exact ⟨rfl, h2, Or.inr (Or.inl rfl), by simp, h5, by simp⟩
      · obtain rfl := Option.some.inj hst.symm
        have hlt : i < y.length := by
          by_contra hge
          exact hc (List.getElem?_eq_none (by omega))
        have hfalse : y[i]? = some false := by
          rw [List.getElem?_eq_getElem hlt] at hb ⊢
          simpa using hb
        refine ⟨rfl, by simp only; omega, Or.inr (Or.inl rfl), by simp, ?_, by simp⟩
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact h5 j hj
        · exact hfalse

/-- **The bridge lemma**: the tape program performs each step of the scanner on the encoding of
its state, within one cell. -/
theorem exec_step (x : List Bool) (s s' : St) (hs : scan.Reaches x s)
    (hst : scan.step s = some s') :
    test (rdIn x (enc x s)) (rdW (enc x s)) = true ∧
      Exec x (fun c => c.space ≤ 1) body (touch x (enc x s)) (enc x s') := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := inv_of_reaches hs
  obtain ⟨y, i, tp⟩ := s
  simp only at h1 h2 h3 h4 h5 h6
  subst h1
  simp only [scan] at hst
  split_ifs at hst with ha hb hc
  · -- a `true` bit: record it
    obtain rfl := Option.some.inj hst.symm
    have htp : tp = [] ∨ tp = [false] := by rcases h3 with h | h | h <;> simp_all
    have ht : touch y (enc y (y, i, tp)) = ⟨0, i, [false], 0⟩ := by
      rcases htp with rfl | rfl <;> rfl
    refine ⟨by rcases htp with rfl | rfl <;> rfl, ?_⟩
    rw [ht]
    refine Exec.iteT (by simp [Config.space]) (by simp [rdIn, hb]) ?_
    exact Exec.act (by simp [touch, eff, rdW, Config.space, writeAt, moveWork])
  · -- the end marker: loop, rejecting
    obtain rfl := Option.some.inj hst.symm
    have htp : tp = [] ∨ tp = [false] := by rcases h3 with h | h | h <;> simp_all
    have ht : touch y (enc y (y, i, tp)) = ⟨0, i, [false], 0⟩ := by
      rcases htp with rfl | rfl <;> rfl
    refine ⟨by rcases htp with rfl | rfl <;> rfl, ?_⟩
    rw [ht]
    refine Exec.iteF (by simp [Config.space]) (by simp [rdIn, hc]) ?_
    refine Exec.iteT (by simp [touch, eff, rdW, Config.space, writeAt, moveWork])
      (by simpa [rdIn, touch, eff, moveIn] using hc) ?_
    exact Exec.act (by simp [touch, eff, rdW, Config.space, writeAt, moveWork])
  · -- a `false` bit: move on
    obtain rfl := Option.some.inj hst.symm
    have htp : tp = [] ∨ tp = [false] := by rcases h3 with h | h | h <;> simp_all
    have ht : touch y (enc y (y, i, tp)) = ⟨0, i, [false], 0⟩ := by
      rcases htp with rfl | rfl <;> rfl
    have hlt : i < y.length := by
      by_contra hge
      exact hc (List.getElem?_eq_none (by omega))
    refine ⟨by rcases htp with rfl | rfl <;> rfl, ?_⟩
    rw [ht]
    refine Exec.iteF (by simp [Config.space]) (by simp [rdIn, hb]) ?_
    refine Exec.iteF (by simp [touch, eff, rdW, Config.space, writeAt, moveWork])
      (by simpa [rdIn, touch, eff, moveIn] using hc) ?_
    have := Exec.act (x := y) (P := fun c => c.space ≤ 1)
      (f := fun _ w => (w, Dir.right, Dir.stay))
      (c := touch y (touch y ⟨0, i, [false], 0⟩))
      (by simp [touch, eff, rdW, Config.space, writeAt, moveWork])
    have heq : enc y (y, i + 1, [false]) = eff y (touch y (touch y ⟨0, i, [false], 0⟩))
        (rdW (touch y (touch y ⟨0, i, [false], 0⟩)), Dir.right, Dir.stay) := by
      simp only [enc, touch, eff, rdW, writeAt, moveIn, moveWork, List.getD_cons_zero,
        Config.mk.injEq, true_and, and_true]
      omega
    rw [heq]
    exact this

theorem scan_accepts_iff (x : List Bool) : scan.Accepts x ↔ true ∈ x := by
  constructor
  · rintro ⟨s, hs, hacc⟩
    obtain ⟨_, _, _, _, _, h6⟩ := inv_of_reaches hs
    have : s.2.2 = [true] := by simpa [scan] using hacc
    exact List.mem_of_getElem? (h6 this)
  · intro hx
    -- scan up to the first `true` bit
    obtain ⟨k, hk, hkx, hfirst⟩ : ∃ k, ∃ hk : k < x.length, x[k] = true ∧
        ∀ j < k, x[j]? = some false := by
      classical
      have hex : ∃ k, ∃ hk : k < x.length, x[k] = true := by
        obtain ⟨k, hk, h⟩ := List.getElem_of_mem hx
        exact ⟨k, hk, h⟩
      refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun j hj => ?_⟩
      have hjlt : j < x.length := lt_trans hj (Nat.find_spec hex).1
      have hne := Nat.find_min hex hj
      rw [List.getElem?_eq_getElem hjlt]
      cases hxj : x[j]
      · rfl
      · exact absurd ⟨hjlt, hxj⟩ hne
    have hreach : ∀ i ≤ k, scan.Reaches x (x, i, if i = 0 then [] else [false]) := by
      intro i
      induction i with
      | zero => intro _; exact AbsMachine.Reaches.start x
      | succ i ih =>
          intro hi
          have hprev := ih (by omega)
          refine hprev.tail ?_
          have hxi : x[i]? = some false := hfirst i (by omega)
          have hne : (if i = 0 then ([] : List Bool) else [false]) ≠ [true] := by
            split <;> simp
          have hil : i < x.length := by omega
          have hxi' : x[i] = false := by simpa [List.getElem?_eq_getElem hil] using hxi
          have hnl : ¬ x.length ≤ i := by omega
          simp [scan, hne, hil, hxi', hnl]
    refine ⟨(x, k, [true]), (hreach k le_rfl).tail ?_, by simp [scan]⟩
    have hne : (if k = 0 then ([] : List Bool) else [false]) ≠ [true] := by split <;> simp
    simp [scan, hne, List.getElem?_eq_getElem hk, hkx]

/-- **`{x | true ∈ x}` is in `DSPACE 1`**, by the machine compiled from `loop test body`. -/
theorem dspace_hasTrue : DSPACE (fun _ => 1) (fun x => true ∈ x) := by
  have h : DSPACE (fun _ => 1) scan.Accepts := by
    refine dspace_loop (t := test) (body := body) (enc := enc) (B := fun _ => 1)
      (fun _ => rfl) ?_ ?_ ?_ ?_ (fun x s s' hs hst => exec_step x s s' hs hst) fun _ => le_rfl
    · intro x; simp only [scan]; split_ifs <;> simp_all
    · intro x s hs
      obtain ⟨_, _, h3, _⟩ := inv_of_reaches hs
      rcases h3 with h | h | h <;> simp [enc, Config.space, h]
    · intro x s hs
      simp only [scan, decide_eq_true_eq]
      constructor
      · intro h; simp [h]
      · intro h; split_ifs at h with h1; simp_all
    · intro x s hs hst
      have : s.2.2 = [true] := by
        simp only [scan] at hst; split_ifs at hst with h1; simp_all
      simp [test, rdW, enc, this]
  obtain ⟨M, hwf, hdet, hsp, hL⟩ := h
  exact ⟨M, hwf, hdet, hsp, fun x => (scan_accepts_iff x).symm.trans (hL x)⟩

end Complexity.Space.Demo
