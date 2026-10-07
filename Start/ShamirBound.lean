/-
**The states of the verifier machine stay polynomially small** (the last exit criterion of
`M21-SUMCHECK-REPLAY`).

Every state reachable by the machine `Complexity.Shamir.stepW` of `Start/ShamirMachine.lean` from
its initial state satisfies an invariant (`Complexity.Shamir.Inv`), whatever the transcript —
including transcripts written by a dishonest prover:

* the rest of the code is no longer than the code, and the linearization counter is at most `N`;
* the point is a word of `N` unary fields, each below `p`, and the claimed value is below `p`;
* the stack is a sequence of such pairs (point, value), and every push consumed at least one bit of
  the transcript, so that the number of pairs plus the length of the rest of the transcript is at
  most the length of the transcript;
* the two flags have at most one bit.

From the invariant every component has length polynomial in the length of the code, `N`, `p` and
the length of the transcript (`Complexity.Shamir.Inv.length_le`).

Main results:

* `Complexity.Shamir.Inv.step` — the invariant is preserved by a step (for `N` at least the length
  of the code);
* `Complexity.Shamir.inv_iterate` — it holds along the whole run;
* `Complexity.Shamir.Inv.length_le` — the bound on the components.
-/

import Start.ShamirReplay

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Shamir

open Complexity.Qbf
open Complexity.Qbf.EvalW (length_fieldsWord)

/-- The stack word of a list of pending claims, the top first. -/
def stackW : List (List ℕ × ℕ) → Word
  | [] => []
  | e :: l => encMsg (fieldsWord e.1) ++ encMsg (un e.2) ++ stackW l

/-- A pending claim of the right shape: `N` coordinates and a value, all below `p`. -/
def GoodClaim (p N : ℕ) (e : List ℕ × ℕ) : Prop :=
  e.1.length = N ∧ (∀ y ∈ e.1, y < p) ∧ e.2 < p

/-- **The invariant of the verifier**, for a code of length at most `cl` and a transcript of
length at most `tl`. -/
def Inv (p N cl tl : ℕ) (s : St) : Prop :=
  s.C.length ≤ cl ∧ s.J.length ≤ N ∧
  (∃ a : List ℕ, s.A = fieldsWord a ∧ a.length = N ∧ ∀ y ∈ a, y < p) ∧
  (∃ v : ℕ, s.V = un v ∧ v < p) ∧
  (∃ l : List (List ℕ × ℕ), s.S = stackW l ∧ (∀ e ∈ l, GoodClaim p N e) ∧
    l.length + s.T.length ≤ tl) ∧
  s.B.length ≤ 1 ∧ s.H.length ≤ 1

variable {p N cl tl : ℕ}

theorem inv_initSt (hp : 1 < p) (C T : Word) :
    Inv p N C.length T.length (initSt N C T) := by
  refine ⟨le_rfl, by simp [initSt], ⟨List.replicate N 0, rfl, by simp, by simp; omega⟩,
    ⟨1, rfl, hp⟩, ⟨[], rfl, by simp, by simp [initSt]⟩, by simp [initSt], by simp [initSt]⟩

theorem Inv.rej {s : St} (h : Inv p N cl tl s) : Inv p N cl tl (rej s) := by
  obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, by simp, by simp⟩

theorem recGet_stackW (e : List ℕ × ℕ) (l : List (List ℕ × ℕ)) :
    recGet (stackW (e :: l)) = fieldsWord e.1 := by
  rw [stackW, List.append_assoc, recGet_encMsg]

theorem recSkip_stackW (e : List ℕ × ℕ) (l : List (List ℕ × ℕ)) :
    recSkip (stackW (e :: l)) = encMsg (un e.2) ++ stackW l := by
  rw [stackW, List.append_assoc, recSkip_encMsg]

/-- Popping, after moving to a shorter code. -/
theorem Inv.pop {s : St} (h : Inv p N cl tl s) {C' : Word} (hC : C'.length ≤ cl) :
    Inv p N cl tl (pop { s with C := C' }) := by
  obtain ⟨-, h2, h3, h4, ⟨l, hS, hl, hlen⟩, h6, h7⟩ := h
  unfold Shamir.pop
  split
  · exact ⟨hC, h2, h3, h4, ⟨l, hS, hl, hlen⟩, h6, by simp⟩
  · rename_i hne
    cases l with
    | nil => exact absurd hS hne
    | cons e l =>
        obtain ⟨he1, he2, he3⟩ := hl e (by simp)
        refine ⟨hC, h2, ⟨e.1, ?_, he1, he2⟩, ⟨e.2, ?_, he3⟩,
          ⟨l, ?_, fun e' he' => hl e' (by simp [he']), ?_⟩, h6, h7⟩
        · simp only [hS, recGet_stackW]
        · simp only [hS, recSkip_stackW, recGet_encMsg]
        · simp only [hS, recSkip_stackW, recSkip_encMsg]
        · simp only [List.length_cons] at hlen; simp only; omega

theorem recGet_nil : recGet [] = [] := by simp [recGet]

theorem length_recSkip_lt {T : Word} (h : T ≠ []) : (recSkip T).length < T.length := by
  simp only [recSkip, List.length_drop]
  have : 0 < T.length := List.length_pos_of_ne_nil h
  omega

theorem dropFs_nil : ∀ i, dropFs i [] = []
  | 0 => rfl
  | i + 1 => by
      rw [dropFs, show dropF [] = [] by simp [dropF, drop1], dropFs_nil i]

theorem trimW_nil : trimW [] = [] := by simp [trimW, drop1]

theorem hornerN_lt' (hp : 0 < p) (x : ℕ) : ∀ cs : List ℕ, hornerN x p cs < p
  | [] => hp
  | _ :: _ => Nat.mod_lt _ hp

/-- **The invariant is preserved by a step**, for `N` at least the length of the code. -/
theorem Inv.step (hp : 0 < p) (hN : cl ≤ N) (d : ℕ) {s : St} (h : Inv p N cl tl s) :
    Inv p N cl tl (stepW p N d s) := by
  have hI := h
  obtain ⟨h1, h2, ⟨a, hA, ha, hal⟩, ⟨v, hV, hv⟩, ⟨l, hS, hl, hlen⟩, h6, h7⟩ := h
  unfold stepW
  split_ifs with hH b0 b1 hvar b1' hbin hdeg hJ hlin hquant
  · exact hI
  · -- variable, accepted
    exact hI.pop (by
      have := length_drop1 (s.C.drop 2)
      simp only [List.length_tail, List.length_drop] at this ⊢; omega)
  · exact hI.rej
  · -- negation
    refine ⟨by simp; omega, h2, ⟨a, hA, ha, hal⟩, ⟨_, rfl, Nat.mod_lt _ hp⟩, ⟨l, hS, hl, hlen⟩,
      h6, h7⟩
  · -- conjunction or disjunction, accepted
    have hT : s.T ≠ [] := by
      intro hT
      rw [hT, recGet_nil, trimW_nil, dropFs_nil] at hbin
      exact hbin.2.1 rfl
    refine ⟨by simp; omega, h2, ⟨a, hA, ha, hal⟩, ⟨_, rfl, Nat.mod_lt _ hp⟩,
      ⟨(a, fieldAt 1 (trimW (recGet s.T)) % p) :: l, ?_, ?_, ?_⟩, h6, h7⟩
    · simp [stackW, hS, hA]
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨ha, hal, Nat.mod_lt _ hp⟩
      · exact hl e he
    · have := length_recSkip_lt hT
      have := recSkip_length_le (recSkip s.T)
      simp only [List.length_cons]; omega
  · exact hI.rej
  · exact hI.rej
  · -- a linearization, accepted
    refine ⟨h1, by simp; omega, ⟨a.set s.J.length ((recGet (recSkip s.T)).length % p), ?_, by simp [ha],
      set_lt hal _ _ (Nat.mod_lt _ hp)⟩, ⟨_, rfl, hornerN_lt' hp _ _⟩, ⟨l, hS, hl, ?_⟩, h6, h7⟩
    · rw [hA, setField_fieldsWord _ (by omega)]
    · have := recSkip_length_le s.T
      have := recSkip_length_le (recSkip s.T)
      simp only; omega
  · exact hI.rej
  · -- a quantifier, accepted
    have hC2 : 2 ≤ s.C.length := by
      by_contra hc
      have hb : bit 1 s.C = false := by
        simp [bit, List.drop_eq_nil_of_le (show s.C.length ≤ 1 by omega)]
      contradiction
    have hi : lead1 (s.C.drop 3) < N := by
      have := lead1_le (s.C.drop 3)
      simp only [List.length_drop] at this
      omega
    refine ⟨?_, by simp, ⟨a.set (lead1 (s.C.drop 3)) ((recGet (recSkip s.T)).length % p), ?_,
      by simp [ha], set_lt hal _ _ (Nat.mod_lt _ hp)⟩, ⟨_, rfl, hornerN_lt' hp _ _⟩, ⟨l, hS, hl, ?_⟩, h6, h7⟩
    · have := length_drop1 (s.C.drop 3)
      simp only [List.length_tail, List.length_drop] at this ⊢; omega
    · rw [hA, setField_fieldsWord _ (by omega)]
    · have := recSkip_length_le s.T
      have := recSkip_length_le (recSkip s.T)
      simp only; omega
  · exact hI.rej

/-- The invariant holds along the whole run. -/
theorem inv_iterate (hp : 0 < p) (hN : cl ≤ N) (d : ℕ) {s : St} (h : Inv p N cl tl s) :
    ∀ K, Inv p N cl tl ((stepW p N d)^[K] s)
  | 0 => h
  | K + 1 => by
      rw [Function.iterate_succ_apply']
      exact (inv_iterate hp hN d h K).step hp hN d

theorem length_fieldsWord_le {a : List ℕ} (hal : ∀ y ∈ a, y < p) :
    (fieldsWord a).length ≤ a.length * p := by
  rw [length_fieldsWord]
  induction a with
  | nil => simp
  | cons y a ih =>
      have hy := hal y (by simp)
      have := ih (fun z hz => hal z (by simp [hz]))
      simp only [List.sum_cons, List.length_cons]
      nlinarith

theorem length_stackW_le : ∀ (l : List (List ℕ × ℕ)), (∀ e ∈ l, GoodClaim p N e) →
    (stackW l).length ≤ l.length * (2 * (N * p) + 2 * p + 2)
  | [], _ => by simp [stackW]
  | e :: l, hl => by
      obtain ⟨he1, he2, he3⟩ := hl e (by simp)
      have h1 := length_fieldsWord_le he2
      have ih := length_stackW_le l (fun e' he' => hl e' (by simp [he']))
      rw [he1] at h1
      simp only [stackW, List.length_append, length_encMsg, length_un, List.length_cons]
      nlinarith

/-- **Every component of a state satisfying the invariant is polynomially bounded.** -/
theorem Inv.length_le {s : St} (h : Inv p N cl tl s) :
    s.C.length ≤ cl ∧ s.J.length ≤ N ∧ s.A.length ≤ N * p ∧ s.V.length ≤ p ∧
      s.S.length ≤ tl * (2 * (N * p) + 2 * p + 2) ∧ s.B.length ≤ 1 ∧ s.T.length ≤ tl ∧
      s.H.length ≤ 1 := by
  obtain ⟨h1, h2, ⟨a, hA, ha, hal⟩, ⟨v, hV, hv⟩, ⟨l, hS, hl, hlen⟩, h6, h7⟩ := h
  refine ⟨h1, h2, ?_, by rw [hV, length_un]; omega, ?_, h6, by omega, h7⟩
  · rw [hA, ← ha]; exact length_fieldsWord_le hal
  · rw [hS]
    exact (length_stackW_le l hl).trans (Nat.mul_le_mul_right _ (by omega))

end Complexity.Shamir
