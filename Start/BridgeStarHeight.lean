/-
**Bridge: regular languages are decided in constant space by the host machines** — milestone M31
(`M31-BRIDGE-STARHEIGHT`).

The star-height development (`Start/StarHeight*.lean`, absorbed; main theorem
`GeneralizedStarHeight.main`: every regular language has generalized star height at most `3`)
works with Mathlib's languages and automata (`Language`, `DFA`, `Language.IsRegular`).  The host
complexity theory has its own offline machines with a read-only input and a binary work tape
(`Start/SpaceMachine.lean`).  This module compiles a deterministic finite automaton over `Bool`
into such a machine.

* `Complexity.Space.DFASim.machine` — the machine: one control state per automaton state while
  scanning the input left to right, and a final copy of the automaton state at the end marker;
* `Complexity.Space.DFASim.reach_iff` — its runs: after `n ≤ |x|` steps it has scanned the first
  `n` symbols, after `|x| + 1` steps it halts in the final copy of `eval x`, and it never moves on;
* **`Complexity.Space.dspace_of_isRegular`** — **every regular language over `Bool` is in
  `DSPACE` of the constant bound `1`** (one cell of the work tape);
* **`GeneralizedStarHeight.regular_starHeight_dspace`** — the star-height theorem, for the same
  languages: a regular language over `Bool` has generalized star height at most `3` and is
  decided in constant space by a host machine.
-/

import Start.StarHeightMain
import Start.SpaceMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Classical

namespace Complexity.Space

namespace DFASim

variable {σ : Type} [Fintype σ] (M : DFA Bool σ)

/-- A numbering of the states of the automaton, with the start state at `0`. -/
def num : σ ≃ Fin (Fintype.card σ) :=
  (Fintype.equivFin σ).trans
    (Equiv.swap ((Fintype.equivFin σ) M.start) ⟨0, Fintype.card_pos_iff.mpr ⟨M.start⟩⟩)

/-- The number of a state. -/
def enc (q : σ) : ℕ := (num M q : ℕ)

theorem enc_lt (q : σ) : enc M q < Fintype.card σ := (num M q).isLt

theorem enc_start : enc M M.start = 0 := by
  simp [enc, num, Equiv.swap_apply_left]

/-- The state of a number. -/
def dec (n : ℕ) : σ := if h : n < Fintype.card σ then (num M).symm ⟨n, h⟩ else M.start

theorem dec_enc (q : σ) : dec M (enc M q) = q := by
  simp only [dec, enc_lt, dite_true]
  exact (num M).symm_apply_apply q

/-- **The machine of the automaton.** -/
def machine : Machine where
  states := 2 * Fintype.card σ
  accept := fun c => decide (Fintype.card σ ≤ c ∧ c < 2 * Fintype.card σ ∧
    dec M (c - Fintype.card σ) ∈ M.accept)
  delta := fun c a b =>
    if c < Fintype.card σ then
      match a with
      | some y => [(enc M (M.step (dec M c) y), b, Dir.right, Dir.stay)]
      | none => [(Fintype.card σ + c, b, Dir.stay, Dir.stay)]
    else []

/-- The work tape after `n` steps. -/
def tp (n : ℕ) : List Bool := if n = 0 then [] else [false]

/-- The configuration after scanning the first `n` symbols. -/
def scan (x : List Bool) (n : ℕ) : Config :=
  ⟨enc M (M.evalFrom M.start (x.take n)), n, tp n, 0⟩

/-- The final configuration. -/
def final (x : List Bool) : Config :=
  ⟨Fintype.card σ + enc M (M.eval x), x.length, [false], 0⟩

theorem init_eq_scan (x : List Bool) : init = scan M x 0 := by
  simp [init, scan, tp, enc_start]

theorem writeAt_tp (n : ℕ) : writeAt (tp n) 0 false = [false] := by
  unfold tp
  split <;> rfl

theorem getD_tp (n : ℕ) : (tp n).getD 0 false = false := by
  unfold tp
  split <;> rfl

theorem stepList_scan_lt {x : List Bool} {n : ℕ} (hn : n < x.length) :
    (machine M).stepList x (scan M x n) = [scan M x (n + 1)] := by
  have hlt := enc_lt M (M.evalFrom M.start (x.take n))
  have hx : x[n]? = some x[n] := List.getElem?_eq_getElem hn
  have htake : M.evalFrom M.start (x.take (n + 1)) =
      M.step (M.evalFrom M.start (x.take n)) x[n] := by
    rw [List.take_add_one, hx, Option.toList_some, DFA.evalFrom_append_singleton]
  have hmin : min (n + 1) x.length = n + 1 := by omega
  simp only [Machine.stepList, machine, scan, hlt, ite_true, hx, getD_tp, dec_enc]
  simp only [moveIn, moveWork, hmin, htake, List.map_cons, List.map_nil, writeAt_tp, List.cons.injEq,
    and_true]
  simp [tp]

theorem stepList_scan_length (x : List Bool) :
    (machine M).stepList x (scan M x x.length) = [final M x] := by
  have hlt := enc_lt M (M.evalFrom M.start x)
  have hx : x[x.length]? = none := List.getElem?_eq_none (le_refl _)
  simp only [scan, List.take_length, Machine.stepList, machine, hlt, ite_true, hx, getD_tp]
  simp [moveIn, moveWork, writeAt_tp, final, DFA.eval]

theorem stepList_final (x : List Bool) : (machine M).stepList x (final M x) = [] := by
  have : ¬ (Fintype.card σ + enc M (M.eval x) < Fintype.card σ) := by omega
  simp [Machine.stepList, machine, final, this]

/-- **The runs of the machine.** -/
theorem reach_iff (x : List Bool) :
    ∀ (n : ℕ) (c : Config), Reach.steps ((machine M).Step x) n init c →
      (n ≤ x.length ∧ c = scan M x n) ∨ (n = x.length + 1 ∧ c = final M x) := by
  intro n
  induction n with
  | zero =>
      intro c hc
      rw [Reach.steps_zero] at hc
      exact Or.inl ⟨Nat.zero_le _, by rw [← hc, init_eq_scan M x]⟩
  | succ n ih =>
      intro c hc
      obtain ⟨m, hm, hstep⟩ := (Reach.steps_succ _ _ _ _).mp hc
      rcases ih m hm with ⟨hn, rfl⟩ | ⟨-, rfl⟩
      · rcases Nat.lt_or_ge n x.length with hlt | hge
        · have : c ∈ [scan M x (n + 1)] := by
            rw [← stepList_scan_lt M hlt]
            exact hstep
          exact Or.inl ⟨hlt, List.mem_singleton.mp this⟩
        · have hn' : n = x.length := le_antisymm hn hge
          subst hn'
          have : c ∈ [final M x] := by
            rw [← stepList_scan_length M x]
            exact hstep
          exact Or.inr ⟨rfl, List.mem_singleton.mp this⟩
      · have : c ∈ ([] : List Config) := by
          rw [← stepList_final M x]
          exact hstep
        cases this

theorem reach_scan (x : List Bool) :
    ∀ n, n ≤ x.length → Reach.steps ((machine M).Step x) n init (scan M x n) := by
  intro n
  induction n with
  | zero => intro _; exact init_eq_scan M x
  | succ n ih =>
      intro hn
      refine (Reach.steps_succ _ _ _ _).mpr ⟨scan M x n, ih (by omega), ?_⟩
      show scan M x (n + 1) ∈ (machine M).stepList x (scan M x n)
      rw [stepList_scan_lt M (by omega)]
      exact List.mem_singleton_self _

theorem reach_final (x : List Bool) :
    Reach.steps ((machine M).Step x) (x.length + 1) init (final M x) := by
  refine (Reach.steps_succ _ _ _ _).mpr ⟨scan M x x.length, reach_scan M x _ le_rfl, ?_⟩
  show final M x ∈ (machine M).stepList x (scan M x x.length)
  rw [stepList_scan_length]
  exact List.mem_singleton_self _

theorem wellFormed : (machine M).WellFormed := by
  have hpos : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr ⟨M.start⟩
  refine ⟨by simp only [machine]; omega, fun q a b t ht => ?_⟩
  simp only [machine] at ht ⊢
  split at ht
  · next hq =>
      cases a with
      | some y =>
          simp only [List.mem_singleton] at ht
          subst ht
          have := enc_lt M (M.step (dec M q) y)
          simp only
          omega
      | none =>
          simp only [List.mem_singleton] at ht
          subst ht
          simp only
          omega
  · cases ht

theorem deterministic : (machine M).Deterministic := by
  intro q a b
  simp only [machine]
  split
  · cases a <;> simp
  · simp

theorem spaceBounded : (machine M).SpaceBounded (fun _ => 1) := by
  intro x n c hc
  rcases reach_iff M x n c hc with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · simp only [Config.space, scan, tp]
    split <;> simp
  · simp [Config.space, final]

theorem accepts_iff (x : List Bool) : (machine M).Accepts x ↔ x ∈ M.accepts := by
  rw [DFA.mem_accepts]
  constructor
  · rintro ⟨n, c, hc, hacc⟩
    rcases reach_iff M x n c hc with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · have := enc_lt M (M.evalFrom M.start (x.take n))
      simp only [machine, scan, decide_eq_true_eq] at hacc
      omega
    · simp only [machine, final, decide_eq_true_eq, Nat.add_sub_cancel_left, dec_enc] at hacc
      exact hacc.2.2
  · intro h
    refine ⟨x.length + 1, final M x, reach_final M x, ?_⟩
    have := enc_lt M (M.eval x)
    simp only [machine, final, decide_eq_true_eq, Nat.add_sub_cancel_left, dec_enc]
    exact ⟨by omega, by omega, h⟩

end DFASim

/-- **Every regular language over `Bool` is decided in constant space** (one work cell) by a
host machine. -/
theorem dspace_of_isRegular {L : _root_.Language Bool} (h : L.IsRegular) :
    DSPACE (fun _ => 1) (fun x => x ∈ L) := by
  obtain ⟨σ, hσ, M, rfl⟩ := h
  exact ⟨DFASim.machine M, DFASim.wellFormed M, DFASim.deterministic M, DFASim.spaceBounded M,
    fun x => (DFASim.accepts_iff M x).symm⟩

end Complexity.Space

/-- **The star-height theorem, for host languages**: a regular language over `Bool` has
generalized star height at most `3` and is decided in constant space by a host machine. -/
theorem GeneralizedStarHeight.regular_starHeight_dspace {L : Language Bool} (h : L.IsRegular) :
    GeneralizedStarHeight.HasHeightAtMost L 3 ∧
      Complexity.Space.DSPACE (fun _ => 1) (fun x => x ∈ L) :=
  ⟨GeneralizedStarHeight.main L h, Complexity.Space.dspace_of_isRegular h⟩
