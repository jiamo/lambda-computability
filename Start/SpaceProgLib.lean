/-
**A combinator library for tape programs: exact-state specifications, sweeps, and a register
file laid out in tracks.**

`Start/SpaceProg.lean` gives the structured tape programs (`Complexity.Space.Prog`) and their
compiler into offline machines.  Writing an actual program on top of it — the body of an
evaluator, a compiler from another model — still means reasoning about `Exec` on raw
configurations, whose tapes are lists that grow as cells are visited.  This module supplies the
reusable middle layer that makes writing such programs cheap.

**1. Exact-state specifications.**  A program is specified by
`Complexity.Space.Prog.Runs x B p s s'`:
from every configuration whose *observable state* is `s` — the tape as a function from cells to
bits, the work head, the input head (`Complexity.Space.TState`) — it executes to a configuration
whose observable state is `s'`, every configuration on the way using at most `B` cells.  The tape
as a list, with its growth, never appears again.  Specifications compose along sequencing
(`Runs.seq`), conditionals (`Runs.iteT`, `Runs.iteF`) and loops (`Runs.loop_stages`: a loop
passing through a numbered family of stages, the test failing exactly at the last).

**2. Head movement.**  `Prog.mvR`, `Prog.mvL`, `Prog.moveTo`: moving the work head by a constant.

**3. Tracks.**  With `K` tracks, the work tape is cut into blocks of `2K + 1` cells: cell `0` of a
block is a *ruler* (set only in block `0`, so that the start of the tape can be found again), and
cells `2j + 1`, `2j + 2` hold the *presence* and the *value* bit of track `j` at that block.  A word
on a track occupies the blocks `0, 1, …` with presence bits set, so all tracks grow independently
and every operation is a left-to-right sweep moving by constant offsets
(`Complexity.Space.Tracks.mk`, `Complexity.Space.Tracks.lay`: the layout of a register file
`R : ℕ → Word`).

Main definitions:

* `Complexity.Space.TState`, `Complexity.Space.Config.abs` — the observable state;
* `Complexity.Space.Prog.Runs` — exact-state specifications with a space bound;
* `Complexity.Space.Tracks.mk`, `Complexity.Space.Tracks.lay` — the track layout.
-/

import Mathlib
import Start.SpaceProg
import Start.SpacePadded

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

/-! ### The observable state of a configuration -/

/-- The contents of the work tape as a function from cells to bits; unvisited cells read
`false`. -/
def Config.view (c : Config) : ℕ → Bool := fun i => c.tape.getD i false

/-- What a tape program observes and changes: the work tape as a function, the work head and the
input head. -/
structure TState where
  /-- The work tape, cell by cell. -/
  view : ℕ → Bool
  /-- The work head. -/
  head : ℕ
  /-- The input head. -/
  inHead : ℕ

/-- The observable state of a configuration. -/
def Config.abs (c : Config) : TState := ⟨c.view, c.wHead, c.inHead⟩

theorem view_writeAt (l : List Bool) (h : ℕ) (b : Bool) :
    (fun i => (writeAt l h b).getD i false) = Function.update (fun i => l.getD i false) h b := by
  funext i
  by_cases hi : i = h
  · subst hi; rw [Function.update_self, getD_writeAt_self]
  · rw [Function.update_of_ne hi, getD_writeAt_of_ne _ _ _ _ hi]

theorem abs_eff (x : List Bool) (c : Config) (b : Bool) (di dw : Dir) :
    (eff x c (b, di, dw)).abs =
      ⟨Function.update c.view c.wHead b, moveWork c.wHead dw, moveIn x.length c.inHead di⟩ := by
  simp only [Config.abs, eff]
  congr 1
  exact view_writeAt _ _ _

theorem abs_touch (x : List Bool) (c : Config) : (touch x c).abs = c.abs := by
  rw [touch, abs_eff]
  simp only [Config.abs, moveWork, moveIn, rdW]
  congr 1
  exact Function.update_eq_self _ _

theorem space_eff_le (x : List Bool) (c : Config) (b : Bool) (di dw : Dir) {B : ℕ}
    (hc : c.space ≤ B) (hmv : moveWork c.wHead dw ≤ c.wHead ∨ moveWork c.wHead dw < B) :
    (eff x c (b, di, dw)).space ≤ B := by
  simp only [Config.space, eff, writeAt_length] at hc ⊢
  omega

theorem wHead_lt_of_space_le {c : Config} {B : ℕ} (hc : c.space ≤ B) : c.wHead < B := by
  simp only [Config.space] at hc; omega

namespace Prog

/-! ### Exact-state specifications -/

/-- `Runs x B p s s'`: on the input `x`, the program `p` runs from every configuration with
observable state `s` and at most `B` cells to a configuration with observable state `s'` and at
most `B` cells, every configuration on the way using at most `B` cells. -/
def Runs (x : List Bool) (B : ℕ) (p : Prog) (s s' : TState) : Prop :=
  ∀ c : Config, c.abs = s → c.space ≤ B →
    ∃ d, Exec x (fun c => c.space ≤ B) p c d ∧ d.abs = s' ∧ d.space ≤ B

variable {x : List Bool} {B : ℕ}

theorem Runs.seq {p q : Prog} {s t u : TState} (h₁ : Runs x B p s t) (h₂ : Runs x B q t u) :
    Runs x B (.seq p q) s u := by
  intro c hc hB
  obtain ⟨d, hd, hdt, hdB⟩ := h₁ c hc hB
  obtain ⟨e, he, heu, heB⟩ := h₂ d hdt hdB
  exact ⟨e, .seq hd he, heu, heB⟩

theorem Runs.of_eq {p : Prog} {s s' t t' : TState} (h : Runs x B p s t) (hs : s' = s)
    (ht : t = t') : Runs x B p s' t' := hs ▸ ht ▸ h

/-- One action. -/
theorem Runs.act {f : Option Bool → Bool → Bool × Dir × Dir} {s : TState} {b : Bool} {di dw : Dir}
    (hf : f x[s.inHead]? (s.view s.head) = (b, di, dw))
    (hmv : moveWork s.head dw ≤ s.head ∨ moveWork s.head dw < B) :
    Runs x B (.act f) s
      ⟨Function.update s.view s.head b, moveWork s.head dw, moveIn x.length s.inHead di⟩ := by
  intro c hc hB
  subst hc
  have hf' : f (rdIn x c) (rdW c) = (b, di, dw) := hf
  refine ⟨_, Exec.act hB, ?_, ?_⟩
  · rw [hf', abs_eff]; rfl
  · rw [hf']; exact space_eff_le x c b di dw hB hmv

/-- A conditional whose test succeeds. -/
theorem Runs.iteT {t : Test} {p q : Prog} {s s' : TState}
    (ht : t x[s.inHead]? (s.view s.head) = true) (hp : Runs x B p s s') :
    Runs x B (.ite t p q) s s' := by
  intro c hc hB
  subst hc
  obtain ⟨d, hd, hds, hdB⟩ := hp (touch x c) (abs_touch x c) (by rw [space_touch]; exact hB)
  exact ⟨d, .iteT hB ht hd, hds, hdB⟩

/-- A conditional whose test fails. -/
theorem Runs.iteF {t : Test} {p q : Prog} {s s' : TState}
    (ht : t x[s.inHead]? (s.view s.head) = false) (hq : Runs x B q s s') :
    Runs x B (.ite t p q) s s' := by
  intro c hc hB
  subst hc
  obtain ⟨d, hd, hds, hdB⟩ := hq (touch x c) (abs_touch x c) (by rw [space_touch]; exact hB)
  exact ⟨d, .iteF hB ht hd, hds, hdB⟩

/-- A conditional, by cases on its test. -/
theorem Runs.ite {t : Test} {p q : Prog} {s s' : TState}
    (hp : t x[s.inHead]? (s.view s.head) = true → Runs x B p s s')
    (hq : t x[s.inHead]? (s.view s.head) = false → Runs x B q s s') :
    Runs x B (.ite t p q) s s' := by
  cases ht : t x[s.inHead]? (s.view s.head)
  · exact Runs.iteF ht (hq ht)
  · exact Runs.iteT ht (hp ht)

/-- **Loops through stages.**  If the body takes stage `k` to stage `k + 1` for every `k < L`,
and the test succeeds at the stages before `L` and fails at `L`, the loop takes stage `0` to
stage `L`. -/
theorem Runs.loop_stages {t : Test} {body : Prog} (stage : ℕ → TState) (L : ℕ)
    (htest : ∀ k, k ≤ L →
      t x[(stage k).inHead]? ((stage k).view (stage k).head) = decide (k < L))
    (hbody : ∀ k, k < L → Runs x B body (stage k) (stage (k + 1))) :
    Runs x B (.loop t body) (stage 0) (stage L) := by
  suffices h : ∀ m k, k + m = L → Runs x B (.loop t body) (stage k) (stage L) from
    h L 0 (by omega)
  intro m
  induction m with
  | zero =>
      intro k hk c hc hB
      have ht : t (rdIn x c) (rdW c) = false := by
        have := htest k (by omega)
        rw [← hc] at this
        simp only [show ¬ k < L by omega, decide_false] at this
        exact this
      refine ⟨touch x c, .loopF hB ht, ?_, by rw [space_touch]; exact hB⟩
      rw [abs_touch, hc, show k = L by omega]
  | succ m ih =>
      intro k hk c hc hB
      have ht : t (rdIn x c) (rdW c) = true := by
        have := htest k (by omega)
        rw [← hc] at this
        simp only [show k < L by omega, decide_true] at this
        exact this
      obtain ⟨d, hd, hds, hdB⟩ :=
        hbody k (by omega) (touch x c) (by rw [abs_touch, hc]) (by rw [space_touch]; exact hB)
      obtain ⟨e, he, hes, heB⟩ := ih (k + 1) (by omega) d hds hdB
      exact ⟨e, .loopT hB ht hd he, hes, heB⟩

/-! ### Elementary actions -/

theorem runs_write (b : Bool) (v : ℕ → Bool) (h i : ℕ) :
    Runs x B (write b) ⟨v, h, i⟩ ⟨Function.update v h b, h, i⟩ :=
  Runs.act (f := fun _ _ => (b, .stay, .stay)) (dw := .stay) rfl (Or.inl le_rfl)

theorem runs_skip (v : ℕ → Bool) (h i : ℕ) : Runs x B skip ⟨v, h, i⟩ ⟨v, h, i⟩ :=
  (Runs.act (f := fun _ w => (w, .stay, .stay)) (dw := .stay) rfl (Or.inl le_rfl)).of_eq rfl
    (by simp only [moveWork, moveIn, Function.update_eq_self])

theorem runs_wmoveR (v : ℕ → Bool) (h i : ℕ) (hB : h + 1 < B) :
    Runs x B (wmove .right) ⟨v, h, i⟩ ⟨v, h + 1, i⟩ :=
  (Runs.act (f := fun _ w => (w, .stay, .right)) (dw := .right) rfl (Or.inr hB)).of_eq rfl
    (by simp only [moveWork, moveIn, Function.update_eq_self])

theorem runs_wmoveL (v : ℕ → Bool) (h i : ℕ) :
    Runs x B (wmove .left) ⟨v, h, i⟩ ⟨v, h - 1, i⟩ :=
  (Runs.act (f := fun _ w => (w, .stay, .left)) (dw := .left) rfl
    (Or.inl (by simp [moveWork]))).of_eq rfl
    (by simp only [moveWork, moveIn, Function.update_eq_self])

theorem runs_imoveR (v : ℕ → Bool) (h i : ℕ) :
    Runs x B (imove .right) ⟨v, h, i⟩ ⟨v, h, min (i + 1) x.length⟩ :=
  (Runs.act (f := fun _ w => (w, .right, .stay)) (dw := .stay) rfl (Or.inl le_rfl)).of_eq rfl
    (by simp only [moveWork, moveIn, Function.update_eq_self])

/-! ### Moving the work head by a constant -/

/-- Moving the work head `n` cells to the right (one step more, to have a program for `n = 0`). -/
def mvR : ℕ → Prog
  | 0 => skip
  | n + 1 => .seq (wmove .right) (mvR n)

/-- Moving the work head `n` cells to the left. -/
def mvL : ℕ → Prog
  | 0 => skip
  | n + 1 => .seq (wmove .left) (mvL n)

theorem runs_mvR (n : ℕ) (v : ℕ → Bool) (h i : ℕ) (hB : h + n < B) :
    Runs x B (mvR n) ⟨v, h, i⟩ ⟨v, h + n, i⟩ := by
  induction n generalizing h with
  | zero => exact runs_skip v h i
  | succ n ih =>
      exact (runs_wmoveR v h i (by omega)).seq ((ih (h + 1) (by omega)).of_eq rfl
        (by congr 1; omega))

theorem runs_mvL (n : ℕ) (v : ℕ → Bool) (h i : ℕ) :
    Runs x B (mvL n) ⟨v, h, i⟩ ⟨v, h - n, i⟩ := by
  induction n generalizing h with
  | zero => exact runs_skip v h i
  | succ n ih =>
      exact (runs_wmoveL v h i).seq ((ih (h - 1)).of_eq rfl (by congr 1; omega))

/-- Moving the work head from offset `o` to offset `o'` (relative to the same base). -/
def moveTo (o o' : ℕ) : Prog := if o ≤ o' then mvR (o' - o) else mvL (o - o')

theorem runs_moveTo (o o' : ℕ) (v : ℕ → Bool) (base i : ℕ) (hB : base + o' < B) :
    Runs x B (moveTo o o') ⟨v, base + o, i⟩ ⟨v, base + o', i⟩ := by
  unfold moveTo
  split
  · exact (runs_mvR _ v _ i (by omega)).of_eq rfl (by congr 1; omega)
  · exact (runs_mvL _ v _ i).of_eq rfl (by congr 1; omega)

end Prog

/-! ### Tracks -/

namespace Tracks

/-- The width of a block with `K` tracks: a ruler cell and two cells per track. -/
abbrev wd (K : ℕ) : ℕ := 2 * K + 1

/-- `omega` after unfolding the block width. -/
macro "womega" : tactic => `(tactic| ((try simp only [Complexity.Space.Tracks.wd] at *) <;> omega))

/-- Closing an equation between Boolean-valued conditionals on natural-number comparisons: split
the conditionals, then decide the arithmetic. -/
macro "bool_omega" : tactic => `(tactic| ((try split_ifs) <;> first | rfl | omega |
  (rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, Bool.false_eq_true, false_iff, iff_false,
    true_iff, iff_true, not_and, not_lt]; omega)))

/-- The tape laid out in tracks: cell `0` of block `b` is the ruler (`b = 0`); cells `2j + 1` and
`2j + 2` of block `b` are `P j b` and `V j b`, the presence and the value bit of track `j`. -/
def mk (K : ℕ) (P V : ℕ → ℕ → Bool) : ℕ → Bool := fun i =>
  if i % wd K = 0 then decide (i / wd K = 0)
  else if i % wd K % 2 = 1 then P (i % wd K / 2) (i / wd K)
  else V (i % wd K / 2 - 1) (i / wd K)

theorem pos_div (K b o : ℕ) (ho : o < wd K) : (b * wd K + o) / wd K = b := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by womega), Nat.div_eq_of_lt ho, zero_add]

theorem pos_mod (K b o : ℕ) (ho : o < wd K) : (b * wd K + o) % wd K = o := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]

theorem mk_ruler (K : ℕ) (P V : ℕ → ℕ → Bool) (b : ℕ) : mk K P V (b * wd K) = decide (b = 0) := by
  have h1 := pos_div K b 0 (by womega)
  have h2 := pos_mod K b 0 (by womega)
  simp only [add_zero] at h1 h2
  simp [mk, h1, h2]

theorem mk_pres (K : ℕ) (P V : ℕ → ℕ → Bool) (b j : ℕ) (hj : j < K) :
    mk K P V (b * wd K + (2 * j + 1)) = P j b := by
  have h1 := pos_div K b (2 * j + 1) (by womega)
  have h2 := pos_mod K b (2 * j + 1) (by womega)
  simp only [mk, h1, h2]
  rw [if_neg (by womega), if_pos (by womega)]
  congr 1; womega

theorem mk_val (K : ℕ) (P V : ℕ → ℕ → Bool) (b j : ℕ) (hj : j < K) :
    mk K P V (b * wd K + (2 * j + 2)) = V j b := by
  have h1 := pos_div K b (2 * j + 2) (by womega)
  have h2 := pos_mod K b (2 * j + 2) (by womega)
  simp only [mk, h1, h2]
  rw [if_neg (by womega), if_neg (by womega)]
  congr 1; womega

theorem update_mk_pres (K : ℕ) (P V : ℕ → ℕ → Bool) (b j : ℕ) (hj : j < K) (β : Bool) :
    Function.update (mk K P V) (b * wd K + (2 * j + 1)) β =
      mk K (Function.update P j (Function.update (P j) b β)) V := by
  funext i
  by_cases h : i = b * wd K + (2 * j + 1)
  · subst h; rw [mk_pres _ _ _ _ _ hj]; simp
  · rw [Function.update_of_ne h]
    obtain ⟨b', o, ho, rfl⟩ : ∃ b' o, o < wd K ∧ i = b' * wd K + o :=
      ⟨i / wd K, i % wd K, Nat.mod_lt _ (by womega), (Nat.div_add_mod' i _).symm⟩
    simp only [mk, pos_div K b' o ho, pos_mod K b' o ho, Function.update_apply]
    split_ifs with h1 h2 h3 <;> try rfl
    all_goals
      rw [Function.update_apply, if_neg, h3]
      intro h4; apply h; subst h4; congr 1; womega

theorem update_mk_val (K : ℕ) (P V : ℕ → ℕ → Bool) (b j : ℕ) (hj : j < K) (β : Bool) :
    Function.update (mk K P V) (b * wd K + (2 * j + 2)) β =
      mk K P (Function.update V j (Function.update (V j) b β)) := by
  funext i
  by_cases h : i = b * wd K + (2 * j + 2)
  · subst h; rw [mk_val _ _ _ _ _ hj]; simp
  · rw [Function.update_of_ne h]
    obtain ⟨b', o, ho, rfl⟩ : ∃ b' o, o < wd K ∧ i = b' * wd K + o :=
      ⟨i / wd K, i % wd K, Nat.mod_lt _ (by womega), (Nat.div_add_mod' i _).symm⟩
    simp only [mk, pos_div K b' o ho, pos_mod K b' o ho, Function.update_apply]
    split_ifs with h1 h2 h3 <;> try rfl
    all_goals
      rw [Function.update_apply, if_neg, h3]
      intro h4; apply h; subst h4; congr 1; womega

/-- The layout of a register file: track `j` holds the word `R j`. -/
def lay (K : ℕ) (R : ℕ → List Bool) : ℕ → Bool :=
  mk K (fun j b => decide (b < (R j).length)) (fun j b => (R j).getD b false)

/-- The empty tape with the ruler set is the layout of the empty register file. -/
theorem lay_empty (K : ℕ) :
    Function.update (fun _ => false) 0 true = lay K (fun _ => []) := by
  funext i
  simp only [lay, mk, List.length_nil, Nat.not_lt_zero, decide_false, List.getD_nil]
  by_cases h : i = 0
  · subst h; simp
  · rw [Function.update_of_ne h]
    have hi := (Nat.div_add_mod' i (wd K)).symm
    split_ifs with h1 <;> try rfl
    symm; rw [decide_eq_false_iff_not]
    intro h2; apply h; rw [hi, h1, h2]; simp

-- TRACKS

end Tracks

end Complexity.Space
