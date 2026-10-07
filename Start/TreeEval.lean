/-
**Evaluating sum–max trees in polynomial space.**

A *Cobham tree* (`Complexity.TreeEval.CTree`) is a binary tree whose nodes are words
("positions"), presented by Cobham terms on `[x, position]`: whether a position is a leaf, whether
an inner node is a maximum node (otherwise it is a sum node), its two children, and the bit of a
leaf.  Its value with fuel `n` (`Complexity.TreeEval.val`) adds or maximizes the values of the
children, the leaves counting `0` or `1`.

This module evaluates such a tree by a depth-first traversal with an explicit stack of frames
(position, phase, accumulated value), with the values kept in binary (`Start/BinArith.lean`).  The
traversal is a machine on five words (`Complexity.TreeEval.step`), whose step is given by Cobham
terms, so that `Start/CobhamIterate.lean` runs it in polynomial space: although the traversal
takes exponentially many steps, the stack has at most `n + 1` frames of polynomial size.

Main definitions:

* `Complexity.TreeEval.CTree`, `.val`, `.Good` — the trees, their values, and the predicate that
  the tree below a position is finite within the fuel with positions of bounded length;
* `Complexity.TreeEval.step`, `.stepTs` — the traversal and its step as Cobham terms.

Main results:

* `Complexity.TreeEval.sim` — **the traversal computes the value**: from a frame for a position,
  after `steps` steps the machine has popped that frame and returns a binary word for its value,
  every intermediate stack being polynomially bounded;
* `Complexity.TreeEval.pspace_of_ctree` — **a language deciding `2^c ≤ 2 · value` for a Cobham
  tree of polynomial depth and position size is in `PSPACE`**.
-/

import Start.BinArith
import Start.CobhamIterate
import Start.QbfPspace

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.TreeEval

open Complexity.Shamir

/-- A binary tree of positions presented by Cobham terms on `[x, position]`. -/
structure CTree where
  /-- Nonempty iff the position is a leaf. -/
  isLeaf : Cob
  /-- At an inner node: nonempty iff it is a maximum node (otherwise a sum node). -/
  isMax : Cob
  /-- The first child. -/
  ch0 : Cob
  /-- The second child. -/
  ch1 : Cob
  /-- At a leaf: nonempty iff its value is `1`. -/
  leaf : Cob

variable (T : CTree) (x : Word)

/-- The binary word of the value of a leaf. -/
def lv (p : Word) : Word := if T.leaf.eval [x, p] = [] then [] else [true]

/-- The first child. -/
def c0 (p : Word) : Word := T.ch0.eval [x, p]

/-- The second child. -/
def c1 (p : Word) : Word := T.ch1.eval [x, p]

/-- The value of the tree below a position, with fuel `n`. -/
def val : ℕ → Word → ℕ
  | 0, p => nv (lv T x p)
  | n + 1, p =>
      if T.isLeaf.eval [x, p] = [] then
        (if T.isMax.eval [x, p] = [] then val n (c0 T x p) + val n (c1 T x p)
          else max (val n (c0 T x p)) (val n (c1 T x p)))
      else nv (lv T x p)

/-- The tree below `p` reaches only leaves within depth `n`, through positions of length at
most `B`. -/
def Good (B : ℕ) : ℕ → Word → Prop
  | 0, p => p.length ≤ B ∧ T.isLeaf.eval [x, p] ≠ []
  | n + 1, p => p.length ≤ B ∧
      (T.isLeaf.eval [x, p] ≠ [] ∨ (Good B n (c0 T x p) ∧ Good B n (c1 T x p)))

/-! ### The traversal -/

/-- A state of the traversal: the stack, the returned value, the mode (`[]` descending, `[true]`
returning), the running flag and the answer. -/
structure St where
  S : Word
  V : Word
  Md : Word
  H : Word
  A : Word

/-- A frame: a position, a phase (`[]` before the first child, `[true]` after it) and the value
of the first child. -/
def frame (p ph acc : Word) : Word := encMsg p ++ encMsg ph ++ encMsg acc

theorem encMsg_ne_nil (w : Word) : encMsg w ≠ [] := by simp [encMsg]

@[simp] theorem frame_ne_nil (p ph acc : Word) : frame p ph acc ≠ [] := by
  simp [frame, encMsg]

@[simp] theorem recGet_frame (p ph acc r : Word) : recGet (frame p ph acc ++ r) = p := by
  simp [frame, List.append_assoc]

@[simp] theorem recGet_recSkip_frame (p ph acc r : Word) :
    recGet (recSkip (frame p ph acc ++ r)) = ph := by
  simp [frame, List.append_assoc]

@[simp] theorem recGet_recSkip_recSkip_frame (p ph acc r : Word) :
    recGet (recSkip (recSkip (frame p ph acc ++ r))) = acc := by
  simp [frame, List.append_assoc]

@[simp] theorem recSkip3_frame (p ph acc r : Word) :
    recSkip (recSkip (recSkip (frame p ph acc ++ r))) = r := by
  simp [frame, List.append_assoc]

theorem length_frame (p ph acc : Word) :
    (frame p ph acc).length = 2 * p.length + 2 * ph.length + 2 * acc.length + 3 := by
  simp [frame]; ring

/-- A stack of frames, the top first. -/
def stackW : List (Word × Word × Word) → Word
  | [] => []
  | f :: fs => frame f.1 f.2.1 f.2.2 ++ stackW fs

theorem stackW_append (F G : List (Word × Word × Word)) :
    stackW (F ++ G) = stackW F ++ stackW G := by
  induction F with
  | nil => rfl
  | cons f F ih => simp [stackW, ih, List.append_assoc]

variable (thr : Cob)

/-- One step of the traversal. -/
def step (s : St) : St :=
  if s.Md = [] then
    if T.isLeaf.eval [x, recGet s.S] = [] then
      { s with S := frame (c0 T x (recGet s.S)) [] [] ++ s.S, Md := [] }
    else
      { s with S := recSkip (recSkip (recSkip s.S)), V := lv T x (recGet s.S), Md := [true] }
  else if s.S = [] then
    { s with H := [], A := bw (decide (2 ^ (thr.eval [x]).length ≤ 2 * nv s.V)) }
  else if recGet (recSkip s.S) = [] then
    { s with S := frame (c1 T x (recGet s.S)) [] [] ++
        (frame (recGet s.S) [true] s.V ++ recSkip (recSkip (recSkip s.S))), Md := [] }
  else
    { s with S := recSkip (recSkip (recSkip s.S)),
             V := if T.isMax.eval [x, recGet s.S] = [] then
                 addW (recGet (recSkip (recSkip s.S))) s.V
               else maxW (recGet (recSkip (recSkip s.S))) s.V,
             Md := [true] }

/-- The number of steps the traversal spends below a position. -/
def steps : ℕ → Word → ℕ
  | 0, _ => 1
  | n + 1, p =>
      if T.isLeaf.eval [x, p] = [] then steps n (c0 T x p) + steps n (c1 T x p) + 3 else 1

/-- A frame within the bounds: position of length `≤ B`, phase of length `≤ 1`, accumulated
value of length `≤ n`. -/
def FB (B n : ℕ) (f : Word × Word × Word) : Prop :=
  f.1.length ≤ B ∧ f.2.1.length ≤ 1 ∧ f.2.2.length ≤ n

/-- The shape of the intermediate states while the traversal works below a frame pushed on
`S0`. -/
def Ok (B n : ℕ) (S0 H0 A0 : Word) (Vb : ℕ) (s : St) : Prop :=
  s.H = H0 ∧ s.A = A0 ∧ s.V.length ≤ Vb ∧ s.Md.length ≤ 1 ∧
    ∃ Fs : List (Word × Word × Word), s.S = stackW Fs ++ S0 ∧ Fs ≠ [] ∧ Fs.length ≤ n + 1 ∧
      ∀ f ∈ Fs, FB B n f

theorem Ok.lift {B n : ℕ} {S0 H0 A0 : Word} {Vb Vb' : ℕ} {s : St} (f : Word × Word × Word)
    (h : Ok B n (frame f.1 f.2.1 f.2.2 ++ S0) H0 A0 Vb s) (hf : FB B (n + 1) f) (hV : Vb ≤ Vb') :
    Ok B (n + 1) S0 H0 A0 Vb' s := by
  obtain ⟨h1, h2, h3, h4, Fs, hS, hne, hlen, hFB⟩ := h
  refine ⟨h1, h2, by omega, h4, Fs ++ [f], ?_, by simp, by simp; omega, ?_⟩
  · rw [hS, stackW_append, List.append_assoc]; simp [stackW]
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨a, b, c⟩ := hFB g hg
      exact ⟨a, b, by omega⟩
    · simp at hg; subst hg; exact hf

theorem length_lv_le (p : Word) : (lv T x p).length ≤ 1 := by
  unfold lv; split <;> simp

theorem iterate_split {α : Type*} (f : α → α) (s : α) {a k : ℕ} (h : a ≤ k) :
    f^[k] s = f^[k - a] (f^[a] s) := by
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]

/-- **The traversal computes the value of the tree.**  Started with a frame for `p` on top of an
arbitrary stack `S0`, after `steps n p` steps it has popped the frame and returns a word for the
value of `p`; every intermediate state has the shape `Ok`. -/
theorem sim (B : ℕ) : ∀ (n : ℕ) (p : Word), Good T x B n p → ∀ (S0 V0 H0 A0 : Word),
    (∃ w, (step T x thr)^[steps T x n p] ⟨frame p [] [] ++ S0, V0, [], H0, A0⟩ =
        ⟨S0, w, [true], H0, A0⟩ ∧ nv w = val T x n p ∧ w.length ≤ n + 1) ∧
      ∀ k < steps T x n p, Ok B n S0 H0 A0 (max V0.length (n + 1))
        ((step T x thr)^[k] ⟨frame p [] [] ++ S0, V0, [], H0, A0⟩) := by
  intro n
  induction n with
  | zero =>
      intro p hg S0 V0 H0 A0
      obtain ⟨hB, hleaf⟩ := hg
      refine ⟨⟨lv T x p, ?_, rfl, by have := length_lv_le T x p; omega⟩, ?_⟩
      · simp [steps, step, hleaf]
      · intro k hk
        simp only [steps] at hk
        obtain rfl : k = 0 := by omega
        refine ⟨rfl, rfl, by simp, by simp, [(p, [], [])], by simp [stackW], by simp,
          by simp, ?_⟩
        intro f hf; simp at hf; subst hf; exact ⟨hB, by simp, by simp⟩
  | succ n ih =>
      intro p hg S0 V0 H0 A0
      obtain ⟨hB, hg⟩ := hg
      by_cases hleaf : T.isLeaf.eval [x, p] = []
      · -- an inner node
        obtain ⟨hg0, hg1⟩ : Good T x B n (c0 T x p) ∧ Good T x B n (c1 T x p) := by
          rcases hg with h | h
          · exact absurd hleaf h
          · exact h
        obtain ⟨⟨w0, e0, v0, l0⟩, i0⟩ := ih (c0 T x p) hg0 (frame p [] [] ++ S0) V0 H0 A0
        obtain ⟨⟨w1, e1, v1, l1⟩, i1⟩ := ih (c1 T x p) hg1 (frame p [true] w0 ++ S0) w0 H0 A0
        set s0 := steps T x n (c0 T x p) with hs0
        set s1 := steps T x n (c1 T x p) with hs1
        have hsteps : steps T x (n + 1) p = s0 + s1 + 3 := by simp [steps, hleaf, s0, s1]
        have st1 : step T x thr ⟨frame p [] [] ++ S0, V0, [], H0, A0⟩ =
            ⟨frame (c0 T x p) [] [] ++ (frame p [] [] ++ S0), V0, [], H0, A0⟩ := by
          simp [step, hleaf]
        have st2 : step T x thr ⟨frame p [] [] ++ S0, w0, [true], H0, A0⟩ =
            ⟨frame (c1 T x p) [] [] ++ (frame p [true] w0 ++ S0), w0, [], H0, A0⟩ := by
          simp [step]
        set wf := if T.isMax.eval [x, p] = [] then addW w0 w1 else maxW w0 w1 with hwf
        have st3 : step T x thr ⟨frame p [true] w0 ++ S0, w1, [true], H0, A0⟩ =
            ⟨S0, wf, [true], H0, A0⟩ := by
          simp [step, wf]
        -- the states at the milestones
        have m1 : (step T x thr)^[s0 + 1] ⟨frame p [] [] ++ S0, V0, [], H0, A0⟩ =
            ⟨frame p [] [] ++ S0, w0, [true], H0, A0⟩ := by
          rw [Function.iterate_add_apply, Function.iterate_one, st1, e0]
        have m2 : (step T x thr)^[1 + (s0 + 1)] ⟨frame p [] [] ++ S0, V0, [], H0, A0⟩ =
            ⟨frame (c1 T x p) [] [] ++ (frame p [true] w0 ++ S0), w0, [], H0, A0⟩ := by
          rw [Function.iterate_add_apply, m1, Function.iterate_one, st2]
        have m3 : (step T x thr)^[s1 + (1 + (s0 + 1))] ⟨frame p [] [] ++ S0, V0, [], H0, A0⟩ =
            ⟨frame p [true] w0 ++ S0, w1, [true], H0, A0⟩ := by
          rw [Function.iterate_add_apply, m2, e1]
        refine ⟨⟨wf, ?_, ?_, ?_⟩, ?_⟩
        · rw [hsteps, show s0 + s1 + 3 = 1 + (s1 + (1 + (s0 + 1))) by omega,
            Function.iterate_add_apply, m3, Function.iterate_one, st3]
        · simp only [val, hleaf, if_true, wf]
          split
          · rw [nv_addW, v0, v1]
          · rw [nv_maxW, v0, v1]
        · simp only [wf]
          split
          · rw [length_addW]; omega
          · have := length_maxW_le w0 w1; omega
        · intro k hk
          rw [hsteps] at hk
          have hf0 : FB B (n + 1) (p, [], []) := ⟨hB, by simp, by simp⟩
          have hf1 : FB B (n + 1) (p, [true], w0) := ⟨hB, by simp, l0⟩
          rcases Nat.eq_zero_or_pos k with rfl | hk0
          · refine ⟨rfl, rfl, by simp, by simp, [(p, [], [])], by simp [stackW], by simp,
              by simp, ?_⟩
            intro f hf; simp at hf; subst hf; exact hf0
          rcases Nat.lt_or_ge k (s0 + 1) with hk1 | hk1
          · rw [iterate_split _ _ (show 1 ≤ k by omega), Function.iterate_one, st1]
            exact (i0 (k - 1) (by omega)).lift (p, [], []) hf0
              (by simp only [max_le_iff, le_max_iff]; omega)
          rcases Nat.eq_or_lt_of_le hk1 with hk2 | hk2
          · rw [← hk2, m1]
            refine ⟨rfl, rfl, by simp; omega, by simp, [(p, [], [])], by simp [stackW],
              by simp, by simp, ?_⟩
            intro f hf; simp at hf; subst hf; exact hf0
          rcases Nat.lt_or_ge k (s1 + (1 + (s0 + 1))) with hk3 | hk3
          · rw [iterate_split _ _ (show 1 + (s0 + 1) ≤ k by omega), m2]
            refine (i1 (k - (1 + (s0 + 1))) (by omega)).lift (p, [true], w0)
              hf1 (by simp only [max_le_iff, le_max_iff]; omega)
          · obtain rfl : k = s1 + (1 + (s0 + 1)) := by omega
            rw [m3]
            refine ⟨rfl, rfl, by simp; omega, by simp, [(p, [true], w0)], by simp [stackW],
              by simp, by simp, ?_⟩
            intro f hf; simp at hf; subst hf; exact hf1
      · -- a leaf
        refine ⟨⟨lv T x p, ?_, ?_, by have := length_lv_le T x p; omega⟩, ?_⟩
        · simp [steps, step, hleaf]
        · simp [val, hleaf]
        · intro k hk
          simp only [steps, hleaf, if_false] at hk
          obtain rfl : k = 0 := by omega
          refine ⟨rfl, rfl, by simp, by simp, [(p, [], [])], by simp [stackW], by simp,
            by simp, ?_⟩
          intro f hf; simp at hf; subst hf; exact ⟨hB, by simp, by simp⟩

/-! ### The step as Cobham terms -/

/-- The five words of a state. -/
def toL (s : St) : List Word := [s.S, s.V, s.Md, s.H, s.A]

/-- A frame as a Cobham term. -/
def frameT (a b c : Cob) : Cob :=
  Cob.catT (Cob.catT (Cob.encMsgT a) (Cob.encMsgT b)) (Cob.encMsgT c)

@[simp] theorem eval_frameT (a b c : Cob) (args : List Word) :
    (frameT a b c).eval args = frame (a.eval args) (b.eval args) (c.eval args) := by
  simp [frameT, frame]

/-- The position on top of the stack, on `x :: toL s`. -/
def pT : Cob := Cob.recGetT (.proj 1)
/-- The phase on top of the stack. -/
def phT : Cob := Cob.recGetT (Cob.recSkipT (.proj 1))
/-- The accumulated value on top of the stack. -/
def accT : Cob := Cob.recGetT (Cob.recSkipT (Cob.recSkipT (.proj 1)))
/-- The stack without its top frame. -/
def restT : Cob := Cob.recSkipT (Cob.recSkipT (Cob.recSkipT (.proj 1)))
/-- A tree term at the position on top of the stack. -/
def atP (c : Cob) : Cob := .comp c [.proj 0, pT]

/-- **The step of the traversal as five Cobham terms** on `x :: toL s`. -/
def stepTs : List Cob :=
  [Cob.iteT (.proj 3)
      (Cob.iteT (.proj 1)
        (Cob.iteT phT restT
          (Cob.catT (frameT (atP T.ch1) .empty .empty) (Cob.catT (frameT pT Cob.trueC (.proj 2))
            restT)))
        (.proj 1))
      (Cob.iteT (atP T.isLeaf) restT (Cob.catT (frameT (atP T.ch0) .empty .empty) (.proj 1))),
    Cob.iteT (.proj 3)
      (Cob.iteT (.proj 1)
        (Cob.iteT phT (Cob.iteT (atP T.isMax) (Cob.maxT accT (.proj 2)) (Cob.addT accT (.proj 2)))
          (.proj 2))
        (.proj 2))
      (Cob.iteT (atP T.isLeaf) (Cob.iteT (atP T.leaf) Cob.trueC .empty) (.proj 2)),
    Cob.iteT (.proj 3) (Cob.iteT (.proj 1) (Cob.iteT phT Cob.trueC .empty) (.proj 3))
      (Cob.iteT (atP T.isLeaf) Cob.trueC .empty),
    Cob.iteT (.proj 3) (Cob.iteT (.proj 1) (.proj 4) .empty) (.proj 4),
    Cob.iteT (.proj 3) (Cob.iteT (.proj 1) (.proj 5) (Cob.thrT (.proj 2) (.comp thr [.proj 0])))
      (.proj 5)]

theorem eval_stepTs (s : St) :
    (stepTs T thr).map (fun g => g.eval (x :: toL s)) = toL (step T x thr s) := by
  obtain ⟨S, V, Md, H, A⟩ := s
  have e1 : ∀ c : Cob, (atP c).eval (x :: toL ⟨S, V, Md, H, A⟩) = c.eval [x, recGet S] := by
    intro c; simp [atP, pT, toL]
  simp only [stepTs, List.map_cons, List.map_nil, Cob.eval_iteT_word, e1]
  simp only [toL, step, phT, accT, restT, pT, Cob.eval_recGetT, Cob.eval_recSkipT,
    Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero, eval_frameT, Cob.eval_catT,
    Cob.eval_empty, Cob.eval_trueC, Cob.eval_maxT, Cob.eval_addT, Cob.eval_thrT, Cob.eval_comp,
    List.map_cons, List.map_nil]
  by_cases hMd : Md = []
  · by_cases hl : T.isLeaf.eval [x, recGet S] = []
    · simp [hMd, hl, atP, pT, c0]
    · simp [hMd, hl, lv]
  · by_cases hS : S = []
    · simp [hMd, hS]
    · by_cases hph : recGet (recSkip S) = []
      · simp [hMd, hS, hph, atP, pT, c1]
      · by_cases hm : T.isMax.eval [x, recGet S] = []
        · simp [hMd, hS, hph, hm]
        · simp [hMd, hS, hph, hm]

/-- The initial state, as Cobham terms on `[x]`: a frame for the root. -/
def initTs (root : Cob) : List Cob := [frameT root .empty .empty, .empty, .empty, Cob.trueC, .empty]

/-- The initial state. -/
def init (root : Cob) : St := ⟨frame (root.eval [x]) [] [] ++ [], [], [], [true], []⟩

theorem cobIter_eq (root : Cob) : ∀ k,
    Space.cobIter (initTs root) (stepTs T thr) x k = toL ((step T x thr)^[k] (init x root))
  | 0 => by simp [Space.cobIter, initTs, init, toL]
  | k + 1 => by
      rw [Space.cobIter, cobIter_eq root k, eval_stepTs, Function.iterate_succ_apply']

theorem length_stackW_le {B n : ℕ} : ∀ (Fs : List (Word × Word × Word)), (∀ f ∈ Fs, FB B n f) →
    (stackW Fs).length ≤ Fs.length * (2 * B + 2 * n + 5)
  | [], _ => by simp [stackW]
  | f :: Fs, h => by
      have ih := length_stackW_le Fs (fun g hg => h g (by simp [hg]))
      obtain ⟨h1, h2, h3⟩ := h f (by simp)
      simp only [stackW, List.length_append, length_frame, List.length_cons]
      nlinarith

/-- **Evaluating a Cobham tree in polynomial space.**  If the tree below the root has polynomial
depth `fuel` and positions of polynomial length `B`, then deciding `2 ^ |thr(x)| ≤ 2 · value` is
in `PSPACE`. -/
theorem pspace_of_ctree (T : CTree) (root thr : Cob) (L : Language) (fuel B : ℕ → ℕ)
    (hfuel : PolyBound fuel) (hB : PolyBound B)
    (hgood : ∀ x, Good T x (B x.length) (fuel x.length) (root.eval [x]))
    (hL : ∀ x, L x ↔ 2 ^ (thr.eval [x]).length ≤ 2 * val T x (fuel x.length) (root.eval [x])) :
    Space.PSPACE L := by
  let bnd : ℕ → ℕ := fun n => (fuel n + 1) * (2 * B n + 2 * fuel n + 5) + fuel n + 2
  have hbnd : PolyBound bnd := by
    have h1 := (hfuel.add (polyBound_const 1)).mul
      ((((polyBound_const 2).mul hB).add ((polyBound_const 2).mul hfuel)).add (polyBound_const 5))
    exact ((h1.add hfuel).add (polyBound_const 2)).mono (fun n => le_refl _)
  refine Space.pspace_of_cobIter (initTs root) (stepTs T thr) 5 3 4 L bnd hbnd rfl rfl
    (by norm_num) (by norm_num) (fun x => ?_)
  set n := fuel x.length with hn
  set p := root.eval [x] with hp
  obtain ⟨⟨w, e, v, l⟩, inter⟩ := sim T x thr (B x.length) n p (hgood x) [] [] [true] []
  set N := steps T x n p with hN
  have hinit : init x root = ⟨frame p [] [] ++ [], [], [], [true], []⟩ := rfl
  have efin : (step T x thr)^[N + 1] ⟨frame p [] [] ++ [], [], [], [true], []⟩ =
      ⟨[], w, [true], [], bw (decide (2 ^ (thr.eval [x]).length ≤ 2 * nv w))⟩ := by
    rw [Function.iterate_succ_apply', e]
    simp [step]
  have hbx : ∀ s : St, s.S.length ≤ (n + 1) * (2 * B x.length + 2 * n + 5) →
      s.V.length ≤ n + 1 → s.Md.length ≤ 1 → s.H.length ≤ 1 → s.A.length ≤ 1 →
      ∀ u ∈ toL s, u.length ≤ bnd x.length := by
    intro s h1 h2 h3 h4 h5 u hu
    simp only [toL, List.mem_cons, List.not_mem_nil, or_false] at hu
    simp only [bnd, ← hn]
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> omega
  refine ⟨N + 1, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [cobIter_eq, hinit]
    rcases Nat.lt_or_ge k N with hk1 | hk1
    · obtain ⟨h1, h2, h3, h4, Fs, hS, -, hlen, hFB⟩ := inter k hk1
      refine hbx _ ?_ ?_ h4 ?_ ?_
      · rw [hS, List.append_nil]
        exact (length_stackW_le Fs hFB).trans (Nat.mul_le_mul_right _ hlen)
      · simpa using h3
      · rw [h1]; simp
      · rw [h2]; simp
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk2
    · rw [e]
      exact hbx _ (by simp) l (by simp) (by simp) (by simp)
    · obtain rfl : k = N + 1 := by omega
      rw [efin]
      refine hbx _ (by simp) l (by simp) (by simp) ?_
      cases decide (2 ^ (thr.eval [x]).length ≤ 2 * nv w) <;> simp [bw]
  · intro k hk
    rw [cobIter_eq, hinit]
    rcases Nat.lt_or_ge k N with hk1 | hk1
    · obtain ⟨h1, -⟩ := inter k hk1
      simp only [toL, List.getD_cons_succ, List.getD_cons_zero]
      rw [h1]; simp
    · obtain rfl : k = N := by omega
      rw [e]; simp [toL]
  · rw [cobIter_eq, hinit, efin]; simp [toL]
  · rw [cobIter_eq, hinit, efin, hL x, ← v]
    simp [toL, bw]

end Complexity.TreeEval
