/-
**A Cobham term writing the pinning clauses of a word.**

`Start/PinnedCnf.lean` pins the inputs of a circuit to the bits of a word `u` by unit clauses.
For the pinned formula to be the value of a *polynomial-time* function of `u`, the code of those
clauses must be produced by a Cobham term.  This module builds one:
`Complexity.Tseitin.pinTerm` evaluates at `x` to the code `Sat.encCnf (pinCnfW x)` of the pinning
clauses of `x`.

The term is a bounded recursion on notation over the scanned suffix of `x`, with `x` itself passed
along as a parameter so that the position of the current bit — needed for the unary variable index
of the clause — can be recovered as `|x| - |suffix| - 1`.

Main definitions:

* `Complexity.Tseitin.pinEnc` — the code of the pinning clauses, written as a recursion over the
  word;
* `Complexity.Tseitin.pinTerm` — the Cobham term computing it.

Main results:

* `Complexity.Tseitin.encCnf_pinCnfFrom` — the code of the pinning clauses is `pinEnc`;
* `Complexity.Tseitin.eval_pinTerm` — **the pinning clauses are produced by a Cobham term**.
-/

import Start.PinnedCnf

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Prepending a constant word -/

/-- The Cobham term prepending a fixed word to the value of `t`. -/
def Cob.pre : Word → Cob → Cob
  | [], t => t
  | b :: w, t => .comp (.app b) [Cob.pre w t]

@[simp] theorem Cob.eval_pre (w : Word) (t : Cob) (args : List Word) :
    (Cob.pre w t).eval args = w ++ t.eval args := by
  induction w with
  | nil => simp [Cob.pre]
  | cons b w ih => simp [Cob.pre, ih]

/-- The Cobham term for the word `1^{|t|}`, the unary length of the value of `t`. -/
def Cob.unary (t : Cob) : Cob := .comp .smash [t, Cob.trueC]

@[simp] theorem Cob.eval_unary (t : Cob) (args : List Word) :
    (Cob.unary t).eval args = List.replicate (t.eval args).length true := by
  simp [Cob.unary]

namespace Tseitin

open Complexity.Sat

/-! ### The code of the pinning clauses -/

/-- The code of the two unit clauses pinning the input positions `2 * d` and `2 * d + 1`. -/
def blkWord (d : ℕ) (b : Bool) : Word :=
  encClause [(true, 4 * d)] ++ encClause [(b, 4 * d + 2)]

/-- The code of the pinning clauses of the word `s`, whose bits sit at the positions
`d, d + 1, …`. -/
def pinEnc : ℕ → Word → Word
  | _, [] => []
  | d, b :: s => blkWord d b ++ pinEnc (d + 1) s

theorem encCnf_pinCnfFrom : ∀ (s : Word) (d : ℕ), encCnf (pinCnfFrom d s) = pinEnc d s := by
  intro s
  induction s with
  | nil => intro d; simp [pinCnfFrom, pinEnc, encCnf]
  | cons b s ih =>
      intro d
      rw [pinCnfFrom, pinEnc, blkWord, encCnf, List.flatMap_cons, List.flatMap_cons, ← encCnf,
        ih (d + 1), List.append_assoc]

theorem length_blkWord (d : ℕ) (b : Bool) : (blkWord d b).length ≤ 8 * d + 14 := by
  cases b <;>
    simp only [blkWord, encClause, encLit, List.length_append, List.length_cons,
      List.length_nil, List.length_flatMap, List.length_replicate, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, if_true, if_false, Bool.false_eq_true] <;>
    omega

theorem length_pinEnc : ∀ (s : Word) (d : ℕ),
    (pinEnc d s).length ≤ (8 * (d + s.length) + 14) * s.length := by
  intro s
  induction s with
  | nil => intro d; simp [pinEnc]
  | cons b s ih =>
      intro d
      have h₁ := length_blkWord d b
      have h₂ := ih (d + 1)
      have h₃ : (8 * (d + 1 + s.length) + 14) * s.length
          ≤ (8 * (d + (b :: s).length) + 14) * s.length := by
        simp only [List.length_cons]
        exact Nat.mul_le_mul_right _ (by omega)
      have h₄ : 8 * d + 14 ≤ 8 * (d + (b :: s).length) + 14 := by
        simp only [List.length_cons]
        omega
      rw [pinEnc, List.length_append]
      simp only [List.length_cons] at *
      calc (blkWord d b).length + (pinEnc (d + 1) s).length
          ≤ (8 * (d + (s.length + 1)) + 14) + (8 * (d + (s.length + 1)) + 14) * s.length := by
            omega
        _ = (8 * (d + (s.length + 1)) + 14) * (s.length + 1) := by ring

/-! ### The Cobham term -/

/-- The constant word `1111`, used to multiply a unary length by four. -/
def fourTerm : Cob := Cob.pre [true, true, true, true] .empty

@[simp] theorem eval_fourTerm (args : List Word) :
    fourTerm.eval args = [true, true, true, true] := by
  simp [fourTerm]

/-- In the step of the recursion — where the arguments are the scanned suffix, the recursive value
and the whole word — the unary word `1^{4 d}`, where `d` is the position of the current bit. -/
def offsetTerm : Cob :=
  .comp .smash [.comp Cob.dropU [.comp (.app true) [.proj 0], Cob.unary (.proj 2)], fourTerm]

@[simp] theorem eval_offsetTerm (s r x : Word) :
    offsetTerm.eval [s, r, x] = List.replicate ((x.length - s.length - 1) * 4) true := by
  simp only [offsetTerm, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_dropU,
    Cob.eval_unary, Cob.eval_proj, Cob.eval_app, Cob.eval_smash, eval_fourTerm,
    List.getD_cons_zero, List.getD_cons_succ, List.length_cons, List.drop_replicate,
    List.length_replicate, List.length_nil]
  congr 2

theorem replicate_true_append_cons (n : ℕ) (l : Word) :
    List.replicate n true ++ true :: l = true :: (List.replicate n true ++ l) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

/-- The step of the recursion: the code of the block of the current bit, followed by the code
computed for the rest of the word. -/
def stepTerm (b : Bool) : Cob :=
  .comp Cob.concat
    [Cob.pre [false, false, false, true, false, false]
      (.comp Cob.concat [offsetTerm,
        Cob.pre ([false, false, false] ++ (if b then [true, false, false] else [true, false]))
          (.comp Cob.concat [offsetTerm, Cob.pre [true, true] .empty])]),
      .proj 1]

theorem eval_stepTerm (b : Bool) (s r x : Word) (d : ℕ) (hd : d + s.length + 1 = x.length) :
    (stepTerm b).eval [s, r, x] = blkWord d b ++ r := by
  have hoff : offsetTerm.eval [s, r, x] = List.replicate (4 * d) true := by
    rw [eval_offsetTerm]
    congr 1
    omega
  simp only [stepTerm, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat,
    Cob.eval_pre, Cob.eval_proj, List.getD_cons_zero, List.getD_cons_succ, Cob.eval_empty,
    hoff]
  simp only [blkWord, encClause, encLit, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  cases b <;>
    simp [List.append_assoc, List.replicate_succ, replicate_true_append_cons]

/-- The bound of the recursion: `1^{16 (|x| + 1)^2}`, comfortably longer than the code being
built. -/
def pinBound : Cob :=
  .comp .smash
    [.comp .smash [.comp (.app true) [Cob.unary (.proj 1)], fourTerm],
      .comp .smash [.comp (.app true) [Cob.unary (.proj 1)], fourTerm]]

theorem length_eval_pinBound (s x : Word) :
    (pinBound.eval [s, x]).length = (4 * (x.length + 1)) * (4 * (x.length + 1)) := by
  simp only [pinBound, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash,
    Cob.eval_unary, Cob.eval_proj, Cob.eval_app, eval_fourTerm, List.getD_cons_zero,
    List.getD_cons_succ, List.length_replicate, List.length_cons, List.length_nil]
  ring

/-- The recursion computing the code of the pinning clauses of the suffix scanned so far. -/
def pinRec : Cob := .bRec .empty (stepTerm false) (stepTerm true) pinBound

theorem eval_pinRec (x : Word) : ∀ (s : Word) (d : ℕ), d + s.length = x.length →
    pinRec.eval [s, x] = pinEnc d s := by
  intro s
  induction s with
  | nil => intro d _; simp [pinRec, pinEnc]
  | cons b s ih =>
      intro d hd
      have hd' : d + 1 + s.length = x.length := by
        simp only [List.length_cons] at hd
        omega
      have hrec : pinRec.eval [s, x] = pinEnc (d + 1) s := ih (d + 1) hd'
      have hstep : ∀ c : Bool, (stepTerm c).eval [s, pinEnc (d + 1) s, x]
          = blkWord d c ++ pinEnc (d + 1) s :=
        fun c => eval_stepTerm c s _ x d (by omega)
      have hlen : (pinEnc d (b :: s)).length ≤ (pinBound.eval [b :: s, x]).length := by
        rw [length_eval_pinBound]
        have h := length_pinEnc (b :: s) d
        have hx : d + (b :: s).length = x.length := hd
        rw [hx] at h
        have hle : (b :: s).length ≤ x.length := by
          simp only [List.length_cons] at hx ⊢
          omega
        have : (8 * x.length + 14) * (b :: s).length
            ≤ (8 * x.length + 14) * x.length := Nat.mul_le_mul_left _ hle
        nlinarith [Nat.zero_le x.length]
      rw [pinRec, Cob.eval_bRec_cons, ← pinRec, hrec]
      cases b
      · simp only [Bool.false_eq_true, if_false, hstep false]
        rw [← pinEnc, List.take_of_length_le hlen]
      · simp only [if_true, hstep true]
        rw [← pinEnc, List.take_of_length_le hlen]

/-- **The Cobham term writing the pinning clauses.** -/
def pinTerm : Cob := .comp pinRec [.proj 0, .proj 0]

/-- **The code of the pinning clauses of a word is the value of a Cobham term at that word.** -/
theorem eval_pinTerm (x : Word) : pinTerm.eval [x] = encCnf (pinCnfW x) := by
  rw [pinTerm]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero]
  rw [eval_pinRec x x 0 (by simp), pinCnfW, encCnf_pinCnfFrom]

end Tseitin

end Complexity
