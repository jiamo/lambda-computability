/-
**The code of the reduction formula, written as a stream of blocks.**

`Start/QbfWord.lean` codes a quantified Boolean formula as a binary word and bounds the length of
the code of the formula `Complexity.Qbf.QBF.machineF M x s` of the reduction.  What the
`PSPACE`-hardness of `TQBF` needs on top of that is that the *map* from the input to that word is
computed in polynomial time, i.e. by a term of `Complexity.Cob`.  The Cobham toolkit of this
library computes a word by sweeping a word once and emitting a block at every position
(`Complexity.eval_blkRunTerm`, `Complexity.eval_lrunTerm`), so the shape a compiler needs is:
*the code is a concatenation of blocks, one per position of a counter, each block a simple
function of the position*.

This module puts the code in exactly that shape.  The outer quantifier prefixes of the formula are
concatenations over a range (`Complexity.Qbf.QBF.enc_exBits`, `.enc_allBits`), the finite
conjunctions and disjunctions that make up the machine's own constraints are concatenations over
their case lists (`.enc_conjAll`, `.enc_disjAny`), and — the one place where the formula is really
recursive — the midpoint recursion contributes one block per level, since the recursion has a
*single* recursive call: `Complexity.Qbf.QBF.enc_reachF` writes the code of `reachF … k a b t` as
`k` blocks `Complexity.Qbf.QBF.reachPre` followed by the code of the base case, with the
parameters of level `j` given by the closed formulas `Complexity.Qbf.QBF.aAt`,
`Complexity.Qbf.QBF.bAt` and `t + 3 j`.

Main definitions:

* `Complexity.Qbf.QBF.reachPre` — the block of one level of the midpoint recursion;
* `Complexity.Qbf.QBF.aAt`, `Complexity.Qbf.QBF.bAt` — the endpoint blocks at level `j`.

Main results:

* `Complexity.Qbf.QBF.enc_exBits`, `.enc_allBits` — a quantifier prefix is a concatenation over a
  range;
* `Complexity.Qbf.QBF.enc_conjAll`, `.enc_disjAny` — a finite conjunction or disjunction is a
  concatenation over its list;
* `Complexity.Qbf.QBF.enc_reachF_succ`, `.enc_reachF` — **the code of the reachability formula is
  one block per level of the recursion, followed by the code of the base case**;
* `Complexity.Qbf.QBF.enc_machineF_stream` — **the code of the whole reduction formula is a fixed
  prefix, the codes of the two machine constraints, the blocks of the levels, and the code of the
  base case**.
-/

import Mathlib
import Start.QbfWord

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

/-! ### The code of the generic combinators -/

@[simp] theorem enc_var (i : ℕ) : enc (QBF.var i) = [false, false] ++ unary i := rfl
@[simp] theorem enc_neg (p : QBF) : enc (QBF.neg p) = [false, true] ++ enc p := rfl
@[simp] theorem enc_conj (p q : QBF) :
    enc (QBF.conj p q) = [true, false, false] ++ (enc p ++ enc q) := rfl
@[simp] theorem enc_disj (p q : QBF) :
    enc (QBF.disj p q) = [true, false, true] ++ (enc p ++ enc q) := rfl
@[simp] theorem enc_all (i : ℕ) (p : QBF) :
    enc (QBF.all i p) = [true, true, false] ++ (unary i ++ enc p) := rfl
@[simp] theorem enc_ex (i : ℕ) (p : QBF) :
    enc (QBF.ex i p) = [true, true, true] ++ (unary i ++ enc p) := rfl

/-- The code of a nest of existential quantifiers: one block per bound variable. -/
theorem enc_exBits (o n : ℕ) (p : QBF) :
    enc (exBits o n p)
      = ((List.range n).flatMap fun l => [true, true, true] ++ unary (o + l)) ++ enc p := by
  induction n generalizing o with
  | zero => simp [exBits]
  | succ n ih =>
      rw [exBits, enc_ex, ih (o + 1), List.range_succ_eq_map, List.flatMap_cons]
      simp only [List.flatMap_map, Nat.add_zero, List.append_assoc]
      congr 2
      refine congrArg (· ++ enc p) (List.flatMap_congr ?_)
      intro l _
      congr 2
      omega

/-- The code of a nest of universal quantifiers: one block per bound variable. -/
theorem enc_allBits (o n : ℕ) (p : QBF) :
    enc (allBits o n p)
      = ((List.range n).flatMap fun l => [true, true, false] ++ unary (o + l)) ++ enc p := by
  induction n generalizing o with
  | zero => simp [allBits]
  | succ n ih =>
      rw [allBits, enc_all, ih (o + 1), List.range_succ_eq_map, List.flatMap_cons]
      simp only [List.flatMap_map, Nat.add_zero, List.append_assoc]
      congr 2
      refine congrArg (· ++ enc p) (List.flatMap_congr ?_)
      intro l _
      congr 2
      omega

/-- The code of a finite conjunction: one block per conjunct, then the code of `tt`. -/
theorem enc_conjAll : ∀ ps : List QBF,
    enc (conjAll ps) = (ps.flatMap fun p => [true, false, false] ++ enc p) ++ enc tt
  | [] => by simp [conjAll]
  | p :: ps => by
      rw [conjAll, enc_conj, List.flatMap_cons, enc_conjAll ps]
      simp

/-- The code of a finite disjunction: one block per disjunct, then the code of `ff`. -/
theorem enc_disjAny : ∀ ps : List QBF,
    enc (disjAny ps) = (ps.flatMap fun p => [true, false, true] ++ enc p) ++ enc ff
  | [] => by simp [disjAny]
  | p :: ps => by
      rw [disjAny, enc_disj, List.flatMap_cons, enc_disjAny ps]
      simp

/-! ### One level of the midpoint recursion -/

/-- The antecedent of one level of the midpoint recursion: the two legs of the walk. -/
def legsF (m a b t : ℕ) : QBF :=
  QBF.disj (QBF.conj (eqBlock m (t + 1) a) (eqBlock m (t + 2) t))
    (QBF.conj (eqBlock m (t + 1) t) (eqBlock m (t + 2) b))

/-- **The block of one level of the midpoint recursion**: the three quantifier prefixes over the
scratch blocks, the tag bits of the implication, and the code of its antecedent.  Everything in it
is a function of the width `m` and of the three block indices — no recursion is left. -/
def reachPre (m a b t : ℕ) : List Bool :=
  ((List.range m).flatMap fun l => [true, true, true] ++ unary (t * m + l))
    ++ ((List.range m).flatMap fun l => [true, true, false] ++ unary ((t + 1) * m + l))
    ++ ((List.range m).flatMap fun l => [true, true, false] ++ unary ((t + 2) * m + l))
    ++ [true, false, true, false, true]
    ++ enc (legsF m a b t)

/-- **One level of the recursion contributes one block.** -/
theorem enc_reachF_succ (sF : ℕ → ℕ → QBF) (m k a b t : ℕ) :
    enc (reachF sF m (k + 1) a b t)
      = reachPre m a b t ++ enc (reachF sF m k (t + 1) (t + 2) (t + 3)) := by
  rw [reachF_succ, enc_exBits, enc_allBits, enc_allBits]
  simp only [imp, enc_disj, enc_neg, reachPre, legsF]
  simp [List.append_assoc]

/-- The first endpoint block at level `j` of the recursion started at `(a, b, t)`. -/
def aAt (a t : ℕ) : ℕ → ℕ
  | 0 => a
  | j + 1 => t + 3 * j + 1

/-- The second endpoint block at level `j` of the recursion started at `(a, b, t)`. -/
def bAt (b t : ℕ) : ℕ → ℕ
  | 0 => b
  | j + 1 => t + 3 * j + 2

/-- **The code of the reachability formula is a stream of blocks**: one `reachPre` per level of
the midpoint recursion, with the block indices of level `j` given in closed form, followed by the
code of the base case. -/
theorem enc_reachF (sF : ℕ → ℕ → QBF) (m : ℕ) : ∀ (k a b t : ℕ),
    enc (reachF sF m k a b t)
      = ((List.range k).flatMap fun j => reachPre m (aAt a t j) (bAt b t j) (t + 3 * j))
        ++ enc (reachF sF m 0 (aAt a t k) (bAt b t k) (t + 3 * k)) := by
  intro k
  induction k with
  | zero => intro a b t; simp [aAt, bAt]
  | succ k ih =>
      intro a b t
      rw [enc_reachF_succ, ih (t + 1) (t + 2) (t + 3), List.range_succ_eq_map,
        List.flatMap_cons]
      have haux : ∀ j : ℕ, aAt (t + 1) (t + 3) j = t + 3 * j + 1 := by
        intro j
        cases j with
        | zero => simp [aAt]
        | succ j => simp only [aAt]; omega
      have hbux : ∀ j : ℕ, bAt (t + 2) (t + 3) j = t + 3 * j + 2 := by
        intro j
        cases j with
        | zero => simp [bAt]
        | succ j => simp only [bAt]; omega
      have haux' : ∀ j : ℕ, aAt a t (j + 1) = t + 3 * j + 1 := fun _ => rfl
      have hbux' : ∀ j : ℕ, bAt b t (j + 1) = t + 3 * j + 2 := fun _ => rfl
      have hzero : aAt a t 0 = a := rfl
      have hzero' : bAt b t 0 = b := rfl
      have hshift : ∀ j : ℕ, t + 3 + 3 * j = t + 3 * (j + 1) := by intro j; omega
      simp only [List.flatMap_map, haux, hbux, haux', hbux', hzero, hzero',
        hshift, Nat.mul_zero, Nat.add_zero, List.append_assoc, Nat.succ_eq_add_one]

/-! ### The code of the whole formula -/

open Complexity.Space in
/-- **The code of the reduction formula, as a stream**: the quantifier prefix over the two endpoint
blocks, the tag bits of the two conjunctions, the codes of the initial and accepting constraints,
one block per level of the midpoint recursion, and the code of the base case. -/
theorem enc_machineF_stream (M : Complexity.Space.Machine) (x : List Bool) (s : ℕ) :
    enc (machineF M x s)
      = ((List.range (cfgWidth M x s)).flatMap fun l => [true, true, true] ++ unary l)
        ++ ((List.range (cfgWidth M x s)).flatMap fun l =>
              [true, true, true] ++ unary (cfgWidth M x s + l))
        ++ [true, false, false, true, false, false]
        ++ enc (initF M x s 0) ++ enc (accF M x s 1)
        ++ ((List.range (savitchDepth M x s)).flatMap fun j =>
              reachPre (cfgWidth M x s) (aAt 0 2 j) (bAt 1 2 j) (2 + 3 * j))
        ++ enc (reachF (stepF M x s) (cfgWidth M x s) 0
                  (aAt 0 2 (savitchDepth M x s)) (bAt 1 2 (savitchDepth M x s))
                  (2 + 3 * savitchDepth M x s)) := by
  rw [machineF, enc_exBits, enc_exBits, enc_conj, enc_conj,
    enc_reachF (stepF M x s) (cfgWidth M x s) (savitchDepth M x s) 0 1 2]
  simp [List.append_assoc]

end QBF

end Complexity.Qbf
