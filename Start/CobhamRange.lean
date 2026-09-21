/-
**Emitting one block per index of a range is a Cobham function.**

`Start/CobhamBlock.lean` shows that a *block-emitting recursion* — a sweep of a word emitting a
block at every position — is a Cobham function.  The reductions of this library have to write
words of the shape `(List.range n).flatMap fun l => W l`, one block per index of a range, with `n`
given in unary; this module packages the recursion for exactly that shape, once.

Two small ingredients are needed.  The recursion sweeps a word from the right, so the block at the
position whose suffix has length `c` is the one of index `n - 1 - c`: the index has to be computed
from the counter, which is what `Complexity.Cob.dropN` does — dropping as many bits as its first
argument is long is a Cobham function, and on unary words that is truncated subtraction.  The
length `n` itself reaches the block through the parameter word, whose leading ones carry it
(`Complexity.Cob.leadOnes`).

Main definitions:

* `Complexity.Cob.dropN` — dropping as many bits from the second argument as the first is long;
* `Complexity.rangeEmitTerm` — the term emitting one block per index of a range.

Main results:

* `Complexity.Cob.eval_dropN` — `dropN` drops that many bits, so on unary words it subtracts;
* `Complexity.brun_replicate` — a block-emitting recursion over `1^n` whose blocks depend only on
  the counter emits them in decreasing order of the counter;
* `Complexity.eval_rangeEmitTerm` — **`(List.range n).flatMap W` is a Cobham function of `1^n` and
  of a parameter word whose leading ones are `1^n`**.
-/

import Mathlib
import Start.CobhamBlock

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Dropping a unary number of bits -/

/-- Dropping as many bits off the second argument as the first argument is long.  On unary words
this is truncated subtraction. -/
def Cob.dropN : Cob :=
  .bRec (.proj 0) (.comp Cob.tail [.proj 1]) (.comp Cob.tail [.proj 1]) (.proj 1)

@[simp] theorem Cob.eval_dropN (z w : Word) : Cob.dropN.eval [z, w] = w.drop z.length := by
  induction z with
  | nil => simp [Cob.dropN]
  | cons b z ih =>
      rw [Cob.dropN, Cob.eval_bRec_cons, ← Cob.dropN, ih]
      have hlen : (w.drop z.length).tail.length ≤ w.length := by
        simp only [List.length_tail, List.length_drop]
        omega
      have htake : ((w.drop z.length).tail).take w.length = (w.drop z.length).tail :=
        List.take_of_length_le hlen
      cases b <;>
        simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_tail, Cob.eval_proj,
          List.getD_cons_zero, List.getD_cons_succ, if_true, if_false, Bool.false_eq_true,
          htake, List.length_cons] <;>
        rw [List.tail_drop]

/-- Truncated subtraction of unary words. -/
theorem Cob.eval_dropN_replicate (c n : ℕ) :
    Cob.dropN.eval [List.replicate c true, List.replicate n true]
      = List.replicate (n - c) true := by
  simp [Cob.eval_dropN, List.drop_replicate]

/-! ### The one-state counter -/

/-- The trivial control of the sweep: one state. -/
def posDelta : ℕ → Bool → ℕ := fun _ _ => 0

/-- The counter of the sweep: one per position. -/
def posInc : ℕ → Bool → ℕ := fun _ _ => 1

theorem posDelta_lt : ∀ s b, posDelta s b < 1 := fun _ _ => Nat.zero_lt_one

theorem posInc_le : ∀ s b, posInc s b ≤ 1 := fun _ _ => Nat.le_refl 1

@[simp] theorem rcnt_posInc (x : Word) : rcnt posDelta posInc x = x.length := by
  induction x with
  | nil => simp [rcnt]
  | cons b x ih => simp only [rcnt, posInc, List.length_cons, ih]; omega

/-- A sweep of `1^k` whose blocks depend only on the counter emits them in decreasing order of the
counter. -/
theorem brun_replicate (g : ℕ → Word) : ∀ k : ℕ,
    brun posDelta posInc (fun _ _ _ c => g c) (List.replicate k true)
      = ((List.range k).reverse).flatMap g := by
  intro k
  induction k with
  | zero => simp [brun]
  | succ k ih =>
      rw [List.replicate_succ, brun, ih, rcnt_posInc, List.length_replicate,
        List.range_succ, List.reverse_append]
      simp

/-! ### The emitter -/

/-- **The term emitting one block per index of a range**: swept over `1^n`, with a parameter word
whose leading ones are `1^n`, it writes the blocks of the indices `0, 1, …, n - 1` in this order,
the block of the index `l` being the value of `bT` at `1^l` and the parameter. -/
def rangeEmitTerm (bT : Cob) (K : ℕ) : Cob :=
  blkRunTerm 1 posDelta posInc
    (fun _ _ =>
      .comp bT [.comp Cob.dropN [.proj 1, .comp Cob.tail [.comp Cob.leadOnes [.proj 2]]],
        .proj 2])
    1 K

/-- **Writing one block per index of a range is a Cobham function.** -/
theorem eval_rangeEmitTerm {K n : ℕ} (bT : Cob) (W : ℕ → Word) (p : Word)
    (hp : lead1 p = n)
    (hW : ∀ l : ℕ, bT.eval [List.replicate l true, p] = W l)
    (hb : ∀ l : ℕ, l ≤ n → (W l).length ≤ K * (p.length + 1)) :
    (rangeEmitTerm bT K).eval [List.replicate n true, p]
      = (List.range n).flatMap W := by
  have hblk : ∀ (s : ℕ) (b : Bool) (y : Word) (c : ℕ),
      ((fun (_ : ℕ) (_ : Bool) =>
        Cob.comp bT [Cob.comp Cob.dropN [Cob.proj 1, Cob.comp Cob.tail [Cob.comp Cob.leadOnes
          [Cob.proj 2]]], Cob.proj 2]) s b).eval [y, List.replicate c true, p]
        = W (n - 1 - c) := by
    intro s b y c
    have hlead : Cob.leadOnes.eval [p] = List.replicate n true := by
      rw [Cob.eval_leadOnes p [], hp]
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
      List.getD_cons_succ, Cob.eval_tail, hlead, List.tail_replicate, Cob.eval_dropN,
      List.length_replicate, List.drop_replicate]
    rw [hW]
  have hbound : ∀ (s : ℕ) (b : Bool) (y : Word) (c : ℕ), c ≤ y.length * 1 →
      (W (n - 1 - c)).length ≤ K * (y.length + p.length + 1) := by
    intro s b y c _
    refine le_trans (hb _ (by omega)) ?_
    exact Nat.mul_le_mul_left K (by omega)
  rw [rangeEmitTerm,
    eval_blkRunTerm (m := 1) Nat.zero_lt_one posDelta_lt posInc_le _ p hblk hbound,
    brun_replicate (fun c => W (n - 1 - c)) n]
  have hrev : (List.range n).reverse = (List.range n).map fun j => n - 1 - j := by
    refine List.ext_getElem (by simp) ?_
    intro i h₁ h₂
    have hi : i < n := by simpa using h₁
    rw [List.getElem_reverse]
    simp only [List.getElem_map, List.getElem_range, List.length_range]
  rw [hrev, List.flatMap_map]
  refine List.flatMap_congr ?_
  intro l hl
  have hlt : l < n := List.mem_range.1 hl
  congr 1
  omega


end Complexity
