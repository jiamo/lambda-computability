/-
**One pass over the binary encoding of a state, in a machine model of the library.**

`Start/KrivineSpaceLog.lean` writes a state of the shared Krivine machine with **fixed-width
binary fields** (`Krivine.Impl.encStateBin`), which is what a space bound needs: an address of a
heap of `n` cells costs `log₂ n` bits, not `n`.  `Start/KrivineCobStep.lean` performs a
transition on the *unary* encoding with a term of `Complexity.Cob`, Cobham's class of
polynomial-time word functions.  This module performs a pass over the *binary* encoding.

Because the fields have fixed width, the offsets of the encoding depend only on the width `w` and
on the length of the stack, so the terms come as a family indexed by those two numbers — the
usual shape of a uniform machine model on fixed-width data.  Reading a field is then reading a
block of bits at a known offset, which is what the tools below do.

Main definitions:

* `Complexity.Cob.bitAtT`, `Complexity.Cob.takeNT` — the bit at a given offset, and the block of
  the first `n` bits, as Cobham terms;
* `Krivine.Impl.popStackBinT` — **the pass**: on the binary encoding of a state with a nonempty
  stack it returns the binary encoding of the state with its stack popped, the field holding the
  length of the stack rewritten.

Main results:

* `Complexity.Cob.eval_takeNT` — the block term reads the first `n` bits;
* `Krivine.Impl.eval_popStackBinT` — **the pass is correct**;
* `Krivine.Impl.popStackBinT_compiles` — it compiles into a family of Boolean circuits of size
  polynomial in the length of its input, so the pass costs polynomial time in this model.
-/

import Start.CobhamTseitin
import Start.KrivineCobStep
import Start.KrivineSpaceLog

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Reading a block of bits -/

/-- The bit at offset `i` of the word computed by `t`, as a one-letter word. -/
def Cob.bitAtT (i : ℕ) (t : Cob) : Cob :=
  Cob.iteT (Cob.nthBit i t) (Cob.constT [true]) (Cob.constT [false])

theorem Cob.eval_bitAtT (i : ℕ) (t : Cob) (args : List Word) :
    (Cob.bitAtT i t).eval args = [(t.eval args).getD i false] := by
  have h := Cob.eval_iteW (c := Cob.nthBit i t) (s := Cob.constT [true])
    (t := Cob.constT [false]) (args := args) (Cob.eval_nthBit i t args)
    (Cob.eval_constT _ _) (Cob.eval_constT _ _)
  rw [Cob.bitAtT, h]
  cases (t.eval args).getD i false <;> rfl

/-- The block of the first `n` bits of the word computed by `t`. -/
def Cob.takeNT (n : ℕ) (t : Cob) : Cob :=
  Cob.catL ((List.range n).map (fun i => Cob.bitAtT i t))

theorem take_eq_map_getD (l : Word) : ∀ n, n ≤ l.length →
    ((List.range n).map (fun i => l.getD i false)) = l.take n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro hn
      have hn' : n ≤ l.length := by omega
      have hlt : n < l.length := by omega
      have hget : l[n]? = some (l.getD n false) := by
        rw [List.getElem?_eq_getElem hlt]
        simp [List.getD, List.getElem?_eq_getElem hlt]
      rw [List.range_succ, List.map_append, ih hn', List.take_add_one, hget]
      simp

theorem Cob.eval_takeNT (n : ℕ) (t : Cob) (args : List Word) (h : n ≤ (t.eval args).length) :
    (Cob.takeNT n t).eval args = (t.eval args).take n := by
  rw [Cob.takeNT, Cob.eval_catL, List.map_map]
  have hmap : ((List.range n).map ((fun t' => Cob.eval t' args) ∘
      fun i => Cob.bitAtT i t)) = (List.range n).map (fun i => [(t.eval args).getD i false]) := by
    refine List.map_congr_left ?_
    intro i _
    exact Cob.eval_bitAtT i t args
  rw [hmap, ← take_eq_map_getD (t.eval args) n h]
  induction (List.range n) with
  | nil => simp
  | cons i l ih => simpa using ih

end Complexity

namespace Krivine

namespace Impl

open Complexity

/-! ### The pass -/

/-- **One pass over the binary encoding**: on the encoding of a state whose stack has `k + 1`
entries, in width `w`, this term returns the encoding of the state with its stack popped.  The
code and the environment pointer are copied, the field holding the length of the stack is
rewritten, the first entry of the stack is skipped and the rest of the word is copied. -/
def popStackBinT (w k : ℕ) : Cob :=
  Cob.catL
    [ Cob.takeNT (2 * w + 1) (.proj 0),
      Cob.constT (bitsOf w k),
      Cob.takeNT (k * w) (Cob.tailN (3 * w + 1 + w) (.proj 0)),
      Cob.tailN (3 * w + 1 + (k + 1) * w) (.proj 0) ]

/-- **The pass is correct.** -/
theorem eval_popStackBinT (w k : ℕ) (s : HState) (hk : s.stack.length = k + 1) :
    (popStackBinT w k).eval [encStateBin w s]
      = encStateBin w ⟨s.code, s.env, s.stack.tail, s.heap⟩ := by
  obtain ⟨a, tl, hst⟩ : ∃ a tl, s.stack = a :: tl := by
    cases hs : s.stack with
    | nil => rw [hs] at hk; simp at hk
    | cons a tl => exact ⟨a, tl, rfl⟩
  have htl : tl.length = k := by rw [hst] at hk; simpa using hk
  have hFlen : (tl.flatMap (bitsOf w)).length = k * w := by
    rw [length_flatMap_bitsOf, htl]
  -- the tail of the word, from the heap-length field on
  set R : List Bool := bitsOf w s.heap.length ++ s.heap.flatMap (encCellBin w) with hR
  -- three splittings of the word, at the three offsets the term reads at
  have h1 : encStateBin w s = (bitsOf w s.code ++ encPtrBin w s.env) ++
      (bitsOf w s.stack.length ++ (bitsOf w a ++ (tl.flatMap (bitsOf w) ++ R))) := by
    rw [encStateBin, hst, hR]; simp [List.append_assoc]
  have h2 : encStateBin w s =
      ((bitsOf w s.code ++ encPtrBin w s.env) ++ bitsOf w s.stack.length ++ bitsOf w a) ++
        (tl.flatMap (bitsOf w) ++ R) := by
    rw [h1]; simp [List.append_assoc]
  have h3 : encStateBin w s =
      ((bitsOf w s.code ++ encPtrBin w s.env) ++ bitsOf w s.stack.length ++ bitsOf w a ++
        tl.flatMap (bitsOf w)) ++ R := by
    rw [h2]; simp [List.append_assoc]
  have hlen1 : (bitsOf w s.code ++ encPtrBin w s.env).length = 2 * w + 1 := by
    simp only [List.length_append, bitsOf_length, encPtrBin_length]; omega
  have hlen2 : ((bitsOf w s.code ++ encPtrBin w s.env) ++ bitsOf w s.stack.length ++
      bitsOf w a).length = 3 * w + 1 + w := by
    simp only [List.length_append, bitsOf_length, encPtrBin_length]; omega
  have hlen3 : ((bitsOf w s.code ++ encPtrBin w s.env) ++ bitsOf w s.stack.length ++
      bitsOf w a ++ tl.flatMap (bitsOf w)).length = 3 * w + 1 + (k + 1) * w := by
    simp only [List.length_append, bitsOf_length, encPtrBin_length, hFlen]; ring
  -- the four fields the term concatenates
  have hA : (encStateBin w s).take (2 * w + 1) = bitsOf w s.code ++ encPtrBin w s.env := by
    conv_lhs => rw [h1]
    exact List.take_left' hlen1
  have hB : (encStateBin w s).drop (3 * w + 1 + w) = tl.flatMap (bitsOf w) ++ R := by
    conv_lhs => rw [h2]
    exact List.drop_left' hlen2
  have hC : (encStateBin w s).drop (3 * w + 1 + (k + 1) * w) = R := by
    conv_lhs => rw [h3]
    exact List.drop_left' hlen3
  have hAle : 2 * w + 1 ≤ (encStateBin w s).length := by
    conv_rhs => rw [h1]
    simp only [List.length_append, bitsOf_length, encPtrBin_length]
    omega
  have hBle : k * w ≤ ((encStateBin w s).drop (3 * w + 1 + w)).length := by
    rw [hB]
    simp only [List.length_append, hFlen]
    omega
  -- evaluate
  have hproj : (Cob.proj 0).eval [encStateBin w s] = encStateBin w s := by simp
  rw [popStackBinT]
  simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, Cob.eval_constT]
  rw [Cob.eval_takeNT _ _ _ (by rw [hproj]; exact hAle), hproj, hA]
  rw [Cob.eval_takeNT _ _ _ (by rw [Cob.eval_tailN, hproj]; exact hBle)]
  simp only [Cob.eval_tailN, hproj]
  rw [hB, hC, List.take_left' hFlen]
  rw [encStateBin, hR, hst]
  simp [List.append_assoc, htl]

/-- **The pass compiles into a family of Boolean circuits of polynomial size**, so it costs
polynomial time in this model. -/
theorem popStackBinT_compiles (w k : ℕ) : Tseitin.CobCompiles (popStackBinT w k) :=
  Tseitin.cobCompiles _

end Impl

end Krivine
