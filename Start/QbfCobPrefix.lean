/-
**The quantifier prefixes of the reduction formula are written by a Cobham term.**

`Start/QbfWordStream.lean` puts the code of the reduction formula in a streaming shape: a
concatenation of blocks, one per index of a range.  `Start/CobhamRange.lean` shows that writing
such a concatenation is a Cobham function.  This module joins the two for the first piece of the
code, the quantifier prefixes: the word

`(List.range n).flatMap fun l => tag ++ unary (o + l)`

— which is exactly the code of a nest of `n` quantifiers over the variables `o, …, o + n - 1`, by
`Complexity.Qbf.QBF.enc_exBits` and `Complexity.Qbf.QBF.enc_allBits` — is the value of one Cobham
term at the arguments `1^n` and `1^n 0 1^o`.

Main definitions:

* `Complexity.Qbf.QBF.quantBlockTerm` — the term writing one quantifier of the prefix;
* `Complexity.Qbf.QBF.quantPrefixTerm` — the term writing the whole prefix.

Main results:

* `Complexity.Qbf.QBF.eval_quantBlockTerm` — the block term writes the tag bits and the index in
  unary;
* `Complexity.Qbf.QBF.eval_quantPrefixTerm` — **the quantifier prefix of the code is a Cobham
  function of the width and the offset in unary**;
* `Complexity.Qbf.QBF.enc_exBits_eval`, `Complexity.Qbf.QBF.enc_allBits_eval` — the code of a nest
  of existential or universal quantifiers is that value, followed by the code of the body.
-/

import Mathlib
import Start.CobhamRange
import Start.QbfWordStream

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

open Complexity

/-- The parameter word of the prefix term: the width and the offset in unary, separated by a zero
bit. -/
def widthOffsetWord (n o : ℕ) : Word :=
  List.replicate n true ++ [false] ++ List.replicate o true

@[simp] theorem lead1_widthOffsetWord (n o : ℕ) : lead1 (widthOffsetWord n o) = n := by
  induction n with
  | zero => simp [widthOffsetWord, lead1]
  | succ n ih =>
      have : widthOffsetWord (n + 1) o = true :: widthOffsetWord n o := by
        simp [widthOffsetWord, List.replicate_succ]
      rw [this, lead1, ih]

@[simp] theorem drop1_widthOffsetWord (n o : ℕ) :
    drop1 (widthOffsetWord n o) = false :: List.replicate o true := by
  induction n with
  | zero => simp [widthOffsetWord, drop1]
  | succ n ih =>
      have : widthOffsetWord (n + 1) o = true :: widthOffsetWord n o := by
        simp [widthOffsetWord, List.replicate_succ]
      rw [this, drop1, ih]

/-- **The block of one quantifier**: the tag bits, then the offset and the index in unary. -/
def quantBlockTerm (tag : Word) : Cob :=
  Cob.pre tag
    (.comp Cob.concat
      [.comp Cob.concat [.comp Cob.tail [.comp Cob.dropOnes [.proj 1]], .proj 0],
        Cob.pre [false] .empty])

theorem eval_quantBlockTerm (tag : Word) (l n o : ℕ) :
    (quantBlockTerm tag).eval [List.replicate l true, widthOffsetWord n o]
      = tag ++ unary (o + l) := by
  simp only [quantBlockTerm, Cob.eval_pre, Cob.eval_comp, List.map_cons, List.map_nil,
    Cob.eval_concat, Cob.eval_proj, List.getD_cons_zero, List.getD_cons_succ, Cob.eval_tail,
    Cob.eval_dropOnes, Cob.eval_pre, Cob.eval_empty, List.append_nil, drop1_widthOffsetWord,
    List.tail_cons]
  rw [unary, ← List.replicate_add]

/-- **The term writing a whole quantifier prefix.** -/
def quantPrefixTerm (tag : Word) (K : ℕ) : Cob := rangeEmitTerm (quantBlockTerm tag) K

/-- **The quantifier prefix of the code is a Cobham function** of the width and the offset, given
in unary. -/
theorem eval_quantPrefixTerm (tag : Word) (n o : ℕ) :
    (quantPrefixTerm tag (tag.length + 1)).eval
        [List.replicate n true, widthOffsetWord n o]
      = (List.range n).flatMap fun l => tag ++ unary (o + l) := by
  refine eval_rangeEmitTerm (quantBlockTerm tag) (fun l => tag ++ unary (o + l))
    (widthOffsetWord n o) (lead1_widthOffsetWord n o) (fun l => eval_quantBlockTerm tag l n o)
    ?_
  intro l hl
  have hp : (widthOffsetWord n o).length = n + 1 + o := by
    simp [widthOffsetWord]
    omega
  simp only [List.length_append, length_unary, hp]
  have h2 : tag.length ≤ tag.length * (n + o + 2) := Nat.le_mul_of_pos_right _ (by omega)
  calc tag.length + (o + l + 1)
      ≤ tag.length * (n + o + 2) + (n + o + 2) := Nat.add_le_add h2 (by omega)
    _ = (tag.length + 1) * (n + 1 + o + 1) := by ring

/-- The code of a nest of existential quantifiers is the value of the prefix term, followed by the
code of the body. -/
theorem enc_exBits_eval (o n : ℕ) (p : QBF) :
    enc (exBits o n p)
      = (quantPrefixTerm [true, true, true] 4).eval
          [List.replicate n true, widthOffsetWord n o] ++ enc p := by
  have h := eval_quantPrefixTerm [true, true, true] n o
  simp only [List.length_cons, List.length_nil] at h
  rw [enc_exBits, h]

/-- The code of a nest of universal quantifiers is the value of the prefix term, followed by the
code of the body. -/
theorem enc_allBits_eval (o n : ℕ) (p : QBF) :
    enc (allBits o n p)
      = (quantPrefixTerm [true, true, false] 4).eval
          [List.replicate n true, widthOffsetWord n o] ++ enc p := by
  have h := eval_quantPrefixTerm [true, true, false] n o
  simp only [List.length_cons, List.length_nil] at h
  rw [enc_allBits, h]

end QBF

end Complexity.Qbf
