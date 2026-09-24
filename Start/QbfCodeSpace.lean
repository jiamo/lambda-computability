/-
**The memory of the evaluator, measured against the length of the code.**

`Start/Qbf.lean` evaluates a closed quantified Boolean formula on a stack machine and bounds the
memory it uses by `varBound p + (height p + 1) · (2 w + 2)` bits, where `w` is the width of a
pointer into the formula; with `w = size p` that is quadratic in the *size* of the formula
(`Complexity.Qbf.tqbf_memBits_le_size`).  A membership `TQBF ∈ PSPACE`, however, is a statement
about the *code* of the formula: the input of a machine deciding `Complexity.Qbf.tqbfLang` is the
binary word of `Start/QbfWord.lean`, and the space bound has to be a polynomial in the length of
that word.

This module closes that gap.  Every syntactic measure of a formula is bounded by the length of its
code — the code spends at least one bit per node and writes each variable index in unary — so the
memory of the evaluator is quadratic in the length of the code.  What is left for
`TQBF ∈ PSPACE` is then purely the compilation of the stack machine into the offline machine of
`Start/SpaceMachine.lean`; the bound it must respect is the one proved here.

Main results:

* `Complexity.Qbf.QBF.size_le_length_enc`, `.varBound_le_length_enc`, `.height_lt_length_enc` —
  **the size, the variable bound and the height of a formula are bounded by the length of its
  code**;
* `Complexity.Qbf.tqbf_memBits_le_length_enc` — **deciding a closed formula costs at most
  `2 n² + 3 n` bits, where `n` is the length of its code**;
* `Complexity.Qbf.tqbf_memBits_le_length` — the same, stated for a word of the language
  `Complexity.Qbf.tqbfLang`.
-/

import Mathlib
import Start.QbfWord

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

/-! ### The syntactic measures against the length of the code -/

/-- The code spends at least one bit per node of the formula. -/
theorem size_le_length_enc : ∀ p : QBF, p.size ≤ (enc p).length
  | .var i => by simp [enc, size]
  | .neg p => by
      have := size_le_length_enc p
      simp only [enc, size, List.length_append, List.length_cons, List.length_nil]
      omega
  | .conj p q => by
      have hp := size_le_length_enc p
      have hq := size_le_length_enc q
      simp only [enc, size, List.length_append, List.length_cons, List.length_nil]
      omega
  | .disj p q => by
      have hp := size_le_length_enc p
      have hq := size_le_length_enc q
      simp only [enc, size, List.length_append, List.length_cons, List.length_nil]
      omega
  | .all i p => by
      have := size_le_length_enc p
      simp only [enc, size, List.length_append, List.length_cons, List.length_nil, length_unary]
      omega
  | .ex i p => by
      have := size_le_length_enc p
      simp only [enc, size, List.length_append, List.length_cons, List.length_nil, length_unary]
      omega

/-- Every variable index is written in unary, so the number of variables the evaluator has to
remember is bounded by the length of the code. -/
theorem varBound_le_length_enc : ∀ p : QBF, p.varBound ≤ (enc p).length
  | .var i => by simp [enc, varBound]
  | .neg p => by
      have := varBound_le_length_enc p
      simp only [enc, varBound, List.length_append, List.length_cons, List.length_nil]
      omega
  | .conj p q => by
      have hp := varBound_le_length_enc p
      have hq := varBound_le_length_enc q
      simp only [enc, varBound, List.length_append, List.length_cons, List.length_nil]
      omega
  | .disj p q => by
      have hp := varBound_le_length_enc p
      have hq := varBound_le_length_enc q
      simp only [enc, varBound, List.length_append, List.length_cons, List.length_nil]
      omega
  | .all i p => by
      have := varBound_le_length_enc p
      simp only [enc, varBound, List.length_append, List.length_cons, List.length_nil,
        length_unary]
      omega
  | .ex i p => by
      have := varBound_le_length_enc p
      simp only [enc, varBound, List.length_append, List.length_cons, List.length_nil,
        length_unary]
      omega

/-- The depth of the recursion, hence the number of activation records, is below the length of the
code. -/
theorem height_lt_length_enc (p : QBF) : p.height < (enc p).length :=
  lt_of_lt_of_le (height_lt_size p) (size_le_length_enc p)

end QBF

/-! ### The memory of the evaluator in terms of the code -/

/-- **Deciding a closed formula costs memory quadratic in the length of its code.**  A pointer of
`n = |enc p|` bits addresses the code, the assignment needs one bit per variable and the stack at
most one record per level, and all three measures are bounded by `n`. -/
theorem tqbf_memBits_le_length_enc (p : QBF) (u : St)
    (h : Trace p.height ⟨.eval p, fun _ => false, []⟩ u) :
    memBits (QBF.enc p).length p.varBound u ≤ 2 * (QBF.enc p).length ^ 2
      + 3 * (QBF.enc p).length := by
  have hb := tqbf_memBits_le p (QBF.enc p).length u h
  have hv := QBF.varBound_le_length_enc p
  have hh := QBF.height_lt_length_enc p
  set n := (QBF.enc p).length with hn
  have hmul : (p.height + 1) * (2 * n + 2) ≤ n * (2 * n + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have : n * (2 * n + 2) = 2 * n ^ 2 + 2 * n := by ring
  omega

/-- The same bound for a word of the language: a word of `Complexity.Qbf.tqbfLang` is the code of a
formula, and deciding that formula costs at most `2 |w|² + 3 |w|` bits. -/
theorem tqbf_memBits_le_length (w : List Bool) (p : QBF) (hp : QBF.enc p = w) (u : St)
    (h : Trace p.height ⟨.eval p, fun _ => false, []⟩ u) :
    memBits w.length p.varBound u ≤ 2 * w.length ^ 2 + 3 * w.length := by
  subst hp
  exact tqbf_memBits_le_length_enc p u h

end Complexity.Qbf
