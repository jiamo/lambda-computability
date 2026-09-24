/-
**Comparing unary numbers, and reading a bit at a unary position, with Cobham terms.**

The compilers of this library write a word by sweeping a counter and emitting a block at every
position (`Complexity.eval_rangeEmitTerm`).  The blocks of the reduction to `TQBF` depend on
*tests*: whether the position lies in one region of a configuration rather than another, whether
it is the position marked by a head, whether the bit the machine reads at a position of its input
is set.  The Boolean gadgets of `Start/Sat.lean` — the truth values `Complexity.bw`, the
conditional `Complexity.Cob.iteT` and the connectives — already give the control structure; what
is missing, and what this module adds, is the *arithmetic* of the tests: the comparison of two
numbers given in unary, and the reading of a bit whose position is given in unary (rather than by
a literal, as in `Complexity.Cob.nthBit`).

Main definitions:

* `Complexity.Cob.boolT` — the truth value of a term, normalised;
* `Complexity.Cob.ltU`, `.leU`, `.eqU` — the comparisons of two unary numbers;
* `Complexity.Cob.bitU` — the bit of a word at a unary position.

Main results:

* `Complexity.Cob.eval_boolT` — the normaliser is correct;
* `Complexity.Cob.eval_ltU`, `.eval_leU`, `.eval_eqU` — **the comparison of two unary numbers is
  a Cobham function**;
* `Complexity.Cob.eval_bitU` — **reading the bit of a word at a unary position is a Cobham
  function**.
-/

import Mathlib
import Start.Sat
import Start.CobhamRange

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Normalising a truth value -/

/-- The truth value of a term, normalised to the canonical word: `[true]` when the term is
nonempty, the empty word when it is empty. -/
def Cob.boolT (c : Cob) : Cob := Cob.iteT c Cob.trueC .empty

theorem Cob.eval_boolT (c : Cob) (args : List Word) (b : Bool)
    (hc : c.eval args = [] ↔ b = false) :
    (Cob.boolT c).eval args = bw b := by
  simp only [Cob.boolT, Cob.iteT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC,
    Cob.eval_trueC, Cob.eval_empty]
  by_cases h : c.eval args = []
  · simp [h, hc.1 h]
  · have hb : b = true := by
      cases b with
      | false => exact absurd (hc.2 rfl) h
      | true => rfl
    simp [h, hb]

/-! ### Comparison of unary numbers -/

/-- The strict comparison of the lengths of the words computed by two terms. -/
def Cob.ltU (u v : Cob) : Cob := Cob.boolT (.comp Cob.dropU [u, v])

theorem Cob.eval_ltU (u v : Cob) (args : List Word) :
    (Cob.ltU u v).eval args =
      bw (decide ((u.eval args).length < (v.eval args).length)) := by
  refine Cob.eval_boolT _ args _ ?_
  simp [List.drop_eq_nil_iff]

/-- The comparison `≤` of the lengths of the words computed by two terms. -/
def Cob.leU (u v : Cob) : Cob := Cob.notT (Cob.ltU v u)

theorem Cob.eval_leU (u v : Cob) (args : List Word) :
    (Cob.leU u v).eval args =
      bw (decide ((u.eval args).length ≤ (v.eval args).length)) := by
  rw [Cob.leU, Cob.eval_notT (Cob.eval_ltU v u args)]
  congr 1
  rcases Nat.lt_or_ge (v.eval args).length (u.eval args).length with h | h
  · simp [h, Nat.not_le.2 h]
  · simp [Nat.not_lt.2 h, h]

/-- The equality of the lengths of the words computed by two terms. -/
def Cob.eqU (u v : Cob) : Cob := Cob.andT (Cob.leU u v) (Cob.leU v u)

theorem Cob.eval_eqU (u v : Cob) (args : List Word) :
    (Cob.eqU u v).eval args =
      bw (decide ((u.eval args).length = (v.eval args).length)) := by
  rw [Cob.eqU, Cob.eval_andT (Cob.eval_leU u v args) (Cob.eval_leU v u args)]
  congr 1
  simp [Nat.le_antisymm_iff]

/-! ### Reading a bit at a unary position -/

/-- The bit of the word computed by `xT` at the position given in unary by `iT`; `false` when the
position is out of range. -/
def Cob.bitU (iT xT : Cob) : Cob := .comp .headTrue [.comp Cob.dropU [iT, xT]]

theorem Cob.eval_bitU (iT xT : Cob) (args : List Word) :
    (Cob.bitU iT xT).eval args
      = bw ((xT.eval args).getD (iT.eval args).length false) := by
  simp only [Cob.bitU, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_dropU,
    Cob.eval_headTrue, headD_drop]
  simp [bw]

end Complexity
