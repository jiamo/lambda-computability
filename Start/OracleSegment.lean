/-
**Finite oracle segments.**

Relative computability is formalised in this library by letting a machine read *finite initial
segments* of the oracle: a machine with oracle `A : ℕ → Bool` is an ordinary partial recursive
code that receives, besides its real input, a number coding the list `[A 0, …, A (s-1)]`.  This
file sets up that coding and its basic laws; `Start/OracleMachine.lean` builds the relativised
machines on top of it.

* `Lambda.Oracle.segList`, `Lambda.Oracle.segNum` — the initial segment of the oracle, as a list
  of booleans and as a number;
* `Lambda.Oracle.segQuery` — the oracle answer a machine reads off a segment code, `none` when the
  query exceeds the segment;
* `Lambda.Oracle.segQuery_segNum` — a query below the length of the segment returns the true
  oracle value, and a query beyond it returns `none`;
* `Lambda.Oracle.segQuery_mono` — answers already given are never revised by a longer segment;
* `Lambda.Oracle.segNum_congr` — the segment only depends on the oracle below its length, which is
  the form of the *use principle* used later.
-/

import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Oracle

open Encodable

/-- The initial segment `[A 0, …, A (s-1)]` of the oracle `A`. -/
def segList (A : ℕ → Bool) (s : ℕ) : List Bool := (List.range s).map A

/-- The initial segment of the oracle `A` of length `s`, as a number. -/
def segNum (A : ℕ → Bool) (s : ℕ) : ℕ := encode (segList A s)

/-- The list of oracle answers coded by a number; garbage codes stand for the empty segment. -/
def segDecode (sigma : ℕ) : List Bool := (decode (α := List Bool) sigma).getD []

/-- The answer a machine gets when it queries position `x` of the segment coded by `sigma`;
`none` means that the segment is too short, in which case the machine is stuck. -/
def segQuery (sigma x : ℕ) : Option Bool := (segDecode sigma)[x]?

@[simp] theorem segList_length (A : ℕ → Bool) (s : ℕ) : (segList A s).length = s := by
  simp [segList]

@[simp] theorem segDecode_segNum (A : ℕ → Bool) (s : ℕ) :
    segDecode (segNum A s) = segList A s := by
  simp [segDecode, segNum]

theorem segList_getElem? (A : ℕ → Bool) (s x : ℕ) :
    (segList A s)[x]? = if x < s then some (A x) else none := by
  by_cases hx : x < s
  · rw [segList, List.getElem?_map, List.getElem?_range hx]
    simp [hx]
  · rw [segList, List.getElem?_map,
      List.getElem?_eq_none (by simpa using Nat.not_lt.1 hx)]
    simp [hx]

theorem segQuery_segNum (A : ℕ → Bool) (s x : ℕ) :
    segQuery (segNum A s) x = if x < s then some (A x) else none := by
  simp [segQuery, segList_getElem?]

theorem segQuery_segNum_of_lt {A : ℕ → Bool} {s x : ℕ} (h : x < s) :
    segQuery (segNum A s) x = some (A x) := by
  simp [segQuery_segNum, h]

/-- Longer segments never revise an answer already given. -/
theorem segQuery_mono {A : ℕ → Bool} {s t x : ℕ} {b : Bool} (hst : s ≤ t)
    (h : segQuery (segNum A s) x = some b) : segQuery (segNum A t) x = some b := by
  rw [segQuery_segNum] at h ⊢
  by_cases hx : x < s
  · simp only [hx, if_true] at h
    simp [lt_of_lt_of_le hx hst, h]
  · simp [hx] at h

/-- The segment of length `s` only depends on the oracle below `s`: the *use principle*. -/
theorem segNum_congr {A B : ℕ → Bool} {s : ℕ} (h : ∀ n < s, A n = B n) :
    segNum A s = segNum B s := by
  have : segList A s = segList B s := by
    simp only [segList]
    refine List.map_congr_left ?_
    intro n hn
    exact h n (List.mem_range.1 hn)
  simp [segNum, this]

end Oracle
end Lambda
