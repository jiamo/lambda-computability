import Start.StarHeightCoreIdentity

/-!
# The automata for the stars of the twelve classes

`fStep i` reads a word block by block and remembers the walk state and `comp` of the current block;
it rejects once a completed block lies outside the class `F_{i+1}`.  `fData i` is the strictly
locally testable description of `F_{i+1}∗` (prefixes, suffixes, forbidden factors).  `f_check`
compares the two automata on the reachable part of their product.
-/

namespace GeneralizedStarHeight

/-- The automaton reading the blocks of a word in `Fᵢ∗`: the walk state and `comp` of the current
block; `none` once a completed block lies outside the class. -/
def fStep (i : Fin 12) : Option (ZMod 3 × W3) → Fin 3 → Option (ZMod 3 × W3)
  | none, _ => none
  | some (s, c), a =>
    if s + step3 a = 0 then (if cls (comp (c ++ [a])) = i.succ then some (0, []) else none)
    else some (s + step3 a, comp (c ++ [a]))

/-- Acceptance: no incomplete block. -/
def fAcc : Option (ZMod 3 × W3) → Bool
  | none => false
  | some (s, _) => decide (s = 0)

/-- The strictly locally testable data: prefixes, suffixes and forbidden factors of `Fᵢ∗`. -/
def fData : Fin 12 → List W3 × List W3 × List W3 := ![
  ([[0]], [[2]], [[0, 0], [1], [2, 2]]),
  ([[0, 0, 2], [0, 1, 2]], [[0, 2, 2], [1, 2, 2]],
    [[0, 0, 0], [0, 0, 1], [0, 2, 0, 0], [0, 2, 0, 1], [1, 0], [1, 1], [1, 2, 0, 0], [1, 2, 0, 1],
      [2, 2, 0, 2], [2, 2, 1], [2, 2, 2]]),
  ([[0, 0, 1], [0, 0, 2], [0, 1, 2]], [[0, 0, 1], [2, 0, 1]],
    [[0, 0, 0], [0, 0, 1, 2], [1, 0, 1, 0], [1, 0, 2], [1, 1], [2, 0, 0], [2, 0, 1, 2], [2, 1, 0],
      [2, 2]]),
  ([[0, 0, 2], [0, 1, 0], [0, 1, 2]], [[0, 1, 0], [2, 1, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 1], [1, 0, 0, 2], [1, 0, 1], [1, 0, 2], [1, 1], [2, 0, 0], [2, 0, 1],
      [2, 2]]),
  ([[0, 0], [0, 1]], [[1, 1]],
    [[0, 0, 0], [0, 0, 1], [0, 1, 0], [1, 0, 2], [1, 1, 1], [1, 1, 2], [2, 0, 0], [2, 0, 1],
      [2, 1, 0], [2, 2]]),
  ([[1, 0], [1, 1]], [[0, 0]],
    [[0, 0, 0], [0, 0, 2], [0, 1, 2], [1, 0, 1], [1, 1, 0], [1, 1, 1], [2, 0, 1], [2, 1, 0],
      [2, 1, 1], [2, 2]]),
  ([[1, 0, 1], [1, 0, 2], [1, 1, 2]], [[1, 0, 1], [2, 0, 1]],
    [[0, 0], [0, 1, 0], [0, 1, 1, 2], [0, 1, 2], [1, 1, 1, 0], [1, 1, 1, 1], [2, 1, 0], [2, 1, 1],
      [2, 2]]),
  ([[1, 0, 2], [1, 1, 0], [1, 1, 2]], [[1, 1, 0], [2, 1, 0]],
    [[0, 0], [0, 1, 0, 1], [0, 1, 2], [1, 1, 0, 2], [1, 1, 1], [2, 0, 1], [2, 1, 0, 2], [2, 1, 1],
      [2, 2]]),
  ([[2]], [[0]], [[0, 0], [1], [2, 2]]),
  ([[2, 2, 0], [2, 2, 1]], [[2, 1, 0]],
    [[0, 0], [0, 1], [1, 0, 2, 0], [1, 0, 2, 1], [1, 1], [1, 2, 2], [2, 0, 2, 2], [2, 2, 2]]),
  ([[2, 2, 0], [2, 2, 1]], [[2, 0, 0]],
    [[0, 0, 0], [0, 0, 2, 0], [0, 0, 2, 1], [0, 1], [1, 0], [1, 1], [1, 2, 2], [2, 0, 2, 2],
      [2, 2, 2]]),
  ([[2, 2, 0], [2, 2, 1]], [[2, 0, 1]],
    [[0, 0], [0, 1, 2, 0], [0, 1, 2, 1], [0, 2, 2], [1, 0], [1, 1], [2, 1, 2, 2], [2, 2, 2]])]

lemma f_check : ∀ i : Fin 12, pairCheck [0, 1, 2] (fStep i) (sltStep (fData i).2.2) (some (0, []))
    (some ([], [])) fAcc (sltAcc true (fData i).1 (fData i).2.1) 60 = true := by
  decide +kernel

lemma fData_ok : ∀ i : Fin 12, (∀ p ∈ (fData i).1, p.length ≤ 3) ∧
    (∀ s ∈ (fData i).2.1, s.length ≤ 3) ∧ ∀ g ∈ (fData i).2.2, g ≠ [] ∧ g.length ≤ 4 := by
  decide

end GeneralizedStarHeight
