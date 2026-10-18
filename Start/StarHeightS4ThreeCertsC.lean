import Start.StarHeightS4ThreeTable

/-!
# Certificates for classes of letter triples of `S₄` (part C)

Classes of triples of letters of `S₄` (no double transposition, distinct letters, generating `S₄`)
for which the good coset automata of `S₄` separate `S₄` (`D = 1`).  Letters are written in Lean's
convention: the table `p0 p1 p2 p3` of a letter lists its images of `0, 1, 2, 3`.

For each class `Knn`: the letters `Knn.L`; two or three coset automata of `S₄` on at most four
states (embedded in `Fin 4`; unused states are fixed by every letter), with base state `0`; for
each, the certificate that its return automaton has an aperiodic transformation monoid
(`decide +kernel`); the list `Knn.R` of the `24` reachable joint states with the value of the
morphism; and `Knn.height_one`, an instance of `height_one_of_tableOK`.

* `K19`: `0132 0231 3021` (automata on 4, 3, 2 states)
* `K20`: `0132 0231 3102` (automata on 4, 3, 2 states)
* `K21`: `0132 0231 3201` (automata on 4, 3, 2 states)
* `K22`: `0132 1203 1230` (automata on 4, 3, 2 states)
* `K23`: `0132 1203 1302` (automata on 4, 3, 2 states)
* `K24`: `0132 1203 2013` (automata on 4, 3, 2 states)
* `K25`: `0132 1203 2031` (automata on 4, 3, 2 states)
* `K26`: `0132 1203 3012` (automata on 4, 3, 2 states)
* `K27`: `0132 1203 3201` (automata on 4, 3, 2 states)
-/

-- The certificates below are checked one at a time, which keeps the peak memory low.
set_option Elab.async false

namespace GeneralizedStarHeight

namespace S4Three

open S4Two

/-! ### `K19`: letters `0132 0231 3021` -/

namespace K19

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 1, 3, 2], [0, 2, 3, 1], [3, 0, 2, 1]]

/-- Automaton `a0` (transformation monoid of its return automaton: 42 elements). -/
def a0 : List (List ℕ) := [[1, 1, 2], [0, 3, 1], [2, 2, 3], [3, 0, 0]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 21 elements). -/
def a1 : List (List ℕ) := [[1, 1, 2], [0, 2, 0], [2, 0, 1], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[1, 0, 0], [0, 1, 1], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 1], [0, 1, 3, 2]), ([1, 1, 0], [0, 2, 3, 1]), ([2, 2, 0], [3, 0, 2, 1]),
    ([3, 2, 1], [0, 3, 2, 1]), ([1, 0, 1], [2, 0, 3, 1]), ([0, 0, 1], [0, 2, 1, 3]),
    ([3, 2, 0], [0, 3, 1, 2]), ([1, 0, 0], [1, 0, 3, 2]), ([2, 2, 1], [3, 0, 1, 2]),
    ([2, 0, 0], [3, 2, 1, 0]), ([3, 1, 0], [1, 3, 2, 0]), ([0, 1, 1], [1, 0, 2, 3]),
    ([0, 1, 0], [2, 0, 1, 3]), ([3, 1, 1], [2, 3, 1, 0]), ([1, 2, 1], [1, 2, 3, 0]),
    ([1, 2, 0], [2, 1, 3, 0]), ([2, 0, 1], [3, 1, 2, 0]), ([2, 1, 1], [3, 2, 0, 1]),
    ([2, 1, 0], [3, 1, 0, 2]), ([3, 0, 1], [1, 3, 0, 2]), ([0, 2, 0], [1, 2, 0, 3]),
    ([3, 0, 0], [2, 3, 0, 1]), ([0, 2, 1], [2, 1, 0, 3])]

/-- **Every language recognized by a morphism with these letters has height at most one.** -/
theorem height_one (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : ∀ x i, T (FreeMonoid.of x) i = letT L x i) (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_tableOK L [a0, a1, a2] R (by decide +kernel) ?_ T hT F
  intro t ht q
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact good_baseN _ 0 _ a0_cert q
  · exact good_baseN _ 0 _ a1_cert q
  · exact good_baseN _ 0 _ a2_cert q

end K19

/-! ### `K20`: letters `0132 0231 3102` -/

namespace K20

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 1, 3, 2], [0, 2, 3, 1], [3, 1, 0, 2]]

/-- Automaton `a0` (transformation monoid of its return automaton: 49 elements). -/
def a0 : List (List ℕ) := [[1, 1, 2], [0, 3, 0], [2, 2, 1], [3, 0, 3]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 14 elements). -/
def a1 : List (List ℕ) := [[1, 1, 1], [0, 2, 2], [2, 0, 0], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[1, 0, 0], [0, 1, 1], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 1], [0, 1, 3, 2]), ([1, 1, 0], [0, 2, 3, 1]), ([2, 1, 0], [3, 1, 0, 2]),
    ([3, 2, 1], [0, 3, 2, 1]), ([0, 2, 1], [2, 1, 0, 3]), ([0, 0, 1], [0, 2, 1, 3]),
    ([3, 2, 0], [0, 3, 1, 2]), ([0, 2, 0], [1, 2, 0, 3]), ([2, 0, 1], [3, 1, 2, 0]),
    ([2, 2, 0], [3, 0, 2, 1]), ([1, 2, 0], [2, 1, 3, 0]), ([3, 0, 1], [1, 3, 0, 2]),
    ([1, 0, 1], [2, 0, 3, 1]), ([2, 1, 1], [3, 2, 0, 1]), ([3, 0, 0], [2, 3, 0, 1]),
    ([1, 2, 1], [1, 2, 3, 0]), ([1, 0, 0], [1, 0, 3, 2]), ([2, 0, 0], [3, 2, 1, 0]),
    ([2, 2, 1], [3, 0, 1, 2]), ([3, 1, 0], [1, 3, 2, 0]), ([0, 1, 1], [1, 0, 2, 3]),
    ([3, 1, 1], [2, 3, 1, 0]), ([0, 1, 0], [2, 0, 1, 3])]

/-- **Every language recognized by a morphism with these letters has height at most one.** -/
theorem height_one (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : ∀ x i, T (FreeMonoid.of x) i = letT L x i) (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_tableOK L [a0, a1, a2] R (by decide +kernel) ?_ T hT F
  intro t ht q
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact good_baseN _ 0 _ a0_cert q
  · exact good_baseN _ 0 _ a1_cert q
  · exact good_baseN _ 0 _ a2_cert q

end K20

/-! ### `K21`: letters `0132 0231 3201` -/

namespace K21

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 1, 3, 2], [0, 2, 3, 1], [3, 2, 0, 1]]

/-- Automaton `a0` (transformation monoid of its return automaton: 39 elements). -/
def a0 : List (List ℕ) := [[1, 1, 2], [0, 3, 3], [2, 2, 1], [3, 0, 0]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 14 elements). -/
def a1 : List (List ℕ) := [[1, 1, 1], [0, 2, 0], [2, 0, 2], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[1, 0, 1], [0, 1, 0], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 1], [0, 1, 3, 2]), ([1, 1, 0], [0, 2, 3, 1]), ([2, 1, 1], [3, 2, 0, 1]),
    ([3, 2, 1], [0, 3, 2, 1]), ([3, 0, 0], [2, 3, 0, 1]), ([0, 0, 1], [0, 2, 1, 3]),
    ([3, 2, 0], [0, 3, 1, 2]), ([3, 0, 1], [1, 3, 0, 2]), ([2, 0, 0], [3, 2, 1, 0]),
    ([2, 2, 1], [3, 0, 1, 2]), ([1, 0, 0], [1, 0, 3, 2]), ([0, 2, 0], [1, 2, 0, 3]),
    ([3, 1, 1], [2, 3, 1, 0]), ([0, 1, 0], [2, 0, 1, 3]), ([0, 1, 1], [1, 0, 2, 3]),
    ([2, 1, 0], [3, 1, 0, 2]), ([0, 2, 1], [2, 1, 0, 3]), ([3, 1, 0], [1, 3, 2, 0]),
    ([2, 2, 0], [3, 0, 2, 1]), ([2, 0, 1], [3, 1, 2, 0]), ([1, 2, 0], [2, 1, 3, 0]),
    ([1, 2, 1], [1, 2, 3, 0]), ([1, 0, 1], [2, 0, 3, 1])]

/-- **Every language recognized by a morphism with these letters has height at most one.** -/
theorem height_one (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : ∀ x i, T (FreeMonoid.of x) i = letT L x i) (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_tableOK L [a0, a1, a2] R (by decide +kernel) ?_ T hT F
  intro t ht q
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact good_baseN _ 0 _ a0_cert q
  · exact good_baseN _ 0 _ a1_cert q
  · exact good_baseN _ 0 _ a2_cert q

end K21

/-! ### `K22`: letters `0132 1203 1230` -/

namespace K22

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 1, 3, 2], [1, 2, 0, 3], [1, 2, 3, 0]]

/-- Automaton `a0` (transformation monoid of its return automaton: 41 elements). -/
def a0 : List (List ℕ) := [[1, 2, 2], [0, 1, 0], [2, 3, 3], [3, 0, 1]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 20 elements). -/
def a1 : List (List ℕ) := [[1, 2, 2], [0, 0, 1], [2, 1, 0], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[1, 0, 1], [0, 1, 0], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 1], [0, 1, 3, 2]), ([2, 2, 0], [1, 2, 0, 3]), ([2, 2, 1], [1, 2, 3, 0]),
    ([1, 0, 1], [1, 3, 0, 2]), ([0, 1, 0], [1, 3, 2, 0]), ([3, 1, 0], [2, 0, 1, 3]),
    ([3, 0, 1], [2, 0, 3, 1]), ([3, 1, 1], [2, 3, 1, 0]), ([3, 0, 0], [2, 3, 0, 1]),
    ([1, 2, 1], [3, 0, 1, 2]), ([0, 2, 0], [3, 0, 2, 1]), ([2, 0, 0], [3, 2, 1, 0]),
    ([2, 1, 1], [3, 2, 0, 1]), ([0, 2, 1], [0, 3, 2, 1]), ([1, 2, 0], [0, 3, 1, 2]),
    ([0, 0, 1], [3, 1, 2, 0]), ([1, 1, 0], [3, 1, 0, 2]), ([2, 1, 0], [0, 2, 3, 1]),
    ([2, 0, 1], [0, 2, 1, 3]), ([3, 2, 0], [2, 1, 3, 0]), ([3, 2, 1], [2, 1, 0, 3]),
    ([1, 0, 0], [1, 0, 3, 2]), ([0, 1, 1], [1, 0, 2, 3])]

/-- **Every language recognized by a morphism with these letters has height at most one.** -/
theorem height_one (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : ∀ x i, T (FreeMonoid.of x) i = letT L x i) (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_tableOK L [a0, a1, a2] R (by decide +kernel) ?_ T hT F
  intro t ht q
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact good_baseN _ 0 _ a0_cert q
  · exact good_baseN _ 0 _ a1_cert q
  · exact good_baseN _ 0 _ a2_cert q

end K22

/-! ### `K23`: letters `0132 1203 1302` -/

namespace K23

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 1, 3, 2], [1, 2, 0, 3], [1, 3, 0, 2]]

/-- Automaton `a0` (transformation monoid of its return automaton: 41 elements). -/
def a0 : List (List ℕ) := [[1, 2, 1], [0, 1, 2], [2, 3, 3], [3, 0, 0]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 20 elements). -/
def a1 : List (List ℕ) := [[1, 1, 2], [0, 2, 1], [2, 0, 0], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[1, 0, 1], [0, 1, 0], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 1], [0, 1, 3, 2]), ([2, 1, 0], [1, 2, 0, 3]), ([1, 2, 1], [1, 3, 0, 2]),
    ([2, 0, 1], [1, 2, 3, 0]), ([3, 2, 0], [2, 0, 1, 3]), ([3, 1, 1], [2, 3, 1, 0]),
    ([0, 2, 0], [1, 3, 2, 0]), ([1, 0, 1], [3, 0, 1, 2]), ([2, 0, 0], [3, 2, 1, 0]),
    ([3, 2, 1], [2, 0, 3, 1]), ([0, 0, 1], [0, 3, 2, 1]), ([3, 0, 0], [2, 3, 0, 1]),
    ([0, 2, 1], [3, 1, 2, 0]), ([0, 1, 0], [3, 0, 2, 1]), ([2, 2, 0], [0, 2, 3, 1]),
    ([2, 1, 1], [3, 2, 0, 1]), ([3, 1, 0], [2, 1, 3, 0]), ([1, 1, 0], [0, 3, 1, 2]),
    ([1, 2, 0], [3, 1, 0, 2]), ([1, 0, 0], [1, 0, 3, 2]), ([2, 2, 1], [0, 2, 1, 3]),
    ([3, 0, 1], [2, 1, 0, 3]), ([0, 1, 1], [1, 0, 2, 3])]

/-- **Every language recognized by a morphism with these letters has height at most one.** -/
theorem height_one (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : ∀ x i, T (FreeMonoid.of x) i = letT L x i) (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_tableOK L [a0, a1, a2] R (by decide +kernel) ?_ T hT F
  intro t ht q
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact good_baseN _ 0 _ a0_cert q
  · exact good_baseN _ 0 _ a1_cert q
  · exact good_baseN _ 0 _ a2_cert q

end K23

/-! ### `K24`: letters `0132 1203 2013` -/

namespace K24

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 1, 3, 2], [1, 2, 0, 3], [2, 0, 1, 3]]

/-- Automaton `a0` (transformation monoid of its return automaton: 58 elements). -/
def a0 : List (List ℕ) := [[1, 2, 3], [0, 1, 1], [2, 3, 0], [3, 0, 2]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 21 elements). -/
def a1 : List (List ℕ) := [[1, 2, 1], [0, 0, 2], [2, 1, 0], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[1, 0, 0], [0, 1, 1], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 1], [0, 1, 3, 2]), ([2, 2, 0], [1, 2, 0, 3]), ([3, 1, 0], [2, 0, 1, 3]),
    ([1, 0, 1], [1, 3, 0, 2]), ([1, 2, 1], [3, 0, 1, 2]), ([2, 2, 1], [1, 2, 3, 0]),
    ([3, 0, 1], [2, 0, 3, 1]), ([0, 1, 0], [1, 3, 2, 0]), ([0, 2, 0], [3, 0, 2, 1]),
    ([3, 1, 1], [2, 3, 1, 0]), ([0, 0, 1], [3, 1, 2, 0]), ([0, 2, 1], [0, 3, 2, 1]),
    ([2, 1, 1], [3, 2, 0, 1]), ([2, 0, 0], [3, 2, 1, 0]), ([3, 2, 0], [2, 1, 3, 0]),
    ([2, 1, 0], [0, 2, 3, 1]), ([3, 0, 0], [2, 3, 0, 1]), ([1, 1, 0], [3, 1, 0, 2]),
    ([1, 2, 0], [0, 3, 1, 2]), ([3, 2, 1], [2, 1, 0, 3]), ([2, 0, 1], [0, 2, 1, 3]),
    ([1, 0, 0], [1, 0, 3, 2]), ([0, 1, 1], [1, 0, 2, 3])]

/-- **Every language recognized by a morphism with these letters has height at most one.** -/
theorem height_one (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : ∀ x i, T (FreeMonoid.of x) i = letT L x i) (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_tableOK L [a0, a1, a2] R (by decide +kernel) ?_ T hT F
  intro t ht q
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact good_baseN _ 0 _ a0_cert q
  · exact good_baseN _ 0 _ a1_cert q
  · exact good_baseN _ 0 _ a2_cert q

end K24

/-! ### `K25`: letters `0132 1203 2031` -/

namespace K25

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 1, 3, 2], [1, 2, 0, 3], [2, 0, 3, 1]]

/-- Automaton `a0` (transformation monoid of its return automaton: 55 elements). -/
def a0 : List (List ℕ) := [[1, 2, 3], [0, 1, 0], [2, 3, 1], [3, 0, 2]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 20 elements). -/
def a1 : List (List ℕ) := [[1, 1, 2], [0, 2, 1], [2, 0, 0], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[1, 0, 1], [0, 1, 0], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 1], [0, 1, 3, 2]), ([2, 1, 0], [1, 2, 0, 3]), ([3, 2, 1], [2, 0, 3, 1]),
    ([1, 2, 1], [1, 3, 0, 2]), ([0, 1, 0], [3, 0, 2, 1]), ([2, 0, 1], [1, 2, 3, 0]),
    ([3, 2, 0], [2, 0, 1, 3]), ([0, 0, 1], [0, 3, 2, 1]), ([2, 0, 0], [3, 2, 1, 0]),
    ([0, 2, 0], [1, 3, 2, 0]), ([1, 0, 1], [3, 0, 1, 2]), ([2, 2, 0], [0, 2, 3, 1]),
    ([3, 1, 1], [2, 3, 1, 0]), ([1, 2, 0], [3, 1, 0, 2]), ([1, 1, 0], [0, 3, 1, 2]),
    ([2, 1, 1], [3, 2, 0, 1]), ([3, 1, 0], [2, 1, 3, 0]), ([3, 0, 1], [2, 1, 0, 3]),
    ([2, 2, 1], [0, 2, 1, 3]), ([3, 0, 0], [2, 3, 0, 1]), ([0, 2, 1], [3, 1, 2, 0]),
    ([1, 0, 0], [1, 0, 3, 2]), ([0, 1, 1], [1, 0, 2, 3])]

/-- **Every language recognized by a morphism with these letters has height at most one.** -/
theorem height_one (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : ∀ x i, T (FreeMonoid.of x) i = letT L x i) (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_tableOK L [a0, a1, a2] R (by decide +kernel) ?_ T hT F
  intro t ht q
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact good_baseN _ 0 _ a0_cert q
  · exact good_baseN _ 0 _ a1_cert q
  · exact good_baseN _ 0 _ a2_cert q

end K25

/-! ### `K26`: letters `0132 1203 3012` -/

namespace K26

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 1, 3, 2], [1, 2, 0, 3], [3, 0, 1, 2]]

/-- Automaton `a0` (transformation monoid of its return automaton: 55 elements). -/
def a0 : List (List ℕ) := [[1, 2, 1], [0, 1, 3], [2, 3, 0], [3, 0, 2]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 20 elements). -/
def a1 : List (List ℕ) := [[1, 2, 2], [0, 0, 1], [2, 1, 0], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[1, 0, 1], [0, 1, 0], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 1], [0, 1, 3, 2]), ([2, 2, 0], [1, 2, 0, 3]), ([1, 2, 1], [3, 0, 1, 2]),
    ([1, 0, 1], [1, 3, 0, 2]), ([3, 1, 0], [2, 0, 1, 3]), ([2, 2, 1], [1, 2, 3, 0]),
    ([0, 0, 1], [3, 1, 2, 0]), ([0, 2, 0], [3, 0, 2, 1]), ([3, 0, 0], [2, 3, 0, 1]),
    ([0, 1, 0], [1, 3, 2, 0]), ([3, 2, 0], [2, 1, 3, 0]), ([3, 0, 1], [2, 0, 3, 1]),
    ([2, 1, 1], [3, 2, 0, 1]), ([3, 1, 1], [2, 3, 1, 0]), ([1, 1, 0], [3, 1, 0, 2]),
    ([1, 2, 0], [0, 3, 1, 2]), ([2, 1, 0], [0, 2, 3, 1]), ([2, 0, 0], [3, 2, 1, 0]),
    ([3, 2, 1], [2, 1, 0, 3]), ([2, 0, 1], [0, 2, 1, 3]), ([0, 2, 1], [0, 3, 2, 1]),
    ([1, 0, 0], [1, 0, 3, 2]), ([0, 1, 1], [1, 0, 2, 3])]

/-- **Every language recognized by a morphism with these letters has height at most one.** -/
theorem height_one (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : ∀ x i, T (FreeMonoid.of x) i = letT L x i) (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_tableOK L [a0, a1, a2] R (by decide +kernel) ?_ T hT F
  intro t ht q
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact good_baseN _ 0 _ a0_cert q
  · exact good_baseN _ 0 _ a1_cert q
  · exact good_baseN _ 0 _ a2_cert q

end K26

/-! ### `K27`: letters `0132 1203 3201` -/

namespace K27

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 1, 3, 2], [1, 2, 0, 3], [3, 2, 0, 1]]

/-- Automaton `a0` (transformation monoid of its return automaton: 36 elements). -/
def a0 : List (List ℕ) := [[1, 2, 2], [0, 1, 3], [2, 3, 1], [3, 0, 0]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 14 elements). -/
def a1 : List (List ℕ) := [[1, 2, 1], [0, 0, 0], [2, 1, 2], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[1, 0, 1], [0, 1, 0], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 1], [0, 1, 3, 2]), ([2, 2, 0], [1, 2, 0, 3]), ([2, 1, 1], [3, 2, 0, 1]),
    ([1, 0, 1], [1, 3, 0, 2]), ([3, 0, 0], [2, 3, 0, 1]), ([2, 2, 1], [1, 2, 3, 0]),
    ([3, 1, 0], [2, 0, 1, 3]), ([1, 2, 1], [3, 0, 1, 2]), ([2, 0, 0], [3, 2, 1, 0]),
    ([3, 0, 1], [2, 0, 3, 1]), ([1, 0, 0], [1, 0, 3, 2]), ([0, 1, 0], [1, 3, 2, 0]),
    ([3, 1, 1], [2, 3, 1, 0]), ([0, 2, 0], [3, 0, 2, 1]), ([0, 1, 1], [1, 0, 2, 3]),
    ([1, 2, 0], [0, 3, 1, 2]), ([0, 0, 1], [3, 1, 2, 0]), ([3, 2, 0], [2, 1, 3, 0]),
    ([0, 2, 1], [0, 3, 2, 1]), ([2, 0, 1], [0, 2, 1, 3]), ([2, 1, 0], [0, 2, 3, 1]),
    ([1, 1, 0], [3, 1, 0, 2]), ([3, 2, 1], [2, 1, 0, 3])]

/-- **Every language recognized by a morphism with these letters has height at most one.** -/
theorem height_one (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : ∀ x i, T (FreeMonoid.of x) i = letT L x i) (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_tableOK L [a0, a1, a2] R (by decide +kernel) ?_ T hT F
  intro t ht q
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact good_baseN _ 0 _ a0_cert q
  · exact good_baseN _ 0 _ a1_cert q
  · exact good_baseN _ 0 _ a2_cert q

end K27
end S4Three

end GeneralizedStarHeight
