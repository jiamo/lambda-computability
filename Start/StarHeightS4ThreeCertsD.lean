import Start.StarHeightS4ThreeTable

/-!
# Certificates for classes of letter triples of `S₄` (part D)

Classes of triples of letters of `S₄` (no double transposition, distinct letters, generating `S₄`)
for which the good coset automata of `S₄` separate `S₄` (`D = 1`).  Letters are written in Lean's
convention: the table `p0 p1 p2 p3` of a letter lists its images of `0, 1, 2, 3`.

For each class `Knn`: the letters `Knn.L`; two or three coset automata of `S₄` on at most four
states (embedded in `Fin 4`; unused states are fixed by every letter), with base state `0`; for
each, the certificate that its return automaton has an aperiodic transformation monoid
(`decide +kernel`); the list `Knn.R` of the `24` reachable joint states with the value of the
morphism; and `Knn.height_one`, an instance of `height_one_of_tableOK`.

* `K28`: `0132 1230 1302` (automata on 4, 4, 2 states)
* `K29`: `0132 1230 2031` (automata on 4, 4, 2 states)
* `K30`: `0132 1230 2310` (automata on 4, 3, 2 states)
* `K31`: `0132 1230 3012` (automata on 4, 3, 2 states)
* `K32`: `0132 1230 3201` (automata on 4, 3, 2 states)
* `K33`: `0231 0312 1230` (automata on 4, 3, 2 states)
* `K34`: `0231 1203 1230` (automata on 4, 3, 2 states)
* `K35`: `0231 1203 1302` (automata on 4, 3, 2 states)
* `K36`: `0231 1230 1302` (automata on 4, 3, 2 states)
-/

-- The certificates below are checked one at a time, which keeps the peak memory low.
set_option Elab.async false

namespace GeneralizedStarHeight

namespace S4Three

open S4Two

/-! ### `K28`: letters `0132 1230 1302` -/

namespace K28

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 1, 3, 2], [1, 2, 3, 0], [1, 3, 0, 2]]

/-- Automaton `a0` (transformation monoid of its return automaton: 54 elements). -/
def a0 : List (List ℕ) := [[1, 1, 2], [0, 2, 0], [2, 3, 3], [3, 0, 1]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 54 elements). -/
def a1 : List (List ℕ) := [[1, 2, 1], [0, 0, 2], [2, 3, 3], [3, 1, 0]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 4 elements). -/
def a2 : List (List ℕ) := [[1, 1, 1], [0, 0, 0], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 1], [0, 1, 3, 2]), ([1, 2, 1], [1, 2, 3, 0]), ([2, 1, 1], [1, 3, 0, 2]),
    ([2, 0, 0], [1, 3, 2, 0]), ([0, 2, 0], [1, 2, 0, 3]), ([2, 3, 0], [2, 3, 0, 1]),
    ([0, 3, 0], [2, 0, 1, 3]), ([3, 0, 0], [3, 0, 2, 1]), ([3, 2, 0], [3, 2, 1, 0]),
    ([3, 2, 1], [3, 2, 0, 1]), ([3, 1, 1], [3, 0, 1, 2]), ([1, 3, 1], [2, 0, 3, 1]),
    ([2, 3, 1], [2, 3, 1, 0]), ([3, 0, 1], [3, 1, 2, 0]), ([2, 0, 1], [0, 3, 2, 1]),
    ([0, 2, 1], [0, 2, 1, 3]), ([0, 3, 1], [2, 1, 0, 3]), ([1, 3, 0], [2, 1, 3, 0]),
    ([1, 2, 0], [0, 2, 3, 1]), ([2, 1, 0], [0, 3, 1, 2]), ([3, 1, 0], [3, 1, 0, 2]),
    ([1, 1, 0], [1, 0, 3, 2]), ([0, 0, 1], [1, 0, 2, 3])]

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

end K28

/-! ### `K29`: letters `0132 1230 2031` -/

namespace K29

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 1, 3, 2], [1, 2, 3, 0], [2, 0, 3, 1]]

/-- Automaton `a0` (transformation monoid of its return automaton: 53 elements). -/
def a0 : List (List ℕ) := [[1, 1, 1], [0, 2, 3], [2, 3, 0], [3, 0, 2]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 53 elements). -/
def a1 : List (List ℕ) := [[1, 2, 3], [0, 0, 0], [2, 3, 1], [3, 1, 2]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 4 elements). -/
def a2 : List (List ℕ) := [[1, 1, 1], [0, 0, 0], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 1], [0, 1, 3, 2]), ([1, 2, 1], [1, 2, 3, 0]), ([1, 3, 1], [2, 0, 3, 1]),
    ([2, 0, 0], [1, 3, 2, 0]), ([3, 0, 0], [3, 0, 2, 1]), ([0, 2, 0], [1, 2, 0, 3]),
    ([2, 3, 0], [2, 3, 0, 1]), ([3, 1, 0], [3, 1, 0, 2]), ([0, 3, 0], [2, 0, 1, 3]),
    ([2, 1, 0], [0, 3, 1, 2]), ([3, 2, 0], [3, 2, 1, 0]), ([2, 1, 1], [1, 3, 0, 2]),
    ([3, 2, 1], [3, 2, 0, 1]), ([0, 3, 1], [2, 1, 0, 3]), ([3, 1, 1], [3, 0, 1, 2]),
    ([0, 2, 1], [0, 2, 1, 3]), ([2, 3, 1], [2, 3, 1, 0]), ([3, 0, 1], [3, 1, 2, 0]),
    ([0, 0, 1], [1, 0, 2, 3]), ([2, 0, 1], [0, 3, 2, 1]), ([1, 3, 0], [2, 1, 3, 0]),
    ([1, 1, 0], [1, 0, 3, 2]), ([1, 2, 0], [0, 2, 3, 1])]

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

end K29

/-! ### `K30`: letters `0132 1230 2310` -/

namespace K30

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 1, 3, 2], [1, 2, 3, 0], [2, 3, 1, 0]]

/-- Automaton `a0` (transformation monoid of its return automaton: 44 elements). -/
def a0 : List (List ℕ) := [[1, 1, 2], [0, 2, 3], [2, 3, 1], [3, 0, 0]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 15 elements). -/
def a1 : List (List ℕ) := [[1, 2, 1], [0, 1, 0], [2, 0, 2], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 3 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 4 elements). -/
def a2 : List (List ℕ) := [[1, 1, 1], [0, 0, 0], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 1], [0, 1, 3, 2]), ([1, 2, 1], [1, 2, 3, 0]), ([2, 1, 1], [2, 3, 1, 0]),
    ([2, 1, 0], [1, 3, 2, 0]), ([3, 0, 0], [3, 2, 1, 0]), ([0, 2, 0], [1, 2, 0, 3]),
    ([2, 0, 0], [2, 3, 0, 1]), ([3, 2, 0], [3, 0, 2, 1]), ([3, 1, 0], [3, 1, 0, 2]),
    ([1, 0, 0], [1, 0, 3, 2]), ([2, 0, 1], [1, 3, 0, 2]), ([3, 1, 1], [3, 2, 0, 1]),
    ([1, 0, 1], [2, 0, 3, 1]), ([0, 2, 1], [2, 1, 0, 3]), ([0, 1, 1], [1, 0, 2, 3]),
    ([2, 2, 1], [0, 3, 2, 1]), ([3, 2, 1], [3, 0, 1, 2]), ([0, 0, 1], [0, 2, 1, 3]),
    ([3, 0, 1], [3, 1, 2, 0]), ([1, 1, 0], [0, 2, 3, 1]), ([0, 1, 0], [2, 0, 1, 3]),
    ([2, 2, 0], [0, 3, 1, 2]), ([1, 2, 0], [2, 1, 3, 0])]

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

end K30

/-! ### `K31`: letters `0132 1230 3012` -/

namespace K31

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 1, 3, 2], [1, 2, 3, 0], [3, 0, 1, 2]]

/-- Automaton `a0` (transformation monoid of its return automaton: 54 elements). -/
def a0 : List (List ℕ) := [[1, 1, 2], [0, 3, 0], [2, 0, 3], [3, 2, 1]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 15 elements). -/
def a1 : List (List ℕ) := [[1, 2, 2], [0, 1, 1], [2, 0, 0], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 3 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 4 elements). -/
def a2 : List (List ℕ) := [[1, 1, 1], [0, 0, 0], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 1], [0, 1, 3, 2]), ([1, 2, 1], [1, 2, 3, 0]), ([2, 2, 1], [3, 0, 1, 2]),
    ([3, 1, 0], [1, 3, 2, 0]), ([0, 1, 0], [2, 0, 1, 3]), ([0, 2, 0], [1, 2, 0, 3]),
    ([3, 0, 0], [2, 3, 0, 1]), ([2, 2, 0], [3, 0, 2, 1]), ([3, 0, 1], [1, 3, 0, 2]),
    ([2, 1, 1], [3, 2, 0, 1]), ([1, 0, 1], [2, 0, 3, 1]), ([2, 0, 1], [3, 1, 2, 0]),
    ([3, 1, 1], [2, 3, 1, 0]), ([0, 0, 1], [0, 2, 1, 3]), ([1, 2, 0], [2, 1, 3, 0]),
    ([2, 0, 0], [3, 2, 1, 0]), ([3, 2, 0], [0, 3, 1, 2]), ([2, 1, 0], [3, 1, 0, 2]),
    ([1, 1, 0], [0, 2, 3, 1]), ([0, 2, 1], [2, 1, 0, 3]), ([3, 2, 1], [0, 3, 2, 1]),
    ([0, 1, 1], [1, 0, 2, 3]), ([1, 0, 0], [1, 0, 3, 2])]

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

end K31

/-! ### `K32`: letters `0132 1230 3201` -/

namespace K32

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 1, 3, 2], [1, 2, 3, 0], [3, 2, 0, 1]]

/-- Automaton `a0` (transformation monoid of its return automaton: 44 elements). -/
def a0 : List (List ℕ) := [[1, 2, 2], [0, 0, 3], [2, 3, 1], [3, 1, 0]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 15 elements). -/
def a1 : List (List ℕ) := [[1, 2, 1], [0, 1, 0], [2, 0, 2], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 3 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 4 elements). -/
def a2 : List (List ℕ) := [[1, 1, 1], [0, 0, 0], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 1], [0, 1, 3, 2]), ([2, 2, 1], [1, 2, 3, 0]), ([2, 1, 1], [3, 2, 0, 1]),
    ([0, 1, 0], [1, 3, 2, 0]), ([3, 0, 0], [2, 3, 0, 1]), ([2, 2, 0], [1, 2, 0, 3]),
    ([1, 2, 0], [0, 3, 1, 2]), ([2, 0, 0], [3, 2, 1, 0]), ([3, 1, 0], [2, 0, 1, 3]),
    ([1, 0, 0], [1, 0, 3, 2]), ([1, 0, 1], [1, 3, 0, 2]), ([2, 0, 1], [0, 2, 1, 3]),
    ([3, 1, 1], [2, 3, 1, 0]), ([1, 2, 1], [3, 0, 1, 2]), ([0, 1, 1], [1, 0, 2, 3]),
    ([3, 0, 1], [2, 0, 3, 1]), ([0, 2, 1], [0, 3, 2, 1]), ([0, 0, 1], [3, 1, 2, 0]),
    ([3, 2, 1], [2, 1, 0, 3]), ([0, 2, 0], [3, 0, 2, 1]), ([2, 1, 0], [0, 2, 3, 1]),
    ([3, 2, 0], [2, 1, 3, 0]), ([1, 1, 0], [3, 1, 0, 2])]

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

end K32

/-! ### `K33`: letters `0231 0312 1230` -/

namespace K33

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 2, 3, 1], [0, 3, 1, 2], [1, 2, 3, 0]]

/-- Automaton `a0` (transformation monoid of its return automaton: 61 elements). -/
def a0 : List (List ℕ) := [[1, 2, 3], [2, 0, 2], [0, 1, 0], [3, 3, 1]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 21 elements). -/
def a1 : List (List ℕ) := [[1, 2, 1], [2, 0, 0], [0, 1, 2], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[0, 0, 1], [1, 1, 0], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 0], [0, 2, 3, 1]), ([2, 2, 0], [0, 3, 1, 2]), ([3, 1, 1], [1, 2, 3, 0]),
    ([2, 0, 1], [2, 3, 1, 0]), ([0, 2, 1], [3, 1, 2, 0]), ([3, 2, 1], [1, 3, 0, 2]),
    ([3, 0, 1], [1, 0, 2, 3]), ([1, 0, 0], [2, 3, 0, 1]), ([0, 1, 1], [2, 1, 0, 3]),
    ([1, 2, 1], [2, 0, 3, 1]), ([0, 1, 0], [3, 1, 0, 2]), ([1, 0, 1], [3, 2, 0, 1]),
    ([2, 1, 1], [3, 0, 1, 2]), ([3, 2, 0], [1, 2, 0, 3]), ([1, 2, 0], [3, 0, 2, 1]),
    ([2, 1, 0], [2, 0, 1, 3]), ([0, 2, 0], [2, 1, 3, 0]), ([3, 0, 0], [1, 0, 3, 2]),
    ([2, 0, 0], [3, 2, 1, 0]), ([3, 1, 0], [1, 3, 2, 0]), ([2, 2, 1], [0, 2, 1, 3]),
    ([0, 0, 1], [0, 1, 3, 2]), ([1, 1, 1], [0, 3, 2, 1])]

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

end K33

/-! ### `K34`: letters `0231 1203 1230` -/

namespace K34

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 2, 3, 1], [1, 2, 0, 3], [1, 2, 3, 0]]

/-- Automaton `a0` (transformation monoid of its return automaton: 34 elements). -/
def a0 : List (List ℕ) := [[1, 2, 2], [3, 1, 3], [2, 3, 1], [0, 0, 0]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 21 elements). -/
def a1 : List (List ℕ) := [[1, 2, 1], [2, 0, 0], [0, 1, 2], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[0, 0, 1], [1, 1, 0], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 0], [0, 2, 3, 1]), ([2, 2, 0], [1, 2, 0, 3]), ([2, 1, 1], [1, 2, 3, 0]),
    ([3, 2, 0], [0, 3, 1, 2]), ([1, 0, 0], [2, 3, 0, 1]), ([3, 0, 1], [2, 3, 1, 0]),
    ([2, 0, 0], [1, 0, 3, 2]), ([3, 1, 0], [2, 0, 1, 3]), ([1, 2, 1], [2, 0, 3, 1]),
    ([2, 2, 1], [1, 3, 0, 2]), ([0, 1, 0], [3, 1, 0, 2]), ([0, 2, 1], [3, 1, 2, 0]),
    ([1, 2, 0], [3, 0, 2, 1]), ([3, 1, 1], [3, 0, 1, 2]), ([0, 1, 1], [2, 1, 0, 3]),
    ([2, 1, 0], [1, 3, 2, 0]), ([1, 1, 1], [0, 3, 2, 1]), ([0, 2, 0], [2, 1, 3, 0]),
    ([0, 0, 1], [0, 1, 3, 2]), ([2, 0, 1], [1, 0, 2, 3]), ([1, 0, 1], [3, 2, 0, 1]),
    ([3, 0, 0], [3, 2, 1, 0]), ([3, 2, 1], [0, 2, 1, 3])]

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

end K34

/-! ### `K35`: letters `0231 1203 1302` -/

namespace K35

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 2, 3, 1], [1, 2, 0, 3], [1, 3, 0, 2]]

/-- Automaton `a0` (transformation monoid of its return automaton: 49 elements). -/
def a0 : List (List ℕ) := [[1, 2, 2], [3, 1, 0], [2, 3, 3], [0, 0, 1]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 21 elements). -/
def a1 : List (List ℕ) := [[1, 2, 2], [2, 0, 1], [0, 1, 0], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[0, 0, 1], [1, 1, 0], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 0], [0, 2, 3, 1]), ([2, 2, 0], [1, 2, 0, 3]), ([2, 2, 1], [1, 3, 0, 2]),
    ([3, 2, 0], [0, 3, 1, 2]), ([1, 0, 0], [2, 3, 0, 1]), ([0, 1, 1], [2, 1, 0, 3]),
    ([2, 0, 0], [1, 0, 3, 2]), ([3, 1, 0], [2, 0, 1, 3]), ([3, 0, 1], [2, 3, 1, 0]),
    ([2, 0, 1], [1, 0, 2, 3]), ([3, 1, 1], [3, 0, 1, 2]), ([3, 0, 0], [3, 2, 1, 0]),
    ([0, 1, 0], [3, 1, 0, 2]), ([1, 0, 1], [3, 2, 0, 1]), ([1, 2, 0], [3, 0, 2, 1]),
    ([0, 2, 1], [3, 1, 2, 0]), ([1, 2, 1], [2, 0, 3, 1]), ([2, 1, 0], [1, 3, 2, 0]),
    ([3, 2, 1], [0, 2, 1, 3]), ([0, 2, 0], [2, 1, 3, 0]), ([1, 1, 1], [0, 3, 2, 1]),
    ([2, 1, 1], [1, 2, 3, 0]), ([0, 0, 1], [0, 1, 3, 2])]

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

end K35

/-! ### `K36`: letters `0231 1230 1302` -/

namespace K36

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 2, 3, 1], [1, 2, 3, 0], [1, 3, 0, 2]]

/-- Automaton `a0` (transformation monoid of its return automaton: 46 elements). -/
def a0 : List (List ℕ) := [[1, 2, 2], [3, 3, 0], [2, 1, 3], [0, 0, 1]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 20 elements). -/
def a1 : List (List ℕ) := [[1, 1, 2], [2, 0, 1], [0, 2, 0], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[0, 1, 1], [1, 0, 0], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 0], [0, 2, 3, 1]), ([2, 1, 1], [1, 2, 3, 0]), ([2, 2, 1], [1, 3, 0, 2]),
    ([3, 2, 0], [0, 3, 1, 2]), ([3, 0, 1], [2, 3, 1, 0]), ([0, 1, 1], [2, 1, 0, 3]),
    ([1, 0, 0], [2, 3, 0, 1]), ([3, 1, 0], [2, 0, 1, 3]), ([2, 0, 1], [1, 0, 2, 3]),
    ([1, 2, 0], [3, 0, 2, 1]), ([3, 0, 0], [3, 2, 1, 0]), ([0, 2, 1], [3, 1, 2, 0]),
    ([1, 0, 1], [3, 2, 0, 1]), ([0, 1, 0], [3, 1, 0, 2]), ([1, 2, 1], [2, 0, 3, 1]),
    ([2, 0, 0], [1, 0, 3, 2]), ([2, 1, 0], [1, 3, 2, 0]), ([3, 1, 1], [3, 0, 1, 2]),
    ([0, 2, 0], [2, 1, 3, 0]), ([0, 0, 1], [0, 1, 3, 2]), ([1, 1, 1], [0, 3, 2, 1]),
    ([3, 2, 1], [0, 2, 1, 3]), ([2, 2, 0], [1, 2, 0, 3])]

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

end K36
end S4Three

end GeneralizedStarHeight
