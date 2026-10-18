import Start.StarHeightS4ThreeTable

/-!
# Certificates for classes of letter triples of `S₄` (part E)

Classes of triples of letters of `S₄` (no double transposition, distinct letters, generating `S₄`)
for which the good coset automata of `S₄` separate `S₄` (`D = 1`).  Letters are written in Lean's
convention: the table `p0 p1 p2 p3` of a letter lists its images of `0, 1, 2, 3`.

For each class `Knn`: the letters `Knn.L`; two or three coset automata of `S₄` on at most four
states (embedded in `Fin 4`; unused states are fixed by every letter), with base state `0`; for
each, the certificate that its return automaton has an aperiodic transformation monoid
(`decide +kernel`); the list `Knn.R` of the `24` reachable joint states with the value of the
morphism; and `Knn.height_one`, an instance of `height_one_of_tableOK`.

* `K37`: `0231 1230 1320` (automata on 4, 3, 2 states)
* `K38`: `0231 1230 2013` (automata on 4, 3, 2 states)
* `K39`: `0231 1230 2031` (automata on 4, 3, 2 states)
* `K40`: `0231 1230 2310` (automata on 4, 3, 2 states)
* `K41`: `0231 1230 3012` (automata on 4, 3, 2 states)
* `K42`: `0231 1230 3102` (automata on 4, 3, 2 states)
* `K43`: `0231 1302 2013` (automata on 4, 3, 2 states)
* `K44`: `1230 1302 2031` (automata on 4, 3, 2 states)
* `K45`: `1230 1302 2310` (automata on 4, 4, 2 states)
-/

-- The certificates below are checked one at a time, which keeps the peak memory low.
set_option Elab.async false

namespace GeneralizedStarHeight

namespace S4Three

open S4Two

/-! ### `K37`: letters `0231 1230 1320` -/

namespace K37

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 2, 3, 1], [1, 2, 3, 0], [1, 3, 2, 0]]

/-- Automaton `a0` (transformation monoid of its return automaton: 40 elements). -/
def a0 : List (List ℕ) := [[1, 2, 2], [3, 3, 0], [2, 1, 1], [0, 0, 3]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 14 elements). -/
def a1 : List (List ℕ) := [[1, 1, 1], [2, 0, 2], [0, 2, 0], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[0, 1, 0], [1, 0, 1], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 0], [0, 2, 3, 1]), ([2, 1, 1], [1, 2, 3, 0]), ([2, 1, 0], [1, 3, 2, 0]),
    ([3, 2, 0], [0, 3, 1, 2]), ([3, 0, 1], [2, 3, 1, 0]), ([0, 2, 0], [2, 1, 3, 0]),
    ([2, 2, 1], [1, 3, 0, 2]), ([1, 0, 0], [2, 3, 0, 1]), ([1, 2, 1], [2, 0, 3, 1]),
    ([2, 2, 0], [1, 2, 0, 3]), ([1, 0, 1], [3, 2, 0, 1]), ([1, 2, 0], [3, 0, 2, 1]),
    ([0, 2, 1], [3, 1, 2, 0]), ([3, 0, 0], [3, 2, 1, 0]), ([0, 1, 1], [2, 1, 0, 3]),
    ([0, 1, 0], [3, 1, 0, 2]), ([3, 1, 1], [3, 0, 1, 2]), ([2, 0, 0], [1, 0, 3, 2]),
    ([2, 0, 1], [1, 0, 2, 3]), ([3, 1, 0], [2, 0, 1, 3]), ([0, 0, 1], [0, 1, 3, 2]),
    ([3, 2, 1], [0, 2, 1, 3]), ([1, 1, 1], [0, 3, 2, 1])]

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

end K37

/-! ### `K38`: letters `0231 1230 2013` -/

namespace K38

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 2, 3, 1], [1, 2, 3, 0], [2, 0, 1, 3]]

/-- Automaton `a0` (transformation monoid of its return automaton: 47 elements). -/
def a0 : List (List ℕ) := [[1, 1, 2], [3, 2, 0], [2, 3, 1], [0, 0, 3]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 14 elements). -/
def a1 : List (List ℕ) := [[1, 1, 1], [2, 0, 2], [0, 2, 0], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[0, 1, 0], [1, 0, 1], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 0], [0, 2, 3, 1]), ([1, 1, 1], [1, 2, 3, 0]), ([2, 1, 0], [2, 0, 1, 3]),
    ([3, 2, 0], [0, 3, 1, 2]), ([2, 0, 1], [2, 3, 1, 0]), ([0, 2, 0], [3, 0, 2, 1]),
    ([3, 2, 1], [1, 3, 0, 2]), ([2, 0, 0], [2, 3, 0, 1]), ([0, 2, 1], [3, 1, 2, 0]),
    ([2, 2, 0], [2, 1, 3, 0]), ([3, 0, 1], [0, 1, 3, 2]), ([1, 2, 0], [1, 2, 0, 3]),
    ([3, 0, 0], [1, 0, 3, 2]), ([2, 1, 1], [2, 1, 0, 3]), ([3, 1, 0], [3, 1, 0, 2]),
    ([1, 0, 0], [3, 2, 1, 0]), ([1, 2, 1], [0, 2, 1, 3]), ([0, 0, 1], [1, 0, 2, 3]),
    ([3, 1, 1], [3, 0, 1, 2]), ([1, 0, 1], [3, 2, 0, 1]), ([0, 1, 1], [0, 3, 2, 1]),
    ([0, 1, 0], [1, 3, 2, 0]), ([2, 2, 1], [2, 0, 3, 1])]

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

end K38

/-! ### `K39`: letters `0231 1230 2031` -/

namespace K39

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 2, 3, 1], [1, 2, 3, 0], [2, 0, 3, 1]]

/-- Automaton `a0` (transformation monoid of its return automaton: 36 elements). -/
def a0 : List (List ℕ) := [[1, 1, 1], [2, 2, 3], [0, 3, 0], [3, 0, 2]]

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
    ([1, 1, 0], [0, 2, 3, 1]), ([1, 1, 1], [1, 2, 3, 0]), ([1, 2, 1], [2, 0, 3, 1]),
    ([2, 2, 0], [0, 3, 1, 2]), ([2, 0, 1], [2, 3, 1, 0]), ([3, 1, 1], [3, 0, 1, 2]),
    ([2, 2, 1], [1, 3, 0, 2]), ([2, 0, 0], [2, 3, 0, 1]), ([3, 1, 0], [3, 1, 0, 2]),
    ([3, 0, 0], [3, 2, 1, 0]), ([3, 2, 1], [3, 1, 2, 0]), ([0, 0, 1], [1, 0, 2, 3]),
    ([0, 1, 1], [2, 1, 0, 3]), ([0, 2, 0], [1, 2, 0, 3]), ([2, 1, 0], [1, 3, 2, 0]),
    ([3, 2, 0], [3, 0, 2, 1]), ([0, 1, 0], [2, 0, 1, 3]), ([0, 2, 1], [0, 2, 1, 3]),
    ([2, 1, 1], [0, 3, 2, 1]), ([3, 0, 1], [3, 2, 0, 1]), ([1, 2, 0], [2, 1, 3, 0]),
    ([1, 0, 0], [1, 0, 3, 2]), ([1, 0, 1], [0, 1, 3, 2])]

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

end K39

/-! ### `K40`: letters `0231 1230 2310` -/

namespace K40

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 2, 3, 1], [1, 2, 3, 0], [2, 3, 1, 0]]

/-- Automaton `a0` (transformation monoid of its return automaton: 46 elements). -/
def a0 : List (List ℕ) := [[1, 1, 2], [2, 2, 3], [0, 3, 1], [3, 0, 0]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 20 elements). -/
def a1 : List (List ℕ) := [[1, 2, 1], [2, 1, 0], [0, 0, 2], [3, 3, 3]]

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
    ([1, 1, 0], [0, 2, 3, 1]), ([1, 2, 1], [1, 2, 3, 0]), ([2, 1, 1], [2, 3, 1, 0]),
    ([2, 2, 0], [0, 3, 1, 2]), ([3, 0, 1], [3, 1, 2, 0]), ([2, 0, 1], [1, 3, 0, 2]),
    ([2, 0, 0], [2, 3, 0, 1]), ([3, 2, 0], [3, 0, 2, 1]), ([0, 2, 1], [2, 1, 0, 3]),
    ([3, 1, 0], [3, 1, 0, 2]), ([1, 0, 0], [1, 0, 3, 2]), ([3, 1, 1], [3, 2, 0, 1]),
    ([0, 2, 0], [1, 2, 0, 3]), ([0, 1, 0], [2, 0, 1, 3]), ([0, 1, 1], [1, 0, 2, 3]),
    ([3, 2, 1], [3, 0, 1, 2]), ([1, 1, 1], [0, 1, 3, 2]), ([3, 0, 0], [3, 2, 1, 0]),
    ([0, 0, 1], [0, 2, 1, 3]), ([1, 0, 1], [2, 0, 3, 1]), ([2, 1, 0], [1, 3, 2, 0]),
    ([2, 2, 1], [0, 3, 2, 1]), ([1, 2, 0], [2, 1, 3, 0])]

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

end K40

/-! ### `K41`: letters `0231 1230 3012` -/

namespace K41

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 2, 3, 1], [1, 2, 3, 0], [3, 0, 1, 2]]

/-- Automaton `a0` (transformation monoid of its return automaton: 74 elements). -/
def a0 : List (List ℕ) := [[1, 2, 3], [3, 3, 2], [2, 1, 0], [0, 0, 1]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 14 elements). -/
def a1 : List (List ℕ) := [[1, 1, 1], [2, 0, 0], [0, 2, 2], [3, 3, 3]]

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
    ([1, 1, 0], [0, 2, 3, 1]), ([2, 1, 1], [1, 2, 3, 0]), ([3, 1, 1], [3, 0, 1, 2]),
    ([3, 2, 0], [0, 3, 1, 2]), ([3, 0, 1], [2, 3, 1, 0]), ([2, 0, 1], [1, 0, 2, 3]),
    ([2, 2, 1], [1, 3, 0, 2]), ([1, 0, 0], [2, 3, 0, 1]), ([0, 2, 1], [3, 1, 2, 0]),
    ([1, 2, 1], [2, 0, 3, 1]), ([0, 1, 1], [2, 1, 0, 3]), ([0, 1, 0], [3, 1, 0, 2]),
    ([1, 2, 0], [3, 0, 2, 1]), ([0, 2, 0], [2, 1, 3, 0]), ([3, 1, 0], [2, 0, 1, 3]),
    ([1, 0, 1], [3, 2, 0, 1]), ([2, 2, 0], [1, 2, 0, 3]), ([2, 0, 0], [1, 0, 3, 2]),
    ([3, 0, 0], [3, 2, 1, 0]), ([3, 2, 1], [0, 2, 1, 3]), ([0, 0, 1], [0, 1, 3, 2]),
    ([2, 1, 0], [1, 3, 2, 0]), ([1, 1, 1], [0, 3, 2, 1])]

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

end K41

/-! ### `K42`: letters `0231 1230 3102` -/

namespace K42

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 2, 3, 1], [1, 2, 3, 0], [3, 1, 0, 2]]

/-- Automaton `a0` (transformation monoid of its return automaton: 47 elements). -/
def a0 : List (List ℕ) := [[1, 1, 2], [2, 3, 1], [0, 0, 3], [3, 2, 0]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 14 elements). -/
def a1 : List (List ℕ) := [[1, 1, 1], [2, 0, 2], [0, 2, 0], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[0, 1, 0], [1, 0, 1], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 0], [0, 2, 3, 1]), ([1, 1, 1], [1, 2, 3, 0]), ([2, 1, 0], [3, 1, 0, 2]),
    ([2, 2, 0], [0, 3, 1, 2]), ([3, 0, 1], [2, 3, 1, 0]), ([1, 2, 0], [1, 2, 0, 3]),
    ([2, 2, 1], [1, 3, 0, 2]), ([3, 0, 0], [2, 3, 0, 1]), ([1, 2, 1], [0, 2, 1, 3]),
    ([0, 2, 0], [3, 0, 2, 1]), ([0, 0, 1], [1, 0, 2, 3]), ([3, 2, 0], [2, 1, 3, 0]),
    ([0, 2, 1], [3, 1, 2, 0]), ([3, 1, 1], [2, 1, 0, 3]), ([0, 1, 1], [0, 3, 2, 1]),
    ([2, 0, 0], [1, 0, 3, 2]), ([3, 2, 1], [2, 0, 3, 1]), ([1, 0, 0], [3, 2, 1, 0]),
    ([3, 1, 0], [2, 0, 1, 3]), ([2, 1, 1], [3, 0, 1, 2]), ([0, 1, 0], [1, 3, 2, 0]),
    ([2, 0, 1], [0, 1, 3, 2]), ([1, 0, 1], [3, 2, 0, 1])]

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

end K42

/-! ### `K43`: letters `0231 1302 2013` -/

namespace K43

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[0, 2, 3, 1], [1, 3, 0, 2], [2, 0, 1, 3]]

/-- Automaton `a0` (transformation monoid of its return automaton: 93 elements). -/
def a0 : List (List ℕ) := [[1, 2, 3], [3, 0, 1], [2, 3, 0], [0, 1, 2]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 14 elements). -/
def a1 : List (List ℕ) := [[1, 2, 1], [2, 1, 2], [0, 0, 0], [3, 3, 3]]

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a1) 0) 400) 4 = true := by
  decide +kernel

/-- Automaton `a2` (transformation monoid of its return automaton: 8 elements). -/
def a2 : List (List ℕ) := [[0, 1, 0], [1, 0, 1], [2, 2, 2], [3, 3, 3]]

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a2) 0) 400) 3 = true := by
  decide +kernel

/-- The joint states with the tables of the value. -/
def R : List (List (Fin 4) × List (Fin 4)) := [([0, 0, 0], [0, 1, 2, 3]),
    ([1, 1, 0], [0, 2, 3, 1]), ([2, 2, 1], [1, 3, 0, 2]), ([3, 1, 0], [2, 0, 1, 3]),
    ([3, 2, 0], [0, 3, 1, 2]), ([0, 1, 1], [2, 1, 0, 3]), ([1, 2, 0], [3, 0, 2, 1]),
    ([2, 0, 1], [1, 0, 2, 3]), ([3, 0, 0], [3, 2, 1, 0]), ([0, 0, 1], [0, 1, 3, 2]),
    ([0, 2, 0], [2, 1, 3, 0]), ([1, 1, 1], [0, 3, 2, 1]), ([2, 2, 0], [1, 2, 0, 3]),
    ([1, 0, 1], [3, 2, 0, 1]), ([2, 0, 0], [1, 0, 3, 2]), ([1, 2, 1], [2, 0, 3, 1]),
    ([2, 1, 0], [1, 3, 2, 0]), ([3, 2, 1], [0, 2, 1, 3]), ([1, 0, 0], [2, 3, 0, 1]),
    ([2, 1, 1], [1, 2, 3, 0]), ([0, 1, 0], [3, 1, 0, 2]), ([3, 1, 1], [3, 0, 1, 2]),
    ([3, 0, 1], [2, 3, 1, 0]), ([0, 2, 1], [3, 1, 2, 0])]

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

end K43

/-! ### `K44`: letters `1230 1302 2031` -/

namespace K44

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[1, 2, 3, 0], [1, 3, 0, 2], [2, 0, 3, 1]]

/-- Automaton `a0` (transformation monoid of its return automaton: 75 elements). -/
def a0 : List (List ℕ) := [[1, 2, 3], [2, 3, 2], [3, 1, 0], [0, 0, 1]]

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
    ([1, 1, 1], [1, 2, 3, 0]), ([2, 2, 1], [1, 3, 0, 2]), ([3, 2, 1], [2, 0, 3, 1]),
    ([2, 0, 0], [2, 3, 0, 1]), ([3, 1, 0], [2, 0, 1, 3]), ([2, 1, 0], [3, 1, 0, 2]),
    ([3, 2, 0], [3, 0, 2, 1]), ([1, 0, 0], [3, 2, 1, 0]), ([0, 2, 0], [0, 3, 1, 2]),
    ([3, 1, 1], [3, 0, 1, 2]), ([1, 2, 1], [3, 1, 2, 0]), ([0, 2, 1], [0, 2, 1, 3]),
    ([0, 0, 1], [0, 1, 3, 2]), ([0, 1, 1], [0, 3, 2, 1]), ([3, 0, 1], [1, 0, 2, 3]),
    ([1, 0, 1], [2, 3, 1, 0]), ([2, 1, 1], [2, 1, 0, 3]), ([2, 0, 1], [3, 2, 0, 1]),
    ([0, 1, 0], [0, 2, 3, 1]), ([1, 1, 0], [1, 3, 2, 0]), ([2, 2, 0], [1, 2, 0, 3]),
    ([3, 0, 0], [1, 0, 3, 2]), ([1, 2, 0], [2, 1, 3, 0])]

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

end K44

/-! ### `K45`: letters `1230 1302 2310` -/

namespace K45

/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/
def L : List (List ℕ) := [[1, 2, 3, 0], [1, 3, 0, 2], [2, 3, 1, 0]]

/-- Automaton `a0` (transformation monoid of its return automaton: 49 elements). -/
def a0 : List (List ℕ) := [[1, 2, 1], [2, 3, 3], [3, 1, 0], [0, 0, 2]]

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a0) 0) 400) 5 = true := by
  decide +kernel

/-- Automaton `a1` (transformation monoid of its return automaton: 49 elements). -/
def a1 : List (List ℕ) := [[1, 1, 2], [3, 2, 3], [0, 3, 1], [2, 0, 0]]

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
    ([1, 1, 1], [1, 2, 3, 0]), ([2, 1, 1], [1, 3, 0, 2]), ([1, 2, 1], [2, 3, 1, 0]),
    ([2, 3, 0], [2, 3, 0, 1]), ([3, 2, 0], [2, 0, 1, 3]), ([3, 3, 0], [3, 0, 2, 1]),
    ([1, 2, 0], [3, 2, 1, 0]), ([0, 3, 0], [0, 2, 3, 1]), ([2, 0, 0], [3, 1, 0, 2]),
    ([3, 1, 0], [1, 0, 3, 2]), ([3, 2, 1], [3, 0, 1, 2]), ([1, 0, 1], [3, 1, 2, 0]),
    ([0, 0, 1], [0, 1, 3, 2]), ([0, 3, 1], [0, 3, 2, 1]), ([0, 2, 1], [0, 2, 1, 3]),
    ([2, 0, 1], [2, 1, 0, 3]), ([3, 3, 1], [2, 0, 3, 1]), ([3, 1, 1], [1, 0, 2, 3]),
    ([2, 3, 1], [3, 2, 0, 1]), ([2, 1, 0], [1, 2, 0, 3]), ([1, 1, 0], [1, 3, 2, 0]),
    ([1, 0, 0], [2, 1, 3, 0]), ([0, 2, 0], [0, 3, 1, 2])]

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

end K45
end S4Three

end GeneralizedStarHeight
