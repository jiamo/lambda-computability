import Start.StarHeightIndexPrime

/-!
# Languages recognized by `S₃` have generalized star height at most two

Task `M28-STARHEIGHT-TWO-S3` (big round 2, run 4; rebuilt in run 7).

* `alternatingGroup_three_comm`: `A₃` is abelian.
* `height_one_of_S3`: every language recognized by `S₃ = Equiv.Perm (Fin 3)` has generalized star
  height at most one. It is `height_one_of_abelian_prime_index` with `N = alternatingGroup (Fin 3)`,
  an abelian normal subgroup of index `2`.
* `height_two_of_S3`: the terminal statement of the row (height at most two).

The result is not new: `S₃` has an abelian normal subgroup of prime index.
-/

namespace GeneralizedStarHeight

universe u

variable {Alphabet : Type u}

/-- `A₃` is abelian. -/
theorem alternatingGroup_three_comm :
    ∀ x ∈ alternatingGroup (Fin 3), ∀ y ∈ alternatingGroup (Fin 3), x * y = y * x := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide

/-- Every language recognized by `S₃` has generalized star height at most one. -/
theorem height_one_of_S3 [Finite Alphabet] (T : FreeMonoid Alphabet →* Equiv.Perm (Fin 3))
    (F : Set (Equiv.Perm (Fin 3))) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact height_one_of_abelian_prime_index (alternatingGroup (Fin 3)) alternatingGroup_three_comm
    (p := 2) (alternatingGroup.index_eq_two (α := Fin 3)) T F

/-- **`M28-STARHEIGHT-TWO-S3`**: every language recognized by `S₃` has generalized star height at
most two. -/
theorem height_two_of_S3 [Finite Alphabet] (T : FreeMonoid Alphabet →* Equiv.Perm (Fin 3))
    (F : Set (Equiv.Perm (Fin 3))) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 2 := by
  obtain ⟨P, hP, hh⟩ := height_one_of_S3 T F
  exact ⟨P, hP, by omega⟩

end GeneralizedStarHeight
