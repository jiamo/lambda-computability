import Start.StarHeightIndexThreeAll
import Start.GroupOrderLtTwenty

/-!
# Generalized star height one for every group of order less than `20`

Every finite group of order less than `20` has an abelian normal subgroup `N` of index at most `3`
(`exists_abelian_normal_index_le_three`).  By the index of `N`:
* index `1`: `G` is abelian, `height_one_of_comm`;
* index `2`: `height_one_of_abelian_index_two`;
* index `3`: `height_one_of_abelian_index_three`.
-/

namespace GeneralizedStarHeight

universe u

variable {Alphabet : Type u}

/-- **Every language recognized by a finite group of order less than `20` has generalized star
height at most one.** -/
theorem height_one_of_card_lt_twenty [Finite Alphabet] {G : Type} [Group G] [Fintype G]
    (hG : Fintype.card G < 20) (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  obtain ⟨N, hN, hab, hidx⟩ := exists_abelian_normal_index_le_three hG
  have h0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show N.index = 1 ∨ N.index = 2 ∨ N.index = 3 by omega) with h1 | h2 | h3
  · rw [Subgroup.index_eq_one] at h1
    subst h1
    exact height_one_of_comm (fun x y => hab x trivial y trivial) T F
  · exact height_one_of_abelian_index_two N hab h2 T F
  · exact height_one_of_abelian_index_three N hab h3 T F

end GeneralizedStarHeight
