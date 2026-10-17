import Start.StarHeightIndexThreeAll
import Start.GroupOrderLtTwentyFour

/-!
# Generalized star height one for groups of order less than `24`, except `F₂₀`

`height_one_of_card_lt_twentyfour_of_centralizer`: every language recognized by a finite group of
order less than `24` has generalized star height at most one, provided that in order `20` the
centralizer of a Sylow `5`-subgroup has more than `5` elements.  This hypothesis replaces
`IsEmpty (G ≃* F20)`: the groups of order `20` it excludes act faithfully on their Sylow
`5`-subgroup, which characterizes `F₂₀ = Z₅ ⋊ Z₄` (not formalized here).
-/

namespace GeneralizedStarHeight

universe u

variable {Alphabet : Type u}

/-- **Groups of order less than `24`, except `F₂₀`.** -/
theorem height_one_of_card_lt_twentyfour_of_centralizer [Finite Alphabet] {G : Type} [Group G]
    [Fintype G] (hG : Fintype.card G < 24)
    (hC : Fintype.card G = 20 → ∀ P : Sylow 5 G, 5 < Nat.card (Subgroup.centralizer (P : Set G)))
    (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  obtain ⟨N, hN, hab, hidx⟩ := exists_abelian_normal_index_le_three_of_lt_24 hG hC
  have h0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show N.index = 1 ∨ N.index = 2 ∨ N.index = 3 by omega) with h1 | h2 | h3
  · rw [Subgroup.index_eq_one] at h1
    subst h1
    exact height_one_of_comm (fun x y => hab x trivial y trivial) T F
  · exact height_one_of_abelian_index_two N hab h2 T F
  · exact height_one_of_abelian_index_three N hab h3 T F

end GeneralizedStarHeight
