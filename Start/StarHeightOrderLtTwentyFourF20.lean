import Start.GroupOrderTwentyF20
import Start.StarHeightOrderLtTwentyFour
import Start.StarHeightZ4PM1

/-!
# Generalized star height one for groups of order less than `24`

* `height_one_of_card_lt_twentyfour`: every language recognized by a finite group of order `< 24`
  that is not isomorphic to `F₂₀` has generalized star height at most one.  The centralizer
  hypothesis of `height_one_of_card_lt_twentyfour_of_centralizer` fails only for `F₂₀`
  (`mulEquiv_F20_of_centralizer`).
* `height_one_of_card_lt_twentyfour_of_rot2`: if `Z4CoreRot2` holds, every finite group of order
  `< 24` (`F₂₀` by `height_one_F20_of_rot2`).
-/

namespace GeneralizedStarHeight

universe u

variable {Alphabet : Type u}

open GroupLtTwenty in
/-- **Groups of order less than `24`, except `F₂₀`.** -/
theorem height_one_of_card_lt_twentyfour [Finite Alphabet] {G : Type} [Group G] [Fintype G]
    (hG : Fintype.card G < 24) (hF : IsEmpty (G ≃* F20)) (T : FreeMonoid Alphabet →* G)
    (F : Set G) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_card_lt_twentyfour_of_centralizer hG (fun h20 P => ?_) T F
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hGn : Nat.card G = 20 := by rw [Nat.card_eq_fintype_card, h20]
  have hP : Nat.card P = 5 := by
    simpa using card_sylow_eq P (k := 1) (by rw [hGn]; norm_num) (by rw [hGn]; norm_num)
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer (P : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact subgroup_comm_of_card_prime (P : Subgroup G) hP b hb a ha
  have hdvd : 5 ∣ Nat.card (Subgroup.centralizer (P : Set G)) := by
    have := Subgroup.card_dvd_of_le hPC
    rwa [hP] at this
  have hpos : 0 < Nat.card (Subgroup.centralizer (P : Set G)) := Nat.card_pos
  by_contra hle
  have h5 : Nat.card (Subgroup.centralizer (P : Set G)) = 5 := by
    obtain ⟨k, hk⟩ := hdvd
    rw [hk] at hle hpos ⊢
    have : k = 1 := by omega
    rw [this]
  obtain ⟨e⟩ := mulEquiv_F20_of_centralizer h20 P h5
  exact hF.false e

/-- **Under `Z4CoreRot2`, every group of order less than `24`.** -/
theorem height_one_of_card_lt_twentyfour_of_rot2 (h2 : Z4CoreRot2) [Finite Alphabet] {G : Type}
    [Group G] [Fintype G] (hG : Fintype.card G < 24) (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  by_cases hF : Nonempty (G ≃* F20)
  · obtain ⟨e⟩ := hF
    have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) =
        {w | (e.toMonoidHom.comp T) (FreeMonoid.ofList w) ∈ e.symm ⁻¹' F} := by
      ext w
      simp
    rw [heq]
    exact height_one_F20_of_rot2 h2 _ _
  · exact height_one_of_card_lt_twentyfour hG (not_nonempty_iff.mp hF) T F

end GeneralizedStarHeight
