import Start.GroupOrderLtTwenty

/-!
# Groups of order less than `24`, except the Frobenius-type case of order `20`

`exists_abelian_normal_index_le_three_of_lt_24`: if `|G| < 24`, and in order `20` the centralizer of
a Sylow `5`-subgroup has more than `5` elements, then `G` has an abelian normal subgroup of index
`1`, `2` or `3`.

* Orders `< 20`: `good_of_card_lt_twenty`.
* Order `21`: the Sylow `7`-subgroup is normal, cyclic, of index `3`.
* Order `22`: a subgroup of order `11` has index `2`.  Order `23`: `G` is cyclic.
* Order `20`: the Sylow `5`-subgroup `P` is normal and lies in its centralizer `C`.  If `|C| = 10`,
  `C` is abelian (central `P` of index `2`) of index `2`; if `|C| = 20`, `P` is central and
  `|G| ≤ 4 |Z(G)|`.

The excluded groups of order `20` are those where `C = P`, i.e. `G` acts faithfully on `P` through
`Aut(Z₅) ≅ Z₄`: the group `F₂₀ = Z₅ ⋊ Z₄`.  That this is the only such group is not formalized.
-/

namespace GeneralizedStarHeight

namespace GroupLtTwenty

open Subgroup

variable {G : Type*} [Group G]

lemma good_of_card_twentyone [Finite G] (h : Nat.card G = 21) : Good G := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 G) := inferInstance
  have hP : Nat.card P = 7 := by
    simpa using card_sylow_eq P (k := 1) (by rw [h]; norm_num) (by rw [h]; norm_num)
  have hidx : (P : Subgroup G).index = 3 := by
    have := (P : Subgroup G).card_mul_index
    rw [hP, h] at this
    omega
  have hs := card_sylow_modEq_one 7 G
  have hd := P.card_dvd_index
  rw [hidx] at hd
  have hpos : 0 < Nat.card (Sylow 7 G) := Nat.card_pos
  have hle : Nat.card (Sylow 7 G) ≤ 3 := Nat.le_of_dvd (by norm_num) hd
  have h1 : Nat.card (Sylow 7 G) = 1 := by
    unfold Nat.ModEq at hs
    interval_cases (Nat.card (Sylow 7 G)) <;> simp_all
  have : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.mp h1).1
  exact ⟨P, Sylow.normal_of_subsingleton P, subgroup_comm_of_card_prime _ hP, by omega⟩

lemma good_of_card_twenty [Finite G] (h : Nat.card G = 20)
    (hC : ∀ P : Sylow 5 G, 5 < Nat.card (centralizer (P : Set G))) : Good G := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 G) := inferInstance
  have hP : Nat.card P = 5 := by
    simpa using card_sylow_eq P (k := 1) (by rw [h]; norm_num) (by rw [h]; norm_num)
  have hPc := subgroup_comm_of_card_prime (P : Subgroup G) hP
  set C := centralizer (P : Set G) with hCdef
  have hPC : (P : Subgroup G) ≤ C := by
    intro x hx
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro y hy
    exact hPc y hy x hx
  have hdvdC : Nat.card C ∣ 20 := h ▸ Subgroup.card_subgroup_dvd_card C
  have hdvdP : 5 ∣ Nat.card C := hP ▸ Subgroup.card_dvd_of_le hPC
  have hgt : 5 < Nat.card C := hC P
  have hcases : Nat.card C = 10 ∨ Nat.card C = 20 := by
    have hle : Nat.card C ≤ 20 := Nat.le_of_dvd (by norm_num) hdvdC
    interval_cases (Nat.card C) <;> omega
  rcases hcases with h10 | h20
  · have hcomm := comm_of_le_central C (P : Subgroup G) hPC
      (fun k hk x hx => ((Subgroup.mem_centralizer_iff.mp hx) k hk)) (by rw [h10, hP])
    exact good_of_comm_subgroup C hcomm (by rw [h, h10])
  · have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C (by rw [h20, h])
    have hPZ : (P : Subgroup G) ≤ center G := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ C := htop ▸ Subgroup.mem_top g
      exact ((Subgroup.mem_centralizer_iff.mp hg) x hx).symm
    have := Subgroup.card_le_of_le hPZ
    exact good_of_card_center (by omega)

/-- **Orders `20` to `23`.** -/
theorem good_of_card_lt_twentyfour [Finite G] (hG : Nat.card G < 24)
    (hC : Nat.card G = 20 → ∀ P : Sylow 5 G, 5 < Nat.card (centralizer (P : Set G))) : Good G := by
  by_cases h20 : Nat.card G < 20
  · exact good_of_card_lt_twenty h20
  have f11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have f23 : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  rcases (show Nat.card G = 20 ∨ Nat.card G = 21 ∨ Nat.card G = 22 ∨ Nat.card G = 23 by omega) with
    h | h | h | h
  · exact good_of_card_twenty h (hC h)
  · exact good_of_card_twentyone h
  · exact good_of_card_two_mul_prime (q := 11) (by rw [h])
  · exact good_of_card_prime (p := 23) h

end GroupLtTwenty

open GroupLtTwenty in
/-- **Every finite group of order less than `24` whose Sylow `5`-subgroups, in order `20`, have
centralizers of order `> 5`, has an abelian normal subgroup of index at most `3`.** -/
theorem exists_abelian_normal_index_le_three_of_lt_24 {G : Type} [Group G] [Fintype G]
    (hG : Fintype.card G < 24)
    (hC : Fintype.card G = 20 → ∀ P : Sylow 5 G, 5 < Nat.card (Subgroup.centralizer (P : Set G))) :
    ∃ N : Subgroup G, N.Normal ∧ (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) ∧ N.index ≤ 3 :=
  good_of_card_lt_twentyfour (by rwa [Nat.card_eq_fintype_card])
    (fun h => hC (by rwa [Nat.card_eq_fintype_card] at h))

end GeneralizedStarHeight
