import Start.StarHeightShear

/-!
# A barrier: `L(abac, 1, 2)` is not recognized by groups with metabelian `2`-subgroups

`TwoSubgroupsMetabelian Γ`: every `2`-subgroup `P` of `Γ` satisfies `⁅⁅P, P⁆, ⁅P, P⁆⁆ = ⊥`.

* `not_recognizes_abac`: if `Γ` is finite and `TwoSubgroupsMetabelian Γ`, no
  `T : FreeMonoid (Fin 3) →* Γ` and `F : Set Γ` give
  `{u | scount [0,1,0,2] u % 2 = 1} = {u | T (FreeMonoid.ofList u) ∈ F}`.
* Closure: `TwoSubgroupsMetabelian.pi`, `.prod` (a `2`-subgroup embeds in the product of its
  projections), `.of_metabelian`, `.of_card_dvd_eight`, and `twoSubgroupsMetabelian_perm_four`
  (`S₄`, whose `2`-subgroups have order dividing `8`).
* `not_recognizes_abac_pi`: so no Boolean combination of languages recognized by such groups is
  `L(abac, 1, 2)`.

The proof.  `UT5` is the group of `5 × 5` upper unitriangular matrices over `F₂` (ten entries
`aᵢⱼ`, `i < j`), of order `2¹⁰`; `abacHom` sends the letters `a, b, c` to the mod-`2` counting
matrices of `abac`, and `(abacHom u).a04 = scount abac u mod 2` (`abacHom_row`).
(i) If `T u = T v` then `abacHom u = abacHom v` (`abacHom_eq_of_T_eq`): the contexts `x, y` with
`x ∈ {ε, a, ab, aba}`, `y ∈ {ε, c, ac, bac}` read off every entry (`abac_separate`).
(ii) So `abacHom` factors through a hom `φ` from the finite group `range T`.
(iii) For a Sylow `2`-subgroup `S` of `range T`, the index of `φ(S)` in `φ(range T)` divides the
odd index of `S` and is a power of `2`, so `φ(S) = φ(range T)`.
(iv) `S` is metabelian, but `⁅⁅M a, M b⁆, ⁅M a, M c⁆⁆ ≠ 1` (`decide`).
-/

namespace GeneralizedStarHeight

open scoped commutatorElement

/-! ### The unitriangular group `UT₅(F₂)` -/

/-- Upper unitriangular `5 × 5` matrices over `F₂`, by their ten entries above the diagonal. -/
@[ext] structure UT5 where
  a01 : ZMod 2
  a02 : ZMod 2
  a03 : ZMod 2
  a04 : ZMod 2
  a12 : ZMod 2
  a13 : ZMod 2
  a14 : ZMod 2
  a23 : ZMod 2
  a24 : ZMod 2
  a34 : ZMod 2
  deriving DecidableEq

namespace UT5

/-- The entries above the diagonal. -/
def equivFun : UT5 ≃ (Fin 10 → ZMod 2) where
  toFun x := ![x.a01, x.a02, x.a03, x.a04, x.a12, x.a13, x.a14, x.a23, x.a24, x.a34]
  invFun f := ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9⟩
  left_inv _ := rfl
  right_inv f := by funext i; fin_cases i <;> rfl

instance : Fintype UT5 := Fintype.ofEquiv _ equivFun.symm

lemma card : Fintype.card UT5 = 2 ^ 10 := by
  rw [Fintype.card_congr equivFun]; simp

instance : One UT5 := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

/-- The matrix product. -/
instance : Mul UT5 := ⟨fun x y =>
  ⟨x.a01 + y.a01, x.a02 + y.a02 + x.a01 * y.a12,
    x.a03 + y.a03 + x.a01 * y.a13 + x.a02 * y.a23,
    x.a04 + y.a04 + x.a01 * y.a14 + x.a02 * y.a24 + x.a03 * y.a34,
    x.a12 + y.a12, x.a13 + y.a13 + x.a12 * y.a23,
    x.a14 + y.a14 + x.a12 * y.a24 + x.a13 * y.a34,
    x.a23 + y.a23, x.a24 + y.a24 + x.a23 * y.a34, x.a34 + y.a34⟩⟩

/-- The (left) inverse, row by row. -/
instance : Inv UT5 := ⟨fun x =>
  let y01 := -x.a01
  let y02 := -x.a02 - y01 * x.a12
  let y03 := -x.a03 - y01 * x.a13 - y02 * x.a23
  let y04 := -x.a04 - y01 * x.a14 - y02 * x.a24 - y03 * x.a34
  let y12 := -x.a12
  let y13 := -x.a13 - y12 * x.a23
  let y14 := -x.a14 - y12 * x.a24 - y13 * x.a34
  let y23 := -x.a23
  let y24 := -x.a24 - y23 * x.a34
  let y34 := -x.a34
  ⟨y01, y02, y03, y04, y12, y13, y14, y23, y24, y34⟩⟩

lemma mul_def (x y : UT5) : x * y =
    ⟨x.a01 + y.a01, x.a02 + y.a02 + x.a01 * y.a12,
      x.a03 + y.a03 + x.a01 * y.a13 + x.a02 * y.a23,
      x.a04 + y.a04 + x.a01 * y.a14 + x.a02 * y.a24 + x.a03 * y.a34,
      x.a12 + y.a12, x.a13 + y.a13 + x.a12 * y.a23,
      x.a14 + y.a14 + x.a12 * y.a24 + x.a13 * y.a34,
      x.a23 + y.a23, x.a24 + y.a24 + x.a23 * y.a34, x.a34 + y.a34⟩ := rfl

lemma one_def : (1 : UT5) = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := rfl

instance : Group UT5 where
  mul_assoc x y z := by ext <;> simp only [mul_def] <;> ring
  one_mul x := by ext <;> simp only [mul_def, one_def] <;> ring
  mul_one x := by ext <;> simp only [mul_def, one_def] <;> ring
  inv_mul_cancel x := by ext <;> simp only [mul_def, one_def, Inv.inv] <;> ring

/-- `UT₅(F₂)` is a `2`-group. -/
lemma isPGroup : IsPGroup 2 UT5 :=
  IsPGroup.of_card (n := 10) (by rw [Nat.card_eq_fintype_card, card])

/-- The counting matrix of the letter `a` of `abac`: `I + E₀₁ + E₂₃`. -/
def Ma : UT5 := ⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩
/-- The counting matrix of the letter `b` of `abac`: `I + E₁₂`. -/
def Mb : UT5 := ⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩
/-- The counting matrix of the letter `c` of `abac`: `I + E₃₄`. -/
def Mc : UT5 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩

/-- **The double commutator `⁅⁅M a, M b⁆, ⁅M a, M c⁆⁆` is not trivial.** -/
lemma double_commutator_ne_one : ⁅⁅Ma, Mb⁆, ⁅Ma, Mc⁆⁆ ≠ 1 := by decide

end UT5

open UT5

/-- The letter matrices of `abac` (`a = 0`, `b = 1`, `c = 2`). -/
def abacMat : Fin 3 → UT5 := ![Ma, Mb, Mc]

/-- The transition hom of the mod-`2` counting automaton of `abac`. -/
def abacHom : FreeMonoid (Fin 3) →* UT5 := FreeMonoid.lift abacMat

lemma abacHom_snoc (u : List (Fin 3)) (z : Fin 3) :
    abacHom (FreeMonoid.ofList (u ++ [z])) = abacHom (FreeMonoid.ofList u) * abacMat z := by
  rw [FreeMonoid.ofList_append, map_mul, FreeMonoid.ofList_singleton]
  rfl

/-- **Row `0` of `abacHom u`**: the counts modulo `2` of the prefixes of `abac`. -/
lemma abacHom_row (u : List (Fin 3)) :
    (abacHom (FreeMonoid.ofList u)).a01 = (u.count 0 : ZMod 2) ∧
      (abacHom (FreeMonoid.ofList u)).a02 = (scount [0, 1] u : ZMod 2) ∧
      (abacHom (FreeMonoid.ofList u)).a03 = (scount [0, 1, 0] u : ZMod 2) ∧
      (abacHom (FreeMonoid.ofList u)).a04 = (scount [0, 1, 0, 2] u : ZMod 2) := by
  induction u using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | append_singleton u z ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      have e2 : scount [0, 1] (u ++ [z]) = scount [0, 1] u + if z = 1 then scount [0] u else 0 :=
        scount_snoc (1 : Fin 3) z u [0]
      have e3 : scount [0, 1, 0] (u ++ [z]) =
          scount [0, 1, 0] u + if z = 0 then scount [0, 1] u else 0 :=
        scount_snoc (0 : Fin 3) z u [0, 1]
      have e4 : scount [0, 1, 0, 2] (u ++ [z]) =
          scount [0, 1, 0, 2] u + if z = 2 then scount [0, 1, 0] u else 0 :=
        scount_snoc (2 : Fin 3) z u [0, 1, 0]
      rw [abacHom_snoc, mul_def, e2, e3, e4, List.count_append, scount_singleton]
      simp only [h1, h2, h3, h4]
      fin_cases z <;> simp [abacMat, Ma, Mb, Mc]

/-- `abacHom u` determines `scount abac u` modulo `2`. -/
lemma abacHom_a04 (u : List (Fin 3)) :
    (abacHom (FreeMonoid.ofList u)).a04 = (scount [0, 1, 0, 2] u : ZMod 2) :=
  (abacHom_row u).2.2.2

/-- **Separation.** The functionals `m ↦ (abacHom x * m * abacHom y).a04` determine `m`. -/
lemma abac_separate (m m' : UT5)
    (h : ∀ x y : List (Fin 3), (abacHom (FreeMonoid.ofList x) * m * abacHom (FreeMonoid.ofList y)).a04 =
      (abacHom (FreeMonoid.ofList x) * m' * abacHom (FreeMonoid.ofList y)).a04) : m = m' := by
  have x0 : abacHom (FreeMonoid.ofList []) = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by decide
  have x1 : abacHom (FreeMonoid.ofList [0]) = ⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩ := by decide
  have x2 : abacHom (FreeMonoid.ofList [0, 1]) = ⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩ := by decide
  have x3 : abacHom (FreeMonoid.ofList [0, 1, 0]) = ⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩ := by decide
  have y1 : abacHom (FreeMonoid.ofList [2]) = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩ := by decide
  have y2 : abacHom (FreeMonoid.ofList [0, 2]) = ⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩ := by decide
  have y3 : abacHom (FreeMonoid.ofList [1, 0, 2]) = ⟨1, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩ := by decide
  have h00 := h [] []
  have h01 := h [] [2]
  have h02 := h [] [0, 2]
  have h03 := h [] [1, 0, 2]
  have h10 := h [0] []
  have h11 := h [0] [2]
  have h12 := h [0] [0, 2]
  have h20 := h [0, 1] []
  have h21 := h [0, 1] [2]
  have h30 := h [0, 1, 0] []
  rw [x0, y1, y2, y3, x1, x2, x3] at *
  simp only [mul_def] at h00 h01 h02 h03 h10 h11 h12 h20 h21 h30
  ext
  · linear_combination -h02 + h03
  · linear_combination -h01 + h02
  · linear_combination -h00 + h01
  · linear_combination h00
  · linear_combination h01 - h02 - h11 + h12
  · linear_combination h00 - h01 - h10 + h11
  · linear_combination -h00 + h10
  · linear_combination h10 - h11 - h20 + h21
  · linear_combination -h10 + h20
  · linear_combination -h00 + h10 - h20 + h30

lemma natCast_zmod_two_eq {n m : ℕ} (h : n % 2 = 1 ↔ m % 2 = 1) : (n : ZMod 2) = m := by
  rw [ZMod.natCast_eq_natCast_iff']
  omega

/-- **(i)** If `T` recognizes `L(abac, 1, 2)` and `T u = T v`, then `abacHom u = abacHom v`. -/
lemma abacHom_eq_of_T_eq {Γ : Type} [Monoid Γ] (T : FreeMonoid (Fin 3) →* Γ) (F : Set Γ)
    (hL : ∀ u : List (Fin 3), scount [0, 1, 0, 2] u % 2 = 1 ↔ T (FreeMonoid.ofList u) ∈ F)
    (u v : FreeMonoid (Fin 3)) (huv : T u = T v) : abacHom u = abacHom v := by
  refine abac_separate _ _ fun x y => ?_
  have key : ∀ w : FreeMonoid (Fin 3),
      (abacHom (FreeMonoid.ofList x) * abacHom w * abacHom (FreeMonoid.ofList y)).a04 =
        (scount [0, 1, 0, 2] (x ++ FreeMonoid.toList w ++ y) : ZMod 2) := by
    intro w
    rw [← abacHom_a04, FreeMonoid.ofList_append, FreeMonoid.ofList_append, map_mul, map_mul,
      FreeMonoid.ofList_toList]
  rw [key, key]
  refine natCast_zmod_two_eq ?_
  rw [hL, hL, FreeMonoid.ofList_append, FreeMonoid.ofList_append, FreeMonoid.ofList_append,
    FreeMonoid.ofList_append, map_mul, map_mul, map_mul, map_mul, FreeMonoid.ofList_toList,
    FreeMonoid.ofList_toList, huv]

/-! ### `2`-subgroups -/

/-- Every `2`-subgroup `P` of `Γ` is metabelian: `⁅⁅P, P⁆, ⁅P, P⁆⁆ = ⊥`. -/
def TwoSubgroupsMetabelian (Γ : Type) [Group Γ] : Prop :=
  ∀ P : Subgroup Γ, IsPGroup 2 P → ⁅⁅P, P⁆, ⁅P, P⁆⁆ = ⊥

/-- The range of a monoid hom into a finite group, as a subgroup. -/
def rangeSubgroup {α Γ : Type} [Group Γ] [Finite Γ] (T : FreeMonoid α →* Γ) : Subgroup Γ where
  carrier := Set.range T
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, map_mul T x y⟩
  one_mem' := ⟨1, map_one T⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    refine ⟨x ^ (orderOf (T x) - 1), ?_⟩
    have hpos := (isOfFinOrder_of_finite (T x)).orderOf_pos
    rw [map_pow]
    refine (eq_inv_of_mul_eq_one_left ?_)
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]

lemma mem_rangeSubgroup {α Γ : Type} [Group Γ] [Finite Γ] (T : FreeMonoid α →* Γ)
    (w : FreeMonoid α) : T w ∈ rangeSubgroup T := ⟨w, rfl⟩

/-- **(ii)** `abacHom` through `range T`. -/
noncomputable def abacPhi {Γ : Type} [Group Γ] [Finite Γ] (T : FreeMonoid (Fin 3) →* Γ) (F : Set Γ)
    (hL : ∀ u : List (Fin 3), scount [0, 1, 0, 2] u % 2 = 1 ↔ T (FreeMonoid.ofList u) ∈ F) :
    rangeSubgroup T →* UT5 where
  toFun g := abacHom (Classical.choose g.2)
  map_one' := by
    have h := Classical.choose_spec (1 : rangeSubgroup T).2
    rw [abacHom_eq_of_T_eq T F hL _ 1 (by rw [h, map_one]; rfl), map_one]
  map_mul' g g' := by
    have h := Classical.choose_spec (g * g').2
    have h1 := Classical.choose_spec g.2
    have h2 := Classical.choose_spec g'.2
    rw [← map_mul]
    refine abacHom_eq_of_T_eq T F hL _ _ ?_
    rw [h, map_mul, h1, h2]
    rfl

lemma abacPhi_apply {Γ : Type} [Group Γ] [Finite Γ] (T : FreeMonoid (Fin 3) →* Γ) (F : Set Γ)
    (hL : ∀ u : List (Fin 3), scount [0, 1, 0, 2] u % 2 = 1 ↔ T (FreeMonoid.ofList u) ∈ F)
    (w : FreeMonoid (Fin 3)) : abacPhi T F hL ⟨T w, mem_rangeSubgroup T w⟩ = abacHom w :=
  abacHom_eq_of_T_eq T F hL _ _ (Classical.choose_spec (mem_rangeSubgroup T w))

/-- **The barrier.** If every `2`-subgroup of the finite group `Γ` is metabelian, then
`L(abac, 1, 2) = {u | scount [a,b,a,c] u odd}` is not recognized by `Γ`. -/
theorem not_recognizes_abac {Γ : Type} [Group Γ] [Finite Γ] (hΓ : TwoSubgroupsMetabelian Γ)
    (T : FreeMonoid (Fin 3) →* Γ) (F : Set Γ) :
    {u : List (Fin 3) | scount [0, 1, 0, 2] u % 2 = 1} ≠ {u | T (FreeMonoid.ofList u) ∈ F} := by
  intro hEq
  have hL : ∀ u : List (Fin 3), scount [0, 1, 0, 2] u % 2 = 1 ↔ T (FreeMonoid.ofList u) ∈ F :=
    fun u => Set.ext_iff.1 hEq u
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := rangeSubgroup T
  set φ := abacPhi T F hL
  obtain ⟨S⟩ : Nonempty (Sylow 2 R) := inferInstance
  set φ' := φ.rangeRestrict
  have hsurj : Function.Surjective φ' := MonoidHom.rangeRestrict_surjective φ
  -- (iii) the image of `S` is everything
  have hidx1 : ((S : Subgroup R).map φ').index ∣ (S : Subgroup R).index :=
    Subgroup.index_map_dvd _ hsurj
  have hnd : ¬ 2 ∣ (S : Subgroup R).index := S.not_dvd_index
  have hpr : IsPGroup 2 φ.range := UT5.isPGroup.to_subgroup _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.1 hpr)
  have hidx2 : ((S : Subgroup R).map φ').index ∣ 2 ^ n := hn ▸ Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hidx2
  have hj0 : j = 0 := by
    by_contra hj0
    exact hnd (dvd_trans (hj ▸ dvd_pow_self 2 hj0) hidx1)
  have htop : (S : Subgroup R).map φ' = ⊤ := Subgroup.index_eq_one.1 (by rw [hj, hj0, pow_zero])
  have hpre : ∀ w : FreeMonoid (Fin 3), ∃ s ∈ (S : Subgroup R), φ s = abacHom w := by
    intro w
    have hm : φ' ⟨T w, mem_rangeSubgroup T w⟩ ∈ (S : Subgroup R).map φ' := htop ▸ Subgroup.mem_top _
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.1 hm
    refine ⟨s, hs, ?_⟩
    have := congrArg Subtype.val hse
    rw [MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict] at this
    rw [this, abacPhi_apply]
  obtain ⟨sa, hsa, hφa⟩ := hpre (FreeMonoid.of 0)
  obtain ⟨sb, hsb, hφb⟩ := hpre (FreeMonoid.of 1)
  obtain ⟨sc, hsc, hφc⟩ := hpre (FreeMonoid.of 2)
  -- (iv) `S` is metabelian
  set P := (S : Subgroup R).map R.subtype
  have hP : ⁅⁅P, P⁆, ⁅P, P⁆⁆ = ⊥ := hΓ P (S.isPGroup'.map _)
  have ma : (sa : Γ) ∈ P := Subgroup.mem_map_of_mem _ hsa
  have mb : (sb : Γ) ∈ P := Subgroup.mem_map_of_mem _ hsb
  have mc : (sc : Γ) ∈ P := Subgroup.mem_map_of_mem _ hsc
  have hmem := Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator ma mb)
    (Subgroup.commutator_mem_commutator ma mc)
  rw [hP, Subgroup.mem_bot] at hmem
  have hR : ⁅⁅sa, sb⁆, ⁅sa, sc⁆⁆ = 1 := by
    apply R.subtype_injective
    rw [map_commutatorElement, map_commutatorElement, map_commutatorElement, map_one]
    exact hmem
  have := congrArg φ hR
  rw [map_commutatorElement, map_commutatorElement, map_commutatorElement, map_one, hφa, hφb,
    hφc] at this
  exact UT5.double_commutator_ne_one this

/-! ### Closure of the hypothesis -/

namespace TwoSubgroupsMetabelian

/-- The hypothesis passes to a group with a jointly injective family of homs to such groups. -/
theorem of_injective {Γ : Type} [Group Γ] {ι : Type} {Δ : ι → Type} [∀ i, Group (Δ i)]
    (f : ∀ i, Γ →* Δ i) (hinj : ∀ x, (∀ i, f i x = 1) → x = 1)
    (h : ∀ i, TwoSubgroupsMetabelian (Δ i)) : TwoSubgroupsMetabelian Γ := by
  intro P hP
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  refine hinj x fun i => ?_
  have := Subgroup.mem_map_of_mem (f i) hx
  rw [Subgroup.map_commutator, Subgroup.map_commutator, h i _ (hP.map (f i)),
    Subgroup.mem_bot] at this
  exact this

/-- **Products.** -/
theorem pi {ι : Type} {Δ : ι → Type} [∀ i, Group (Δ i)] (h : ∀ i, TwoSubgroupsMetabelian (Δ i)) :
    TwoSubgroupsMetabelian (∀ i, Δ i) :=
  of_injective (fun i => Pi.evalMonoidHom Δ i) (fun _ hx => funext hx) h

/-- **Binary products.** -/
theorem prod {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] (h₁ : TwoSubgroupsMetabelian Γ₁)
    (h₂ : TwoSubgroupsMetabelian Γ₂) : TwoSubgroupsMetabelian (Γ₁ × Γ₂) := by
  intro P hP
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hf := Subgroup.mem_map_of_mem (MonoidHom.fst Γ₁ Γ₂) hx
  have hs := Subgroup.mem_map_of_mem (MonoidHom.snd Γ₁ Γ₂) hx
  rw [Subgroup.map_commutator, Subgroup.map_commutator, h₁ _ (hP.map _), Subgroup.mem_bot] at hf
  rw [Subgroup.map_commutator, Subgroup.map_commutator, h₂ _ (hP.map _), Subgroup.mem_bot] at hs
  exact Prod.ext hf hs

/-- **Metabelian groups.** -/
theorem of_metabelian {Γ : Type} [Group Γ]
    (h : ⁅⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆, ⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆⁆ = ⊥) :
    TwoSubgroupsMetabelian Γ := fun _ _ =>
  eq_bot_iff.2 (h ▸ Subgroup.commutator_mono (Subgroup.commutator_mono le_top le_top)
    (Subgroup.commutator_mono le_top le_top))

end TwoSubgroupsMetabelian

lemma comm_of_card_dvd_four {Q : Type} [Group Q] [Finite Q] (h : Nat.card Q ∣ 2 ^ 2) :
    ∀ a b : Q, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, hQ⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  interval_cases m
  · have : Subsingleton Q := (Nat.card_eq_one_iff_unique.1 (by simpa using hQ)).1
    intro a b; exact Subsingleton.elim _ _
  · have := isCyclic_of_prime_card (p := 2) (by simpa using hQ)
    exact fun a b => (IsCyclic.commGroup (α := Q)).mul_comm a b
  · exact fun a b => (IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ).is_comm.comm a b

/-- **A group of order dividing `8` is metabelian**: its centre is nontrivial, so the quotient by
the centre has order at most `4` and is abelian, and the derived subgroup lies in the centre. -/
lemma metabelian_of_card_dvd_eight {Q : Type} [Group Q] [Finite Q] (h : Nat.card Q ∣ 2 ^ 3) :
    ⁅⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆, ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases subsingleton_or_nontrivial Q with hs | hn
  · exact Subsingleton.elim _ _
  obtain ⟨m, hm, hQ⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  have hp : IsPGroup 2 Q := IsPGroup.of_card hQ
  have hZ := hp.center_nontrivial
  set Z := Subgroup.center Q
  have hZ2 : 1 < Nat.card Z := Finite.one_lt_card_iff_nontrivial.2 hZ
  have hidx : Z.index ∣ 2 ^ 2 := by
    have h1 := Z.index_mul_card
    rw [hQ] at h1
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ h1)
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ h1)
    rw [hk', hj', ← pow_add] at h1
    have := Nat.pow_right_injective le_rfl h1
    have hj1 : j ≠ 0 := by rintro rfl; rw [hj'] at hZ2; simp at hZ2
    rw [hk']; exact pow_dvd_pow 2 (by omega)
  have hcomm : ∀ a b : Q ⧸ Z, a * b = b * a := comm_of_card_dvd_four (by
    rw [← Subgroup.index]; exact hidx)
  have h1 : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro g _ h _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcomm (g : Q ⧸ Z) h]; group
  have h2 : ⁅Z, Z⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro g hg h _
    rw [Subgroup.mem_bot, commutatorElement_def, ← Subgroup.mem_center_iff.1 hg h]; group
  exact eq_bot_iff.2 (h2 ▸ Subgroup.commutator_mono h1 h1)

/-- **Groups whose `2`-subgroups have order dividing `8`.** -/
theorem TwoSubgroupsMetabelian.of_card_dvd_eight {Γ : Type} [Group Γ]
    (h : ∀ P : Subgroup Γ, IsPGroup 2 P → Nat.card P ∣ 2 ^ 3) : TwoSubgroupsMetabelian Γ := by
  intro P hP
  have hfin : Finite P := by
    have := h P hP
    exact Nat.finite_of_card_ne_zero (fun h0 => by rw [h0] at this; norm_num at this)
  have hQ := metabelian_of_card_dvd_eight (h P hP)
  have hrange : (⊤ : Subgroup P).map P.subtype = P := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hrange, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hQ, Subgroup.map_bot]

/-- **`S₄`**: its `2`-subgroups have order dividing `8`, so they are metabelian. -/
theorem twoSubgroupsMetabelian_perm_four : TwoSubgroupsMetabelian (Equiv.Perm (Fin 4)) := by
  refine TwoSubgroupsMetabelian.of_card_dvd_eight fun P hP => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  have h24 : Nat.card P ∣ 24 := by
    have := Subgroup.card_subgroup_dvd_card P
    rwa [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 4)), Fintype.card_perm,
      Fintype.card_fin] at this
  rw [hn] at h24 ⊢
  refine pow_dvd_pow 2 ?_
  by_contra hlt
  have : 2 ^ 4 ∣ 24 := dvd_trans (pow_dvd_pow 2 (by omega)) h24
  norm_num at this

/-- **No Boolean combination** of languages recognized by finite groups whose `2`-subgroups are
metabelian is `L(abac, 1, 2)`. -/
theorem not_recognizes_abac_pi {ι : Type} [Finite ι] {Δ : ι → Type} [∀ i, Group (Δ i)]
    [∀ i, Finite (Δ i)] (hΔ : ∀ i, TwoSubgroupsMetabelian (Δ i))
    (T : ∀ i, FreeMonoid (Fin 3) →* Δ i) (F : Set (∀ i, Δ i)) :
    {u : List (Fin 3) | scount [0, 1, 0, 2] u % 2 = 1} ≠
      {u | (fun i => T i (FreeMonoid.ofList u)) ∈ F} :=
  not_recognizes_abac (TwoSubgroupsMetabelian.pi hΔ) (MonoidHom.pi T) F

/-- **`S₄` cannot recognize `L(abac, 1, 2)`**, even through Boolean combinations. -/
theorem not_recognizes_abac_perm_four {ι : Type} [Finite ι]
    (T : ι → FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4)) (F : Set (ι → Equiv.Perm (Fin 4))) :
    {u : List (Fin 3) | scount [0, 1, 0, 2] u % 2 = 1} ≠
      {u | (fun i => T i (FreeMonoid.ofList u)) ∈ F} :=
  not_recognizes_abac_pi (fun _ => twoSubgroupsMetabelian_perm_four) T F

end GeneralizedStarHeight
