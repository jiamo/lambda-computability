import Start.StarHeightPrimeCount

/-!
# Generalized star height one for an abelian normal subgroup of prime index, one moving coset

* `height_one_of_prime_index_pure`: let `N` be an abelian normal subgroup of prime index `p` of a
  finite group `G`, and `g ∈ G`.  If `T : FreeMonoid Alphabet →* G` sends every letter into `N` or
  into `gN`, every language recognized by `T` has generalized star height at most one.
* Corollaries: `height_one_of_abelian_index_two` (every group with an abelian normal subgroup of
  index two; Pin–Straubing–Thérien 1992, Theorem 7.6, restricted to groups),
  `height_one_quaternionGroup` (in particular `QuaternionGroup 3`, the dicyclic group of order 12),
  `height_one_dihedralGroup`, and `height_one_alternatingGroup_four_pure` (`A₄` when every letter
  lies in `V ∪ σV`, `V` the Klein four subgroup).

The proof: the telescoping of `Start/StarHeightIndexThree.lean` writes `T w` as a product, in the
abelian `N`, of the values of the pairs (state, letter), times a representative of the final
state.  The state of a prefix is `γ ^ k` with `γ = gN` and `k` the number of letters outside `N`,
so the number of positions reading `x` in a given state is `pcount`, which has height one by
`pcount_height_one`.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

variable {Alphabet : Type u}

section Assembly

open Classical

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (T : FreeMonoid Alphabet →* G)

lemma tpairs_count_eq_pcount (γ : G ⧸ N) (mv : Alphabet → Bool)
    (hmv : ∀ a, psi N T (FreeMonoid.of a) = if mv a then γ else 1) {p : ℕ}
    (hord : orderOf γ = p) {h : ℕ} (hh : h < p) (a : Alphabet) :
    ∀ (w : List Alphabet) (s : ℕ), (tpairs N T (γ ^ s) w).count (γ ^ h, a) = pcount mv p h a s w
  | [], _ => rfl
  | b :: w, s => by
      rw [tpairs, pcount, List.count_cons]
      have hstep : γ ^ s * psi N T (FreeMonoid.of b) = γ ^ (if mv b then s + 1 else s) := by
        rw [hmv b]; split_ifs <;> simp [pow_succ]
      rw [hstep, tpairs_count_eq_pcount γ mv hmv hord hh a w, add_comm]
      congr 1
      have hiff : (γ ^ s = γ ^ h) ↔ s % p = h := by
        rw [pow_eq_pow_iff_modEq, hord, Nat.ModEq, Nat.mod_eq_of_lt hh]
      by_cases hb : b = a
      · subst hb
        by_cases hs : s % p = h
        · simp [hs, hiff.mpr hs]
        · have : ¬ γ ^ s = γ ^ h := fun e => hs (hiff.mp e)
          simp [hs, this]
      · simp [hb]

/-- The main theorem, for `g ∉ N`. -/
theorem height_one_of_prime_index_pure_aux [Finite Alphabet] [Fintype G]
    (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) {p : ℕ} [hp : Fact p.Prime]
    (hidx : N.index = p) (g : G) (hg : g ∉ N)
    (hT : ∀ a, T (FreeMonoid.of a) ∈ N ∨ g⁻¹ * T (FreeMonoid.of a) ∈ N) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have := Fintype.ofFinite Alphabet
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hcard : Nat.card (G ⧸ N) = p := hidx
  set γ : G ⧸ N := (g : G ⧸ N) with hγ
  have hγ1 : γ ≠ 1 := fun h => hg ((QuotientGroup.eq_one_iff g).mp h)
  have hord : orderOf γ = p := by
    have hd : orderOf γ ∣ p := hcard ▸ orderOf_dvd_natCard γ
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp.out _ hd) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hγ1
    · exact h
  have hgen : ∀ q : G ⧸ N, ∃ h, h < p ∧ γ ^ h = q := by
    intro q
    have htop : Subgroup.zpowers γ = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, hcard])
    have hq : q ∈ Subgroup.zpowers γ := htop ▸ Subgroup.mem_top q
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    refine ⟨(k % (p : ℤ)).toNat, ?_, ?_⟩
    · have h0 := Int.emod_lt_of_pos k (by exact_mod_cast hp.out.pos : (0 : ℤ) < p)
      have h1 := hp.out.pos
      have h2 := Int.emod_nonneg k (show (p : ℤ) ≠ 0 by exact_mod_cast hp.out.ne_zero)
      omega
    · rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.out.ne_zero)),
        ← hord, zpow_mod_orderOf]
  choose hix hixlt hixeq using hgen
  let mv : Alphabet → Bool := fun a => decide (T (FreeMonoid.of a) ∉ N)
  have hmv : ∀ a, psi N T (FreeMonoid.of a) = if mv a then γ else 1 := by
    intro a
    simp only [mv, psi_apply]
    by_cases ha : T (FreeMonoid.of a) ∈ N
    · simp [ha, (QuotientGroup.eq_one_iff _).mpr ha]
    · simp only [ha, not_false_eq_true, decide_true, if_true, hγ]
      rcases hT a with h | h
      · exact absurd h ha
      · exact (QuotientGroup.eq.mpr (by simpa using h)).symm
  have hcount : ∀ (w : List Alphabet) (pr : (G ⧸ N) × Alphabet),
      (tpairs N T 1 w).count pr = pcount mv p (hix pr.1) pr.2 0 w := by
    intro w pr
    have := tpairs_count_eq_pcount N T γ mv hmv hord (hixlt pr.1) pr.2 w 0
    rw [pow_zero, hixeq] at this
    exact this
  have hval : ∀ w : List Alphabet, T (FreeMonoid.ofList w) =
      (valN N T hab (fun pr => (tpairs N T 1 w).count pr % Nat.card N) : G) *
        rep N (psi N T (FreeMonoid.ofList w)) := by
    intro w
    have ht := telescope N T 1 w
    rw [rep_one, one_mul, one_mul, list_prod_cv N T hab, mul_inv_eq_iff_eq_mul] at ht
    exact ht
  have hQ : ∀ x y : G ⧸ N, x * y = y * x := by
    have := isCyclic_of_prime_card (p := p) hcard
    exact fun x y => (IsCyclic.commGroup (α := G ⧸ N)).mul_comm x y
  let Idx := {z : (G ⧸ N) × ((G ⧸ N) × Alphabet → Fin (Nat.card N)) //
    (valN N T hab (fun pr => (z.2 pr : ℕ)) : G) * rep N z.1 ∈ F}
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) = ⨆ z : Idx,
      ({w | psi N T (FreeMonoid.ofList w) = z.1.1} ⊓
        ⨅ pr : (G ⧸ N) × Alphabet,
          {w | pcount mv p (hix pr.1) pr.2 0 w % Nat.card N = z.1.2 pr}) := by
    ext w
    constructor
    · intro hw
      refine Language.mem_iSup.mpr ⟨⟨(psi N T (FreeMonoid.ofList w), fun pr =>
        ⟨(tpairs N T 1 w).count pr % Nat.card N, Nat.mod_lt _ Nat.card_pos⟩), ?_⟩, rfl, ?_⟩
      · show _ ∈ F
        rw [← hval]; exact hw
      · refine HasHeightAtMost.mem_iInf_lang.mpr fun pr => ?_
        show _ = _
        simp only
        rw [hcount]
    · intro hw
      obtain ⟨z, hz1, hz2⟩ := Language.mem_iSup.mp hw
      have hz2' := HasHeightAtMost.mem_iInf_lang.mp hz2
      show T (FreeMonoid.ofList w) ∈ F
      rw [hval]
      have hres : (fun pr => (tpairs N T 1 w).count pr % Nat.card N) =
          fun pr => (z.1.2 pr : ℕ) := by
        funext pr
        rw [hcount]; exact hz2' pr
      have hz1' : psi N T (FreeMonoid.ofList w) = z.1.1 := hz1
      rw [hres, hz1']
      exact z.2
  rw [heq]
  refine HasHeightAtMost.iSup _ fun z => HasHeightAtMost.inter ?_ ?_
  · simpa using height_one_of_comm hQ (psi N T) {z.1.1}
  · exact HasHeightAtMost.iInf _ fun pr =>
      pcount_height_one mv hp.out (hixlt pr.1) pr.2 Nat.card_pos (z.1.2 pr).2

end Assembly

/-- **Generalized star height one for an abelian normal subgroup of prime index, when every letter
lies in `N` or in one coset `gN`.** -/
theorem height_one_of_prime_index_pure [Finite Alphabet] {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) {p : ℕ} [Fact p.Prime]
    (hidx : N.index = p) (g : G) (T : FreeMonoid Alphabet →* G)
    (hT : ∀ a, T (FreeMonoid.of a) ∈ N ∨ g⁻¹ * T (FreeMonoid.of a) ∈ N) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  by_cases hg : g ∈ N
  · have hN : N ≠ ⊤ := by
      intro h
      rw [← Subgroup.index_eq_one, hidx] at h
      exact (Fact.out : p.Prime).one_lt.ne' h
    obtain ⟨g', hg'⟩ : ∃ g', g' ∉ N := by
      by_contra h
      push Not at h
      exact hN (eq_top_iff.mpr fun x _ => h x)
    refine height_one_of_prime_index_pure_aux N T hab hidx g' hg' (fun a => Or.inl ?_) F
    rcases hT a with h | h
    · exact h
    · have := N.mul_mem hg h
      simpa using this
  · exact height_one_of_prime_index_pure_aux N T hab hidx g hg hT F

/-- **Index two** (Pin–Straubing–Thérien 1992, Theorem 7.6, restricted to groups). -/
theorem height_one_of_abelian_index_two [Finite Alphabet] {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hidx : N.index = 2)
    (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have hN : N ≠ ⊤ := by
    intro h
    rw [← Subgroup.index_eq_one, hidx] at h
    exact absurd h (by norm_num)
  obtain ⟨g, hg⟩ : ∃ g, g ∉ N := by
    by_contra h
    push Not at h
    exact hN (eq_top_iff.mpr fun x _ => h x)
  refine height_one_of_prime_index_pure N hab hidx g T (fun a => ?_) F
  by_cases ha : T (FreeMonoid.of a) ∈ N
  · exact Or.inl ha
  · right
    have hcard : Nat.card (G ⧸ N) = 2 := hidx
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : G ⧸ N)).mp hcard
    have h1 : ((g : G) : G ⧸ N) = y := hy _ (fun h => hg ((QuotientGroup.eq_one_iff _).mp h))
    have h2 : ((T (FreeMonoid.of a) : G) : G ⧸ N) = y :=
      hy _ (fun h => ha ((QuotientGroup.eq_one_iff _).mp h))
    exact QuotientGroup.eq.mp (h1.trans h2.symm)

lemma zpowers_comm {G : Type} [Group G] (c : G) :
    ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Subgroup.zpowers c, x * y = y * x := by
  intro x hx y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_add, ← zpow_add, add_comm]

/-- **Dicyclic groups**, in particular `QuaternionGroup 3` (order 12): the cyclic subgroup
generated by `a 1` is normal of index two. -/
theorem height_one_quaternionGroup [Finite Alphabet] (n : ℕ) [NeZero n]
    (T : FreeMonoid Alphabet →* QuaternionGroup n) (F : Set (QuaternionGroup n)) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  set N := Subgroup.zpowers (QuaternionGroup.a 1 : QuaternionGroup n)
  have hidx : N.index = 2 := by
    have h := N.index_mul_card
    rw [Nat.card_zpowers, QuaternionGroup.orderOf_a_one, Nat.card_eq_fintype_card,
      QuaternionGroup.card] at h
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have : N.index * (2 * n) = 2 * (2 * n) := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right (by omega) this
  have := Subgroup.normal_of_index_eq_two hidx
  exact height_one_of_abelian_index_two N (zpowers_comm _) hidx T F

theorem height_one_quaternionGroup_three [Finite Alphabet]
    (T : FreeMonoid Alphabet →* QuaternionGroup 3) (F : Set (QuaternionGroup 3)) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 :=
  height_one_quaternionGroup 3 T F

/-- **Dihedral groups.** -/
theorem height_one_dihedralGroup [Finite Alphabet] (n : ℕ) [NeZero n]
    (T : FreeMonoid Alphabet →* DihedralGroup n) (F : Set (DihedralGroup n)) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  set N := Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n)
  have hidx : N.index = 2 := by
    have h := N.index_mul_card
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at h
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have : N.index * n = 2 * n := by rw [h]
    exact Nat.eq_of_mul_eq_mul_right hn this
  have := Subgroup.normal_of_index_eq_two hidx
  exact height_one_of_abelian_index_two N (zpowers_comm _) hidx T F

/-- **`A₄` with letters in `V ∪ σV`**, where `V` is the Klein four subgroup and `σ` is any fixed
element (for instance a 3-cycle). -/
theorem height_one_alternatingGroup_four_pure [Finite Alphabet] (σ : alternatingGroup (Fin 4))
    (T : FreeMonoid Alphabet →* alternatingGroup (Fin 4))
    (hT : ∀ a, T (FreeMonoid.of a) ∈ alternatingGroup.kleinFour (Fin 4) ∨
      σ⁻¹ * T (FreeMonoid.of a) ∈ alternatingGroup.kleinFour (Fin 4))
    (F : Set (alternatingGroup (Fin 4))) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have h4 : Nat.card (Fin 4) = 4 := by simp
  have := alternatingGroup.normal_kleinFour h4
  have hK := alternatingGroup.kleinFour_isKleinFour h4
  have hab : ∀ x ∈ alternatingGroup.kleinFour (Fin 4), ∀ y ∈ alternatingGroup.kleinFour (Fin 4),
      x * y = y * x := by
    intro x hx y hy
    have := hK.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hidx : (alternatingGroup.kleinFour (Fin 4)).index = 3 := by
    have h := (alternatingGroup.kleinFour (Fin 4)).index_mul_card
    rw [hK.card_four, nat_card_alternatingGroup, h4] at h
    norm_num [Nat.factorial] at h
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact height_one_of_prime_index_pure _ hab hidx σ T hT F

end GeneralizedStarHeight
