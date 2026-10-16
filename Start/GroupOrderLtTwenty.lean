import Mathlib

/-!
# Every group of order less than `20` has an abelian normal subgroup of index at most `3`

`exists_abelian_normal_index_le_three`: if `|G| < 20`, then `G` has an abelian normal subgroup of
index `1`, `2` or `3`.

* Orders `1`, `p`, `p²`: `G` is abelian.
* Orders `6, 10, 14, 18`: a subgroup of order `n / 2` (prime or the square of a prime) has index `2`.
* Order `15`: the Sylow `5`-subgroup is normal, cyclic and of index `3`.
* Orders `8`, `16`: centralizers, through `comm_of_le_central` (a subgroup `H` with a central
  subgroup `K` such that `|H| ≤ 2|K|` is abelian).
* Order `12`: if the Sylow `3`-subgroup `⟨a⟩` is normal, the centralizer of `a` has index at most
  `2`; otherwise the four Sylow `3`-subgroups have eight elements of order `3`, and the Sylow
  `2`-subgroup is the set of the remaining four elements, hence normal.
-/

namespace GeneralizedStarHeight

namespace GroupLtTwenty

open Subgroup

variable {G : Type*} [Group G]

/-- The conclusion: an abelian normal subgroup of index at most three. -/
def Good (G : Type*) [Group G] : Prop :=
  ∃ N : Subgroup G, N.Normal ∧ (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) ∧ N.index ≤ 3

lemma good_of_comm (h : ∀ x y : G, x * y = y * x) : Good G :=
  ⟨⊤, inferInstance, fun x _ y _ => h x y, by simp⟩

/-- An abelian subgroup of index at most two. -/
lemma good_of_comm_subgroup [Finite G] (H : Subgroup G) (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hcard : Nat.card G ≤ 2 * Nat.card H) : Good G := by
  have hi := H.index_mul_card
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : H.index ≤ 2 := by
    by_contra hc
    push Not at hc
    nlinarith
  rcases (show H.index = 1 ∨ H.index = 2 by omega) with h1 | h2
  · refine ⟨H, ?_, hH, by omega⟩
    rw [Subgroup.index_eq_one] at h1
    rw [h1]; infer_instance
  · exact ⟨H, Subgroup.normal_of_index_eq_two h2, hH, by omega⟩

/-- A proper subgroup has at most half the elements. -/
lemma two_mul_card_le_of_lt [Finite G] {K L : Subgroup G} (hKL : K ≤ L) (hne : K ≠ L) :
    2 * Nat.card K ≤ Nat.card L := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hKL
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hLpos : 0 < Nat.card L := Nat.card_pos
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hKL (by rw [hm, mul_one]))
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hm; omega
  have : 2 ≤ m := by omega
  rw [hm]; nlinarith

/-- **A subgroup with a large central subgroup is abelian.** -/
lemma comm_of_le_central [Finite G] (H K : Subgroup G) (hKH : K ≤ H)
    (hK : ∀ k ∈ K, ∀ x ∈ H, k * x = x * k) (hcard : Nat.card H ≤ 2 * Nat.card K) :
    ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
  by_cases heq : K = H
  · subst heq; intro x hx y hy; exact hK x hx y hy
  obtain ⟨h, hhH, hhK⟩ : ∃ h ∈ H, h ∉ K := by
    by_contra hc
    push Not at hc
    exact heq (le_antisymm hKH hc)
  have hcomm : ∀ x ∈ insert h (K : Set G), ∀ y ∈ insert h (K : Set G), x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact (hK y hy x hhH).symm
    · exact hK x hx y hhH
    · exact hK x hx y (hKH hy)
  have hLc := Subgroup.isMulCommutative_closure hcomm
  have hLH : closure (insert h (K : Set G)) ≤ H :=
    (Subgroup.closure_le H).mpr (Set.insert_subset hhH hKH)
  have hKL : K ≤ closure (insert h (K : Set G)) :=
    fun k hk => Subgroup.subset_closure (Set.mem_insert_of_mem _ hk)
  have hhL : h ∈ closure (insert h (K : Set G)) := Subgroup.subset_closure (Set.mem_insert _ _)
  have hne : K ≠ closure (insert h (K : Set G)) := fun e => hhK (e ▸ hhL)
  have h2 := two_mul_card_le_of_lt hKL hne
  have hLeq : closure (insert h (K : Set G)) = H :=
    Subgroup.eq_of_le_of_card_ge hLH (by omega)
  intro x hx y hy
  rw [← hLeq] at hx hy
  have := hLc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

/-- `⟨Z(G), g⟩` is abelian. -/
lemma closure_insert_center_comm (g : G) :
    ∀ x ∈ closure (insert g (center G : Set G)), ∀ y ∈ closure (insert g (center G : Set G)),
      x * y = y * x := by
  have hcomm : ∀ x ∈ insert g (center G : Set G), ∀ y ∈ insert g (center G : Set G),
      x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · rfl
      · exact ((Subgroup.mem_center_iff.mp hy) x)
    · exact ((Subgroup.mem_center_iff.mp hx) y).symm
  have hLc := Subgroup.isMulCommutative_closure hcomm
  intro x hx y hy
  exact congrArg Subtype.val (hLc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

/-- `⟨Z(G), g⟩` has at least `2 |Z(G)|` elements when `g` is not central. -/
lemma card_closure_insert_center [Finite G] (g : G) (hg : g ∉ center G) :
    2 * Nat.card (center G) ≤ Nat.card (closure (insert g (center G : Set G))) := by
  apply two_mul_card_le_of_lt
  · exact fun k hk => Subgroup.subset_closure (Set.mem_insert_of_mem _ hk)
  · intro e
    exact hg (e ▸ Subgroup.subset_closure (Set.mem_insert _ _))

lemma comm_of_card_center [Finite G] (h : Nat.card G ≤ 2 * Nat.card (center G)) :
    ∀ x y : G, x * y = y * x := by
  have := comm_of_le_central ⊤ (center G) le_top
    (fun k hk x _ => ((Subgroup.mem_center_iff.mp hk) x).symm) (by rwa [Subgroup.card_top])
  exact fun x y => this x trivial y trivial

/-- If `G` is not abelian, a noncentral `g` gives an abelian subgroup with `2 |Z(G)|` elements. -/
lemma good_of_card_center [Finite G] (h : Nat.card G ≤ 4 * Nat.card (center G)) : Good G := by
  by_cases hc : ∀ x y : G, x * y = y * x
  · exact good_of_comm hc
  obtain ⟨g, hg⟩ : ∃ g, g ∉ center G := by
    by_contra hn
    push Not at hn
    exact hc fun x y => ((Subgroup.mem_center_iff.mp (hn y)) x)
  exact good_of_comm_subgroup _ (closure_insert_center_comm g)
    (by have := card_closure_insert_center g hg; omega)

/-- A subgroup of prime order is abelian. -/
lemma subgroup_comm_of_card_prime {p : ℕ} [Fact p.Prime] (K : Subgroup G) (h : Nat.card K = p) :
    ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
  have : IsCyclic K := isCyclic_of_prime_card h
  intro x hx y hy
  exact congrArg Subtype.val ((IsCyclic.commGroup (α := K)).mul_comm ⟨x, hx⟩ ⟨y, hy⟩)

/-- A subgroup of order `p²` is abelian. -/
lemma subgroup_comm_of_card_sq {p : ℕ} [Fact p.Prime] (K : Subgroup G) (h : Nat.card K = p ^ 2) :
    ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
  have hc := IsPGroup.isMulCommutative_of_card_eq_prime_sq h
  intro x hx y hy
  exact congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

/-- Order `2m` with a subgroup of order `m` that is abelian. -/
lemma good_of_subgroup_half [Finite G] {m : ℕ} (hG : Nat.card G = 2 * m) (K : Subgroup G)
    (hK : Nat.card K = m) (hc : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) : Good G :=
  good_of_comm_subgroup K hc (by omega)

/-- The index of the centralizer of `x` is at most the number of possible conjugates of `x`. -/
lemma index_centralizer_le [Finite G] (x : G) (S : Set G) (hS : ∀ g, g * x * g⁻¹ ∈ S) :
    (centralizer {x}).index ≤ Nat.card S := by
  have hS' : Finite S := Set.toFinite S
  let f : G ⧸ centralizer {x} → S := Quotient.lift (fun g => ⟨g * x * g⁻¹, hS g⟩) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ centralizer {x} := QuotientGroup.leftRel_apply.mp hab
    rw [Subgroup.mem_centralizer_singleton_iff] at hab'
    apply Subtype.ext
    show a * x * a⁻¹ = b * x * b⁻¹
    calc a * x * a⁻¹ = a * (x * (a⁻¹ * b)) * b⁻¹ := by group
      _ = a * (a⁻¹ * b * x) * b⁻¹ := by rw [hab']
      _ = b * x * b⁻¹ := by group)
  have hf : Function.Injective f := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    have hab' : a * x * a⁻¹ = b * x * b⁻¹ := congrArg Subtype.val hab
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a⁻¹ * b * x = a⁻¹ * (b * x * b⁻¹) * b := by group
      _ = a⁻¹ * (a * x * a⁻¹) * b := by rw [hab']
      _ = x * (a⁻¹ * b) := by group
  exact Nat.card_le_card_of_injective f hf

/-- The center of a nontrivial `p`-group has at least `p` elements; here, two elements. -/
lemma two_le_card_center_of_two_pow [Finite G] {k : ℕ} (hk : 0 < k) (hG : Nat.card G = 2 ^ k) :
    2 ≤ Nat.card (center G) := by
  have hp : IsPGroup 2 G := IsPGroup.of_card hG
  have : Nontrivial G := by
    rw [← Finite.one_lt_card_iff_nontrivial, hG]
    exact Nat.one_lt_two_pow hk.ne'
  have := hp.center_nontrivial
  exact Finite.one_lt_card_iff_nontrivial.mpr this

/-- The order of a Sylow subgroup, from the exact power of `p` dividing `|G|`. -/
lemma card_sylow_eq [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) {k : ℕ}
    (hk : p ^ k ∣ Nat.card G) (hk1 : ¬ p ^ (k + 1) ∣ Nat.card G) : Nat.card P = p ^ k := by
  rw [P.card_eq_multiplicity]
  congr 1
  have hn : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h1 := (hp.out.pow_dvd_iff_le_factorization hn).mp hk
  have h2 : ¬ k + 1 ≤ (Nat.card G).factorization p := fun h =>
    hk1 ((hp.out.pow_dvd_iff_le_factorization hn).mpr h)
  omega

/-! ### The cases -/

lemma good_of_card_one [Finite G] (h : Nat.card G = 1) : Good G := by
  have := (Nat.card_eq_one_iff_unique.mp h).1
  exact good_of_comm fun x y => Subsingleton.elim _ _

lemma good_of_card_prime [Finite G] {p : ℕ} [Fact p.Prime] (h : Nat.card G = p) : Good G := by
  have := subgroup_comm_of_card_prime (⊤ : Subgroup G) (by rw [Subgroup.card_top, h])
  exact good_of_comm fun x y => this x trivial y trivial

lemma good_of_card_sq [Finite G] {p : ℕ} [Fact p.Prime] (h : Nat.card G = p ^ 2) : Good G := by
  have := subgroup_comm_of_card_sq (⊤ : Subgroup G) (by rw [Subgroup.card_top, h])
  exact good_of_comm fun x y => this x trivial y trivial

lemma good_of_card_two_mul_prime [Finite G] {q : ℕ} [Fact q.Prime] (h : Nat.card G = 2 * q) :
    Good G := by
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) q (n := 1)
    (by rw [h, pow_one]; exact dvd_mul_left q 2)
  rw [pow_one] at hK
  exact good_of_subgroup_half h K hK (subgroup_comm_of_card_prime K hK)

lemma good_of_card_two_mul_sq [Finite G] {q : ℕ} [Fact q.Prime] (h : Nat.card G = 2 * q ^ 2) :
    Good G := by
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) q (n := 2)
    (by rw [h]; exact dvd_mul_left _ 2)
  exact good_of_subgroup_half h K hK (subgroup_comm_of_card_sq K hK)

lemma good_of_card_eight [Finite G] (h : Nat.card G = 8) : Good G := by
  have := two_le_card_center_of_two_pow (G := G) (k := 3) (by norm_num) (by rw [h]; norm_num)
  exact good_of_card_center (by omega)

lemma good_of_card_fifteen [Finite G] (h : Nat.card G = 15) : Good G := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 G) := inferInstance
  have hP : Nat.card P = 5 := by
    simpa using card_sylow_eq P (k := 1) (by rw [h]; norm_num) (by rw [h]; norm_num)
  have hidx : (P : Subgroup G).index = 3 := by
    have := (P : Subgroup G).card_mul_index
    rw [hP, h] at this
    omega
  have hs := card_sylow_modEq_one 5 G
  have hd := P.card_dvd_index
  rw [hidx] at hd
  have hpos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
  have hle : Nat.card (Sylow 5 G) ≤ 3 := Nat.le_of_dvd (by norm_num) hd
  have h1 : Nat.card (Sylow 5 G) = 1 := by
    unfold Nat.ModEq at hs
    interval_cases (Nat.card (Sylow 5 G)) <;> simp_all
  have : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp h1).1
  exact ⟨P, Sylow.normal_of_subsingleton P, subgroup_comm_of_card_prime _ hP, by omega⟩

/-- `⟨Z(G), x⟩` lies in the centralizer of `x` and is central there. -/
lemma closure_insert_center_le_centralizer (x : G) :
    closure (insert x (center G : Set G)) ≤ centralizer (centralizer ({x} : Set G) : Set G) := by
  rw [Subgroup.closure_le]
  intro k hk
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro h hh
  rcases hk with rfl | hk
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hh)
  · exact ((Subgroup.mem_center_iff.mp hk) h)

lemma good_of_card_sixteen [Finite G] (h : Nat.card G = 16) : Good G := by
  have hZ2 := two_le_card_center_of_two_pow (G := G) (k := 4) (by norm_num) (by rw [h]; norm_num)
  by_cases hZ4 : 4 ≤ Nat.card (center G)
  · exact good_of_card_center (by omega)
  have hZ : Nat.card (center G) = 2 := by
    have hd : Nat.card (center G) ∣ 16 := h ▸ Subgroup.card_subgroup_dvd_card _
    have : Nat.card (center G) ≠ 3 := by rintro e; rw [e] at hd; norm_num at hd
    omega
  by_cases hc : ∀ x y : G, x * y = y * x
  · exact good_of_comm hc
  -- the quotient by the center has a nontrivial center
  have hQ : Nat.card (G ⧸ center G) = 8 := by
    have := (center G).card_mul_index
    rw [hZ, h] at this
    rw [← Subgroup.index]
    omega
  have hQZ := two_le_card_center_of_two_pow (G := G ⧸ center G) (k := 3) (by norm_num)
    (by rw [hQ]; norm_num)
  have : Nontrivial (center (G ⧸ center G)) := Finite.one_lt_card_iff_nontrivial.mp hQZ
  obtain ⟨c, hc1⟩ := exists_ne (1 : center (G ⧸ center G))
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (c : G ⧸ center G)
  have hxZ : x ∉ center G := by
    intro hxz
    apply hc1
    apply Subtype.ext
    rw [← hx]
    exact (QuotientGroup.eq_one_iff x).mpr hxz
  have hconj : ∀ y : G, y * x * y⁻¹ * x⁻¹ ∈ center G := by
    intro y
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hy := Subgroup.mem_center_iff.mp c.2 (y : G ⧸ center G)
    show (y : G ⧸ center G) * QuotientGroup.mk x * (y : G ⧸ center G)⁻¹ *
      (QuotientGroup.mk x)⁻¹ = 1
    rw [hx, hy]
    group
  have hidx : (centralizer ({x} : Set G)).index ≤ 2 := by
    have := index_centralizer_le x ((fun z => z * x) '' (center G : Set G)) (fun y =>
      ⟨y * x * y⁻¹ * x⁻¹, hconj y, by group⟩)
    refine this.trans ?_
    calc Nat.card ((fun z => z * x) '' (center G : Set G)) ≤ Nat.card (center G : Set G) :=
          Nat.card_image_le (Set.toFinite _)
      _ = 2 := hZ
  have hne : centralizer ({x} : Set G) ≠ ⊤ := by
    intro e
    apply hxZ
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ centralizer ({x} : Set G) := e ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  have hidx1 : (centralizer ({x} : Set G)).index ≠ 1 := fun e => hne (Subgroup.index_eq_one.mp e)
  have hidx0 : (centralizer ({x} : Set G)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hC : Nat.card (centralizer ({x} : Set G)) = 8 := by
    have := (centralizer ({x} : Set G)).card_mul_index
    rw [h] at this
    have h2 : (centralizer ({x} : Set G)).index = 2 := by omega
    rw [h2] at this
    omega
  have hKC : closure (insert x (center G : Set G)) ≤ centralizer ({x} : Set G) := by
    rw [Subgroup.closure_le]
    intro k hk
    rcases hk with rfl | hk
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_center_iff.mp hk) x).symm
  have hcent := closure_insert_center_le_centralizer x
  have hK := card_closure_insert_center x hxZ
  have hCcomm := comm_of_le_central (centralizer ({x} : Set G))
    (closure (insert x (center G : Set G))) hKC
    (fun k hk y hy => (Subgroup.mem_centralizer_iff.mp (hcent hk) y hy).symm) (by omega)
  exact good_of_comm_subgroup _ hCcomm (by omega)

lemma orderOf_eq_of_mem_card_prime {p : ℕ} [hp : Fact p.Prime] (P : Subgroup G)
    (hP : Nat.card P = p) {a : G} (haP : a ∈ P) (ha : a ≠ 1) : orderOf a = p := by
  have hd : orderOf a ∣ p := hP ▸ Subgroup.orderOf_dvd_natCard P haP
  rcases (Nat.dvd_prime hp.out).mp hd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) ha
  · exact h

lemma eq_zpowers_of_card_prime [Finite G] {p : ℕ} [Fact p.Prime] (P : Subgroup G)
    (hP : Nat.card P = p) {a : G} (haP : a ∈ P) (ha : a ≠ 1) : Subgroup.zpowers a = P := by
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haP)
  rw [Nat.card_zpowers, orderOf_eq_of_mem_card_prime P hP haP ha, hP]

/-- Order `12`, Sylow `3`-subgroup normal: the centralizer of its generator. -/
lemma good_of_card_twelve_of_normal [Finite G] (h : Nat.card G = 12) (P : Subgroup G) [P.Normal]
    (hP : Nat.card P = 3) : Good G := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨a, haP, ha1⟩ : ∃ a ∈ P, a ≠ 1 := by
    by_contra hc
    push Not at hc
    have : P = ⊥ := (Subgroup.eq_bot_iff_forall P).mpr hc
    rw [this, Subgroup.card_bot] at hP
    omega
  have hS : ∀ g, g * a * g⁻¹ ∈ (P : Set G) \ {1} := by
    intro g
    refine ⟨‹P.Normal›.conj_mem a haP g, ?_⟩
    intro h1
    apply ha1
    have h1' : g * a * g⁻¹ = 1 := h1
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h1']; group
  have hcardS : Nat.card ↥((P : Set G) \ {1}) = 2 := by
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem P.one_mem,
      ← Nat.card_coe_set_eq]
    show Nat.card P - 1 = 2
    rw [hP]
  have hidx : (centralizer ({a} : Set G)).index ≤ 2 := hcardS ▸ index_centralizer_le a _ hS
  have hK : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_of_mem_card_prime P hP haP ha1]
  have hKC : Subgroup.zpowers a ≤ centralizer ({a} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hcent : ∀ k ∈ Subgroup.zpowers a, ∀ y ∈ centralizer ({a} : Set G), k * y = y * k := by
    intro k hk y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hy' : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    exact (Commute.zpow_left hy'.symm m).eq
  have hidx0 : (centralizer ({a} : Set G)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmul := (centralizer ({a} : Set G)).card_mul_index
  rw [h] at hmul
  rcases (show (centralizer ({a} : Set G)).index = 1 ∨ (centralizer ({a} : Set G)).index = 2 by
    omega) with h1 | h2
  · -- `a` is central
    have hZ : Subgroup.zpowers a ≤ center G := by
      rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
      intro g
      have : g ∈ centralizer ({a} : Set G) := (Subgroup.index_eq_one.mp h1) ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp this
    have := Subgroup.card_le_of_le hZ
    exact good_of_card_center (by omega)
  · rw [h2] at hmul
    have hC := comm_of_le_central _ _ hKC hcent (by omega)
    exact good_of_comm_subgroup _ hC (by omega)

/-- Order `12`, four Sylow `3`-subgroups: the Sylow `2`-subgroup is unique. -/
lemma good_of_card_twelve_of_four [Finite G] (h : Nat.card G = 12)
    (h4 : Nat.card (Sylow 3 G) = 4) : Good G := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype (Sylow 3 G) := Fintype.ofFinite _
  have hP3 : ∀ P : Sylow 3 G, Nat.card P = 3 := fun P => by
    simpa using card_sylow_eq P (k := 1) (by rw [h]; norm_num) (by rw [h]; norm_num)
  have hfilter : ∀ H : Subgroup G,
      (Finset.univ.filter (fun g => g ∈ H)).card = Nat.card H := by
    intro H
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let A : Sylow 3 G → Finset G := fun P => Finset.univ.filter (fun g => g ∈ P ∧ g ≠ 1)
  have hA : ∀ P, (A P).card = 2 := by
    intro P
    have : A P = (Finset.univ.filter (fun g => g ∈ (P : Subgroup G))).erase 1 := by
      ext g
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [this, Finset.card_erase_of_mem (by simp [(P : Subgroup G).one_mem]), hfilter, hP3]
  have hdisj : ((Finset.univ : Finset (Sylow 3 G)) : Set (Sylow 3 G)).PairwiseDisjoint A := by
    intro P _ P' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro g hg hg'
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hg hg'
    apply hne
    apply Sylow.ext
    rw [← eq_zpowers_of_card_prime _ (hP3 P) hg.1 hg.2,
      ← eq_zpowers_of_card_prime _ (hP3 P') hg'.1 hg'.2]
  let U := (Finset.univ : Finset (Sylow 3 G)).biUnion A
  have hU : U.card = 8 := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun P _ => hA P), Finset.sum_const,
      Finset.card_univ, ← Nat.card_eq_fintype_card, h4]
    rfl
  have hQ4 : ∀ Q : Sylow 2 G, Nat.card Q = 4 := fun Q => by
    simpa using card_sylow_eq Q (k := 2) (by rw [h]; norm_num) (by rw [h]; norm_num)
  have hQU : ∀ Q : Sylow 2 G,
      Finset.univ.filter (fun g => g ∈ (Q : Subgroup G)) = Finset.univ \ U := by
    intro Q
    apply Finset.eq_of_subset_of_card_le
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, U, Finset.mem_biUnion, A,
        Finset.mem_filter, not_exists, not_and]
      intro P hgP hg1
      have h3 : orderOf g ∣ 3 := hP3 P ▸ Subgroup.orderOf_dvd_natCard _ hgP
      have h4' : orderOf g ∣ 4 := hQ4 Q ▸ Subgroup.orderOf_dvd_natCard _ hg
      have : orderOf g = 1 := Nat.dvd_one.mp (by simpa using Nat.dvd_gcd h3 h4')
      exact hg1 (orderOf_eq_one_iff.mp this)
    · rw [Finset.card_univ_sdiff, hU, hfilter, hQ4, ← Nat.card_eq_fintype_card, h]
  have : Subsingleton (Sylow 2 G) := ⟨fun Q Q' => by
    apply Sylow.ext
    ext g
    have := Finset.ext_iff.mp ((hQU Q).trans (hQU Q').symm) g
    simpa using this⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 G) := inferInstance
  refine ⟨Q, Sylow.normal_of_subsingleton Q, subgroup_comm_of_card_sq (p := 2) _ (hQ4 Q), ?_⟩
  have := (Q : Subgroup G).card_mul_index
  rw [hQ4, h] at this
  omega

lemma good_of_card_twelve [Finite G] (h : Nat.card G = 12) : Good G := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 G) := inferInstance
  have hP : Nat.card P = 3 := by
    simpa using card_sylow_eq P (k := 1) (by rw [h]; norm_num) (by rw [h]; norm_num)
  have hidx : (P : Subgroup G).index = 4 := by
    have := (P : Subgroup G).card_mul_index
    rw [hP, h] at this
    omega
  have hs := card_sylow_modEq_one 3 G
  have hd := P.card_dvd_index
  rw [hidx] at hd
  have hpos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
  have hle : Nat.card (Sylow 3 G) ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  have h14 : Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 := by
    unfold Nat.ModEq at hs
    interval_cases (Nat.card (Sylow 3 G)) <;> simp_all
  rcases h14 with h1 | h4
  · have : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp h1).1
    have := Sylow.normal_of_subsingleton P
    exact good_of_card_twelve_of_normal h P hP
  · exact good_of_card_twelve_of_four h h4

/-- **Every group of order less than `20` has an abelian normal subgroup of index at most `3`.** -/
theorem good_of_card_lt_twenty [Finite G] (hG : Nat.card G < 20) : Good G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have f2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have f3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have f5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have f7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have f11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have f13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have f17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have f19 : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  generalize hn : Nat.card G = n at hG hpos
  interval_cases n
  · exact good_of_card_one hn
  · exact good_of_card_prime (p := 2) hn
  · exact good_of_card_prime (p := 3) hn
  · exact good_of_card_sq (p := 2) (by rw [hn]; norm_num)
  · exact good_of_card_prime (p := 5) hn
  · exact good_of_card_two_mul_prime (q := 3) (by rw [hn])
  · exact good_of_card_prime (p := 7) hn
  · exact good_of_card_eight hn
  · exact good_of_card_sq (p := 3) (by rw [hn]; norm_num)
  · exact good_of_card_two_mul_prime (q := 5) (by rw [hn])
  · exact good_of_card_prime (p := 11) hn
  · exact good_of_card_twelve hn
  · exact good_of_card_prime (p := 13) hn
  · exact good_of_card_two_mul_prime (q := 7) (by rw [hn])
  · exact good_of_card_fifteen hn
  · exact good_of_card_sixteen hn
  · exact good_of_card_prime (p := 17) hn
  · exact good_of_card_two_mul_sq (q := 3) (by rw [hn]; norm_num)
  · exact good_of_card_prime (p := 19) hn

end GroupLtTwenty

open GroupLtTwenty in
/-- **Every finite group of order less than `20` has an abelian normal subgroup of index at most
`3`.** -/
theorem exists_abelian_normal_index_le_three {G : Type} [Group G] [Fintype G]
    (hG : Fintype.card G < 20) :
    ∃ N : Subgroup G, N.Normal ∧ (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) ∧ N.index ≤ 3 :=
  good_of_card_lt_twenty (by rwa [Nat.card_eq_fintype_card])

end GeneralizedStarHeight
