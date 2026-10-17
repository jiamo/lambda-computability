import Start.GroupOrderLtTwentyFour
import Start.StarHeightIndexFour

/-!
# The groups of order `20` excluded by the centralizer hypothesis are `F₂₀`

* `mulEquiv_F20_of_centralizer`: if `|G| = 20` and some Sylow `5`-subgroup `P` has
  `|C(P)| = 5`, then `G ≃* F₂₀`.  The Sylow `5`-subgroup `P = ⟨x⟩` is normal and self-centralizing,
  so some `y` conjugates `x` to `x²` (counting: at most `5` elements conjugate `x` to `x` and at most
  `5` to `x⁻¹`, and `x ↦ x³` gives `x ↦ x²` after cubing); then `y⁴ = 1`, and
  `⟨b, a⟩ ↦ x^b y^(log₂ a)` is an injective morphism `F₂₀ →* G` (`GroupF20.toG`,
  `GroupF20.toG_injective`), hence an isomorphism.

The star-height consequences are in `Start/StarHeightOrderLtTwentyFourF20.lean`.
-/

namespace GeneralizedStarHeight

namespace GroupF20

open Subgroup

variable {G : Type*} [Group G]

/-- The discrete logarithm to base `2` in `(ZMod 5)ˣ`. -/
def dlog2 (a : (ZMod 5)ˣ) : ℕ :=
  if (a : ZMod 5) = 1 then 0 else if (a : ZMod 5) = 2 then 1 else if (a : ZMod 5) = 4 then 2 else 3

lemma dlog2_check : ∀ (b₁ b₂ : ZMod 5) (a₁ a₂ : (ZMod 5)ˣ),
    (b₁.val + 2 ^ dlog2 a₁ * b₂.val) % 5 = (((a₁ : ZMod 5) * b₂ + b₁).val) % 5 ∧
      (dlog2 a₁ + dlog2 a₂) % 4 = dlog2 (a₁ * a₂) % 4 := by
  decide

lemma dlog2_lt (a : (ZMod 5)ˣ) : dlog2 a < 4 := by
  unfold dlog2
  split_ifs <;> norm_num

lemma dlog2_eq_zero : ∀ a : (ZMod 5)ˣ, dlog2 a = 0 → a = 1 := by decide

lemma pow_two_dlog : ∀ j : ℕ, j < 4 → (2 ^ j - 1) % 5 = 0 → j = 0 := by decide

/-- `y x^n y⁻¹ = x^(cn)` from `y x y⁻¹ = x^c`. -/
lemma conj_pow {x y : G} {c : ℕ} (hxy : y * x * y⁻¹ = x ^ c) (n : ℕ) :
    y * x ^ n * y⁻¹ = x ^ (c * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have : y * x ^ (n + 1) * y⁻¹ = (y * x ^ n * y⁻¹) * (y * x * y⁻¹) := by group
      rw [this, ih, hxy, ← pow_add]
      ring_nf

lemma conj_pow_pow {x y : G} {c : ℕ} (hxy : y * x * y⁻¹ = x ^ c) (j n : ℕ) :
    y ^ j * x ^ n * (y ^ j)⁻¹ = x ^ (c ^ j * n) := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
      have : y ^ (j + 1) * x ^ n * (y ^ (j + 1))⁻¹ = y ^ j * (y * x ^ n * y⁻¹) * (y ^ j)⁻¹ := by
        group
      rw [this, conj_pow hxy, ih, pow_succ]
      ring_nf

lemma swap_pow {x y : G} (hxy : y * x * y⁻¹ = x ^ 2) (j n : ℕ) :
    y ^ j * x ^ n = x ^ (2 ^ j * n) * y ^ j := by
  rw [← conj_pow_pow hxy]
  group

/-- The morphism `F₂₀ →* G`, `⟨b, a⟩ ↦ x^b y^(log₂ a)`. -/
def toG (x y : G) (hx : x ^ 5 = 1) (hy : y ^ 4 = 1) (hxy : y * x * y⁻¹ = x ^ 2) : F20 →* G :=
  MonoidHom.mk' (fun f => x ^ f.b.val * y ^ dlog2 f.a) fun f g => by
    have hxm : ∀ m n : ℕ, m % 5 = n % 5 → x ^ m = x ^ n := fun m n h => by
      rw [← Nat.mod_add_div m 5, ← Nat.mod_add_div n 5, pow_add, pow_add, pow_mul, pow_mul, hx,
        one_pow, one_pow, h]
    have hym : ∀ m n : ℕ, m % 4 = n % 4 → y ^ m = y ^ n := fun m n h => by
      rw [← Nat.mod_add_div m 4, ← Nat.mod_add_div n 4, pow_add, pow_add, pow_mul, pow_mul, hy,
        one_pow, one_pow, h]
    obtain ⟨h1, h2⟩ := dlog2_check f.b g.b f.a g.a
    show x ^ (f * g).b.val * y ^ dlog2 (f * g).a =
      (x ^ f.b.val * y ^ dlog2 f.a) * (x ^ g.b.val * y ^ dlog2 g.a)
    rw [show (f * g).b = (f.a : ZMod 5) * g.b + f.b from rfl, show (f * g).a = f.a * g.a from rfl]
    rw [show x ^ f.b.val * y ^ dlog2 f.a * (x ^ g.b.val * y ^ dlog2 g.a) =
        x ^ f.b.val * (y ^ dlog2 f.a * x ^ g.b.val) * y ^ dlog2 g.a by group,
      swap_pow hxy, show x ^ f.b.val * (x ^ (2 ^ dlog2 f.a * g.b.val) * y ^ dlog2 f.a) *
        y ^ dlog2 g.a = x ^ (f.b.val + 2 ^ dlog2 f.a * g.b.val) * y ^ (dlog2 f.a + dlog2 g.a) by
        rw [pow_add, pow_add]; group]
    rw [hxm _ _ h1.symm, hym _ _ h2.symm]

/-- `toG` is injective. -/
lemma toG_injective {x y : G} (hx5 : orderOf x = 5) (hy : y ^ 4 = 1)
    (hxy : y * x * y⁻¹ = x ^ 2) :
    Function.Injective (toG x y (hx5 ▸ pow_orderOf_eq_one x) hy hxy) := by
  rw [injective_iff_map_eq_one]
  intro f hf
  change x ^ f.b.val * y ^ dlog2 f.a = 1 at hf
  have h1 : x ^ f.b.val = (y ^ dlog2 f.a)⁻¹ := eq_inv_of_mul_eq_one_left hf
  have h4 : (x ^ f.b.val) ^ 4 = 1 := by
    rw [h1, inv_pow, ← pow_mul, mul_comm, pow_mul, hy, one_pow, inv_one]
  have h5 : (x ^ f.b.val) ^ 5 = 1 := by
    have hx' : x ^ 5 = 1 := hx5 ▸ pow_orderOf_eq_one x
    rw [← pow_mul, mul_comm, pow_mul, hx', one_pow]
  have hxb : x ^ f.b.val = 1 := by
    have : (x ^ f.b.val) ^ 5 = (x ^ f.b.val) ^ 4 * x ^ f.b.val := pow_succ _ 4
    rw [h5, h4, one_mul] at this
    exact this.symm
  have hb : f.b = 0 := by
    have hd := orderOf_dvd_of_pow_eq_one hxb
    rw [hx5] at hd
    have hlt := ZMod.val_lt f.b
    rw [← ZMod.val_eq_zero]
    omega
  rw [hxb, one_mul] at hf
  have hconj := conj_pow_pow hxy (dlog2 f.a) 1
  rw [hf, one_mul, inv_one, mul_one, pow_one, mul_one] at hconj
  have hj : (2 ^ dlog2 f.a - 1) % 5 = 0 := by
    have hpos : 1 ≤ 2 ^ dlog2 f.a := Nat.one_le_two_pow
    have : x ^ (2 ^ dlog2 f.a - 1) = 1 := by
      have e : x ^ (2 ^ dlog2 f.a) = x ^ (2 ^ dlog2 f.a - 1) * x := by
        rw [← pow_succ, Nat.sub_add_cancel hpos]
      rw [← hconj] at e
      exact (mul_eq_right.mp e.symm)
    have hd := orderOf_dvd_of_pow_eq_one this
    rw [hx5] at hd
    exact Nat.mod_eq_zero_of_dvd hd
  have ha := dlog2_eq_zero f.a (pow_two_dlog _ (dlog2_lt _) hj)
  exact F20.ext hb ha

lemma xpow_red {x : G} (hx : x ^ 5 = 1) (r q : ℕ) : x ^ (r + 5 * q) = x ^ r := by
  rw [pow_add, pow_mul, hx, one_pow, mul_one]

/-- Some element conjugates `x` to `x²`, when `⟨x⟩` is normal of order `5`, self-centralizing, in a
group of order `20`. -/
lemma exists_conj_sq [Fintype G] (hG : Fintype.card G = 20) {x : G} (hx5 : orderOf x = 5)
    (hconj : ∀ g : G, ∃ n : ℕ, g * x * g⁻¹ = x ^ n)
    (hcent : ∀ g : G, g * x = x * g → g ∈ Subgroup.zpowers x) :
    ∃ y : G, y * x * y⁻¹ = x ^ 2 := by
  classical
  have hx' : x ^ 5 = 1 := hx5 ▸ pow_orderOf_eq_one x
  have hxm : ∀ m : ℕ, x ^ m = x ^ (m % 5) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m 5, pow_add, pow_mul, hx', one_pow, mul_one]
  by_contra hno
  push Not at hno
  -- every conjugate is `x` or `x⁴`
  have hcase : ∀ g : G, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x ^ 4 := by
    intro g
    obtain ⟨n, hn⟩ := hconj g
    rw [hxm] at hn
    have hlt : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases h : n % 5
    · exfalso
      rw [pow_zero] at hn
      have : x = 1 := by
        have := congrArg (fun z => g⁻¹ * z * g) hn
        simpa [mul_assoc] using this
      rw [this, orderOf_one] at hx5
      exact absurd hx5 (by norm_num)
    · exact Or.inl (by simpa using hn)
    · exact absurd hn (hno g)
    · exfalso
      have h3 := conj_pow_pow hn 3 1
      rw [show 3 ^ 3 * 1 = 2 + 5 * 5 by norm_num, xpow_red hx', pow_one] at h3
      exact hno _ h3
    · exact Or.inr hn
  -- at most `5` of each
  set S1 := Finset.univ.filter (fun g : G => g * x * g⁻¹ = x) with hS1
  set S4 := Finset.univ.filter (fun g : G => g * x * g⁻¹ = x ^ 4) with hS4
  have hcardZ : (Finset.univ.filter (fun g : G => g ∈ Subgroup.zpowers x)).card = 5 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_zpowers, hx5]
  have hS1le : S1.card ≤ 5 := by
    rw [← hcardZ]
    refine Finset.card_le_card fun g hg => ?_
    simp only [hS1, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    refine hcent g ?_
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [hg]
  have hS4le : S4.card ≤ S1.card := by
    rcases S4.eq_empty_or_nonempty with h | ⟨g0, hg0⟩
    · rw [h]; exact Nat.zero_le _
    · simp only [hS4, Finset.mem_filter, Finset.mem_univ, true_and] at hg0
      have hinv : g0⁻¹ * x * g0 = x ^ 4 := by
        have h16 := conj_pow_pow hg0 4 1
        rw [show 4 ^ 4 * 1 = 1 + 5 * 51 by norm_num, xpow_red hx', pow_one] at h16
        have e : g0⁻¹ * x * g0 = g0⁻¹ * (g0 ^ 4 * x * (g0 ^ 4)⁻¹) * g0 := by rw [h16]
        rw [e]
        have := conj_pow_pow hg0 3 1
        rw [show 4 ^ 3 * 1 = 4 + 5 * 12 by norm_num, xpow_red hx', pow_one] at this
        rw [show g0⁻¹ * (g0 ^ 4 * x * (g0 ^ 4)⁻¹) * g0 = g0 ^ 3 * x * (g0 ^ 3)⁻¹ by group, this]
      refine Finset.card_le_card_of_injOn (fun g => g0⁻¹ * g) (fun g hg => ?_)
        (fun a _ b _ hab => mul_left_cancel hab)
      simp only [hS4, hS1, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
      rw [show g0⁻¹ * g * x * (g0⁻¹ * g)⁻¹ = g0⁻¹ * (g * x * g⁻¹) * g0 by group, hg]
      have hinv' : g0⁻¹ * x * g0⁻¹⁻¹ = x ^ 4 := by rw [inv_inv]; exact hinv
      have h44 := conj_pow hinv' 4
      rw [inv_inv, show 4 * 4 = 1 + 5 * 3 by norm_num, xpow_red hx', pow_one] at h44
      exact h44
  have huniv : (Finset.univ : Finset G) ⊆ S1 ∪ S4 := fun g _ => by
    rcases hcase g with h | h
    · exact Finset.mem_union_left _ (by simp [hS1, h])
    · exact Finset.mem_union_right _ (by simp [hS4, h])
  have := (Finset.card_le_card huniv).trans (Finset.card_union_le _ _)
  rw [Finset.card_univ, hG] at this
  omega

end GroupF20

open GroupF20 GroupLtTwenty Subgroup in
/-- **A group of order `20` with a self-centralizing Sylow `5`-subgroup is `F₂₀`.** -/
theorem mulEquiv_F20_of_centralizer {G : Type*} [Group G] [Fintype G] (hG : Fintype.card G = 20)
    (P : Sylow 5 G) (hC : Nat.card (centralizer (P : Set G)) = 5) : Nonempty (G ≃* F20) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hGn : Nat.card G = 20 := by rw [Nat.card_eq_fintype_card, hG]
  have hP : Nat.card P = 5 := by
    simpa using card_sylow_eq P (k := 1) (by rw [hGn]; norm_num) (by rw [hGn]; norm_num)
  -- `P` is normal
  have hidx : (P : Subgroup G).index = 4 := by
    have := (P : Subgroup G).card_mul_index
    rw [hP, hGn] at this
    omega
  have hs := card_sylow_modEq_one 5 G
  have hd := P.card_dvd_index
  rw [hidx] at hd
  have hle : Nat.card (Sylow 5 G) ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
  have h1 : Nat.card (Sylow 5 G) = 1 := by
    unfold Nat.ModEq at hs
    interval_cases (Nat.card (Sylow 5 G)) <;> simp_all
  have : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp h1).1
  have hnormal : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  -- a generator
  obtain ⟨x0, hx0⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 (by rw [hP])
  set x : G := x0.1 with hxdef
  have hx5 : orderOf x = 5 := by rw [hxdef, Subgroup.orderOf_coe, hx0]
  have hxP : x ∈ (P : Subgroup G) := x0.2
  have hZP : Subgroup.zpowers x = (P : Subgroup G) := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxP) ?_
    rw [Nat.card_zpowers, hx5, hP]
  have hconj : ∀ g : G, ∃ n : ℕ, g * x * g⁻¹ = x ^ n := by
    intro g
    have hm : g * x * g⁻¹ ∈ Subgroup.zpowers x := hZP ▸ hnormal.conj_mem x hxP g
    obtain ⟨n, hn⟩ := (isOfFinOrder_of_finite x).mem_powers_iff_mem_zpowers.mpr hm
    exact ⟨n, hn.symm⟩
  have hPC : (P : Subgroup G) ≤ centralizer (P : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact subgroup_comm_of_card_prime (P : Subgroup G) hP b hb a ha
  have hCP : centralizer (P : Set G) = (P : Subgroup G) :=
    (Subgroup.eq_of_le_of_card_ge hPC (by rw [hC, hP])).symm
  have hcent : ∀ g : G, g * x = x * g → g ∈ Subgroup.zpowers x := by
    intro g hg
    rw [hZP, ← hCP, Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ Subgroup.zpowers x := by rw [hZP]; exact hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
    exact ((Commute.zpow_left hg.symm k)).eq
  obtain ⟨y, hxy⟩ := exists_conj_sq hG hx5 hconj hcent
  -- `y⁴ = 1`
  have hx' : x ^ 5 = 1 := hx5 ▸ pow_orderOf_eq_one x
  have hxm : ∀ m : ℕ, x ^ m = x ^ (m % 5) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m 5, pow_add, pow_mul, hx', one_pow, mul_one]
  have hy4 : y ^ 4 = 1 := by
    have h16 := conj_pow_pow hxy 4 1
    rw [show 2 ^ 4 * 1 = 1 + 5 * 3 by norm_num, xpow_red hx', pow_one] at h16
    have hc : y ^ 4 * x = x * y ^ 4 := by
      calc y ^ 4 * x = y ^ 4 * x * (y ^ 4)⁻¹ * y ^ 4 := by group
        _ = x * y ^ 4 := by rw [h16]
    obtain ⟨m, hm⟩ := (isOfFinOrder_of_finite x).mem_powers_iff_mem_zpowers.mpr (hcent _ hc)
    have hm' : x ^ m = y ^ 4 := hm
    have h2 := conj_pow hxy m
    rw [hm', show y * y ^ 4 * y⁻¹ = y ^ 4 by group, ← hm', two_mul, pow_add] at h2
    have : x ^ m = 1 := mul_left_cancel (h2.symm.trans (mul_one _).symm)
    rw [← hm', this]
  have hinj := toG_injective hx5 hy4 hxy
  have hbij : Function.Bijective (toG x y (hx5 ▸ pow_orderOf_eq_one x) hy4 hxy) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by rw [F20.card, hG]⟩
  exact ⟨(MulEquiv.ofBijective _ hbij).symm⟩

end GeneralizedStarHeight
