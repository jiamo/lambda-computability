import Start.StarHeightOrderEightCores

/-!
# `L(aabb, k, 2)` has star height at most one

* `aabb_z4z2_cast_z4` (identity (I)): modulo `2`, the two `Z₄ × Z₂` counts of `aabb` are a sum
  of three `Z₄` counts and a function of `(|u|_a mod 8, |u|_b mod 8)`:
  `#{i : u_i = b, A_i mod 4 ∈ {2,3}, B_i odd} ≡ m₁ + p₁ + r₃ + ⌊(B + 2)/4⌋ + A·[B ≡ 3 mod 4]`,
  with `m₁ = #{i : u_i = b, A_i ≡ 1}`, `p₁ = #{i : u_i = b, A_i + B_i ≡ 1}` and
  `r₃ = #{i : u_i = a, B_i ≡ 3}` (all modulo `4`).
* `goodMod_aabb_two`, `goodMod_bbaa_two`, `height_one_aabb_mod_two`: unconditionally.
* `height_one_two_letters_length_four_mod_two_all` and
  `height_one_two_letters_length_four_mod_prime_all`: every word of length four over two letters,
  modulo every prime.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

variable {α : Type u} [DecidableEq α]

/-- `ρ_m`: `a ↦ 1`, other letters `↦ 0`, in `Z₄`. -/
def aabbRhoM (a : α) (y : α) : Multiplicative (ZMod 4) :=
  if y = a then Multiplicative.ofAdd 1 else 1

/-- `ρ_p`: `a, b ↦ 1`, other letters `↦ 0`, in `Z₄`. -/
def aabbRhoP (a b : α) (y : α) : Multiplicative (ZMod 4) :=
  if y = a then Multiplicative.ofAdd 1 else if y = b then Multiplicative.ofAdd 1 else 1

lemma prod_aabbRhoM (a : α) (v : List α) :
    (v.map (aabbRhoM a)).prod = Multiplicative.ofAdd ((v.count a : ℕ) : ZMod 4) := by
  induction v using List.reverseRecOn with
  | nil => rfl
  | append_singleton v z ih =>
      rw [List.map_append, List.prod_append, ih, count_snoc_ite]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      unfold aabbRhoM
      by_cases hza : z = a
      · simp only [if_pos hza, ← ofAdd_add]; push_cast; rfl
      · simp only [if_neg hza, mul_one, Nat.add_zero]

lemma prod_aabbRhoP {a b : α} (hab : a ≠ b) (v : List α) :
    (v.map (aabbRhoP a b)).prod =
      Multiplicative.ofAdd (((v.count a : ℕ) : ZMod 4) + ((v.count b : ℕ) : ZMod 4)) := by
  induction v using List.reverseRecOn with
  | nil => rfl
  | append_singleton v z ih =>
      rw [List.map_append, List.prod_append, ih, count_snoc_ite, count_snoc_ite]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      unfold aabbRhoP
      by_cases hza : z = a
      · subst hza
        simp only [if_true, if_neg hab, ← ofAdd_add]; push_cast; congr 1; ring
      · by_cases hzb : z = b
        · subst hzb
          simp only [if_neg hza, if_true, ← ofAdd_add]; push_cast; congr 1; ring
        · simp only [if_neg hza, if_neg hzb, mul_one, Nat.add_zero]

/-- The step of identity (I) when a `b` is appended, as a function of `A` and `B`. -/
lemma aabbI_step_b (A B : ℕ) :
    (if Multiplicative.ofAdd ((A : ZMod 4), (B : ZMod 2)) = z4z2G1 then 1 else 0 : ZMod 2) +
      (if Multiplicative.ofAdd ((A : ZMod 4), (B : ZMod 2)) = z4z2G2 then 1 else 0 : ZMod 2) =
    (if (Multiplicative.ofAdd (A : ZMod 4) : Multiplicative (ZMod 4)) = Multiplicative.ofAdd 1
        then 1 else 0 : ZMod 2) +
      (if (Multiplicative.ofAdd ((A : ZMod 4) + (B : ZMod 4)) : Multiplicative (ZMod 4)) =
        Multiplicative.ofAdd 1 then 1 else 0 : ZMod 2) +
      ((((B + 1) + 2) / 4 : ℕ) : ZMod 2) - (((B + 2) / 4 : ℕ) : ZMod 2) +
      (A : ZMod 2) * ((if (B + 1) % 4 = 3 then 1 else 0) - (if B % 4 = 3 then 1 else 0)) := by
  have e1 : (A : ZMod 4) = ((A % 4 : ℕ) : ZMod 4) := (ZMod.natCast_mod A 4).symm
  have e2 : (A : ZMod 2) = ((A % 4 : ℕ) : ZMod 2) := natCast_eq_of_mod_eq (M := 2) dvd_rfl (by omega)
  have e3 : (B : ZMod 4) = ((B % 8 : ℕ) : ZMod 4) :=
    natCast_eq_of_mod_eq (M := 4) dvd_rfl (by omega)
  have e4 : (B : ZMod 2) = ((B % 8 : ℕ) : ZMod 2) :=
    natCast_eq_of_mod_eq (M := 2) dvd_rfl (by omega)
  have e5 : ((((B + 1) + 2) / 4 : ℕ) : ZMod 2) = ((((B % 8 + 1) + 2) / 4 : ℕ) : ZMod 2) :=
    natCast_eq_of_mod_eq (M := 2) dvd_rfl (by omega)
  have e6 : (((B + 2) / 4 : ℕ) : ZMod 2) = (((B % 8 + 2) / 4 : ℕ) : ZMod 2) :=
    natCast_eq_of_mod_eq (M := 2) dvd_rfl (by omega)
  have e7 : (B + 1) % 4 = (B % 8 + 1) % 4 := by omega
  have e8 : B % 4 = (B % 8) % 4 := by omega
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  have hA := Nat.mod_lt A (show 0 < 4 by norm_num)
  have hB := Nat.mod_lt B (show 0 < 8 by norm_num)
  generalize A % 4 = r at hA ⊢
  generalize B % 8 = t at hB ⊢
  interval_cases r <;> interval_cases t <;> decide

/-- **Identity (I)**: modulo `2`,
`#{i : u_i = b, A_i mod 4 ∈ {2,3}, B_i odd} ≡ m₁ + p₁ + r₃ + ⌊(B + 2)/4⌋ + A·[B ≡ 3 mod 4]`. -/
theorem aabb_z4z2_cast_z4 {a b : α} (hab : a ≠ b) (u : List α) :
    ((hcount (aabbRho a b) z4z2G1 b u + hcount (aabbRho a b) z4z2G2 b u : ℕ) : ZMod 2) =
      hcount (aabbRhoM a) (Multiplicative.ofAdd 1) b u +
        hcount (aabbRhoP a b) (Multiplicative.ofAdd 1) b u +
        hcount (aabbRhoM b) (Multiplicative.ofAdd 3) a u +
        (((u.count b + 2) / 4 : ℕ) : ZMod 2) +
        (u.count a : ZMod 2) * (if u.count b % 4 = 3 then 1 else 0) := by
  induction u using List.reverseRecOn with
  | nil => simp [hcount]
  | append_singleton u z ih =>
      rw [hcount_snoc, hcount_snoc, hcount_snoc, hcount_snoc, hcount_snoc, count_snoc_ite,
        count_snoc_ite]
      have two : ∀ t : ZMod 2, t + t = 0 := by decide
      by_cases hza : z = a
      · subst hza
        simp only [if_true, if_neg hab, Nat.add_zero]
        rw [prod_aabbRhoM]
        push_cast at ih ⊢
        rw [ih]
        have h3 : (Multiplicative.ofAdd ((u.count b : ℕ) : ZMod 4) : Multiplicative (ZMod 4)) =
            Multiplicative.ofAdd 3 ↔ u.count b % 4 = 3 := by
          rw [EmbeddingLike.apply_eq_iff_eq]
          have : ((3 : ℕ) : ZMod 4) = 3 := rfl
          rw [← this, ZMod.natCast_eq_natCast_iff']
        simp only [h3]
        linear_combination (-(if u.count b % 4 = 3 then (1 : ZMod 2) else 0)) * two 1
      · by_cases hzb : z = b
        · subst hzb
          simp only [if_true, if_neg (Ne.symm hab), Nat.add_zero]
          rw [prod_aabbRho hab, prod_aabbRhoM, prod_aabbRhoP hab]
          have hs := aabbI_step_b (u.count a) (u.count z)
          push_cast at ih hs ⊢
          linear_combination ih + hs
        · simp only [if_neg hza, if_neg hzb, Nat.add_zero]
          exact ih

/-- The letter-count term of identity (I). -/
def aabbCtr (A B : ℕ) : ℕ := (B + 2) / 4 + A * (if B % 4 = 3 then 1 else 0)

lemma aabbCtr_mod (A B : ℕ) : aabbCtr (A % 8) (B % 8) % 2 = aabbCtr A B % 2 := by
  unfold aabbCtr
  have h : B % 8 % 4 = B % 4 := by omega
  rw [h]
  split_ifs <;> simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero] <;> omega

/-- The letter-count term is good modulo `2`. -/
lemma goodMod_aabbCtr [Finite α] (a b : α) :
    GoodMod 2 (fun u : List α => aabbCtr (u.count a) (u.count b)) := by
  intro k hk
  refine height_one_of_residues_univ (ι := Fin 2) ![fun u => u.count a, fun u => u.count b]
    (M := 8) (by norm_num) (fun i r hr => ?_) _ (fun z => aabbCtr (z 0) (z 1) % 2 = k) ?_
  · fin_cases i
    · exact goodCount_count a 8 r hr
    · exact goodCount_count b 8 r hr
  · intro w
    show aabbCtr _ _ % 2 = k ↔ aabbCtr (w.count a % 8) (w.count b % 8) % 2 = k
    rw [aabbCtr_mod]

/-- **`aabb` modulo `2` over any finite alphabet**, unconditionally. -/
theorem goodMod_aabb_two [Finite α] {a b : α} (hab : a ≠ b) : GoodMod 2 (scount [a, a, b, b]) := by
  refine (goodMod_aabb_iff_z4z2 hab).2 ?_
  refine goodMod_of_det (by norm_num) ![hcount (aabbRhoM a) (Multiplicative.ofAdd 1) b,
    hcount (aabbRhoP a b) (Multiplicative.ofAdd 1) b, hcount (aabbRhoM b) (Multiplicative.ofAdd 3) a,
    fun u => aabbCtr (u.count a) (u.count b)] (fun i => ?_) ?_
  · fin_cases i
    · exact fun k hk => hcoreModTwo_zmod_four.univ _ b _ k hk
    · exact fun k hk => hcoreModTwo_zmod_four.univ _ b _ k hk
    · exact fun k hk => hcoreModTwo_zmod_four.univ _ a _ k hk
    · exact goodMod_aabbCtr a b
  · intro u w h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, aabbCtr] at h0 h1 h2 h3
    have key : ∀ v : List α,
        ((hcount (aabbRho a b) z4z2G1 b v + hcount (aabbRho a b) z4z2G2 b v : ℕ) : ZMod 2) =
          hcount (aabbRhoM a) (Multiplicative.ofAdd 1) b v +
            hcount (aabbRhoP a b) (Multiplicative.ofAdd 1) b v +
            hcount (aabbRhoM b) (Multiplicative.ofAdd 3) a v +
            (((v.count b + 2) / 4 + v.count a * (if v.count b % 4 = 3 then 1 else 0) : ℕ) : ZMod 2) := by
      intro v
      rw [aabb_z4z2_cast_z4 hab v]
      push_cast
      split_ifs <;> ring
    rw [key u, key w, h0, h1, h2, h3]

/-- **`bbaa` modulo `2`**, unconditionally. -/
theorem goodMod_bbaa_two [Finite α] {a b : α} (hab : a ≠ b) : GoodMod 2 (scount [b, b, a, a]) :=
  (goodMod_xxyy_iff 2 hab).1 (goodMod_aabb_two hab)

/-- **`L(aabb, k, 2)` has star height at most one** (letters `a = 0`, `b = 1` of `Fin 2`). -/
theorem height_one_aabb_mod_two {k : ℕ} (hk : k < 2) :
    HasHeightAtMost {u : List (Fin 2) | scount [0, 0, 1, 1] u % 2 = k} 1 :=
  goodMod_aabb_two (α := Fin 2) (by decide) k hk

/-- **Every word of length four over two letters, modulo `2`.** -/
theorem height_one_two_letters_length_four_mod_two_all [Finite α] {x y : α} (hxy : x ≠ y)
    (w : List α) (hw : w.length = 4) (hxy' : ∀ z ∈ w, z = x ∨ z = y) {k : ℕ} (hk : k < 2) :
    HasHeightAtMost {u : List α | scount w u % 2 = k} 1 := by
  by_cases h1 : w = [x, x, y, y]
  · subst h1; exact goodMod_aabb_two hxy k hk
  by_cases h2 : w = [y, y, x, x]
  · subst h2; exact goodMod_bbaa_two hxy k hk
  exact height_one_two_letters_length_four_mod_two hxy w hw hxy' ⟨h1, h2⟩ hk

/-- **Every word of length four over two letters, modulo every prime.** -/
theorem height_one_two_letters_length_four_mod_prime_all [Finite α] (p : ℕ) [Fact p.Prime]
    (x y : α) (w : List α) (hw : w.length = 4) (hxy : ∀ z ∈ w, z = x ∨ z = y) {k : ℕ}
    (hk : k < p) : HasHeightAtMost {u : List α | scount w u % p = k} 1 := by
  by_cases hp : p = 2
  · subst hp
    by_cases hne : x = y
    · subst hne
      have hw' : w = List.replicate 4 x :=
        List.eq_replicate_iff.2 ⟨hw, fun z hz => (hxy z hz).elim id id⟩
      subst hw'
      exact (goodCount_scount_replicate x 4).goodMod 2 k hk
    · exact height_one_two_letters_length_four_mod_two_all hne w hw hxy hk
  · exact height_one_two_letters_length_four_mod_prime p hp x y w hw hxy hk

end GeneralizedStarHeight
