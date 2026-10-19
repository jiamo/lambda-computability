import Start.StarHeightCoreModTwo
import Start.StarHeightColouredPairs
import Start.StarHeightNilpotentFourTwo

/-!
# `aabb` and `abac` modulo `2` as letter-in-state counts on groups of order `8`

* `scount_aabb_eq_psum`: over `ℕ`, for `a ≠ b`,
  `scount [a,a,b,b] u = Σ_{i : u_i = b} C(A_i, 2) · (|u|_b − 1 − B_i)`.
* `scount_aabb_cast_z4z2`: modulo `2`,
  `scount [a,a,b,b] u ≡ (|u|_b + 1) · scount [a,a,b] u + hcount ρ g₁ b u + hcount ρ g₂ b u`
  on `Multiplicative (ZMod 4 × ZMod 2)`, with `ρ a = (1, 0)`, `ρ b = (0, 1)`, `g₁ = (2, 1)`,
  `g₂ = (3, 1)`.
* `aabb_mod_two_iff_z4z2`, `aabb_mod_two_of_core`, and
  `height_one_two_letters_length_four_mod_two_of_core`: every two-letter word of length four
  modulo `2`, from the `Z₄ × Z₂`-core modulo `2`.
* `Z2WrZ2 = (ZMod 2 → ZMod 2) ⋊ ZMod 2` (the dihedral group of order `8`) and
  `cpair_abac_cast_wreath`: modulo `2`,
  `cpair (parCol a) b c 1 0 u ≡ hcount ρ ⟨f₀₁, 1⟩ c u + hcount ρ ⟨f₁₁, 1⟩ c u`.
* `abac_mod_two_iff_wreath` and `abac_mod_two_of_core`: `L(abac, k, 2)` from the
  `Z₂ ≀ Z₂`-core modulo `2`.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

section Common

variable {α : Type u} [DecidableEq α] {H : Type}

/-- A prefix-product count is a `psum`. -/
lemma hcount_eq_psum [Monoid H] [DecidableEq H] (ρ : α → H) (g : H) (x : α) (u : List α) :
    hcount ρ g x u = psum x (fun v => if (v.map ρ).prod = g then 1 else 0) u := by
  classical
  unfold hcount psum
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : u[i]? = some x
  · by_cases h2 : ((u.take i).map ρ).prod = g
    · rw [if_pos ⟨h1, h2⟩, if_pos h1]; exact (if_pos h2).symm
    · rw [if_neg (fun h => h2 h.2), if_pos h1]; exact (if_neg h2).symm
  · rw [if_neg (fun h => h1 h.1), if_neg h1]

lemma hcount_snoc [Monoid H] [DecidableEq H] (ρ : α → H) (g : H) (x : α) (u : List α) (z : α) :
    hcount ρ g x (u ++ [z]) =
      hcount ρ g x u + if z = x then (if (u.map ρ).prod = g then 1 else 0) else 0 := by
  rw [hcount_eq_psum, hcount_eq_psum, psum_snoc]

/-- `psum` congruence using only the positions that read `x`. -/
lemma psum_congr_at (x : α) (g h : List α → ℕ) (u : List α)
    (hgh : ∀ i, u[i]? = some x → g (u.take i) = h (u.take i)) : psum x g u = psum x h u := by
  unfold psum
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : u[i]? = some x
  · rw [if_pos hi, if_pos hi, hgh i hi]
  · rw [if_neg hi, if_neg hi]

lemma count_take_lt_of_getElem? {x : α} {u : List α} {i : ℕ} (hi : u[i]? = some x) :
    (u.take i).count x < u.count x := by
  have hlt : i < u.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hi
    simp at hi
  have h1 : u.take (i + 1) = u.take i ++ [x] := by
    rw [List.take_add_one, hi]; rfl
  have h2 : (u.take (i + 1)).count x ≤ u.count x := (List.take_sublist _ u).count_le x
  rw [h1, List.count_append] at h2
  simp at h2
  omega

end Common

/-! ### `aabb` -/

section AABB

variable {α : Type u} [DecidableEq α]

/-- **`aabb` exactly**: `scount [a,a,b,b] u = Σ_{i : u_i = b} C(A_i, 2) · (|u|_b − 1 − B_i)`. -/
theorem scount_aabb_eq_psum {a b : α} (hab : a ≠ b) (u : List α) :
    scount [a, a, b, b] u =
      psum b (fun v => (v.count a).choose 2 * (u.count b - 1 - v.count b)) u := by
  induction u using List.reverseRecOn with
  | nil => simp [psum_nil]
  | append_singleton u z ih =>
      have e1 := scount_snoc b z u [a, a, b]
      simp only [List.cons_append, List.nil_append] at e1
      rw [e1, psum_snoc, count_snoc_ite]
      by_cases hz : z = b
      · subst hz
        simp only [if_true, Nat.add_sub_cancel, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
        have h3 : scount [a, a, z] u = psum z (fun v => (v.count a).choose 2) u := by
          rw [show [a, a, z] = [a, a] ++ [z] from rfl, scount_snoc_eq_psum]
          exact psum_congr _ _ _ _ fun j _ => scount_aa a _
        rw [ih, h3, ← psum_add]
        refine psum_congr_at _ _ _ _ fun i hi => ?_
        have := count_take_lt_of_getElem? hi
        rw [← Nat.mul_succ]
        congr 1
        omega
      · simp only [if_neg hz, Nat.add_zero]
        exact ih

/-- The letter map `a ↦ (1, 0)`, `b ↦ (0, 1)`, other letters `↦ 1`, into `Z₄ × Z₂`. -/
def aabbRho (a b : α) (y : α) : Multiplicative (ZMod 4 × ZMod 2) :=
  if y = a then Multiplicative.ofAdd (1, 0) else if y = b then Multiplicative.ofAdd (0, 1) else 1

/-- The state `(2, 1)` of `Z₄ × Z₂`. -/
def z4z2G1 : Multiplicative (ZMod 4 × ZMod 2) := Multiplicative.ofAdd (2, 1)

/-- The state `(3, 1)` of `Z₄ × Z₂`. -/
def z4z2G2 : Multiplicative (ZMod 4 × ZMod 2) := Multiplicative.ofAdd (3, 1)

lemma prod_aabbRho {a b : α} (hab : a ≠ b) (v : List α) :
    (v.map (aabbRho a b)).prod = Multiplicative.ofAdd ((v.count a : ZMod 4), (v.count b : ZMod 2)) := by
  induction v using List.reverseRecOn with
  | nil => rfl
  | append_singleton v z ih =>
      rw [List.map_append, List.prod_append, ih, count_snoc_ite, count_snoc_ite]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      unfold aabbRho
      by_cases hza : z = a
      · subst hza
        simp only [if_true, if_neg hab]
        rw [← ofAdd_add]; congr 1; simp only [Prod.mk_add_mk, add_zero]; push_cast; rfl
      · by_cases hzb : z = b
        · subst hzb
          simp only [if_neg hza, if_true]
          rw [← ofAdd_add]; congr 1; simp only [Prod.mk_add_mk, add_zero]; push_cast; rfl
        · simp only [if_neg hza, if_neg hzb, mul_one]
          congr 1

lemma z4z2_indicator (A B : ℕ) :
    (((if Multiplicative.ofAdd ((A : ZMod 4), (B : ZMod 2)) = z4z2G1 then 1 else 0 : ℕ) : ZMod 2) +
      ((if Multiplicative.ofAdd ((A : ZMod 4), (B : ZMod 2)) = z4z2G2 then 1 else 0 : ℕ) : ZMod 2)) =
      (A.choose 2 : ZMod 2) * (B : ZMod 2) := by
  rw [← ZMod.natCast_mod (A.choose 2), choose_two_mod_two, ← ZMod.natCast_mod A 4,
    ← ZMod.natCast_mod B 2]
  have hA := Nat.mod_lt A (show 0 < 4 by norm_num)
  have hB := Nat.mod_lt B (show 0 < 2 by norm_num)
  generalize A % 4 = r at hA ⊢
  generalize B % 2 = s at hB ⊢
  interval_cases r <;> interval_cases s <;> decide

/-- **`aabb` modulo `2` as a `Z₄ × Z₂` count**:
`scount [a,a,b,b] u ≡ (|u|_b + 1) · scount [a,a,b] u + hcount ρ g₁ b u + hcount ρ g₂ b u`. -/
theorem scount_aabb_cast_z4z2 {a b : α} (hab : a ≠ b) (u : List α) :
    (scount [a, a, b, b] u : ZMod 2) =
      ((u.count b : ZMod 2) + 1) * (scount [a, a, b] u : ZMod 2) +
        ((hcount (aabbRho a b) z4z2G1 b u + hcount (aabbRho a b) z4z2G2 b u : ℕ) : ZMod 2) := by
  induction u using List.reverseRecOn with
  | nil => simp [hcount]
  | append_singleton u z ih =>
      have e1 := scount_snoc b z u [a, a, b]
      have e2 := scount_snoc b z u [a, a]
      simp only [List.cons_append, List.nil_append] at e1 e2
      rw [e1, e2, hcount_snoc, hcount_snoc, count_snoc_ite]
      by_cases hz : z = b
      · subst hz
        simp only [if_true]
        rw [prod_aabbRho hab, scount_aa]
        have hi := z4z2_indicator (u.count a) (u.count z)
        push_cast at ih hi ⊢
        rw [ih]
        have two : ∀ t : ZMod 2, t + t = 0 := by decide
        linear_combination -hi - ((u.count z : ZMod 2) + 1) * two (((u.count a).choose 2 : ℕ) : ZMod 2)
      · simp only [if_neg hz, Nat.add_zero]
        exact ih

/-- `(|u|_b + 1) · scount [a,a,b] u` is good modulo every `n`. -/
lemma goodCount_aabb_other [Finite α] (a b : α) :
    GoodCount (fun u : List α => (u.count b + 1) * scount [a, a, b] u) :=
  ((goodCount_count b).add (goodCount_const 1)).mul (goodCount_scount_le_three _ (by simp))

/-- **`aabb` modulo `2` over any finite alphabet**: `scount [a,a,b,b]` is good modulo `2` iff
the sum of the two `Z₄ × Z₂` counts is. -/
theorem goodMod_aabb_iff_z4z2 [Finite α] {a b : α} (hab : a ≠ b) :
    GoodMod 2 (scount [a, a, b, b]) ↔
      GoodMod 2 (fun u => hcount (aabbRho a b) z4z2G1 b u + hcount (aabbRho a b) z4z2G2 b u) := by
  have hP := (goodCount_aabb_other (α := α) a b).goodMod 2
  have two : ∀ t : ZMod 2, t + t = 0 := by decide
  constructor
  · intro hS
    refine GoodMod.two_of_add hS hP fun u => ?_
    have h := scount_aabb_cast_z4z2 hab u
    push_cast at h ⊢
    linear_combination -h - ((u.count b : ZMod 2) + 1) * (scount [a, a, b] u : ZMod 2) * two 1
  · intro hQ
    refine GoodMod.two_of_add hP hQ fun u => ?_
    have h := scount_aabb_cast_z4z2 hab u
    push_cast at h ⊢
    exact h

/-- **`aabb` modulo `2` as a count on `Z₄ × Z₂`** (letters `a = 0`, `b = 1` of `Fin 2`). -/
theorem aabb_mod_two_iff_z4z2 :
    (∀ k, k < 2 → HasHeightAtMost {u : List (Fin 2) | scount [0, 0, 1, 1] u % 2 = k} 1) ↔
      GoodMod 2 (fun u : List (Fin 2) =>
        hcount (aabbRho 0 1) z4z2G1 1 u + hcount (aabbRho 0 1) z4z2G2 1 u) :=
  goodMod_aabb_iff_z4z2 (by decide)

/-- From the `Z₄ × Z₂`-core modulo `2`: `scount [a,a,b,b]` is good modulo `2`. -/
theorem goodMod_aabb_of_core (hcore : HCoreModTwo (Multiplicative (ZMod 4 × ZMod 2))) [Finite α]
    {a b : α} (hab : a ≠ b) : GoodMod 2 (scount [a, a, b, b]) := by
  refine (goodMod_aabb_iff_z4z2 hab).2 ?_
  refine GoodMod.two_of_add (g := hcount (aabbRho a b) z4z2G1 b)
    (h := hcount (aabbRho a b) z4z2G2 b) (fun k hk => hcore.univ _ b _ k hk)
    (fun k hk => hcore.univ _ b _ k hk) fun u => by push_cast; rfl

/-- **`L(aabb, k, 2)` from the `Z₄ × Z₂`-core modulo `2`.** -/
theorem aabb_mod_two_of_core (hcore : HCoreModTwo (Multiplicative (ZMod 4 × ZMod 2))) :
    ∀ k, k < 2 → HasHeightAtMost {u : List (Fin 2) | scount [0, 0, 1, 1] u % 2 = k} 1 :=
  goodMod_aabb_of_core hcore (by decide)

/-- **Every two-letter word of length four modulo `2`, from the `Z₄ × Z₂`-core modulo `2`.** -/
theorem height_one_two_letters_length_four_mod_two_of_core
    (hcore : HCoreModTwo (Multiplicative (ZMod 4 × ZMod 2))) [Finite α] {x y : α} (hxy : x ≠ y)
    (w : List α) (hw : w.length = 4) (hxy' : ∀ z ∈ w, z = x ∨ z = y) {k : ℕ} (hk : k < 2) :
    HasHeightAtMost {u : List α | scount w u % 2 = k} 1 := by
  by_cases h1 : w = [x, x, y, y]
  · subst h1; exact goodMod_aabb_of_core hcore hxy k hk
  by_cases h2 : w = [y, y, x, x]
  · subst h2; exact (goodMod_xxyy_iff 2 hxy).1 (goodMod_aabb_of_core hcore hxy) k hk
  exact height_one_two_letters_length_four_mod_two hxy w hw hxy' ⟨h1, h2⟩ hk

end AABB

/-! ### `Z₂ ≀ Z₂` and `abac` -/

/-- The base group `(ZMod 2 → ZMod 2)` of `Z₂ ≀ Z₂`, written multiplicatively. -/
abbrev Z2Base2 := Multiplicative (ZMod 2 → ZMod 2)

/-- The shift of coordinates by `e`: `(e · g) i = g (i - e)`. -/
def z2shift2 (e : ZMod 2) : Z2Base2 ≃* Z2Base2 where
  toFun g := Multiplicative.ofAdd (fun i => Multiplicative.toAdd g (i - e))
  invFun g := Multiplicative.ofAdd (fun i => Multiplicative.toAdd g (i + e))
  left_inv g := by funext i; simp
  right_inv g := by funext i; simp
  map_mul' g h := by funext i; rfl

/-- `ZMod 2` acting on the base by shifting the coordinates. -/
def z2shiftHom2 : Multiplicative (ZMod 2) →* MulAut Z2Base2 where
  toFun e := z2shift2 (Multiplicative.toAdd e)
  map_one' := by ext g i; simp [z2shift2]
  map_mul' a b := by
    ext g i
    show Multiplicative.toAdd g (i - (Multiplicative.toAdd a + Multiplicative.toAdd b)) =
      Multiplicative.toAdd g (i - Multiplicative.toAdd a - Multiplicative.toAdd b)
    rw [sub_sub]

/-- **The wreath product `Z₂ ≀ Z₂ = (ZMod 2 → ZMod 2) ⋊ ZMod 2`**, the dihedral group of
order `8`. -/
abbrev Z2WrZ2 := Z2Base2 ⋊[z2shiftHom2] Multiplicative (ZMod 2)

namespace Z2WrZ2

instance : Fintype Z2WrZ2 :=
  Fintype.ofEquiv (Z2Base2 × Multiplicative (ZMod 2))
    ⟨fun p => ⟨p.1, p.2⟩, fun x => (x.1, x.2), fun _ => rfl, fun _ => rfl⟩

lemma card : Fintype.card Z2WrZ2 = 8 := rfl

end Z2WrZ2

section ABAC

variable {α : Type u} [DecidableEq α]

/-- The letter map `a ↦ ⟨1, ofAdd 1⟩`, `b ↦ ⟨ofAdd (Pi.single 0 1), 1⟩`, others `↦ 1`. -/
def abacRho (a b : α) (y : α) : Z2WrZ2 :=
  if y = a then ⟨1, Multiplicative.ofAdd 1⟩
  else if y = b then ⟨Multiplicative.ofAdd (Pi.single 0 1), 1⟩ else 1

/-- The state `⟨f₀₁, 1⟩`, `f₀₁ = (0 ↦ 0, 1 ↦ 1)`. -/
def wrG01 : Z2WrZ2 := ⟨Multiplicative.ofAdd ![0, 1], 1⟩

/-- The state `⟨f₁₁, 1⟩`, `f₁₁ = (0 ↦ 1, 1 ↦ 1)`. -/
def wrG11 : Z2WrZ2 := ⟨Multiplicative.ofAdd ![1, 1], 1⟩

/-- The number of `b` read while `|·|_a ≡ i (mod 2)`. -/
def bAt (a b : α) (i : ZMod 2) (u : List α) : ℕ :=
  psum b (fun v => if parCol a v = i then 1 else 0) u

lemma prod_abacRho {a b : α} (hab : a ≠ b) (v : List α) :
    (v.map (abacRho a b)).prod =
      ⟨Multiplicative.ofAdd (fun i => (bAt a b i v : ZMod 2)),
        Multiplicative.ofAdd (v.count a : ZMod 2)⟩ := by
  induction v using List.reverseRecOn with
  | nil => rfl
  | append_singleton v z ih =>
      rw [List.map_append, List.prod_append, ih, count_snoc_ite]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, bAt,
        psum_snoc]
      unfold abacRho
      by_cases hza : z = a
      · subst hza
        simp only [if_true, if_neg hab]
        refine SemidirectProduct.ext ?_ ?_
        · simp
        · simp only [SemidirectProduct.mul_right]
          rw [← ofAdd_add]; congr 1; simp
      · by_cases hzb : z = b
        · subst hzb
          simp only [if_neg hza, if_true]
          refine SemidirectProduct.ext ?_ ?_
          · simp only [SemidirectProduct.mul_left]
            funext i
            show (bAt a z i v : ZMod 2) + (Pi.single 0 1 : ZMod 2 → ZMod 2)
                (i - (v.count a : ZMod 2)) = _
            unfold bAt parCol
            have : ∀ s t : ZMod 2, (Pi.single 0 1 : ZMod 2 → ZMod 2) (s - t) =
                if t = s then 1 else 0 := by decide
            rw [this, show ∀ f : ZMod 2 → ZMod 2, Multiplicative.ofAdd f i = f i from fun _ => rfl]
            push_cast
            rfl
          · simp
        · simp only [if_neg hza, if_neg hzb, mul_one]
          refine SemidirectProduct.ext ?_ ?_
          · simp
          · simp

lemma wreath_indicator (f : ZMod 2 → ZMod 2) (e : ZMod 2) :
    (((if (⟨Multiplicative.ofAdd f, Multiplicative.ofAdd e⟩ : Z2WrZ2) = wrG01 then 1 else 0 : ℕ) :
        ZMod 2) +
      ((if (⟨Multiplicative.ofAdd f, Multiplicative.ofAdd e⟩ : Z2WrZ2) = wrG11 then 1 else 0 : ℕ) :
        ZMod 2)) = if e = 0 then f 1 else 0 := by
  have hf : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  unfold wrG01 wrG11
  rw [hf]
  generalize f 0 = s
  generalize f 1 = t
  revert s t e
  decide

/-- **`abac` modulo `2` as a `Z₂ ≀ Z₂` count**: the pairs (`b` at `|·|_a` odd) before (`c` at
`|·|_a` even) are, modulo `2`, the `c` read in state `⟨f₀₁, 1⟩` or `⟨f₁₁, 1⟩`. -/
theorem cpair_abac_cast_wreath {a b : α} (hab : a ≠ b) (c : α) (u : List α) :
    (cpair (parCol a) b c 1 0 u : ZMod 2) =
      ((hcount (abacRho a b) wrG01 c u + hcount (abacRho a b) wrG11 c u : ℕ) : ZMod 2) := by
  induction u using List.reverseRecOn with
  | nil => simp [cpair, wpair, psum_nil, hcount]
  | append_singleton u z ih =>
      rw [hcount_snoc, hcount_snoc, cpair, wpair, psum_snoc]
      rw [cpair, wpair] at ih
      by_cases hz : z = c
      · subst hz
        simp only [if_true]
        rw [prod_abacRho hab]
        have hi := wreath_indicator (fun i => (bAt a b i u : ZMod 2)) (u.count a : ZMod 2)
        have hin : (psum b (fun v' => if parCol a v' = 1 ∧ parCol a u = 0 then 1 else 0) u : ZMod 2) =
            if (u.count a : ZMod 2) = 0 then (bAt a b 1 u : ZMod 2) else 0 := by
          by_cases h0 : (u.count a : ZMod 2) = 0
          · have h0' : parCol a u = 0 := h0
            rw [if_pos h0]
            unfold bAt
            congr 1
            exact psum_congr _ _ _ _ fun i _ => by simp [h0']
          · have h0' : ¬ parCol a u = 0 := h0
            rw [if_neg h0, (psum_congr _ _ (fun _ => 0) _ fun i _ => by simp [h0']).trans
              (psum_zero _ _)]
            simp
        push_cast at ih hi hin ⊢
        rw [ih, hin, ← hi]
        ring
      · simp only [if_neg hz, Nat.add_zero]
        exact ih

/-- **`abac` modulo `2` as a count on `Z₂ ≀ Z₂`** (letters `a = 0`, `b = 1`, `c = 2` of
`Fin 3`). -/
theorem abac_mod_two_iff_wreath :
    (∀ k, k < 2 → HasHeightAtMost {u : List (Fin 3) | scount [0, 1, 0, 2] u % 2 = k} 1) ↔
      GoodMod 2 (fun u : List (Fin 3) =>
        hcount (abacRho 0 1) wrG01 2 u + hcount (abacRho 0 1) wrG11 2 u) := by
  rw [← cpair_mod_two_iff_abac 1 0]
  constructor
  · intro h
    exact GoodMod.two_congr h fun u => (cpair_abac_cast_wreath (by decide) 2 u).symm
  · intro h
    exact GoodMod.two_congr h fun u => cpair_abac_cast_wreath (by decide) 2 u

/-- **`L(abac, k, 2)` from the `Z₂ ≀ Z₂`-core modulo `2`.** -/
theorem abac_mod_two_of_core (hcore : HCoreModTwo Z2WrZ2) :
    ∀ k, k < 2 → HasHeightAtMost {u : List (Fin 3) | scount [0, 1, 0, 2] u % 2 = k} 1 := by
  refine abac_mod_two_iff_wreath.2 ?_
  exact GoodMod.two_of_add (g := hcount (abacRho 0 1) wrG01 2)
    (h := hcount (abacRho 0 1) wrG11 2) (fun k hk => hcore _ _ 2 _ k hk)
    (fun k hk => hcore _ _ 2 _ k hk) fun u => by push_cast; rfl

end ABAC

end GeneralizedStarHeight
