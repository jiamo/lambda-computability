import Start.StarHeightCosetFamily
import Start.StarHeightRenaming
import Start.StarHeightOrderLtTwenty

/-!
# Generating pairs of `S₄`, up to conjugation and a swap of the two letters

The two-letter normal forms.  Up to simultaneous conjugation and swapping the two letters there
are exactly five generating pairs of `S₄`:

| class | first letter | second letter |
| ----- | ------------ | ------------- |
| `0`   | `(2 3)`      | `(0 1 2)`     |
| `1`   | `(2 3)`      | `(0 1 2 3)`   |
| `2`   | `(1 2 3)`    | `(0 1 2 3)`   |
| `3`   | `(1 2 3)`    | `(0 1 3 2)`   |
| `4`   | `(0 1 2 3)`  | `(0 1 3 2)`   |

* `classify_pairs`: every pair `(A, B)` of permutations of `Fin 4` either has a common fixed
  point, or centralizes one of the three double transpositions, or consists of two even
  permutations, or is conjugate — possibly after swapping `A` and `B` — to one of the five normal
  forms.  This is the finite check `classWit_all` on the `576` pairs of tables (`Fin 4 → Fin 4`),
  transported to permutations by `perm_tab` (every permutation is one of the `24` tables).
* `height_one_of_mem_proper`: in the first three cases both letters lie in a proper subgroup `H`
  of `S₄`, which has order at most `12`, so `height_one_of_card_lt_twenty` applies to the
  restriction of `T` to `H`.
* `conj_language`, `height_one_of_swap`: the two normalizations.  Conjugating `T` by `c` and `F`
  by `c⁻¹ · c` leaves the language unchanged; swapping the two letters renames the alphabet,
  which preserves height (`HasHeightAtMost.comap_equiv`).
-/

-- The certificates below are checked one at a time, which keeps the peak memory low.
set_option Elab.async false

namespace GeneralizedStarHeight

namespace S4Two

open Equiv

/-- The three-cycle `(1 2 3)`. -/
def c123 : Equiv.Perm (Fin 4) := swap 1 2 * swap 2 3

/-- The three-cycle `(0 1 2)`. -/
def c012 : Equiv.Perm (Fin 4) := swap 0 1 * swap 1 2

/-- The four-cycle `(0 1 2 3)`. -/
def c0123 : Equiv.Perm (Fin 4) := swap 0 1 * swap 1 2 * swap 2 3

/-- The four-cycle `(0 1 3 2)`. -/
def c0132 : Equiv.Perm (Fin 4) := swap 0 1 * swap 1 3 * swap 3 2

/-- The first letters of the five normal forms. -/
def repA : Fin 5 → Equiv.Perm (Fin 4) := ![swap 2 3, swap 2 3, c123, c123, c0123]

/-- The second letters of the five normal forms. -/
def repB : Fin 5 → Equiv.Perm (Fin 4) := ![c012, c0123, c0123, c0132, c0132]

/-! ### Permutations of four points as tables -/

/-- The `24` permutations of `Fin 4`, as tables `i ↦ σ i`, in lexicographic order (raw data). -/
def tabL : List (List ℕ) :=
  [[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1], [0, 3, 1, 2], [0, 3, 2, 1],
    [1, 0, 2, 3], [1, 0, 3, 2], [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0],
    [2, 0, 1, 3], [2, 0, 3, 1], [2, 1, 0, 3], [2, 1, 3, 0], [2, 3, 0, 1], [2, 3, 1, 0],
    [3, 0, 1, 2], [3, 0, 2, 1], [3, 1, 0, 2], [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0]]

/-- Lookup in a list of rows of natural numbers. -/
def lk (t : List (List ℕ)) (i x : ℕ) : ℕ := (t.getD i []).getD x 0

/-- The `24` permutations of `Fin 4`, as tables. -/
def tab (i : Fin 24) (x : Fin 4) : Fin 4 := ⟨lk tabL i x % 4, Nat.mod_lt _ (by decide)⟩

/-- The index of the inverse table. -/
def tinv (i : Fin 24) : Fin 24 :=
  ⟨([0, 1, 2, 4, 3, 5, 6, 7, 12, 18, 13, 19, 8, 10, 14, 20, 16, 22, 9, 11, 15, 21, 17, 23] :
    List ℕ).getD i 0 % 24, Nat.mod_lt _ (by decide)⟩

/-- The even tables. -/
def evenT (i : Fin 24) : Bool :=
  ([true, false, false, true, true, false, false, true, true, false, false, true, true, false,
    false, true, true, false, false, true, true, false, false, true] : List Bool).getD i false

lemma tab_tinv : ∀ (i : Fin 24) (x : Fin 4), tab i (tab (tinv i) x) = x := by decide +kernel

lemma tinv_tab : ∀ (i : Fin 24) (x : Fin 4), tab (tinv i) (tab i x) = x := by decide +kernel

/-- The permutation with table `tab i`. -/
def permOf (i : Fin 24) : Equiv.Perm (Fin 4) :=
  ⟨tab i, tab (tinv i), fun x => tinv_tab i x, fun x => tab_tinv i x⟩

lemma coe_permOf (i : Fin 24) : ⇑(permOf i) = tab i := rfl

lemma tab_complete : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∃ i : Fin 24, tab i 0 = a ∧ tab i 1 = b ∧ tab i 2 = c ∧ tab i 3 = d := by decide +kernel

/-- **Every permutation of four points is one of the `24` tables.** -/
lemma perm_tab (σ : Equiv.Perm (Fin 4)) : ∃ i : Fin 24, ⇑σ = tab i := by
  have hne : ∀ x y : Fin 4, x ≠ y → σ x ≠ σ y := fun x y h h' => h (σ.injective h')
  obtain ⟨i, h0, h1, h2, h3⟩ := tab_complete (σ 0) (σ 1) (σ 2) (σ 3) (hne _ _ (by decide))
    (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
    (hne _ _ (by decide))
  refine ⟨i, funext fun x => ?_⟩
  fin_cases x
  · exact h0.symm
  · exact h1.symm
  · exact h2.symm
  · exact h3.symm

/-- Equality of two tables. -/
def feq (f g : Fin 4 → Fin 4) : Bool :=
  decide (f 0 = g 0) && decide (f 1 = g 1) && decide (f 2 = g 2) && decide (f 3 = g 3)

lemma feq_iff {f g : Fin 4 → Fin 4} : feq f g = true ↔ f = g := by
  constructor
  · intro h
    simp only [feq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
    funext x
    fin_cases x
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · rintro rfl
    simp [feq]

/-! ### The classification -/

/-- The three double transpositions. -/
def dtP : Fin 3 → Equiv.Perm (Fin 4) :=
  ![swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

/-- Their tables. -/
def dtT (m : Fin 3) (x : Fin 4) : Fin 4 :=
  ⟨lk [[1, 0, 3, 2], [2, 3, 0, 1], [3, 2, 1, 0]] m x % 4, Nat.mod_lt _ (by decide)⟩

/-- The tables of the first letters of the normal forms. -/
def raT (k : Fin 5) (x : Fin 4) : Fin 4 :=
  ⟨lk [[0, 1, 3, 2], [0, 1, 3, 2], [0, 2, 3, 1], [0, 2, 3, 1], [1, 2, 3, 0]] k x % 4,
    Nat.mod_lt _ (by decide)⟩

/-- The tables of the second letters of the normal forms. -/
def rbT (k : Fin 5) (x : Fin 4) : Fin 4 :=
  ⟨lk [[1, 2, 0, 3], [1, 2, 3, 0], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 0, 2]] k x % 4,
    Nat.mod_lt _ (by decide)⟩

lemma dtP_tab : ∀ (m : Fin 3) (x : Fin 4), dtP m x = dtT m x := by decide +kernel

lemma repA_tab : ∀ (k : Fin 5) (x : Fin 4), repA k x = raT k x := by decide +kernel

lemma repB_tab : ∀ (k : Fin 5) (x : Fin 4), repB k x = rbT k x := by decide +kernel

/-- The fixed point, double transposition, normal form and conjugator encoded by a witness. -/
def wp (n : ℕ) : Fin 4 := ⟨n % 4, Nat.mod_lt _ (by decide)⟩

/-- See `wp`. -/
def wm (n : ℕ) : Fin 3 := ⟨n / 4 % 3, Nat.mod_lt _ (by decide)⟩

/-- See `wp`. -/
def wk (n : ℕ) : Fin 5 := ⟨n / 12 % 5, Nat.mod_lt _ (by decide)⟩

/-- See `wp`. -/
def wc (n : ℕ) : Fin 24 := ⟨n / 60 % 24, Nat.mod_lt _ (by decide)⟩

/-- The classification test on the tables `tab i`, `tab j`, with the witness `n`. -/
def classWit (i j : Fin 24) (n : ℕ) : Bool :=
  (decide (tab i (wp n) = wp n) && decide (tab j (wp n) = wp n)) ||
    (feq (tab i ∘ dtT (wm n)) (dtT (wm n) ∘ tab i) &&
      feq (tab j ∘ dtT (wm n)) (dtT (wm n) ∘ tab j)) ||
    (evenT i && evenT j) ||
    ((feq (tab (wc n) ∘ tab i) (raT (wk n) ∘ tab (wc n)) &&
        feq (tab (wc n) ∘ tab j) (rbT (wk n) ∘ tab (wc n))) ||
      (feq (tab (wc n) ∘ tab i) (rbT (wk n) ∘ tab (wc n)) &&
        feq (tab (wc n) ∘ tab j) (raT (wk n) ∘ tab (wc n))))

/-- The witnesses (computed by a search; checked below). -/
def witL : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 2, 0, 3, 4, 8, 2,
      3, 8, 1, 1, 0, 0, 4, 2, 1, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 72, 60,
      360, 372, 1, 1, 0, 0, 432, 420, 1, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 3, 8, 3, 552, 8, 540,
      3, 8, 3, 660, 8, 672, 312, 180, 300, 8, 192, 8],
    [0, 0, 0, 0, 0, 0, 1320, 0, 0, 24, 36, 0,
      0, 264, 1260, 0, 0, 276, 216, 0, 0, 1080, 204, 0],
    [0, 0, 0, 0, 0, 0, 1380, 0, 0, 96, 84, 0,
      0, 156, 1140, 0, 0, 144, 324, 0, 0, 1200, 336, 0],
    [0, 0, 0, 0, 0, 0, 2, 4, 480, 4, 492, 2,
      120, 252, 4, 240, 4, 132, 4, 2, 600, 2, 612, 4],
    [2, 0, 3, 1320, 1380, 2, 2, 0, 3, 972, 1032, 2,
      3, 1332, 3, 960, 0, 0, 1392, 2, 1020, 2, 0, 0],
    [0, 0, 8, 0, 0, 4, 0, 0, 0, 4, 8, 0,
      0, 8, 4, 0, 0, 0, 4, 0, 0, 8, 0, 0],
    [3, 0, 3, 0, 0, 480, 3, 0, 3, 564, 1044, 0,
      3, 1296, 3, 0, 0, 576, 1056, 0, 0, 720, 1284, 0],
    [4, 12, 552, 24, 96, 4, 972, 4, 564, 4, 48, 984,
      696, 1008, 4, 1104, 4, 588, 4, 1356, 756, 1092, 768, 4],
    [8, 72, 8, 36, 84, 492, 1032, 8, 1044, 48, 8, 504,
      1416, 8, 1152, 816, 8, 828, 1068, 636, 1164, 8, 528, 8],
    [2, 60, 540, 0, 0, 2, 2, 0, 0, 984, 504, 2,
      0, 996, 780, 0, 0, 1224, 1236, 2, 0, 2, 516, 0],
    [3, 360, 3, 0, 0, 120, 3, 0, 3, 696, 1416, 0,
      3, 924, 3, 0, 0, 684, 1404, 0, 0, 840, 936, 0],
    [8, 372, 8, 264, 156, 252, 1332, 8, 1296, 1008, 8, 996,
      924, 8, 912, 384, 8, 168, 408, 1344, 456, 8, 948, 8],
    [1, 1, 3, 1260, 1140, 4, 3, 4, 3, 4, 1152, 780,
      3, 912, 1, 1, 4, 792, 4, 900, 1, 1, 1272, 4],
    [1, 1, 660, 0, 0, 240, 960, 0, 0, 1104, 816, 0,
      0, 384, 1, 1, 0, 804, 396, 0, 1, 1, 1116, 0],
    [0, 0, 8, 0, 0, 4, 0, 0, 0, 4, 8, 0,
      0, 8, 4, 0, 0, 0, 4, 0, 0, 8, 0, 0],
    [0, 0, 672, 276, 144, 132, 0, 0, 576, 588, 828, 1224,
      684, 168, 792, 804, 0, 0, 888, 876, 1176, 1212, 0, 0],
    [4, 432, 312, 216, 324, 4, 1392, 4, 1056, 4, 1068, 1236,
      1404, 408, 4, 396, 4, 888, 4, 864, 444, 852, 228, 4],
    [2, 420, 180, 0, 0, 2, 2, 0, 0, 1356, 636, 2,
      0, 1344, 900, 0, 0, 876, 864, 2, 0, 2, 624, 0],
    [1, 1, 300, 0, 0, 600, 1020, 0, 0, 756, 1164, 0,
      0, 456, 1, 1, 0, 1176, 444, 0, 1, 1, 744, 0],
    [1, 1, 8, 1080, 1200, 2, 2, 8, 720, 1092, 8, 2,
      840, 8, 1, 1, 8, 1212, 852, 2, 1, 1, 732, 8],
    [0, 0, 192, 204, 336, 612, 0, 0, 1284, 768, 528, 516,
      936, 948, 1272, 1116, 0, 0, 228, 624, 744, 732, 0, 0],
    [0, 0, 8, 0, 0, 4, 0, 0, 0, 4, 8, 0,
      0, 8, 4, 0, 0, 0, 4, 0, 0, 8, 0, 0]]

/-- The witness of the pair `(i, j)`. -/
def wit (i j : Fin 24) : ℕ := lk witL i j

/-- **The finite check behind the classification**, on the `576` pairs of tables. -/
lemma classWit_all : ∀ i j : Fin 24, classWit i j (wit i j) = true := by decide +kernel

/-- The even permutations, through their tables. -/
def evenSub : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {σ | ∃ i, ⇑σ = tab i ∧ evenT i = true}
  one_mem' := ⟨0, funext fun x => by revert x; decide, rfl⟩
  mul_mem' := by
    rintro σ τ ⟨i, hi, ei⟩ ⟨j, hj, ej⟩
    have key : ∀ i j : Fin 24, evenT i = true → evenT j = true →
        ∃ k : Fin 24, evenT k = true ∧ ∀ x, tab k x = tab i (tab j x) := by decide +kernel
    obtain ⟨k, ek, hk⟩ := key i j ei ej
    refine ⟨k, funext fun x => ?_, ek⟩
    rw [Equiv.Perm.coe_mul, Function.comp_apply, hi, hj, hk]
  inv_mem' := by
    rintro σ ⟨i, hi, ei⟩
    have key : ∀ i : Fin 24, evenT i = true →
        ∃ k : Fin 24, evenT k = true ∧ ∀ x, tab k (tab i x) = x := by decide +kernel
    obtain ⟨k, ek, hk⟩ := key i ei
    refine ⟨k, funext fun y => ?_, ek⟩
    have h := hk (σ⁻¹ y)
    rw [← hi, show σ (σ⁻¹ y) = y by simp] at h
    exact h.symm

/-- **Classification of pairs of permutations of four points.**  Either the two permutations have
a common fixed point, or both commute with a double transposition, or both are even, or the pair
is conjugate, possibly after swapping the two, to one of the five normal forms. -/
theorem classify_pairs (A B : Equiv.Perm (Fin 4)) :
    (∃ p, A p = p ∧ B p = p) ∨ (∃ m : Fin 3, A * dtP m = dtP m * A ∧ B * dtP m = dtP m * B) ∨
      (A ∈ evenSub ∧ B ∈ evenSub) ∨
      (∃ c : Equiv.Perm (Fin 4), ∃ k : Fin 5,
        (c * A = repA k * c ∧ c * B = repB k * c) ∨ (c * A = repB k * c ∧ c * B = repA k * c)) := by
  obtain ⟨i, hi⟩ := perm_tab A
  obtain ⟨j, hj⟩ := perm_tab B
  have h := classWit_all i j
  simp only [classWit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, feq_iff] at h
  have hdt : ∀ m, ⇑(dtP m) = dtT m := fun m => funext (dtP_tab m)
  have hra : ∀ k, ⇑(repA k) = raT k := fun k => funext (repA_tab k)
  have hrb : ∀ k, ⇑(repB k) = rbT k := fun k => funext (repB_tab k)
  rcases h with ((⟨hpA, hpB⟩ | ⟨hmA, hmB⟩) | ⟨eA, eB⟩) | hk
  · exact Or.inl ⟨wp (wit i j), by rw [hi]; exact hpA, by rw [hj]; exact hpB⟩
  · refine Or.inr (Or.inl ⟨wm (wit i j), ?_, ?_⟩)
    · apply DFunLike.coe_injective
      rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, hi, hdt]
      exact hmA
    · apply DFunLike.coe_injective
      rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, hj, hdt]
      exact hmB
  · exact Or.inr (Or.inr (Or.inl ⟨⟨i, hi, eA⟩, ⟨j, hj, eB⟩⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨permOf (wc (wit i j)), wk (wit i j), ?_⟩))
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨?_, ?_⟩
      · apply DFunLike.coe_injective
        rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, hi, hra, coe_permOf]
        exact h1
      · apply DFunLike.coe_injective
        rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, hj, hrb, coe_permOf]
        exact h2
    · refine Or.inr ⟨?_, ?_⟩
      · apply DFunLike.coe_injective
        rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, hi, hrb, coe_permOf]
        exact h1
      · apply DFunLike.coe_injective
        rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, hj, hra, coe_permOf]
        exact h2

/-! ### Proper subgroups -/

lemma card_lt_twenty_of_ne_top (H : Subgroup (Equiv.Perm (Fin 4))) (hH : H ≠ ⊤) :
    Nat.card H < 20 := by
  classical
  have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  have hdvd : Nat.card H ∣ 24 := h24 ▸ Subgroup.card_subgroup_dvd_card H
  have hne : Nat.card H ≠ 24 := fun h => hH (Subgroup.eq_top_of_card_eq H (by rw [h, h24]))
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hm2 : 2 ≤ m := by
    rcases m with _ | _ | m
    · omega
    · exact absurd (by omega) hne
    · omega
  have hle : Nat.card H * 2 ≤ Nat.card H * m := Nat.mul_le_mul_left _ hm2
  omega

/-- **If both letters lie in a proper subgroup, the recognized languages have height at most
one**, because every proper subgroup of `S₄` has order at most `12`. -/
theorem height_one_of_mem_proper {Alphabet : Type} [Finite Alphabet]
    (H : Subgroup (Equiv.Perm (Fin 4))) (hH : H ≠ ⊤)
    (T : FreeMonoid Alphabet →* Equiv.Perm (Fin 4)) (hmem : ∀ x, T (FreeMonoid.of x) ∈ H)
    (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  have hcard : Fintype.card H < 20 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_lt_twenty_of_ne_top H hH
  set T' : FreeMonoid Alphabet →* H :=
    FreeMonoid.lift fun x => (⟨T (FreeMonoid.of x), hmem x⟩ : H) with hT'
  have hcomp : H.subtype.comp T' = T :=
    FreeMonoid.hom_eq fun x => by simp [T', FreeMonoid.lift_eval_of]
  have hval : ∀ w : List Alphabet,
      ((T' (FreeMonoid.ofList w) : H) : Equiv.Perm (Fin 4)) = T (FreeMonoid.ofList w) := by
    intro w
    conv_rhs => rw [← hcomp]
    rfl
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) =
      {w | T' (FreeMonoid.ofList w) ∈ (Subtype.val ⁻¹' F : Set H)} := by
    ext w
    show T (FreeMonoid.ofList w) ∈ F ↔ ((T' (FreeMonoid.ofList w) : H) : Equiv.Perm (Fin 4)) ∈ F
    rw [hval w]
  rw [heq]
  exact height_one_of_card_lt_twenty hcard T' _

lemma stab_ne_top (p : Fin 4) : MulAction.stabilizer (Equiv.Perm (Fin 4)) p ≠ ⊤ := by
  intro h
  obtain ⟨q, hq⟩ : ∃ q : Fin 4, q ≠ p := ⟨if p = 0 then 1 else 0, by fin_cases p <;> decide⟩
  have hmem : swap p q ∈ MulAction.stabilizer (Equiv.Perm (Fin 4)) p := h ▸ Subgroup.mem_top _
  rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, swap_apply_left] at hmem
  exact hq hmem

lemma centralizer_ne_top (m : Fin 3) :
    Subgroup.centralizer ({dtP m} : Set (Equiv.Perm (Fin 4))) ≠ ⊤ := by
  have hτ : ∀ m : Fin 3, ∃ τ : Fin 24, dtT m (tab τ 0) ≠ tab τ (dtT m 0) := by decide +kernel
  obtain ⟨τ, hτm⟩ := hτ m
  intro h
  have hmem : permOf τ ∈ Subgroup.centralizer ({dtP m} : Set (Equiv.Perm (Fin 4))) :=
    h ▸ Subgroup.mem_top _
  rw [Subgroup.mem_centralizer_iff] at hmem
  have h0 := congrArg (fun σ : Equiv.Perm (Fin 4) => σ 0) (hmem (dtP m) rfl)
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, coe_permOf, dtP_tab] at h0
  exact hτm h0

lemma evenSub_ne_top : evenSub ≠ ⊤ := by
  intro h
  have hmem : swap (0 : Fin 4) 1 ∈ evenSub := h ▸ Subgroup.mem_top _
  obtain ⟨i, hi, ei⟩ := hmem
  have hodd : ∀ i : Fin 24, evenT i = true →
      tab i 0 ≠ 1 ∨ tab i 1 ≠ 0 ∨ tab i 2 ≠ 2 ∨ tab i 3 ≠ 3 := by decide +kernel
  have h0 := congrFun hi 0
  have h1 := congrFun hi 1
  have h2 := congrFun hi 2
  have h3 := congrFun hi 3
  simp only [swap_apply_left, swap_apply_right] at h0 h1
  rw [swap_apply_of_ne_of_ne (by decide) (by decide)] at h2 h3
  rcases hodd i ei with h | h | h | h
  · exact h h0.symm
  · exact h h1.symm
  · exact h h2.symm
  · exact h h3.symm

/-! ### Normalizations -/

/-- Conjugating the morphism and the target set leaves the recognized language unchanged. -/
lemma conj_language {Alphabet : Type} (c : Equiv.Perm (Fin 4))
    (T : FreeMonoid Alphabet →* Equiv.Perm (Fin 4)) (F : Set (Equiv.Perm (Fin 4))) :
    ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) =
      {w | ((MulAut.conj c).toMonoidHom.comp T) (FreeMonoid.ofList w) ∈
        {g | c⁻¹ * g * c ∈ F}} := by
  ext w
  show T (FreeMonoid.ofList w) ∈ F ↔ c⁻¹ * (c * T (FreeMonoid.ofList w) * c⁻¹) * c ∈ F
  rw [show c⁻¹ * (c * T (FreeMonoid.ofList w) * c⁻¹) * c = T (FreeMonoid.ofList w) by group]

lemma map_ofList_swap (w : List (Fin 2)) :
    (FreeMonoid.map (Equiv.swap (0 : Fin 2) 1)) (FreeMonoid.ofList w) =
      FreeMonoid.ofList (w.map (Equiv.swap (0 : Fin 2) 1)) := rfl

/-- **Swapping the two letters preserves height.** -/
lemma height_one_of_swap {M : Type*} [Monoid M] (T : FreeMonoid (Fin 2) →* M) (F : Set M)
    (h : HasHeightAtMost {w | (T.comp (FreeMonoid.map (Equiv.swap (0 : Fin 2) 1)))
      (FreeMonoid.ofList w) ∈ F} 1) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have key := HasHeightAtMost.comap_equiv (Equiv.swap (0 : Fin 2) 1) h
  have heq : ({w : List (Fin 2) | List.map (Equiv.swap (0 : Fin 2) 1) w ∈
        {v | (T.comp (FreeMonoid.map (Equiv.swap (0 : Fin 2) 1)))
          (FreeMonoid.ofList v) ∈ F}} : Language (Fin 2)) =
      {w | T (FreeMonoid.ofList w) ∈ F} := by
    ext w
    show T ((FreeMonoid.map (Equiv.swap (0 : Fin 2) 1))
        (FreeMonoid.ofList (w.map (Equiv.swap (0 : Fin 2) 1)))) ∈ F ↔
      T (FreeMonoid.ofList w) ∈ F
    rw [map_ofList_swap, List.map_map]
    have hid : (Equiv.swap (0 : Fin 2) 1) ∘ (Equiv.swap (0 : Fin 2) 1) = id := by
      funext x
      simp
    rw [hid, List.map_id]
  exact heq ▸ key

end S4Two

end GeneralizedStarHeight
