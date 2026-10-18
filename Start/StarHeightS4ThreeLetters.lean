import Start.StarHeightS4ThreeCertsA
import Start.StarHeightS4ThreeCertsB
import Start.StarHeightS4ThreeCertsC
import Start.StarHeightS4ThreeCertsD
import Start.StarHeightS4ThreeCertsE
import Start.StarHeightS4ThreeHitsA
import Start.StarHeightS4ThreeHitsB
import Start.StarHeightS4TwoLetters

/-!
# `S₄` over three letters without double transpositions

`height_one_S4_three_letters`: for every morphism `T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4)`
none of whose letters is a double transposition, every language `{w | T w ∈ F}` has generalized
star height at most one.  `height_one_S4_three_letters_or_proper` also admits letters that lie in
a proper subgroup of `S₄` (double transpositions allowed).

The proof reduces an arbitrary triple of letters, in three stages, to one of `56` class
representatives (`repL`), up to conjugation and a permutation of the three letters:

1. conjugate the first letter to one of five cycle-type representatives (`R0`, witnesses `w1L`);
2. conjugate the second letter by the centralizer of the first (witnesses `w2L`); the pairs that
   remain are the `43` pairs of `P3`;
3. for each pair of `P3` and each of the `24` third letters, a witness (`w3L`, checked by
   `fin3`) says that a letter is a double transposition (excluded), or two letters are equal
   (`height_one_S4_two_values`), or the three letters lie in one of the eight maximal subgroups
   (`height_one_of_mem_proper`), or the triple is conjugate, after a permutation of the letters,
   to a class representative.

The class representatives: `45` classes with `D = 1` (`StarHeightS4ThreeCertsA`–`E`, of which
`K01`–`K05` have an identity letter), the `10` lifted classes of `StarHeightS4ThreeHitsA/B`,
and the Coxeter class `S4Cox.coxT`.  All checks are `decide +kernel` on tables of `Fin 4`; no
search over all `24 ^ 3` triples is run in the kernel.
-/

-- The certificates below are checked one at a time, which keeps the peak memory low.
set_option Elab.async false

namespace GeneralizedStarHeight

namespace S4Three

open S4Two

/-! ### Invariance under conjugation and renaming of letters -/

/-- The double transpositions of `Fin 4`. -/
def dbl : Set (Equiv.Perm (Fin 4)) := {σ | σ * σ = 1 ∧ ∀ i, σ i ≠ i}

/-- Every language recognized by `T` has generalized star height at most one. -/
def AllHeightOne (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4)) : Prop :=
  ∀ F : Set (Equiv.Perm (Fin 4)),
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1

/-- The conjugate morphism `w ↦ c * T w * c⁻¹`. -/
def conjT (c : Equiv.Perm (Fin 4)) (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4)) :
    FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4) :=
  (MulAut.conj c).toMonoidHom.comp T

lemma conjT_of (c : Equiv.Perm (Fin 4)) (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (x : Fin 3) : conjT c T (FreeMonoid.of x) = c * T (FreeMonoid.of x) * c⁻¹ := rfl

lemma allHeightOne_of_conj (c : Equiv.Perm (Fin 4)) (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (h : AllHeightOne (conjT c T)) : AllHeightOne T := by
  intro F
  rw [conj_language c T F]
  exact h _

lemma allHeightOne_of_perm (π : Equiv.Perm (Fin 3)) (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (h : AllHeightOne (T.comp (FreeMonoid.map π))) : AllHeightOne T := by
  intro F
  have key := HasHeightAtMost.comap_equiv π.symm (h F)
  have heq : ({w : List (Fin 3) | List.map π.symm w ∈
      {v : List (Fin 3) | (T.comp (FreeMonoid.map π)) (FreeMonoid.ofList v) ∈ F}} :
        Language (Fin 3)) = {w | T (FreeMonoid.ofList w) ∈ F} := by
    ext w
    show T ((FreeMonoid.map π) (FreeMonoid.ofList (w.map π.symm))) ∈ F ↔
      T (FreeMonoid.ofList w) ∈ F
    rw [show (FreeMonoid.map π) (FreeMonoid.ofList (w.map π.symm)) =
      FreeMonoid.ofList ((w.map π.symm).map π) from rfl, List.map_map]
    simp
  exact heq ▸ key

lemma conj_not_dbl {σ : Equiv.Perm (Fin 4)} (c : Equiv.Perm (Fin 4)) (h : σ ∉ dbl) :
    c * σ * c⁻¹ ∉ dbl := by
  rintro ⟨h1, h2⟩
  refine h ⟨?_, fun i hi => h2 (c i) ?_⟩
  · calc σ * σ = c⁻¹ * (c * σ * c⁻¹ * (c * σ * c⁻¹)) * c := by group
      _ = 1 := by rw [h1]; group
  · simp [Equiv.Perm.mul_apply, hi]

/-- Two equal letters: at most two values. -/
lemma allHeightOne_of_eq01 (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (h : T (FreeMonoid.of 0) = T (FreeMonoid.of 1)) : AllHeightOne T := fun F =>
  height_one_S4_two_values T ![0, 0, 1]
    (FreeMonoid.lift ![T (FreeMonoid.of 0), T (FreeMonoid.of 2)]) (fun x => by fin_cases x <;> simp [h]) F

lemma allHeightOne_of_eq02 (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (h : T (FreeMonoid.of 0) = T (FreeMonoid.of 2)) : AllHeightOne T :=
  allHeightOne_of_perm (Equiv.swap 1 2) T (allHeightOne_of_eq01 _ (by
    show T (FreeMonoid.of (Equiv.swap (1 : Fin 3) 2 0)) =
      T (FreeMonoid.of (Equiv.swap (1 : Fin 3) 2 1))
    rw [show Equiv.swap (1 : Fin 3) 2 0 = 0 by decide,
      show Equiv.swap (1 : Fin 3) 2 1 = 2 by decide]
    exact h))

lemma allHeightOne_of_eq12 (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (h : T (FreeMonoid.of 1) = T (FreeMonoid.of 2)) : AllHeightOne T :=
  allHeightOne_of_perm (Equiv.swap 0 2) T (allHeightOne_of_eq01 _ (by
    show T (FreeMonoid.of (Equiv.swap (0 : Fin 3) 2 0)) =
      T (FreeMonoid.of (Equiv.swap (0 : Fin 3) 2 1))
    rw [show Equiv.swap (0 : Fin 3) 2 0 = 2 by decide,
      show Equiv.swap (0 : Fin 3) 2 1 = 1 by decide]
    exact h.symm))

/-! ### Tables -/

/-- Double transpositions, on tables. -/
def dblT (i : Fin 24) : Bool :=
  decide (∀ x, tab i (tab i x) = x) && decide (∀ x, tab i x ≠ x)

lemma mem_dbl_of_dblT {σ : Equiv.Perm (Fin 4)} {i : Fin 24} (hσ : ⇑σ = tab i)
    (h : dblT i = true) : σ ∈ dbl := by
  simp only [dblT, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨Equiv.ext fun x => ?_, fun x => ?_⟩
  · rw [Equiv.Perm.mul_apply, hσ, h.1 x, Equiv.Perm.one_apply]
  · rw [hσ]
    exact h.2 x

/-- Membership in the `m`-th maximal subgroup, on tables: the stabilizers of the points `0`–`3`,
the centralizers of the three double transpositions, and the even permutations. -/
def inMax (m : Fin 8) (i : Fin 24) : Bool :=
  if h : m.val < 4 then decide (tab i ⟨m.val, h⟩ = ⟨m.val, h⟩)
  else if h' : m.val < 7 then
    decide (∀ x, tab i (dtT ⟨m.val - 4, by omega⟩ x) = dtT ⟨m.val - 4, by omega⟩ (tab i x))
  else evenT i

/-- The eight maximal subgroups of `S₄`. -/
def maxSub (m : Fin 8) : Subgroup (Equiv.Perm (Fin 4)) :=
  if h : m.val < 4 then MulAction.stabilizer (Equiv.Perm (Fin 4)) (⟨m.val, h⟩ : Fin 4)
  else if h' : m.val < 7 then
    Subgroup.centralizer ({dtP ⟨m.val - 4, by omega⟩} : Set (Equiv.Perm (Fin 4)))
  else evenSub

lemma maxSub_ne_top (m : Fin 8) : maxSub m ≠ ⊤ := by
  unfold maxSub
  split_ifs
  · exact stab_ne_top _
  · exact centralizer_ne_top _
  · exact evenSub_ne_top

lemma mem_maxSub {σ : Equiv.Perm (Fin 4)} {i : Fin 24} {m : Fin 8} (hσ : ⇑σ = tab i)
    (h : inMax m i = true) : σ ∈ maxSub m := by
  unfold maxSub
  unfold inMax at h
  split_ifs at h ⊢ with h1 h2
  · rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, hσ]
    exact of_decide_eq_true h
  · rw [Subgroup.mem_centralizer_iff]
    rintro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    refine Equiv.ext fun x => ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hσ, dtP_tab, dtP_tab]
    exact ((of_decide_eq_true h) x).symm
  · exact ⟨i, hσ, h⟩

/-- The six permutations of the three letters. -/
def perm3 : Fin 6 → Equiv.Perm (Fin 3) :=
  ![1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2, Equiv.swap 0 1 * Equiv.swap 1 2,
    Equiv.swap 1 2 * Equiv.swap 0 1]

/-- Their tables. -/
def p3T (p : Fin 6) (x : Fin 3) : Fin 3 :=
  ⟨lk [[0, 1, 2], [1, 0, 2], [2, 1, 0], [0, 2, 1], [1, 2, 0], [2, 0, 1]] p x % 3,
    Nat.mod_lt _ (by decide)⟩

lemma perm3_apply : ∀ (p : Fin 6) (x : Fin 3), perm3 p x = p3T p x := by decide

/-- The index of the conjugate `c * i * c⁻¹` (raw data). -/
def cjL : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23], [0, 1, 5, 4, 3, 2, 6, 7, 11, 10, 9, 8, 19, 18, 21, 20, 23, 22, 13, 12, 15, 14,
    17, 16], [0, 5, 2, 4, 3, 1, 14, 16, 12, 17, 13, 15, 8, 10, 6, 11, 7, 9, 22, 20, 19, 21, 18,
    23], [0, 5, 1, 3, 4, 2, 14, 16, 15, 13, 17, 12, 20, 22, 21, 19, 23, 18, 10, 8, 11, 6, 9, 7],
    [0, 2, 5, 3, 4, 1, 21, 23, 19, 22, 18, 20, 11, 9, 6, 8, 7, 10, 17, 15, 12, 14, 13, 16], [0, 2,
    1, 4, 3, 5, 21, 23, 20, 18, 22, 19, 15, 17, 14, 12, 16, 13, 9, 11, 8, 6, 10, 7], [0, 1, 14, 15,
    20, 21, 6, 7, 12, 13, 18, 19, 8, 9, 2, 3, 23, 22, 10, 11, 4, 5, 17, 16], [0, 1, 21, 20, 15, 14,
    6, 7, 19, 18, 13, 12, 11, 10, 5, 4, 16, 17, 9, 8, 3, 2, 22, 23], [0, 21, 14, 20, 15, 1, 2, 23,
    8, 22, 9, 3, 12, 18, 6, 19, 7, 13, 17, 4, 11, 5, 10, 16], [0, 21, 1, 15, 20, 14, 2, 23, 3, 9,
    22, 8, 4, 17, 5, 11, 16, 10, 18, 12, 19, 6, 13, 7], [0, 14, 21, 15, 20, 1, 5, 16, 11, 17, 10,
    4, 19, 13, 6, 12, 7, 18, 22, 3, 8, 2, 9, 23], [0, 14, 1, 20, 15, 21, 5, 16, 4, 10, 17, 11, 3,
    22, 2, 8, 23, 9, 13, 19, 12, 6, 18, 7], [0, 5, 6, 11, 19, 21, 14, 16, 8, 10, 22, 20, 12, 17, 2,
    4, 23, 18, 13, 15, 3, 1, 9, 7], [0, 5, 21, 19, 11, 6, 14, 16, 20, 22, 10, 8, 15, 13, 1, 3, 7,
    9, 17, 12, 4, 2, 18, 23], [0, 21, 6, 19, 11, 5, 2, 23, 12, 18, 17, 4, 8, 22, 14, 20, 16, 10, 9,
    3, 15, 1, 13, 7], [0, 21, 5, 11, 19, 6, 2, 23, 4, 17, 18, 12, 3, 9, 1, 15, 7, 13, 22, 8, 20,
    14, 10, 16], [0, 6, 21, 11, 19, 5, 1, 7, 15, 9, 13, 3, 20, 10, 14, 8, 16, 22, 18, 4, 12, 2, 17,
    23], [0, 6, 5, 19, 11, 21, 1, 7, 3, 13, 9, 15, 4, 18, 2, 12, 23, 17, 10, 20, 8, 14, 22, 16],
    [0, 2, 6, 8, 12, 14, 21, 23, 11, 9, 17, 15, 19, 22, 5, 3, 16, 13, 18, 20, 4, 1, 10, 7], [0, 2,
    14, 12, 8, 6, 21, 23, 15, 17, 9, 11, 20, 18, 1, 4, 7, 10, 22, 19, 3, 5, 13, 16], [0, 14, 6, 12,
    8, 2, 5, 16, 19, 13, 22, 3, 11, 17, 21, 15, 23, 9, 10, 4, 20, 1, 18, 7], [0, 14, 2, 8, 12, 6,
    5, 16, 3, 22, 13, 19, 4, 10, 1, 20, 7, 18, 17, 11, 15, 21, 9, 23], [0, 6, 14, 8, 12, 2, 1, 7,
    20, 10, 18, 4, 15, 9, 21, 11, 23, 17, 13, 3, 19, 5, 22, 16], [0, 6, 2, 12, 8, 14, 1, 7, 4, 18,
    10, 20, 3, 13, 5, 19, 16, 22, 9, 15, 11, 21, 17, 23]]

/-- The index of the conjugate `c * i * c⁻¹`. -/
def cj (c i : Fin 24) : Fin 24 := ⟨lk cjL c i % 24, Nat.mod_lt _ (by decide)⟩

lemma cj_spec : ∀ (c i : Fin 24) (x : Fin 4), tab (cj c i) x = tab c (tab i (tab (tinv c) x)) := by
  decide +kernel

lemma conjT_tab (c : Fin 24) (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4)) (t : Fin 3 → Fin 24)
    (ht : ∀ x, ⇑(T (FreeMonoid.of x)) = tab (t x)) (x : Fin 3) :
    ⇑(conjT (permOf c) T (FreeMonoid.of x)) = tab (cj c (t x)) := by
  funext y
  rw [conjT_of, cj_spec]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, coe_permOf, ht]
  rfl

/-! ### The class representatives -/

/-- The letters of the `56` class representatives: `K01`–`K45`, then the ten lifted classes of
`StarHeightS4ThreeHitsA/B` (in file order), then `S4Cox.coxT`. -/
def repL : List (List (List ℕ)) := [K01.L, K02.L, K03.L, K04.L, K05.L, K06.L, K07.L, K08.L, K09.L,
    K10.L, K11.L, K12.L, K13.L, K14.L, K15.L, K16.L, K17.L, K18.L, K19.L, K20.L, K21.L, K22.L,
    K23.L, K24.L, K25.L, K26.L, K27.L, K28.L, K29.L, K30.L, K31.L, K32.L, K33.L, K34.L, K35.L,
    K36.L, K37.L, K38.L, K39.L, K40.L, K41.L, K42.L, K43.L, K44.L, K45.L, [[0, 1, 3, 2], [0, 2, 1,
    3], [3, 0, 1, 2]], [[0, 1, 3, 2], [0, 2, 1, 3], [3, 0, 2, 1]], [[0, 1, 3, 2], [0, 2, 1, 3], [2,
    1, 0, 3]], [[0, 1, 3, 2], [0, 3, 1, 2], [1, 0, 2, 3]], [[0, 1, 3, 2], [1, 0, 2, 3], [3, 0, 1,
    2]], [[0, 1, 3, 2], [2, 0, 1, 3], [3, 0, 2, 1]], [[0, 1, 3, 2], [2, 0, 1, 3], [3, 2, 0, 1]],
    [[0, 1, 3, 2], [2, 0, 1, 3], [1, 3, 2, 0]], [[0, 3, 1, 2], [2, 0, 1, 3], [3, 2, 0, 1]], [[0, 3,
    1, 2], [2, 0, 3, 1], [3, 2, 0, 1]], [[1, 0, 2, 3], [0, 2, 1, 3], [0, 1, 3, 2]]]

/-- **Every class representative.** -/
theorem classHeight : ∀ k : Fin 56, ∀ T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4),
    (∀ x i, T (FreeMonoid.of x) i = letT (repL.getD k []) x i) → AllHeightOne T := by
  intro k
  fin_cases k
  · exact fun T hT => K01.height_one T hT
  · exact fun T hT => K02.height_one T hT
  · exact fun T hT => K03.height_one T hT
  · exact fun T hT => K04.height_one T hT
  · exact fun T hT => K05.height_one T hT
  · exact fun T hT => K06.height_one T hT
  · exact fun T hT => K07.height_one T hT
  · exact fun T hT => K08.height_one T hT
  · exact fun T hT => K09.height_one T hT
  · exact fun T hT => K10.height_one T hT
  · exact fun T hT => K11.height_one T hT
  · exact fun T hT => K12.height_one T hT
  · exact fun T hT => K13.height_one T hT
  · exact fun T hT => K14.height_one T hT
  · exact fun T hT => K15.height_one T hT
  · exact fun T hT => K16.height_one T hT
  · exact fun T hT => K17.height_one T hT
  · exact fun T hT => K18.height_one T hT
  · exact fun T hT => K19.height_one T hT
  · exact fun T hT => K20.height_one T hT
  · exact fun T hT => K21.height_one T hT
  · exact fun T hT => K22.height_one T hT
  · exact fun T hT => K23.height_one T hT
  · exact fun T hT => K24.height_one T hT
  · exact fun T hT => K25.height_one T hT
  · exact fun T hT => K26.height_one T hT
  · exact fun T hT => K27.height_one T hT
  · exact fun T hT => K28.height_one T hT
  · exact fun T hT => K29.height_one T hT
  · exact fun T hT => K30.height_one T hT
  · exact fun T hT => K31.height_one T hT
  · exact fun T hT => K32.height_one T hT
  · exact fun T hT => K33.height_one T hT
  · exact fun T hT => K34.height_one T hT
  · exact fun T hT => K35.height_one T hT
  · exact fun T hT => K36.height_one T hT
  · exact fun T hT => K37.height_one T hT
  · exact fun T hT => K38.height_one T hT
  · exact fun T hT => K39.height_one T hT
  · exact fun T hT => K40.height_one T hT
  · exact fun T hT => K41.height_one T hT
  · exact fun T hT => K42.height_one T hT
  · exact fun T hT => K43.height_one T hT
  · exact fun T hT => K44.height_one T hT
  · exact fun T hT => K45.height_one T hT
  · intro T hT
    have hTc : T = C0132_0213_1230.T := FreeMonoid.hom_eq fun x => Equiv.ext fun i => by
      rw [hT, C0132_0213_1230.T_of]
      revert x i
      decide
    subst hTc
    exact C0132_0213_1230.height_one
  · intro T hT
    have hTc : T = C0132_0213_1320.T := FreeMonoid.hom_eq fun x => Equiv.ext fun i => by
      rw [hT, C0132_0213_1320.T_of]
      revert x i
      decide
    subst hTc
    exact C0132_0213_1320.height_one
  · intro T hT
    have hTc : T = C0132_0213_2103.T := FreeMonoid.hom_eq fun x => Equiv.ext fun i => by
      rw [hT, C0132_0213_2103.T_of]
      revert x i
      decide
    subst hTc
    exact C0132_0213_2103.height_one
  · intro T hT
    have hTc : T = C0132_0231_1023.T := FreeMonoid.hom_eq fun x => Equiv.ext fun i => by
      rw [hT, C0132_0231_1023.T_of]
      revert x i
      decide
    subst hTc
    exact C0132_0231_1023.height_one
  · intro T hT
    have hTc : T = C0132_1023_1230.T := FreeMonoid.hom_eq fun x => Equiv.ext fun i => by
      rw [hT, C0132_1023_1230.T_of]
      revert x i
      decide
    subst hTc
    exact C0132_1023_1230.height_one
  · intro T hT
    have hTc : T = C0132_1203_1320.T := FreeMonoid.hom_eq fun x => Equiv.ext fun i => by
      rw [hT, C0132_1203_1320.T_of]
      revert x i
      decide
    subst hTc
    exact C0132_1203_1320.height_one
  · intro T hT
    have hTc : T = C0132_1203_2310.T := FreeMonoid.hom_eq fun x => Equiv.ext fun i => by
      rw [hT, C0132_1203_2310.T_of]
      revert x i
      decide
    subst hTc
    exact C0132_1203_2310.height_one
  · intro T hT
    have hTc : T = C0132_1203_3021.T := FreeMonoid.hom_eq fun x => Equiv.ext fun i => by
      rw [hT, C0132_1203_3021.T_of]
      revert x i
      decide
    subst hTc
    exact C0132_1203_3021.height_one
  · intro T hT
    have hTc : T = C0231_1203_2310.T := FreeMonoid.hom_eq fun x => Equiv.ext fun i => by
      rw [hT, C0231_1203_2310.T_of]
      revert x i
      decide
    subst hTc
    exact C0231_1203_2310.height_one
  · intro T hT
    have hTc : T = C0231_1302_2310.T := FreeMonoid.hom_eq fun x => Equiv.ext fun i => by
      rw [hT, C0231_1302_2310.T_of]
      revert x i
      decide
    subst hTc
    exact C0231_1302_2310.height_one
  · intro T hT
    have hTc : T = S4Cox.coxT := FreeMonoid.hom_eq fun x => Equiv.ext fun i => by
      rw [hT, S4Cox.coxT, FreeMonoid.lift_eval_of]
      revert x i
      decide
    subst hTc
    exact S4Cox.height_one_S4_coxeter

/-! ### The final check -/

/-- The triple `a, b, c` is the class representative `k` after the permutation `p` of the letters
and conjugation by `cc`. -/
def classOK (k : ℕ) (p : Fin 6) (cc a b c : Fin 24) : Bool :=
  (List.finRange 3).all fun x => (List.finRange 4).all fun i =>
    decide (tab cc (tab (![a, b, c] (p3T p x)) (tab (tinv cc) i)) = letT (repL.getD k []) x i)

/-- The parts of a witness. -/
def wM (n : ℕ) : Fin 8 := ⟨n / 4 % 8, Nat.mod_lt _ (by decide)⟩

/-- See `wM`. -/
def wK (n : ℕ) : Fin 56 := ⟨n / 4 % 56, Nat.mod_lt _ (by decide)⟩

/-- See `wM`. -/
def wP (n : ℕ) : Fin 6 := ⟨n / 224 % 6, Nat.mod_lt _ (by decide)⟩

/-- See `wM`. -/
def wC (n : ℕ) : Fin 24 := ⟨n / 1344 % 24, Nat.mod_lt _ (by decide)⟩

/-- **The check of a witness `n` for the letter triple `a, b, c`.**  `n % 4`: `0` a double
transposition, `1` two equal letters, `2` a common maximal subgroup `wM n`, `3` the class `wK n`
after the permutation `wP n` and conjugation by `wC n`. -/
def fin3 (a b c : Fin 24) (n : ℕ) : Bool :=
  if n % 4 = 0 then dblT a || dblT b || dblT c
  else if n % 4 = 1 then decide (a = b) || decide (a = c) || decide (b = c)
  else if n % 4 = 2 then inMax (wM n) a && inMax (wM n) b && inMax (wM n) c
  else classOK (wK n) (wP n) (wC n) a b c

lemma vec_three (t : Fin 3 → Fin 24) (y : Fin 3) : ![t 0, t 1, t 2] y = t y := by
  fin_cases y <;> rfl

lemma eq_of_tab {σ τ : Equiv.Perm (Fin 4)} {i j : Fin 24} (hσ : ⇑σ = tab i) (hτ : ⇑τ = tab j)
    (h : i = j) : σ = τ :=
  DFunLike.coe_injective (hσ.trans (h ▸ hτ.symm))

/-- **Soundness of the final check.** -/
theorem allHeightOne_of_fin3 (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : ∀ x, T (FreeMonoid.of x) ∉ dbl) (t : Fin 3 → Fin 24)
    (ht : ∀ x, ⇑(T (FreeMonoid.of x)) = tab (t x)) (n : ℕ)
    (h : fin3 (t 0) (t 1) (t 2) n = true) : AllHeightOne T := by
  unfold fin3 at h
  split_ifs at h
  · simp only [Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact absurd (mem_dbl_of_dblT (ht 0) h) (hT 0)
    · exact absurd (mem_dbl_of_dblT (ht 1) h) (hT 1)
    · exact absurd (mem_dbl_of_dblT (ht 2) h) (hT 2)
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with (h | h) | h
    · exact allHeightOne_of_eq01 T (eq_of_tab (ht 0) (ht 1) h)
    · exact allHeightOne_of_eq02 T (eq_of_tab (ht 0) (ht 2) h)
    · exact allHeightOne_of_eq12 T (eq_of_tab (ht 1) (ht 2) h)
  · simp only [Bool.and_eq_true] at h
    refine fun F => height_one_of_mem_proper (maxSub (wM n)) (maxSub_ne_top _) T
      (fun x => ?_) F
    fin_cases x
    · exact mem_maxSub (ht 0) h.1.1
    · exact mem_maxSub (ht 1) h.1.2
    · exact mem_maxSub (ht 2) h.2
  · simp only [classOK, List.all_eq_true, List.mem_finRange, decide_eq_true_eq, true_implies,
      vec_three] at h
    refine allHeightOne_of_perm (perm3 (wP n)) T ?_
    refine allHeightOne_of_conj (permOf (wC n)) _ ?_
    refine classHeight (wK n) _ fun x i => ?_
    rw [conjT_of, ← h x i]
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, coe_permOf, MonoidHom.coe_comp,
      FreeMonoid.map_of, perm3_apply, ht]
    rfl

/-! ### The three stages -/

/-- Representatives of the five cycle types: `1`, `(2 3)`, `(0 1)(2 3)`, `(1 2 3)`, `(0 1 2 3)`. -/
def R0 : List (Fin 24) := [0, 1, 7, 3, 9]

/-- Stage 1: a conjugator taking the first letter to `R0` (raw data). -/
def w1L : List ℕ := [0, 0, 3, 0, 1, 2, 16, 0, 9, 0, 1, 8, 11, 4, 13, 6, 2, 2, 5, 10, 7, 12, 3, 3]

/-- Stage 1: a conjugator taking the first letter to `R0`. -/
def w1 (a : Fin 24) : Fin 24 := ⟨w1L.getD a 0 % 24, Nat.mod_lt _ (by decide)⟩

/-- Stage 2: a conjugator in the centralizer of the first letter (raw data). -/
def w2L : List (List ℕ) := [[0, 0, 3, 0, 1, 2, 16, 0, 9, 0, 1, 8, 11, 4, 13, 6, 2, 2, 5, 10, 7, 12,
    3, 3], [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 6, 6, 6, 6, 0, 0, 7, 7, 7, 7, 1, 1], [], [0, 0, 3,
    0, 0, 4, 0, 0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3], [], [], [], [0, 0, 0, 0, 1, 1,
    16, 0, 17, 0, 1, 16, 23, 6, 6, 6, 0, 0, 7, 22, 7, 7, 1, 1], [], [0, 0, 9, 0, 0, 0, 16, 0, 9, 0,
    0, 16, 9, 16, 9, 18, 0, 9, 0, 16, 18, 18, 18, 9], [], [], [], [], [], [], [], [], [], [], [],
    [], [], []]

/-- Stage 2: a conjugator in the centralizer of the first letter. -/
def w2 (r b : Fin 24) : Fin 24 := ⟨lk w2L r b % 24, Nat.mod_lt _ (by decide)⟩

/-- Pairs of `P3`, part 0. -/
def P3_0 : List (Fin 24 × Fin 24) := [(0, 0), (0, 1), (0, 3), (0, 7), (0, 9)]

/-- Pairs of `P3`, part 1. -/
def P3_1 : List (Fin 24 × Fin 24) := [(1, 0), (1, 1), (1, 2), (1, 3), (1, 6)]

/-- Pairs of `P3`, part 2. -/
def P3_2 : List (Fin 24 × Fin 24) := [(1, 7), (1, 8), (1, 9), (1, 16), (1, 17)]

/-- Pairs of `P3`, part 3. -/
def P3_3 : List (Fin 24 × Fin 24) := [(7, 0), (7, 1), (7, 2), (7, 3), (7, 7)]

/-- Pairs of `P3`, part 4. -/
def P3_4 : List (Fin 24 × Fin 24) := [(7, 9), (7, 16), (7, 17), (3, 0), (3, 1)]

/-- Pairs of `P3`, part 5. -/
def P3_5 : List (Fin 24 × Fin 24) := [(3, 3), (3, 4), (3, 6), (3, 7), (3, 8)]

/-- Pairs of `P3`, part 6. -/
def P3_6 : List (Fin 24 × Fin 24) := [(3, 9), (3, 10), (3, 11), (9, 0), (9, 1)]

/-- Pairs of `P3`, part 7. -/
def P3_7 : List (Fin 24 × Fin 24) := [(9, 3), (9, 4), (9, 5), (9, 7), (9, 9)]

/-- Pairs of `P3`, part 8. -/
def P3_8 : List (Fin 24 × Fin 24) := [(9, 10), (9, 16), (9, 18)]

/-- The pairs of letters that remain after stage 2. -/
def P3 : List (Fin 24 × Fin 24) :=
  P3_0 ++ P3_1 ++ P3_2 ++ P3_3 ++ P3_4 ++ P3_5 ++ P3_6 ++ P3_7 ++ P3_8

/-- Stage 3: the witnesses, row `j` for the `j`-th pair of `P3` (raw data). -/
def w3L : List (List ℕ) := [[1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1,
    0], [1, 1, 2, 2, 2, 2, 18, 0, 3, 7, 1351, 1347, 8067, 8071, 6, 6, 0, 18, 9415, 9411, 6, 6, 18,
    0], [1, 2, 2, 1, 2, 2, 30243, 0, 30, 11, 15, 30, 30, 5387, 28899, 30, 0, 5391, 4047, 30, 30,
    24867, 4043, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1,
    679, 12775, 683, 2031, 22, 22183, 0, 12779, 1, 19, 22187, 15471, 21523, 22, 24875, 0, 12115,
    22, 30255, 16815, 24871, 24211, 0], [1, 1, 2, 2, 2, 2, 18, 0, 227, 231, 1575, 1571, 8291, 8295,
    6, 6, 0, 18, 9639, 9635, 6, 6, 18, 0], [1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1,
    1, 1, 1, 1, 1, 0], [2, 1, 1, 2, 2, 2, 31135, 0, 23, 7127, 27, 7131, 31, 35, 191, 6975, 0, 6979,
    183, 187, 6967, 24639, 6971, 0], [2, 1, 2, 1, 2, 2, 1539, 0, 39, 43, 47, 51, 55, 59, 26687, 63,
    0, 67, 71, 75, 79, 25335, 83, 0], [18, 1, 31807, 2211, 867, 30463, 1, 0, 32003, 9607, 8263,
    30659, 23939, 1543, 23743, 10275, 0, 18, 199, 22595, 8931, 22399, 18, 0], [0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1123, 1, 695, 711, 2067, 6683, 31555, 0,
    1, 87, 91, 8267, 95, 99, 8767, 8791, 0, 8271, 103, 8275, 10155, 10267, 107, 0], [1127, 1, 8023,
    715, 2063, 2043, 10279, 0, 759, 1, 111, 2107, 8835, 115, 8771, 8795, 0, 119, 123, 10183, 10151,
    10263, 127, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [18,
    1, 7875, 739, 2099, 6523, 18, 0, 8943, 791, 2143, 2123, 8843, 8863, 26683, 8819, 0, 1, 10199,
    2223, 10147, 25347, 18, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 2, 2, 1, 2, 2, 30467, 0, 30, 235, 239,
    30, 30, 5611, 29123, 30, 0, 5615, 4271, 30, 30, 25091, 4267, 0], [2, 1, 2, 1, 2, 2, 1763, 0,
    263, 267, 271, 275, 279, 283, 26015, 287, 0, 291, 295, 299, 303, 24663, 307, 0], [1, 1, 1, 1,
    1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0], [2, 2, 2, 1, 1, 2, 31455, 0, 30,
    131, 1699, 30, 30, 5507, 26079, 30, 0, 3043, 7075, 30, 30, 27423, 4163, 0], [30019, 2659,
    31839, 1, 29887, 30487, 1, 0, 23819, 29883, 29895, 22451, 31863, 29879, 23931, 31339, 0, 31343,
    29891, 30503, 31347, 19451, 29899, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0], [30, 1159, 12607, 1, 30, 6571, 23371, 0, 1, 135, 139, 30, 30, 28587, 28711,
    30, 0, 31351, 2903, 30, 30, 19467, 28583, 0], [1131, 1163, 5211, 1, 803, 6579, 30779, 0, 807,
    1, 143, 147, 151, 155, 29451, 25447, 0, 159, 163, 30827, 167, 25399, 4859, 0], [1135, 1167,
    5219, 1, 2595, 6567, 30791, 0, 811, 815, 1, 11367, 171, 6211, 29443, 7607, 0, 7611, 2907,
    28215, 26135, 28207, 4863, 0], [30, 1171, 5207, 1, 30, 11279, 22003, 0, 30, 819, 11815, 1, 30,
    6215, 20819, 30, 0, 27927, 4875, 30, 30, 27383, 4855, 0], [1, 903, 12999, 907, 2255, 22, 22407,
    0, 13003, 1, 243, 22411, 15695, 21747, 22, 25099, 0, 12339, 22, 30479, 17039, 25095, 24435, 0],
    [455, 1, 7351, 939, 2287, 2267, 31559, 0, 983, 1, 335, 2331, 9059, 339, 8995, 9019, 0, 343,
    347, 10407, 10375, 10487, 351, 0], [459, 491, 4539, 1, 1027, 5907, 30107, 0, 1031, 1, 367, 371,
    375, 379, 28779, 24775, 0, 383, 387, 30155, 391, 24727, 5083, 0], [1807, 1839, 7239, 579, 1,
    3203, 31463, 0, 13383, 1, 2383, 2379, 28887, 4475, 28879, 25463, 0, 3743, 7779, 1739, 6487,
    27427, 6491, 0], [22, 1819, 4515, 6355, 3651, 1, 30043, 0, 11755, 1, 11775, 11731, 11855, 6399,
    22, 6379, 0, 3703, 22, 14403, 6479, 27363, 14455, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 1, 0], [1811, 1903, 13343, 1263, 1935, 11327, 23411, 0, 23451, 1, 1, 22779, 28891, 175,
    26103, 25471, 0, 179, 1743, 28219, 26143, 25431, 1747, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [22, 9979, 7291, 1283, 7331, 22, 31483, 0, 13379, 1,
    23471, 22787, 31523, 8687, 22, 25475, 0, 27503, 1, 19427, 10019, 19387, 4655, 0]]

/-- Stage 3: the witness for the pair `pr` and the third letter `c`. -/
def w3 (pr : Fin 24 × Fin 24) (c : Fin 24) : ℕ := lk w3L (P3.idxOf pr) c

lemma stage1_check : ∀ a : Fin 24, cj (w1 a) a ∈ R0 := by decide +kernel

lemma stage2_check : ∀ r ∈ R0, ∀ b : Fin 24, cj (w2 r b) r = r ∧ (r, cj (w2 r b) b) ∈ P3 := by
  decide +kernel

lemma stage3_check_0 : ∀ pr ∈ P3_0, ∀ c : Fin 24, fin3 pr.1 pr.2 c (w3 pr c) = true := by
  decide +kernel

lemma stage3_check_1 : ∀ pr ∈ P3_1, ∀ c : Fin 24, fin3 pr.1 pr.2 c (w3 pr c) = true := by
  decide +kernel

lemma stage3_check_2 : ∀ pr ∈ P3_2, ∀ c : Fin 24, fin3 pr.1 pr.2 c (w3 pr c) = true := by
  decide +kernel

lemma stage3_check_3 : ∀ pr ∈ P3_3, ∀ c : Fin 24, fin3 pr.1 pr.2 c (w3 pr c) = true := by
  decide +kernel

lemma stage3_check_4 : ∀ pr ∈ P3_4, ∀ c : Fin 24, fin3 pr.1 pr.2 c (w3 pr c) = true := by
  decide +kernel

lemma stage3_check_5 : ∀ pr ∈ P3_5, ∀ c : Fin 24, fin3 pr.1 pr.2 c (w3 pr c) = true := by
  decide +kernel

lemma stage3_check_6 : ∀ pr ∈ P3_6, ∀ c : Fin 24, fin3 pr.1 pr.2 c (w3 pr c) = true := by
  decide +kernel

lemma stage3_check_7 : ∀ pr ∈ P3_7, ∀ c : Fin 24, fin3 pr.1 pr.2 c (w3 pr c) = true := by
  decide +kernel

lemma stage3_check_8 : ∀ pr ∈ P3_8, ∀ c : Fin 24, fin3 pr.1 pr.2 c (w3 pr c) = true := by
  decide +kernel

lemma stage3_check : ∀ pr ∈ P3, ∀ c : Fin 24, fin3 pr.1 pr.2 c (w3 pr c) = true := by
  intro pr hpr
  simp only [P3, List.mem_append, or_assoc] at hpr
  rcases hpr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact stage3_check_0 pr h0
  · exact stage3_check_1 pr h1
  · exact stage3_check_2 pr h2
  · exact stage3_check_3 pr h3
  · exact stage3_check_4 pr h4
  · exact stage3_check_5 pr h5
  · exact stage3_check_6 pr h6
  · exact stage3_check_7 pr h7
  · exact stage3_check_8 pr h8

lemma allHeightOne_of_P3 (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : ∀ x, T (FreeMonoid.of x) ∉ dbl) (t : Fin 3 → Fin 24)
    (ht : ∀ x, ⇑(T (FreeMonoid.of x)) = tab (t x)) (hp : (t 0, t 1) ∈ P3) : AllHeightOne T :=
  allHeightOne_of_fin3 T hT t ht _ (stage3_check _ hp (t 2))

lemma allHeightOne_of_R0 (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : ∀ x, T (FreeMonoid.of x) ∉ dbl) (t : Fin 3 → Fin 24)
    (ht : ∀ x, ⇑(T (FreeMonoid.of x)) = tab (t x)) (h0 : t 0 ∈ R0) : AllHeightOne T := by
  obtain ⟨hc0, hc1⟩ := stage2_check (t 0) h0 (t 1)
  refine allHeightOne_of_conj (permOf (w2 (t 0) (t 1))) T ?_
  refine allHeightOne_of_P3 _ (fun x => by rw [conjT_of]; exact conj_not_dbl _ (hT x))
    (fun x => cj (w2 (t 0) (t 1)) (t x)) (conjT_tab _ T t ht) ?_
  rw [hc0]
  exact hc1

/-! ### The theorems -/

/-- **Every language over three letters recognized by `S₄`, no letter of which is a double
transposition, has generalized star height at most one.** -/
theorem height_one_S4_three_letters (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : ∀ x, T (FreeMonoid.of x) ∉ dbl) (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  choose t ht using fun x => perm_tab (T (FreeMonoid.of x))
  refine allHeightOne_of_conj (permOf (w1 (t 0))) T ?_ F
  exact allHeightOne_of_R0 _ (fun x => by rw [conjT_of]; exact conj_not_dbl _ (hT x))
    (fun x => cj (w1 (t 0)) (t x)) (conjT_tab _ T t ht) (stage1_check (t 0))

/-- **The same, when the letters may instead lie in a proper subgroup of `S₄`.** -/
theorem height_one_S4_three_letters_or_proper (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : (∀ x, T (FreeMonoid.of x) ∉ dbl) ∨
      Subgroup.closure (Set.range fun x => T (FreeMonoid.of x)) ≠ ⊤)
    (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  rcases hT with hT | hT
  · exact height_one_S4_three_letters T hT F
  · exact height_one_of_mem_proper _ hT T (fun x => Subgroup.subset_closure ⟨x, rfl⟩) F

end S4Three

end GeneralizedStarHeight
