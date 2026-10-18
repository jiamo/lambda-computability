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
@CJL@

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
@REPL@

/-- **Every class representative.** -/
theorem classHeight : ∀ k : Fin 56, ∀ T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4),
    (∀ x i, T (FreeMonoid.of x) i = letT (repL.getD k []) x i) → AllHeightOne T := by
  intro k
  fin_cases k
@CASES@

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
@W1L@

/-- Stage 1: a conjugator taking the first letter to `R0`. -/
def w1 (a : Fin 24) : Fin 24 := ⟨w1L.getD a 0 % 24, Nat.mod_lt _ (by decide)⟩

/-- Stage 2: a conjugator in the centralizer of the first letter (raw data). -/
@W2L@

/-- Stage 2: a conjugator in the centralizer of the first letter. -/
def w2 (r b : Fin 24) : Fin 24 := ⟨lk w2L r b % 24, Nat.mod_lt _ (by decide)⟩

@P3@

/-- Stage 3: the witnesses, row `j` for the `j`-th pair of `P3` (raw data). -/
@W3L@

/-- Stage 3: the witness for the pair `pr` and the third letter `c`. -/
def w3 (pr : Fin 24 × Fin 24) (c : Fin 24) : ℕ := lk w3L (P3.idxOf pr) c

lemma stage1_check : ∀ a : Fin 24, cj (w1 a) a ∈ R0 := by decide +kernel

lemma stage2_check : ∀ r ∈ R0, ∀ b : Fin 24, cj (w2 r b) r = r ∧ (r, cj (w2 r b) b) ∈ P3 := by
  decide +kernel

@STAGE3@

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
