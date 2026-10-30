import Start.MartinLof

/-!
# Big round 2, run 2, item W9: the halves of a Martin-Löf random join are random
(row M24-VAN-LAMBALGEN)

The unrelativized half of van Lambalgen's theorem, for the Martin-Löf tests of
`Start/MartinLof.lean`: if the join `A ⊕ B` (with `A` on the even and `B` on the odd positions) is
Martin-Löf random, so are `A` and `B`.

* `halfSeq b Z = (n ↦ Z (2n + b))` and its finite-string analogue `halfList b`;
* **`map_halfSeq_cantorMeasure`** — taking every second bit preserves the fair-coin measure;
* `openOf_half` — the open set of the strings whose half lies in `S` is the preimage of `openOf S`;
* `MLTest.half b T` — the pull-back of a test along `halfSeq b` (`MLTest.half_level`);
* **`MLRandom.join_left`**, **`MLRandom.join_right`**;
* relativized tests: `MLTestRel X` (enumeration matrix computable in the oracle `X`, Mathlib's
  `ComputableIn`), `MLRandomRel X Z`, and `MLRandomRel.mlRandom`.
-/

set_option autoImplicit false

namespace Lambda

open MeasureTheory

/-- Every second bit of a sequence, starting at position `b`. -/
def halfSeq (b : ℕ) (Z : ℕ → Bool) : ℕ → Bool := fun n => Z (2 * n + b)

theorem measurable_halfSeq (b : ℕ) : Measurable (halfSeq b) :=
  Measurable.of_eval fun n => measurable_pi_apply (2 * n + b)

/-- `n ↦ 2n + b`, as an embedding. -/
def halfEmb (b : ℕ) : ℕ ↪ ℕ := ⟨(2 * · + b), fun x y h => by simp only at h; omega⟩

@[simp] theorem halfEmb_apply (b n : ℕ) : halfEmb b n = 2 * n + b := rfl

theorem halfEmb_div (b n : ℕ) (hb : b < 2) : (2 * n + b) / 2 = n := by omega

/-- **Taking every second bit preserves the fair-coin measure.** -/
theorem map_halfSeq_cantorMeasure (b : ℕ) (hb : b < 2) :
    cantorMeasure.map (halfSeq b) = cantorMeasure := by
  unfold cantorMeasure
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  rw [Measure.map_apply (measurable_halfSeq b) (.pi s.countable_toSet fun i _ => ht i)]
  have hpre : halfSeq b ⁻¹' Set.pi (↑s) t =
      Set.pi (↑(s.map (halfEmb b))) (fun i => t (i / 2)) := by
    ext Z
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_map, halfEmb_apply,
      Set.mem_image, Finset.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      halfSeq]
    refine forall₂_congr fun a _ => ?_
    rw [halfEmb_div b a hb]
  rw [hpre, Measure.infinitePi_pi _ (fun i _ => ht _), Finset.prod_map]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [halfEmb_apply]
  rw [halfEmb_div b i hb]

/-- Every second bit of a finite string, starting at position `b`. -/
def halfList (b : ℕ) (τ : List Bool) : List Bool :=
  (List.range ((τ.length + 1 - b) / 2)).map fun i => τ.getD (2 * i + b) Bool.false

@[simp] theorem halfList_length (b : ℕ) (τ : List Bool) :
    (halfList b τ).length = (τ.length + 1 - b) / 2 := by
  simp [halfList]

theorem halfList_getElem (b : ℕ) (τ : List Bool) (i : ℕ) (h : i < (halfList b τ).length) :
    (halfList b τ)[i] = τ.getD (2 * i + b) Bool.false := by
  simp [halfList]

theorem primrec_halfList (b : ℕ) : Primrec (halfList b) := by
  have h1 : Primrec fun τ : List Bool => List.range ((τ.length + 1 - b) / 2) :=
    Primrec.list_range.comp
      (Primrec.nat_div.comp
        (Primrec.nat_sub.comp (Primrec.succ.comp Primrec.list_length) (Primrec.const b))
        (Primrec.const 2))
  have h2 : Primrec₂ fun (τ : List Bool) (i : ℕ) => τ.getD (2 * i + b) Bool.false :=
    (Primrec.list_getD Bool.false).comp Primrec.fst
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
        (Primrec.const b))
  exact Primrec.list_map h1 h2

theorem halfSeq_mem_cylinder (b : ℕ) {Z : ℕ → Bool} {τ : List Bool} (h : Z ∈ cylinder τ) :
    halfSeq b Z ∈ cylinder (halfList b τ) := by
  intro i hi
  rw [halfList_getElem]
  have hi' : 2 * i + b < τ.length := by simp at hi; omega
  rw [List.getD_eq_getElem _ _ hi']
  exact h (2 * i + b) hi'

/-- The open set of the strings whose half lies in `S` is the preimage of `openOf S`. -/
theorem openOf_half (b : ℕ) (S : Set (List Bool)) :
    openOf {τ | halfList b τ ∈ S} = halfSeq b ⁻¹' openOf S := by
  ext Z
  simp only [Set.mem_preimage, mem_openOf, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨τ, hτ, hZ⟩
    exact ⟨_, hτ, halfSeq_mem_cylinder b hZ⟩
  · rintro ⟨σ, hσ, hZ⟩
    refine ⟨prefixList Z (2 * σ.length + b), ?_, mem_cylinder_prefixList Z _⟩
    have : halfList b (prefixList Z (2 * σ.length + b)) = σ := by
      refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
      rw [halfList_getElem]
      have hi : 2 * i + b < (prefixList Z (2 * σ.length + b)).length := by simp; omega
      rw [List.getD_eq_getElem _ _ hi, prefixList_getElem]
      exact hZ i h2
    rw [this]; exact hσ

theorem measurableSet_openOf (S : Set (List Bool)) : MeasurableSet (openOf S) :=
  MeasurableSet.biUnion S.to_countable fun σ _ => measurableSet_cylinder σ

theorem half_enter_computable (b : ℕ) (T : MLTest) :
    Computable fun p : ℕ × List Bool × ℕ => T.enter p.1 (halfList b p.2.1) p.2.2 := by
  have hg : Computable fun p : ℕ × List Bool × ℕ => (p.1, halfList b p.2.1, p.2.2) :=
    Computable.pair Computable.fst (Computable.pair
      ((primrec_halfList b).to_comp.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd))
  exact Computable.comp (f := fun q : ℕ × List Bool × ℕ => T.enter q.1 q.2.1 q.2.2)
    (g := fun p : ℕ × List Bool × ℕ => (p.1, halfList b p.2.1, p.2.2)) T.enter_computable hg

/-- The pull-back of a Martin-Löf test along `halfSeq b`. -/
def MLTest.half (b : ℕ) (hb : b < 2) (T : MLTest) : MLTest where
  enter c τ j := T.enter c (halfList b τ) j
  enter_computable := half_enter_computable b T
  measure_le c := by
    have e : openOf {τ | ∃ j, T.enter c (halfList b τ) j = Bool.true} =
        halfSeq b ⁻¹' openOf (T.strings c) := openOf_half b (T.strings c)
    rw [e, ← Measure.map_apply (measurable_halfSeq b) (measurableSet_openOf _),
      map_halfSeq_cantorMeasure b hb]
    exact T.measure_le c

theorem MLTest.half_level (b : ℕ) (hb : b < 2) (T : MLTest) (c : ℕ) (Z : ℕ → Bool) :
    Z ∈ (T.half b hb).level c ↔ halfSeq b Z ∈ T.level c := by
  have h1 : (T.half b hb).level c = openOf {τ | halfList b τ ∈ T.strings c} := rfl
  rw [h1, openOf_half]
  rfl

/-- If `halfSeq b Z` is not random, neither is `Z`. -/
theorem MLRandom.of_halfSeq (b : ℕ) (hb : b < 2) {Z : ℕ → Bool} (h : MLRandom Z) :
    MLRandom (halfSeq b Z) := by
  intro T
  obtain ⟨c, hc⟩ := h (T.half b hb)
  exact ⟨c, fun hZ => hc ((MLTest.half_level b hb T c Z).2 hZ)⟩

/-- **The even half of a Martin-Löf random join is Martin-Löf random.** -/
theorem MLRandom.join_left (A B : ℕ → Bool) :
    MLRandom (fun n => if n % 2 = 0 then A (n / 2) else B (n / 2)) → MLRandom A := by
  intro h
  have e : halfSeq 0 (fun n => if n % 2 = 0 then A (n / 2) else B (n / 2)) = A := by
    funext n; simp [halfSeq]
  simpa [e] using MLRandom.of_halfSeq 0 (by decide) h

/-- **The odd half of a Martin-Löf random join is Martin-Löf random.** -/
theorem MLRandom.join_right (A B : ℕ → Bool) :
    MLRandom (fun n => if n % 2 = 0 then A (n / 2) else B (n / 2)) → MLRandom B := by
  intro h
  have e : halfSeq 1 (fun n => if n % 2 = 0 then A (n / 2) else B (n / 2)) = B := by
    funext n
    simp only [halfSeq]
    rw [ite_eq_right (by omega)]
    congr 1
    omega
  simpa [e] using MLRandom.of_halfSeq 1 (by decide) h

/-! ### Relativized tests -/

/-- The oracle of a set `X ⊆ ℕ`, as a total function `ℕ → ℕ` (`1` on members, `0` elsewhere). -/
def oracleOf (X : ℕ → Bool) : Set (ℕ →. ℕ) := {fun n => Part.some (bif X n then 1 else 0)}

/-- A **Martin-Löf test relative to an oracle `X`**: as `MLTest`, with the enumeration matrix
computable in `X`. -/
structure MLTestRel (X : ℕ → Bool) where
  enter : ℕ → List Bool → ℕ → Bool
  enter_computableIn :
    ComputableIn (oracleOf X) fun p : ℕ × List Bool × ℕ => enter p.1 p.2.1 p.2.2
  measure_le : ∀ c : ℕ,
    cantorMeasure (openOf {σ | ∃ j, enter c σ j = Bool.true}) ≤ (2 : ENNReal)⁻¹ ^ c

/-- The `c`-th open set of a relativized test. -/
def MLTestRel.level {X : ℕ → Bool} (T : MLTestRel X) (c : ℕ) : Set (ℕ → Bool) :=
  openOf {σ | ∃ j, T.enter c σ j = Bool.true}

/-- **Martin-Löf randomness relative to `X`.** -/
def MLRandomRel (X Z : ℕ → Bool) : Prop := ∀ T : MLTestRel X, ∃ c, Z ∉ T.level c

/-- Every unrelativized test is a test relative to any oracle. -/
def MLTest.toRel (T : MLTest) (X : ℕ → Bool) : MLTestRel X where
  enter := T.enter
  enter_computableIn := T.enter_computable.computableIn
  measure_le := T.measure_le

/-- Randomness relative to an oracle implies randomness. -/
theorem MLRandomRel.mlRandom {X Z : ℕ → Bool} (h : MLRandomRel X Z) : MLRandom Z := fun T =>
  h (T.toRel X)

end Lambda
