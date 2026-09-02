/-
# From a Martin-Löf test to a Kraft–Chaitin request stream (superseded draft)

SCRATCH FILE.  This is an earlier draft of the construction that is now carried out, in full and
in the library proper, by `Start/OmegaURandom.lean` (`KC.discovered`, `KC.cutLength`,
`KC.covered`, `KC.piece`, `KC.testReq`, their computability, `KC.sum_wtOpt_testReq_le` and
`KC.mlRandom_omegaSeq`).  It is kept only as a record of the first attempt: it is not part of the
`Start` library target, nothing depends on it, and it does not compile (several of its
computability proofs exhaust the elaborator, which is exactly what the applied-composition
lemmas of `Start/OmegaURandom.lean` were written to avoid).

This file is the combinatorial heart of the converse half of the Levin–Schnorr theorem for the
universal prefix machine `KC.U` of `Start/KCMachine.lean`.

A Martin-Löf test `T` (`Lambda.MLTest`) enumerates, at each level `c`, a set of strings whose
cylinders cover an open set of measure at most `2 ^ (-c)`.  The enumeration is turned into a
*disjoint* one: the strings are discovered one at a time, and the `j`-th discovery is cut into
cylinders of a common length `KC.cutLength` — chosen at least `c` and at least every length seen
so far — from which everything already covered is removed.  The resulting family `KC.piece` is
pairwise incomparable, so the sum of its weights is at most the measure of the level, at most
`2 ^ (-c)`.

Feeding level `2 * k + 2` to the Kraft–Chaitin machine with a saving of `k` bits therefore costs
at most `2 ^ k * 2 ^ (-(2 * k + 2)) = 2 ^ (-(k + 2))`, and summing over `k` gives total weight at
most `1 / 2`.  The resulting request stream is `KC.testReq`.
-/

import Start.KCMachine
import Start.KCComputable
import Start.MartinLof

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace KC

open MeasureTheory

------------------------------------------------------------------------
-- Cylinders
------------------------------------------------------------------------

theorem eq_prefixList_of_mem_cylinder {σ : List Bool} {X : ℕ → Bool}
    (h : X ∈ Lambda.cylinder σ) : σ = Lambda.prefixList X σ.length := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  rw [Lambda.prefixList_getElem]
  exact (h i h1).symm

theorem prefix_or_prefix_of_mem_cylinder {σ τ : List Bool} {X : ℕ → Bool}
    (hσ : X ∈ Lambda.cylinder σ) (hτ : X ∈ Lambda.cylinder τ) : σ <+: τ ∨ τ <+: σ := by
  rcases Nat.le_total σ.length τ.length with h | h
  · left
    rw [eq_prefixList_of_mem_cylinder hσ, eq_prefixList_of_mem_cylinder hτ]
    exact Lambda.prefixList_prefix h
  · right
    rw [eq_prefixList_of_mem_cylinder hσ, eq_prefixList_of_mem_cylinder hτ]
    exact Lambda.prefixList_prefix h

theorem cylinder_disjoint {σ τ : List Bool} (h1 : ¬ σ <+: τ) (h2 : ¬ τ <+: σ) :
    Disjoint (Lambda.cylinder σ) (Lambda.cylinder τ) := by
  rw [Set.disjoint_left]
  intro X hX hX'
  rcases prefix_or_prefix_of_mem_cylinder hX hX' with h | h
  · exact h1 h
  · exact h2 h

theorem measurableSet_cylinder (σ : List Bool) : MeasurableSet (Lambda.cylinder σ) := by
  rw [Lambda.cylinder_eq_pi]
  exact MeasurableSet.pi (Set.toFinite _).countable fun i _ => MeasurableSet.singleton _

theorem prefix_eq_of_length {σ τ : List Bool} (h : σ <+: τ) (hlen : τ.length ≤ σ.length) :
    σ = τ :=
  h.eq_of_length (le_antisymm h.length_le hlen)

/-- Being a prefix is a primitive recursive relation on bit strings. -/
theorem primrec_isPrefix : PrimrecPred fun p : List Bool × List Bool => p.1 <+: p.2 := by
  have hlen : PrimrecPred fun p : List Bool × List Bool => p.1.length ≤ p.2.length :=
    Primrec.nat_le.comp (Primrec.list_length.comp Primrec.fst)
      (Primrec.list_length.comp Primrec.snd)
  have hval : PrimrecPred fun p : List Bool × List Bool =>
      BitStr.toNat p.1 = BitStr.toNat p.2 / 2 ^ (p.2.length - p.1.length) :=
    Primrec.eq.comp (BitStr.primrec_toNat.comp Primrec.fst)
      (Primrec.nat_div.comp (BitStr.primrec_toNat.comp Primrec.snd)
        (primrec_two_pow.comp (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.snd)
          (Primrec.list_length.comp Primrec.fst))))
  exact (hlen.and hval).of_eq fun _ => BitStr.prefix_iff.symm

------------------------------------------------------------------------
-- Discovering the strings of a level, one at a time
------------------------------------------------------------------------

/-- The bit string coded by a natural number. -/
def decodeStr (j : ℕ) : List Bool := (Encodable.decode (α := List Bool) j).getD []

theorem primrec_decodeStr : Primrec decodeStr :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

@[simp] theorem decodeStr_encode (σ : List Bool) : decodeStr (Encodable.encode σ) = σ := by
  simp [decodeStr]

/-- `σ` has not entered level `c` of the test at any stage below `s`. -/
def noEnter (T : Lambda.MLTest) (p : ℕ × List Bool) : ℕ → Bool
  | 0 => true
  | s + 1 => noEnter T p s && !(T.enter p.1 p.2 s)

theorem noEnter_eq_rec (T : Lambda.MLTest) (p : ℕ × List Bool) (s : ℕ) :
    noEnter T p s =
      Nat.rec (motive := fun _ => Bool) true (fun k IH => IH && !(T.enter p.1 p.2 k)) s := by
  induction s with
  | zero => rfl
  | succ s ih => rw [noEnter, ih]

theorem noEnter_iff (T : Lambda.MLTest) (c : ℕ) (σ : List Bool) (s : ℕ) :
    noEnter T (c, σ) s = true ↔ ∀ s' < s, T.enter c σ s' = false := by
  induction s with
  | zero => simp [noEnter]
  | succ s ih =>
      rw [noEnter]
      simp only [Bool.and_eq_true, ih, Bool.not_eq_eq_eq_not, Bool.not_true]
      constructor
      · rintro ⟨h1, h2⟩ s' hs'
        rcases Nat.lt_succ_iff_lt_or_eq.1 hs' with h | rfl
        · exact h1 s' h
        · exact h2
      · intro h
        exact ⟨fun s' hs' => h s' (by omega), h s (by omega)⟩

/-- The string discovered at step `j` of level `c`: the step codes a pair `(σ, s)`, and `σ` is
discovered when `s` is the first stage at which it enters level `c`. -/
def discovered (T : Lambda.MLTest) (c j : ℕ) : Option (List Bool) :=
  if (T.enter c (decodeStr j.unpair.1) j.unpair.2 &&
        noEnter T (c, decodeStr j.unpair.1) j.unpair.2) = true then
    some (decodeStr j.unpair.1)
  else none

theorem discovered_mem {T : Lambda.MLTest} {c j : ℕ} {σ : List Bool}
    (h : discovered T c j = some σ) : σ ∈ T.strings c := by
  unfold discovered at h
  by_cases hc : (T.enter c (decodeStr j.unpair.1) j.unpair.2 &&
      noEnter T (c, decodeStr j.unpair.1) j.unpair.2) = true
  · rw [if_pos hc] at h
    have hσ : decodeStr j.unpair.1 = σ := Option.some_injective _ h
    simp only [Bool.and_eq_true] at hc
    exact ⟨j.unpair.2, hσ ▸ hc.1⟩
  · rw [if_neg hc] at h
    exact absurd h (by simp)

theorem exists_discovered {T : Lambda.MLTest} {c : ℕ} {σ : List Bool} (h : σ ∈ T.strings c) :
    ∃ j, discovered T c j = some σ := by
  classical
  obtain ⟨s, hs⟩ := h
  have hex : ∃ s, T.enter c σ s = true := ⟨s, hs⟩
  refine ⟨Nat.pair (Encodable.encode σ) (Nat.find hex), ?_⟩
  unfold discovered
  rw [Nat.unpair_pair]
  simp only [decodeStr_encode]
  have h1 : T.enter c σ (Nat.find hex) = true := Nat.find_spec hex
  have h2 : noEnter T (c, σ) (Nat.find hex) = true := by
    rw [noEnter_iff]
    intro s' hs'
    simpa using Nat.find_min hex hs'
  rw [if_pos (by rw [h1, h2]; rfl)]

------------------------------------------------------------------------
-- Cutting the discoveries into disjoint cylinders
------------------------------------------------------------------------

/-- The length of an optional bit string. -/
def lenOpt : Option (List Bool) → ℕ
  | none => 0
  | some τ => τ.length

/-- The common length at which the `j`-th discovery of level `c` is cut into cylinders: at least
`c`, and at least every length discovered so far. -/
def cutLength (T : Lambda.MLTest) (c : ℕ) : ℕ → ℕ
  | 0 => max c (lenOpt (discovered T c 0))
  | j + 1 => max (cutLength T c j) (lenOpt (discovered T c (j + 1)))

theorem le_cutLength (T : Lambda.MLTest) (c j : ℕ) : c ≤ cutLength T c j := by
  induction j with
  | zero => exact le_max_left _ _
  | succ j ih => exact le_trans ih (le_max_left _ _)

theorem lenOpt_le_cutLength (T : Lambda.MLTest) (c j : ℕ) :
    lenOpt (discovered T c j) ≤ cutLength T c j := by
  cases j with
  | zero => exact le_max_right _ _
  | succ j => exact le_max_right _ _

theorem cutLength_mono (T : Lambda.MLTest) (c : ℕ) : Monotone (cutLength T c) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

/-- `τ` is covered by no string discovered before step `j`. -/
def uncovered (T : Lambda.MLTest) (p : ℕ × List Bool) : ℕ → Bool
  | 0 => true
  | j + 1 =>
    uncovered T p j && ((discovered T p.1 j).map fun σ => !decide (σ <+: p.2)).getD true

theorem uncovered_eq_rec (T : Lambda.MLTest) (p : ℕ × List Bool) (j : ℕ) :
    uncovered T p j =
      Nat.rec (motive := fun _ => Bool) true
        (fun k IH => IH && ((discovered T p.1 k).map fun σ => !decide (σ <+: p.2)).getD true) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [uncovered, ih]

theorem uncovered_iff (T : Lambda.MLTest) (c : ℕ) (τ : List Bool) (j : ℕ) :
    uncovered T (c, τ) j = true ↔ ∀ j' < j, ∀ σ, discovered T c j' = some σ → ¬ σ <+: τ := by
  induction j with
  | zero => simp [uncovered]
  | succ j ih =>
      rw [uncovered]
      simp only [Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h1, h2⟩ j' hj' σ hσ hpre
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h | rfl
        · exact h1 j' h σ hσ hpre
        · rw [hσ] at h2
          simp only [Option.map_some, Option.getD_some, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_false_iff_not] at h2
          exact h2 hpre
      · intro h
        refine ⟨fun j' hj' σ hσ => h j' (by omega) σ hσ, ?_⟩
        cases hd : discovered T c j with
        | none => rfl
        | some σ =>
            simp only [Option.map_some, Option.getD_some, Bool.not_eq_eq_eq_not, Bool.not_true,
              decide_eq_false_iff_not]
            exact h j (by omega) σ hd

/-- The candidate piece attached to the discovery `σ` at step `(j, m)` of level `c`. -/
def pieceOf (T : Lambda.MLTest) (c j m : ℕ) (σ : List Bool) : Option (List Bool) :=
  if (decide (m < 2 ^ cutLength T c j) &&
      decide (σ <+: BitStr.ofNat (cutLength T c j) m) &&
      uncovered T (c, BitStr.ofNat (cutLength T c j) m) j) = true then
    some (BitStr.ofNat (cutLength T c j) m)
  else none

/-- The string requested at step `(j, m)` of level `c`: the `m`-th string of the cutting length,
if it extends the `j`-th discovery and is covered by no earlier one. -/
def piece (T : Lambda.MLTest) (c j m : ℕ) : Option (List Bool) :=
  (discovered T c j).bind (pieceOf T c j m)

theorem piece_eq_some {T : Lambda.MLTest} {c j m : ℕ} {τ : List Bool}
    (h : piece T c j m = some τ) :
    τ = BitStr.ofNat (cutLength T c j) m ∧ m < 2 ^ cutLength T c j ∧
      (∃ σ, discovered T c j = some σ ∧ σ <+: τ) ∧
      ∀ j' < j, ∀ σ, discovered T c j' = some σ → ¬ σ <+: τ := by
  unfold piece at h
  cases hd : discovered T c j with
  | none =>
      rw [hd] at h
      exact absurd (show (none : Option (List Bool)) = some τ from h) (by simp)
  | some σ =>
      rw [hd] at h
      replace h : pieceOf T c j m σ = some τ := h
      unfold pieceOf at h
      by_cases hc : (decide (m < 2 ^ cutLength T c j) &&
          decide (σ <+: BitStr.ofNat (cutLength T c j) m) &&
          uncovered T (c, BitStr.ofNat (cutLength T c j) m) j) = true
      · rw [if_pos hc] at h
        have hτ : BitStr.ofNat (cutLength T c j) m = τ := Option.some_injective _ h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨h1, h2⟩, h3⟩ := hc
        refine ⟨hτ.symm, h1, ⟨σ, hd, hτ ▸ h2⟩, ?_⟩
        rw [← hτ]
        exact (uncovered_iff T c _ j).1 h3
      · rw [if_neg hc] at h
        exact absurd h (by simp)

theorem piece_length {T : Lambda.MLTest} {c j m : ℕ} {τ : List Bool}
    (h : piece T c j m = some τ) : τ.length = cutLength T c j := by
  rw [(piece_eq_some h).1, BitStr.length_ofNat]

theorem piece_subset {T : Lambda.MLTest} {c j m : ℕ} {τ : List Bool}
    (h : piece T c j m = some τ) : Lambda.cylinder τ ⊆ T.level c := by
  obtain ⟨-, -, ⟨σ, hσ, hpre⟩, -⟩ := piece_eq_some h
  refine le_trans (Lambda.cylinder_mono hpre) ?_
  intro X hX
  exact Lambda.mem_openOf.2 ⟨σ, discovered_mem hσ, hX⟩

theorem piece_incomparable_of_lt {T : Lambda.MLTest} {c j m j' m' : ℕ} {τ τ' : List Bool}
    (hj : j < j') (h : piece T c j m = some τ) (h' : piece T c j' m' = some τ') :
    ¬ τ <+: τ' ∧ ¬ τ' <+: τ := by
  obtain ⟨-, -, ⟨σ, hσ, hσp⟩, -⟩ := piece_eq_some h
  obtain ⟨-, -, -, hun'⟩ := piece_eq_some h'
  have hno : ¬ σ <+: τ' := hun' j hj σ hσ
  have hlen : τ.length ≤ τ'.length := by
    rw [piece_length h, piece_length h']
    exact cutLength_mono T c (le_of_lt hj)
  refine ⟨fun hp => hno (hσp.trans hp), fun hp => ?_⟩
  have heq : τ' = τ := prefix_eq_of_length hp hlen
  exact hno (heq ▸ hσp)

theorem piece_incomparable_of_ne {T : Lambda.MLTest} {c j m m' : ℕ} {τ τ' : List Bool}
    (hm : m ≠ m') (h : piece T c j m = some τ) (h' : piece T c j m' = some τ') :
    ¬ τ <+: τ' ∧ ¬ τ' <+: τ := by
  obtain ⟨hτ, hlt, -, -⟩ := piece_eq_some h
  obtain ⟨hτ', hlt', -, -⟩ := piece_eq_some h'
  have hne : τ ≠ τ' := fun he => hm (BitStr.ofNat_inj hlt hlt' (by rw [← hτ, ← hτ', he]))
  have hlen : τ.length = τ'.length := by rw [piece_length h, piece_length h']
  exact ⟨fun hp => hne (prefix_eq_of_length hp (le_of_eq hlen.symm)),
    fun hp => hne (prefix_eq_of_length hp (le_of_eq hlen)).symm⟩

/-- The pieces of level `c`, indexed by a single natural number. -/
def pieceAt (T : Lambda.MLTest) (c i : ℕ) : Option (List Bool) :=
  piece T c i.unpair.1 i.unpair.2

theorem pieceAt_incomparable {T : Lambda.MLTest} {c i i' : ℕ} {τ τ' : List Bool}
    (hne : i ≠ i') (h : pieceAt T c i = some τ) (h' : pieceAt T c i' = some τ') :
    ¬ τ <+: τ' ∧ ¬ τ' <+: τ := by
  unfold pieceAt at h h'
  rcases lt_trichotomy i.unpair.1 i'.unpair.1 with hlt | heq | hgt
  · exact piece_incomparable_of_lt hlt h h'
  · have hm : i.unpair.2 ≠ i'.unpair.2 := fun hm =>
      hne (by rw [← Nat.pair_unpair i, ← Nat.pair_unpair i', heq, hm])
    rw [heq] at h
    exact piece_incomparable_of_ne hm h h'
  · exact (piece_incomparable_of_lt hgt h' h).symm

------------------------------------------------------------------------
-- The weight of the pieces of a level
------------------------------------------------------------------------

/-- The weight `2 ^ (-|τ|)` of an optional bit string. -/
noncomputable def strWt : Option (List Bool) → ℝ
  | none => 0
  | some τ => wt τ.length

theorem strWt_nonneg (o : Option (List Bool)) : 0 ≤ strWt o := by
  cases o with
  | none => exact le_rfl
  | some τ => exact le_of_lt (wt_pos _)

/-- **The pieces of a level have total weight at most the measure of the level.** -/
theorem sum_strWt_pieceAt_le (T : Lambda.MLTest) (c : ℕ) (G : Finset ℕ) :
    ∑ i ∈ G, strWt (pieceAt T c i) ≤ (2 : ℝ)⁻¹ ^ c := by
  classical
  set G' := G.filter (fun i => (pieceAt T c i).isSome = true) with hG'def
  have hsubG : G' ⊆ G := Finset.filter_subset _ _
  have hzero : ∀ i ∈ G, i ∉ G' → strWt (pieceAt T c i) = 0 := by
    intro i hi hni
    cases hp : pieceAt T c i with
    | none => rfl
    | some τ => exact absurd (Finset.mem_filter.2 ⟨hi, by rw [hp]; rfl⟩) hni
  rw [← Finset.sum_subset hsubG hzero]
  set f : ℕ → List Bool := fun i => (pieceAt T c i).getD [] with hfdef
  have hsome : ∀ i ∈ G', pieceAt T c i = some (f i) := by
    intro i hi
    have h := (Finset.mem_filter.1 hi).2
    cases hp : pieceAt T c i with
    | none => rw [hp] at h; exact absurd h (by simp)
    | some τ => rw [hfdef]; simp [hp]
  have hdisj : (G' : Set ℕ).PairwiseDisjoint fun i => Lambda.cylinder (f i) := by
    intro i hi i' hi' hne
    obtain ⟨hn1, hn2⟩ := pieceAt_incomparable hne (hsome i hi) (hsome i' hi')
    exact cylinder_disjoint hn1 hn2
  have hmeas : Lambda.cantorMeasure (⋃ i ∈ G', Lambda.cylinder (f i))
      = ∑ i ∈ G', Lambda.cantorMeasure (Lambda.cylinder (f i)) :=
    measure_biUnion_finset hdisj fun i _ => measurableSet_cylinder _
  have hle : ∑ i ∈ G', (2 : ENNReal)⁻¹ ^ (f i).length ≤ (2 : ENNReal)⁻¹ ^ c := by
    calc ∑ i ∈ G', (2 : ENNReal)⁻¹ ^ (f i).length
        = Lambda.cantorMeasure (⋃ i ∈ G', Lambda.cylinder (f i)) := by
          rw [hmeas]
          exact Finset.sum_congr rfl fun i _ => (Lambda.cantorMeasure_cylinder _).symm
      _ ≤ Lambda.cantorMeasure (T.level c) := by
          refine measure_mono (Set.iUnion₂_subset fun i hi => ?_)
          exact piece_subset (hsome i hi)
      _ ≤ (2 : ENNReal)⁻¹ ^ c := T.measure_level_le c
  have hreal : ∑ i ∈ G', strWt (pieceAt T c i) = ∑ i ∈ G', (2 : ℝ)⁻¹ ^ (f i).length :=
    Finset.sum_congr rfl fun i hi => by rw [hsome i hi]; rfl
  rw [hreal]
  simp only [Lambda.ennreal_two_inv_pow] at hle
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle

------------------------------------------------------------------------
-- The request stream
------------------------------------------------------------------------

/-- The request stream attached to a Martin-Löf test: the index `i` codes `(k, j, m)`, and the
request compresses the `(j, m)`-th piece of level `2 * k + 2` by `k` bits. -/
def testReq (T : Lambda.MLTest) (i : ℕ) : Option (ℕ × ℕ) :=
  (pieceAt T (2 * i.unpair.1 + 2) i.unpair.2).map fun τ =>
    (τ.length - i.unpair.1, Encodable.encode τ)

theorem testReq_pair (T : Lambda.MLTest) (k j m : ℕ) :
    testReq T (Nat.pair k (Nat.pair j m)) =
      (piece T (2 * k + 2) j m).map fun τ => (τ.length - k, Encodable.encode τ) := by
  unfold testReq pieceAt
  simp only [Nat.unpair_pair]

theorem wt_sub {k n : ℕ} (h : k ≤ n) : wt (n - k) = 2 ^ k * wt n := by
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by omega⟩
  unfold wt
  rw [Nat.add_sub_cancel_left, pow_add]
  have h2 : ((2 : ℝ)⁻¹) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
  calc ((2 : ℝ)⁻¹) ^ d = (((2 : ℝ)⁻¹) ^ k * 2 ^ k) * ((2 : ℝ)⁻¹) ^ d := by rw [h2, one_mul]
    _ = 2 ^ k * (((2 : ℝ)⁻¹) ^ k * ((2 : ℝ)⁻¹) ^ d) := by ring

theorem wtOpt_testReq (T : Lambda.MLTest) (i : ℕ) :
    wtOpt (testReq T i) = 2 ^ i.unpair.1 * strWt (pieceAt T (2 * i.unpair.1 + 2) i.unpair.2) := by
  unfold testReq
  cases hp : pieceAt T (2 * i.unpair.1 + 2) i.unpair.2 with
  | none => simp [wtOpt, strWt]
  | some τ =>
      have hlen : 2 * i.unpair.1 + 2 ≤ τ.length := by
        rw [piece_length hp]
        exact le_cutLength T _ _
      show wt (τ.length - i.unpair.1) = 2 ^ i.unpair.1 * wt τ.length
      exact wt_sub (by omega)

theorem sum_wtOpt_testReq_fiber_le (T : Lambda.MLTest) (k : ℕ) (G : Finset ℕ)
    (hG : ∀ i ∈ G, i.unpair.1 = k) :
    ∑ i ∈ G, wtOpt (testReq T i) ≤ wt (k + 2) := by
  classical
  have h1 : ∑ i ∈ G, wtOpt (testReq T i)
      = 2 ^ k * ∑ i ∈ G, strWt (pieceAt T (2 * k + 2) i.unpair.2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [wtOpt_testReq, hG i hi]
  have hinj : ∀ i ∈ G, ∀ i' ∈ G, i.unpair.2 = i'.unpair.2 → i = i' := by
    intro i hi i' hi' h
    rw [← Nat.pair_unpair i, ← Nat.pair_unpair i', hG i hi, hG i' hi', h]
  have h2 : ∑ i ∈ G, strWt (pieceAt T (2 * k + 2) i.unpair.2)
      = ∑ u ∈ G.image (fun i => i.unpair.2), strWt (pieceAt T (2 * k + 2) u) :=
    (Finset.sum_image (g := fun u => strWt (pieceAt T (2 * k + 2) u)) hinj).symm
  have h3 : ∑ u ∈ G.image (fun i => i.unpair.2), strWt (pieceAt T (2 * k + 2) u)
      ≤ (2 : ℝ)⁻¹ ^ (2 * k + 2) := sum_strWt_pieceAt_le T (2 * k + 2) _
  have h4 : (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ (2 * k + 2) = wt (k + 2) := by
    unfold wt
    rw [show 2 * k + 2 = k + (k + 2) by ring, pow_add]
    have h5 : ((2 : ℝ)⁻¹) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
    calc (2 : ℝ) ^ k * (((2 : ℝ)⁻¹) ^ k * ((2 : ℝ)⁻¹) ^ (k + 2))
        = (((2 : ℝ)⁻¹) ^ k * 2 ^ k) * ((2 : ℝ)⁻¹) ^ (k + 2) := by ring
      _ = ((2 : ℝ)⁻¹) ^ (k + 2) := by rw [h5, one_mul]
  rw [h1, h2, ← h4]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

/-- **The requests of a test have total weight at most one.** -/
theorem sum_wtOpt_testReq_le (T : Lambda.MLTest) (F : Finset ℕ) :
    ∑ i ∈ F, wtOpt (testReq T i) ≤ 1 := by
  classical
  refine sum_le_of_range_le (fun i => wtOpt_nonneg _) (fun M => ?_) F
  have hmaps : ∀ i ∈ Finset.range M, i.unpair.1 ∈ Finset.range M := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    exact lt_of_le_of_lt (Nat.unpair_left_le i) hi
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ k ∈ Finset.range M, ∑ i ∈ (Finset.range M).filter (fun i => i.unpair.1 = k),
          wtOpt (testReq T i)
      ≤ ∑ k ∈ Finset.range M, wt (k + 2) :=
        Finset.sum_le_sum fun k _ => sum_wtOpt_testReq_fiber_le T k _
          fun i hi => (Finset.mem_filter.1 hi).2
    _ ≤ 1 / 2 := sum_wt_succ_succ_le M
    _ ≤ 1 := by norm_num

/-- **Every sequence caught by level `2 * k + 2` of a test has a requested prefix.** -/
theorem exists_piece_prefix {T : Lambda.MLTest} {X : ℕ → Bool} {k : ℕ}
    (h : X ∈ T.level (2 * k + 2)) :
    ∃ i N, testReq T i = some (N - k, Encodable.encode (Lambda.prefixList X N)) ∧ k ≤ N := by
  classical
  obtain ⟨σ, hσ, hX⟩ := Lambda.mem_openOf.1 h
  obtain ⟨j₀, hj₀⟩ := exists_discovered hσ
  have hex : ∃ j, ∃ σ', discovered T (2 * k + 2) j = some σ' ∧ X ∈ Lambda.cylinder σ' :=
    ⟨j₀, σ, hj₀, hX⟩
  obtain ⟨σ', hσ'd, hσ'X⟩ := Nat.find_spec hex
  set J := Nat.find hex with hJ
  set N := cutLength T (2 * k + 2) J with hN
  have hlenτ : (Lambda.prefixList X N).length = N := Lambda.prefixList_length X N
  have hlenσ' : σ'.length ≤ N := by
    have hle := lenOpt_le_cutLength T (2 * k + 2) J
    rw [hσ'd] at hle
    exact hle
  have hσ'τ : σ' <+: Lambda.prefixList X N := by
    rw [eq_prefixList_of_mem_cylinder hσ'X]
    exact Lambda.prefixList_prefix hlenσ'
  have hun : uncovered T (2 * k + 2, Lambda.prefixList X N) J = true := by
    rw [uncovered_iff]
    intro j' hj' ρ hρ hpre
    exact Nat.find_min hex hj'
      ⟨ρ, hρ, Lambda.cylinder_mono hpre (Lambda.mem_cylinder_prefixList X N)⟩
  have hm : BitStr.toNat (Lambda.prefixList X N) < 2 ^ N := by
    have hlt := BitStr.toNat_lt (Lambda.prefixList X N)
    rwa [hlenτ] at hlt
  have hofNat : BitStr.ofNat N (BitStr.toNat (Lambda.prefixList X N)) = Lambda.prefixList X N := by
    have hof := BitStr.ofNat_toNat (Lambda.prefixList X N)
    rwa [hlenτ] at hof
  have hpiece : piece T (2 * k + 2) J (BitStr.toNat (Lambda.prefixList X N))
      = some (Lambda.prefixList X N) := by
    unfold piece
    rw [hσ'd]
    show pieceOf T (2 * k + 2) J (BitStr.toNat (Lambda.prefixList X N)) σ' = _
    unfold pieceOf
    simp only [← hN, hofNat]
    rw [if_pos (by rw [decide_eq_true hm, decide_eq_true hσ'τ, hun])]
  refine ⟨Nat.pair k (Nat.pair J (BitStr.toNat (Lambda.prefixList X N))), N, ?_, ?_⟩
  · rw [testReq_pair, hpiece, Option.map_some, hlenτ]
  · have := le_cutLength T (2 * k + 2) J
    omega

------------------------------------------------------------------------
-- Computability of the request stream
------------------------------------------------------------------------

theorem computable_noEnter (T : Lambda.MLTest) :
    Computable fun q : (ℕ × List Bool) × ℕ => noEnter T q.1 q.2 := by
  have henter : Computable fun z : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) =>
      T.enter z.1.1.1 z.1.1.2 z.2.1 :=
    T.enter_computable.comp
      ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
          (Computable.fst.comp Computable.snd)))
  have hstep : Computable₂ fun (q : (ℕ × List Bool) × ℕ) (r : ℕ × Bool) =>
      (r.2 && !(T.enter q.1.1 q.1.2 r.1)) :=
    Computable₂.comp (Primrec.dom_bool₂ (fun a b : Bool => a && !b)).to_comp
      (Computable.snd.comp Computable.snd) henter
  refine (Computable.nat_rec Computable.snd (Computable.const true) hstep).of_eq fun q => ?_
  exact (noEnter_eq_rec T q.1 q.2).symm

theorem computable_discovered (T : Lambda.MLTest) :
    Computable fun q : ℕ × ℕ => discovered T q.1 q.2 := by
  have hstr : Computable fun q : ℕ × ℕ => decodeStr q.2.unpair.1 :=
    (primrec_decodeStr.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))).to_comp
  have hs : Computable fun q : ℕ × ℕ => q.2.unpair.2 :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have henter : Computable fun q : ℕ × ℕ =>
      T.enter q.1 (decodeStr q.2.unpair.1) q.2.unpair.2 :=
    T.enter_computable.comp (Computable.fst.pair (hstr.pair hs))
  have hno : Computable fun q : ℕ × ℕ =>
      noEnter T (q.1, decodeStr q.2.unpair.1) q.2.unpair.2 :=
    (computable_noEnter T).comp ((Computable.fst.pair hstr).pair hs)
  have hcond : Computable fun q : ℕ × ℕ =>
      (T.enter q.1 (decodeStr q.2.unpair.1) q.2.unpair.2 &&
        noEnter T (q.1, decodeStr q.2.unpair.1) q.2.unpair.2) :=
    Computable₂.comp (Primrec.dom_bool₂ (fun a b : Bool => a && b)).to_comp henter hno
  refine (Computable.cond hcond (Computable.option_some.comp hstr)
    (Computable.const none)).of_eq fun q => ?_
  unfold discovered
  cases h : (T.enter q.1 (decodeStr q.2.unpair.1) q.2.unpair.2 &&
      noEnter T (q.1, decodeStr q.2.unpair.1) q.2.unpair.2) with
  | false => simp
  | true => simp

theorem computable_lenOpt : Computable lenOpt := by
  have hg : Computable₂ fun (_ : Option (List Bool)) (τ : List Bool) => τ.length :=
    Computable.list_length.comp Computable.snd
  refine (Computable.option_casesOn Computable.id (Computable.const 0) hg).of_eq fun o => ?_
  cases o <;> rfl

theorem computable_cutLength (T : Lambda.MLTest) :
    Computable fun q : ℕ × ℕ => cutLength T q.1 q.2 := by
  have hdisc : Computable fun z : (ℕ × ℕ) × (ℕ × ℕ) => discovered T z.1.1 (z.2.1 + 1) :=
    (computable_discovered T).comp ((Computable.fst.comp Computable.fst).pair
      (Computable.succ.comp (Computable.fst.comp Computable.snd)))
  have hstep : Computable₂ fun (q : ℕ × ℕ) (r : ℕ × ℕ) =>
      max r.2 (lenOpt (discovered T q.1 (r.1 + 1))) :=
    Computable₂.comp Primrec.nat_max.to_comp (Computable.snd.comp Computable.snd)
      (computable_lenOpt.comp hdisc)
  have hbase : Computable fun q : ℕ × ℕ => max q.1 (lenOpt (discovered T q.1 0)) :=
    Computable₂.comp Primrec.nat_max.to_comp Computable.fst
      (computable_lenOpt.comp ((computable_discovered T).comp
        (Computable.fst.pair (Computable.const 0))))
  refine (Computable.nat_rec Computable.snd hbase hstep).of_eq fun q => ?_
  obtain ⟨c, j⟩ := q
  induction j with
  | zero => rfl
  | succ j ih => rw [cutLength, ← ih]

theorem computable_uncovered (T : Lambda.MLTest) :
    Computable fun q : (ℕ × List Bool) × ℕ => uncovered T q.1 q.2 := by
  have hdisc : Computable fun z : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) =>
      discovered T z.1.1.1 z.2.1 :=
    (computable_discovered T).comp
      ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.fst.comp Computable.snd))
  have hg : Computable₂ fun (z : ((ℕ × List Bool) × ℕ) × (ℕ × Bool)) (σ : List Bool) =>
      !decide (σ <+: z.1.1.2) :=
    Computable.comp (Primrec.dom_bool (fun b : Bool => !b)).to_comp
      (Computable₂.comp primrec_isPrefix.to_comp Computable.snd
        (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))))
  have hbit : Computable fun z : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) =>
      ((discovered T z.1.1.1 z.2.1).map fun σ => !decide (σ <+: z.1.1.2)).getD true :=
    Computable.option_getD (Computable.option_map hdisc hg) (Computable.const true)
  have hstep : Computable₂ fun (q : (ℕ × List Bool) × ℕ) (r : ℕ × Bool) =>
      (r.2 && ((discovered T q.1.1 r.1).map fun σ => !decide (σ <+: q.1.2)).getD true) :=
    Computable₂.comp (Primrec.dom_bool₂ (fun a b : Bool => a && b)).to_comp
      (Computable.snd.comp Computable.snd) hbit
  refine (Computable.nat_rec Computable.snd (Computable.const true) hstep).of_eq fun q => ?_
  exact (uncovered_eq_rec T q.1 q.2).symm

theorem computable_piece (T : Lambda.MLTest) :
    Computable fun q : ℕ × ℕ × ℕ => piece T q.1 q.2.1 q.2.2 := by
  have hc : Computable fun q : ℕ × ℕ × ℕ => q.1 := Computable.fst
  have hj : Computable fun q : ℕ × ℕ × ℕ => q.2.1 := Computable.fst.comp Computable.snd
  have hm : Computable fun q : ℕ × ℕ × ℕ => q.2.2 := Computable.snd.comp Computable.snd
  have hcut : Computable fun q : ℕ × ℕ × ℕ => cutLength T q.1 q.2.1 :=
    (computable_cutLength T).comp (hc.pair hj)
  have hstr : Computable fun q : ℕ × ℕ × ℕ => BitStr.ofNat (cutLength T q.1 q.2.1) q.2.2 :=
    Computable₂.comp BitStr.primrec_ofNat.to_comp hcut hm
  have hdisc : Computable fun q : ℕ × ℕ × ℕ => discovered T q.1 q.2.1 :=
    (computable_discovered T).comp (hc.pair hj)
  have hlt : Computable fun q : ℕ × ℕ × ℕ => decide (q.2.2 < 2 ^ cutLength T q.1 q.2.1) :=
    Computable₂.comp Primrec.nat_lt.to_comp hm (Computable.comp primrec_two_pow.to_comp hcut)
  have hunc : Computable fun q : ℕ × ℕ × ℕ =>
      uncovered T (q.1, BitStr.ofNat (cutLength T q.1 q.2.1) q.2.2) q.2.1 :=
    (computable_uncovered T).comp ((hc.pair hstr).pair hj)
  have hpre : Computable fun z : (ℕ × ℕ × ℕ) × List Bool =>
      decide (z.2 <+: BitStr.ofNat (cutLength T z.1.1 z.1.2.1) z.1.2.2) :=
    Computable₂.comp primrec_isPrefix.to_comp Computable.snd (hstr.comp Computable.fst)
  have hcond : Computable fun z : (ℕ × ℕ × ℕ) × List Bool =>
      (decide (z.1.2.2 < 2 ^ cutLength T z.1.1 z.1.2.1) &&
        decide (z.2 <+: BitStr.ofNat (cutLength T z.1.1 z.1.2.1) z.1.2.2) &&
        uncovered T (z.1.1, BitStr.ofNat (cutLength T z.1.1 z.1.2.1) z.1.2.2) z.1.2.1) :=
    Computable₂.comp (Primrec.dom_bool₂ (fun a b : Bool => a && b)).to_comp
      (Computable₂.comp (Primrec.dom_bool₂ (fun a b : Bool => a && b)).to_comp
        (hlt.comp Computable.fst) hpre)
      (hunc.comp Computable.fst)
  have hg : Computable₂ fun (q : ℕ × ℕ × ℕ) (σ : List Bool) => pieceOf T q.1 q.2.1 q.2.2 σ := by
    refine (Computable.cond hcond (Computable.option_some.comp (hstr.comp Computable.fst))
      (Computable.const none)).of_eq fun z => ?_
    unfold pieceOf
    cases hb : (decide (z.1.2.2 < 2 ^ cutLength T z.1.1 z.1.2.1) &&
        decide (z.2 <+: BitStr.ofNat (cutLength T z.1.1 z.1.2.1) z.1.2.2) &&
        uncovered T (z.1.1, BitStr.ofNat (cutLength T z.1.1 z.1.2.1) z.1.2.2) z.1.2.1) with
    | false => simp
    | true => simp
  exact Computable.option_bind hdisc hg

theorem computable_testReq (T : Lambda.MLTest) : Computable (testReq T) := by
  have hidx : Computable fun i : ℕ => ((2 * i.unpair.1 + 2, i.unpair.2.unpair.1,
      i.unpair.2.unpair.2) : ℕ × ℕ × ℕ) :=
    ((Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.unpair))
      (Primrec.const 2)).pair
      ((Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).pair
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))).to_comp
  have hpiece : Computable fun i : ℕ => pieceAt T (2 * i.unpair.1 + 2) i.unpair.2 :=
    ((computable_piece T).comp hidx).of_eq fun i => rfl
  have hg : Computable₂ fun (i : ℕ) (τ : List Bool) =>
      ((τ.length - i.unpair.1, Encodable.encode τ) : ℕ × ℕ) :=
    ((Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))).pair
      (Primrec.encode.comp Primrec.snd)).to_comp
  exact Computable.option_map hpiece hg

end KC
