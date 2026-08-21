/-
Prefix-free sets of bit strings and the Kraft inequality.

A set `S` of bit strings is *prefix free* when no element of `S` is a proper prefix of another
element of `S`.  Kraft's inequality says that the weights `2 ^ (-|w|)` of the elements of a prefix
free set sum to at most `1`.

The proof here is the standard counting argument.  Fix a finite prefix free family and let `N`
bound the lengths of its members.  Each member `w` is extended in exactly `2 ^ (N - |w|)` ways to a
string of length `N`, and prefix freeness makes these families of extensions pairwise disjoint, so
`∑ 2 ^ (N - |w|) ≤ 2 ^ N`.  Dividing by `2 ^ N` gives the finite Kraft inequality, and the infinite
version follows because the weights are nonnegative.

The results are stated for an arbitrary index type equipped with a prefix free coding
`c : ι → List Bool`, which is the shape needed for Chaitin's `Ω` in `Start/ChaitinOmega.lean`.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Kraft

open scoped BigOperators

noncomputable section

/-- The weight of a bit string: `2 ^ (-|w|)`. -/
def wt (w : List Bool) : ℝ := (2 : ℝ)⁻¹ ^ w.length

theorem wt_pos (w : List Bool) : 0 < wt w := by
  have : (0 : ℝ) < (2 : ℝ)⁻¹ := by norm_num
  exact pow_pos this _

theorem wt_nonneg (w : List Bool) : 0 ≤ wt w := (wt_pos w).le

/-- Rescaled weight: `2 ^ N * wt w = 2 ^ (N - |w|)` for `|w| ≤ N`. -/
theorem two_pow_mul_wt {w : List Bool} {N : ℕ} (h : w.length ≤ N) :
    (2 : ℝ) ^ N * wt w = ((2 : ℕ) ^ (N - w.length) : ℕ) := by
  have hsplit : (2 : ℝ) ^ (N - w.length) * (2 : ℝ) ^ w.length = (2 : ℝ) ^ N := by
    rw [← pow_add]
    congr 1
    omega
  have hpos : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
  rw [wt, inv_pow]
  push_cast
  field_simp
  linarith [hsplit]

------------------------------------------------------------------------
-- Bit strings of a fixed length
------------------------------------------------------------------------

/-- The finite set of all bit strings of length `n`. -/
def boolLists : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => ((Finset.univ : Finset Bool) ×ˢ boolLists n).image (fun p => p.1 :: p.2)

@[simp] theorem mem_boolLists {w : List Bool} : ∀ {n : ℕ}, w ∈ boolLists n ↔ w.length = n := by
  induction w with
  | nil =>
      intro n
      cases n with
      | zero => simp [boolLists]
      | succ n => simp [boolLists]
  | cons b w ih =>
      intro n
      cases n with
      | zero => simp [boolLists]
      | succ n =>
          simp only [boolLists, Finset.mem_image, Finset.mem_product, Finset.mem_univ,
            true_and, List.length_cons, Nat.add_right_cancel_iff]
          constructor
          · rintro ⟨⟨c, v⟩, hv, hcv⟩
            have hb : c = b := (List.cons.injEq _ _ _ _ ▸ hcv).1
            have hw : v = w := (List.cons.injEq _ _ _ _ ▸ hcv).2
            subst hb; subst hw
            exact ih.mp hv
          · intro hlen
            exact ⟨(b, w), ih.mpr hlen, rfl⟩

theorem card_boolLists (n : ℕ) : (boolLists n).card = 2 ^ n := by
  induction n with
  | zero => simp [boolLists]
  | succ n ih =>
      have hinj : Set.InjOn (fun p : Bool × List Bool => p.1 :: p.2)
          (↑((Finset.univ : Finset Bool) ×ˢ boolLists n) : Set (Bool × List Bool)) := by
        rintro ⟨a, u⟩ _ ⟨b, v⟩ _ h
        simp only [List.cons.injEq] at h
        simp [h.1, h.2]
      rw [boolLists, Finset.card_image_of_injOn hinj, Finset.card_product, ih]
      simp [pow_succ]
      ring

/-- All the extensions of `w` to a string of length `w.length + n`. -/
def ext (w : List Bool) (n : ℕ) : Finset (List Bool) := (boolLists n).image (fun u => w ++ u)

theorem mem_ext {w x : List Bool} {n : ℕ} :
    x ∈ ext w n ↔ w <+: x ∧ x.length = w.length + n := by
  constructor
  · rintro hx
    simp only [ext, Finset.mem_image, mem_boolLists] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨List.prefix_append _ _, by simp [hu]⟩
  · rintro ⟨⟨u, rfl⟩, hlen⟩
    simp only [ext, Finset.mem_image, mem_boolLists]
    refine ⟨u, ?_, rfl⟩
    simp at hlen
    omega

theorem card_ext (w : List Bool) (n : ℕ) : (ext w n).card = 2 ^ n := by
  have hinj : Set.InjOn (fun u => w ++ u) (boolLists n) := by
    intro u _ v _ h
    exact List.append_cancel_left h
  rw [ext, Finset.card_image_of_injOn hinj, card_boolLists]

------------------------------------------------------------------------
-- Kraft's inequality
------------------------------------------------------------------------

/-- A coding `c` is prefix free when no code word is a prefix of another one. -/
def PrefixFreeCoding {ι : Type*} (c : ι → List Bool) : Prop :=
  ∀ i j : ι, c i <+: c j → i = j

open Classical in
/-- Finite Kraft inequality, counting form: if `c` is prefix free on the finite set `F` and all
code words of `F` have length at most `N`, then `∑ 2 ^ (N - |c i|) ≤ 2 ^ N`. -/
theorem sum_two_pow_sub_le {ι : Type*} {c : ι → List Bool} (hc : PrefixFreeCoding c)
    (F : Finset ι) {N : ℕ} (hN : ∀ i ∈ F, (c i).length ≤ N) :
    ∑ i ∈ F, 2 ^ (N - (c i).length) ≤ 2 ^ N := by
  classical
  have hdisj : (↑F : Set ι).PairwiseDisjoint (fun i => ext (c i) (N - (c i).length)) := by
    intro i hi j hj hij
    refine Finset.disjoint_left.mpr ?_
    intro x hxi hxj
    rw [mem_ext] at hxi hxj
    have hcomp := List.prefix_or_prefix_of_prefix hxi.1 hxj.1
    exact hij (hcomp.elim (fun h => hc i j h) (fun h => (hc j i h).symm))
  have hsub : F.biUnion (fun i => ext (c i) (N - (c i).length)) ⊆ boolLists N := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    rw [mem_ext] at hxi
    have := hN i hi
    rw [mem_boolLists, hxi.2]
    omega
  have hcard := Finset.card_biUnion hdisj
  have hle : (F.biUnion (fun i => ext (c i) (N - (c i).length))).card ≤ (boolLists N).card :=
    Finset.card_le_card hsub
  rw [hcard, card_boolLists] at hle
  calc ∑ i ∈ F, 2 ^ (N - (c i).length)
      = ∑ i ∈ F, (ext (c i) (N - (c i).length)).card := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [card_ext]
    _ ≤ 2 ^ N := hle

/-- Finite Kraft inequality: the weights of finitely many pairwise incomparable code words sum to
at most `1`. -/
theorem sum_wt_le_one {ι : Type*} {c : ι → List Bool} (hc : PrefixFreeCoding c) (F : Finset ι) :
    ∑ i ∈ F, wt (c i) ≤ 1 := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i ∈ F, (c i).length ≤ N :=
    ⟨∑ i ∈ F, (c i).length, fun i hi => Finset.single_le_sum (f := fun i => (c i).length)
      (fun j _ => Nat.zero_le _) hi⟩
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  rw [← mul_le_mul_iff_of_pos_left hpos, mul_one, Finset.mul_sum]
  have hstep : ∀ i ∈ F, (2 : ℝ) ^ N * wt (c i) = (((2 : ℕ) ^ (N - (c i).length) : ℕ) : ℝ) :=
    fun i hi => two_pow_mul_wt (hN i hi)
  rw [Finset.sum_congr rfl hstep, ← Nat.cast_sum]
  have hnat := sum_two_pow_sub_le hc F hN
  calc ((∑ i ∈ F, (2 : ℕ) ^ (N - (c i).length) : ℕ) : ℝ)
      ≤ (((2 : ℕ) ^ N : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (2 : ℝ) ^ N := by push_cast; ring

/-- The weights of a prefix free coding are summable. -/
theorem summable_wt {ι : Type*} {c : ι → List Bool} (hc : PrefixFreeCoding c) :
    Summable (fun i => wt (c i)) :=
  summable_of_sum_le (fun i => wt_nonneg (c i)) (fun F => sum_wt_le_one hc F)

/-- Kraft's inequality: `∑ 2 ^ (-|c i|) ≤ 1` for a prefix free coding `c`. -/
theorem tsum_wt_le_one {ι : Type*} {c : ι → List Bool} (hc : PrefixFreeCoding c) :
    ∑' i, wt (c i) ≤ 1 :=
  tsum_le_of_sum_le' zero_le_one (fun F => sum_wt_le_one hc F)

/-- A subfamily of a prefix free coding leaves room for the weight of any code word outside it:
`∑_{P i} 2 ^ (-|c i|) + 2 ^ (-|c j|) ≤ 1` whenever `¬ P j`. -/
theorem tsum_wt_add_le_one {ι : Type*} {c : ι → List Bool} (hc : PrefixFreeCoding c)
    {P : ι → Prop} {j : ι} (hj : ¬ P j) :
    (∑' i : {i // P i}, wt (c i)) + wt (c j) ≤ 1 := by
  classical
  have key : ∀ F : Finset {i // P i}, ∑ i ∈ F, wt (c ↑i) ≤ 1 - wt (c j) := by
    intro F
    have hnot : j ∉ F.image (Subtype.val) := by
      intro hmem
      obtain ⟨i, _, hij⟩ := Finset.mem_image.mp hmem
      exact hj (hij ▸ i.2)
    have hsum := sum_wt_le_one hc (insert j (F.image (Subtype.val)))
    rw [Finset.sum_insert hnot,
      Finset.sum_image (fun a _ b _ h => Subtype.ext h)] at hsum
    linarith
  have hzero : (0 : ℝ) ≤ 1 - wt (c j) := by simpa using key ∅
  have hle : (∑' i : {i // P i}, wt (c ↑i)) ≤ 1 - wt (c j) := tsum_le_of_sum_le' hzero key
  linarith

end

end Kraft
