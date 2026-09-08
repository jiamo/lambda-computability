/-
**Computable analysis in `K₂`: a computable real function is continuous.**

`Start/KleeneTwo.lean` builds Kleene's second algebra `K₂`, whose elements are the partial
continuous operations on Baire space.  `K₂` is the algebra of *type-two* computability, and this
module runs the standard construction of computable analysis on top of it: a real number is
presented by a **name** — a sequence of rationals converging to it at a fixed speed — and a
function `f : ℝ → ℝ` is computable when a single element of `K₂` turns every name of `x` into a
name of `f x`.

The theorem is that computability of this kind forces continuity, with an explicit modulus.  It
is the type-two counterpart of the Kreisel–Lacombe–Shoenfield theorem, and its proof is the one
lemma the earlier module already had: a value of `α | β` is produced by a finite initial segment
of `β` (`Realizability.KleeneTwo.appK_continuous`).  The finite segment of the name of `x` that
the computation of the `k`-th rational of the output reads is a modulus: any `y` close enough to
`x` has a name beginning with that same segment, so the output name of `f y` begins with the same
segment too, and the two values are within `2 ^ (1 - k)` of each other.

* `Realizability.KleeneTwo.ratOf` — the rational coded by a natural number, and
  `exists_ratOf_near`, the density that makes names exist;
* `Realizability.KleeneTwo.IsName`, `.IsFastName` — a name of `x` (error at most `2 ^ (-i)` at
  stage `i`) and a fast one (error at most `2 ^ (-i-1)`), with `exists_fastName`;
* `Realizability.KleeneTwo.glue` — the name of a nearby point obtained by keeping the first `N`
  rationals of a fast name of `x` (`glue_isName`): this is what makes the modulus work;
* `Realizability.KleeneTwo.Realizes`, `.IsComputableFun` — `α` computes `f`, and `f` is
  computable;
* `Realizability.KleeneTwo.Realizes.exists_modulus` — **the modulus of continuity**;
* `Realizability.KleeneTwo.IsComputableFun.continuous` — **a computable real function is
  continuous**;
* `Realizability.KleeneTwo.not_isComputableFun_step` — hence the step function is not
  computable, although each of its values is a computable real;
* `Realizability.KleeneTwo.isComputableFun_id`, `.isComputableFun_const` — the theorem is not
  vacuous: the identity and the constants are computable, realized by canonical associates.

What is *not* claimed is the Kreisel–Lacombe–Shoenfield theorem itself, which is the same
statement for *Markov* computability — a function defined only on the computable reals and
computed from indices of algorithms rather than from names.  There continuity is a genuinely
harder theorem; here it is Kleene's continuity principle.
-/

import Start.KleeneTwo
import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Realizability

namespace KleeneTwo

/-! ### Rationals coded by naturals -/

/-- The rational number coded by a natural number, through the standard denumeration of `ℚ`. -/
def ratOf (n : ℕ) : ℚ := Denumerable.ofNat ℚ n

/-- Every rational is coded. -/
theorem ratOf_surjective : Function.Surjective ratOf := fun q =>
  ⟨Denumerable.eqv ℚ q, Denumerable.ofNat_encode q⟩

/-- Every real number is approximated by coded rationals to any accuracy. -/
theorem exists_ratOf_near (x : ℝ) {e : ℝ} (he : 0 < e) : ∃ n : ℕ, |(ratOf n : ℝ) - x| < e := by
  obtain ⟨q, hq⟩ := exists_rat_near x he
  obtain ⟨n, rfl⟩ := ratOf_surjective q
  exact ⟨n, by rwa [abs_sub_comm]⟩

/-! ### Names -/

/-- `IsName β x` : the sequence of rationals coded by `β` converges to `x` with error at most
`2 ^ (-i)` at stage `i`.  This is the representation of the reals used in computable analysis. -/
def IsName (β : ℕ → ℕ) (x : ℝ) : Prop := ∀ i, |(ratOf (β i) : ℝ) - x| ≤ 1 / 2 ^ i

/-- A *fast* name: the error at stage `i` is at most `2 ^ (-i-1)`, half of what a name must
achieve.  The spare half is what allows the first entries of a fast name of `x` to be reused as
the first entries of a name of a nearby point. -/
def IsFastName (β : ℕ → ℕ) (x : ℝ) : Prop := ∀ i, |(ratOf (β i) : ℝ) - x| ≤ 1 / 2 ^ (i + 1)

theorem IsFastName.isName {β : ℕ → ℕ} {x : ℝ} (h : IsFastName β x) : IsName β x := by
  intro i
  refine (h i).trans ?_
  rw [div_le_div_iff_of_pos_left (by norm_num) (by positivity) (by positivity)]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- Every real number has a fast name. -/
theorem exists_fastName (x : ℝ) : ∃ β : ℕ → ℕ, IsFastName β x := by
  choose g hg using fun i : ℕ => exists_ratOf_near x (e := 1 / 2 ^ (i + 1)) (by positivity)
  exact ⟨g, fun i => (hg i).le⟩

/-- Keep the first `N` entries of `β` and continue with `γ`. -/
def glue (β γ : ℕ → ℕ) (N : ℕ) : ℕ → ℕ := fun i => if i < N then β i else γ i

theorem glue_agree (β γ : ℕ → ℕ) (N : ℕ) : ∀ i < N, glue β γ N i = β i := by
  intro i hi
  simp [glue, hi]

/-- **The gluing lemma.**  If `β` is a fast name of `x`, `γ` is a name of `y` and `y` is within
`2 ^ (-N-1)` of `x`, then the sequence that follows `β` for `N` steps and `γ` afterwards is a
name of `y`. -/
theorem glue_isName {β γ : ℕ → ℕ} {x y : ℝ} {N : ℕ} (hβ : IsFastName β x) (hγ : IsName γ y)
    (hxy : |y - x| ≤ 1 / 2 ^ (N + 1)) : IsName (glue β γ N) y := by
  intro i
  by_cases hi : i < N
  · have hstep : (1 : ℝ) / 2 ^ (N + 1) ≤ 1 / 2 ^ (i + 1) := by
      rw [div_le_div_iff_of_pos_left (by norm_num) (by positivity) (by positivity)]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hsum : (1 : ℝ) / 2 ^ (i + 1) + 1 / 2 ^ (i + 1) = 1 / 2 ^ i := by
      field_simp
      ring
    have h1 : |(ratOf (glue β γ N i) : ℝ) - y| ≤ |(ratOf (β i) : ℝ) - x| + |x - y| := by
      rw [glue, if_pos hi]
      simpa using abs_sub_le ((ratOf (β i) : ℝ)) x y
    calc |(ratOf (glue β γ N i) : ℝ) - y|
        ≤ |(ratOf (β i) : ℝ) - x| + |x - y| := h1
      _ ≤ 1 / 2 ^ (i + 1) + 1 / 2 ^ (i + 1) := by
          gcongr
          · exact hβ i
          · rw [abs_sub_comm]; exact hxy.trans hstep
      _ = 1 / 2 ^ i := hsum
  · rw [glue, if_neg hi]
    exact hγ i

/-! ### Computable real functions -/

/-- `Realizes α f` : the element `α` of `K₂` **computes** `f`, that is, it turns every name of
every real `x` into a name of `f x`. -/
def Realizes (α : ℕ → ℕ) (f : ℝ → ℝ) : Prop :=
  ∀ (x : ℝ) (β : ℕ → ℕ), IsName β x → ∃ g, g ∈ appK α β ∧ IsName g (f x)

/-- A **computable real function**: one computed by some element of `K₂`. -/
def IsComputableFun (f : ℝ → ℝ) : Prop := ∃ α, Realizes α f

/-- **The modulus of continuity of a computable real function.**  For every point `x` and every
accuracy `k` there is a stage `N` such that all `y` within `2 ^ (-N-1)` of `x` have `f y` within
`2 ^ (1-k)` of `f x`. -/
theorem Realizes.exists_modulus {α : ℕ → ℕ} {f : ℝ → ℝ} (hα : Realizes α f) (x : ℝ) (k : ℕ) :
    ∃ N : ℕ, ∀ y : ℝ, |y - x| ≤ 1 / 2 ^ (N + 1) → |f y - f x| ≤ 1 / 2 ^ k + 1 / 2 ^ k := by
  obtain ⟨β, hβ⟩ := exists_fastName x
  obtain ⟨g, hg, hgname⟩ := hα x β hβ.isName
  obtain ⟨N, hN⟩ := appK_continuous hg k
  refine ⟨N, fun y hy => ?_⟩
  obtain ⟨γ, hγ⟩ := exists_fastName y
  have hglue : IsName (glue β γ N) y := glue_isName hβ hγ.isName hy
  obtain ⟨g', hg', hg'name⟩ := hα y (glue β γ N) hglue
  have hval : g' k = g k := hN (glue β γ N) g' (glue_agree β γ N) hg'
  have h1 : |(ratOf (g' k) : ℝ) - f y| ≤ 1 / 2 ^ k := hg'name k
  have h2 : |(ratOf (g k) : ℝ) - f x| ≤ 1 / 2 ^ k := hgname k
  rw [hval] at h1
  calc |f y - f x| ≤ |f y - (ratOf (g k) : ℝ)| + |(ratOf (g k) : ℝ) - f x| :=
        abs_sub_le _ _ _
    _ ≤ 1 / 2 ^ k + 1 / 2 ^ k := by
        gcongr
        rw [abs_sub_comm]
        exact h1

/-- **A computable real function is continuous.** -/
theorem Realizes.continuous {α : ℕ → ℕ} {f : ℝ → ℝ} (hα : Realizes α f) : Continuous f := by
  rw [Metric.continuous_iff]
  intro x e he
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 : ℝ) / 2 ^ k + 1 / 2 ^ k < e := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (half_pos he) (by norm_num : (1 : ℝ) / 2 < 1)
    refine ⟨k, ?_⟩
    rw [div_pow, one_pow] at hk
    linarith
  obtain ⟨N, hN⟩ := hα.exists_modulus x k
  refine ⟨1 / 2 ^ (N + 1), by positivity, fun y hy => ?_⟩
  rw [Real.dist_eq] at hy ⊢
  exact lt_of_le_of_lt (hN y hy.le) hk

theorem IsComputableFun.continuous {f : ℝ → ℝ} (hf : IsComputableFun f) : Continuous f := by
  obtain ⟨α, hα⟩ := hf
  exact hα.continuous

/-- The step function is not computable, although all of its values are computable reals: the
obstruction is continuity, not the values. -/
theorem not_isComputableFun_step :
    ¬ IsComputableFun (fun x : ℝ => if x < 0 then 0 else 1) := by
  rintro ⟨α, hα⟩
  obtain ⟨N, hN⟩ := hα.exists_modulus 0 2
  have hpos : (0 : ℝ) < 1 / 2 ^ (N + 1) := by positivity
  have hneg : (-(1 / 2 ^ (N + 1)) : ℝ) < 0 := neg_lt_zero.2 hpos
  have hy : |(-(1 / 2 ^ (N + 1)) : ℝ) - 0| ≤ 1 / 2 ^ (N + 1) := by
    rw [sub_zero, abs_neg, abs_of_nonneg hpos.le]
  have hval : |(0 : ℝ) - 1| ≤ 1 / 2 ^ 2 + 1 / 2 ^ 2 := by
    simpa [hneg] using hN (-(1 / 2 ^ (N + 1))) hy
  norm_num at hval

/-! ### The notion is not vacuous -/

/-- The identity is computable: it is realized by the canonical associate of the identity
operation of Baire space. -/
theorem isComputableFun_id : IsComputableFun (fun x : ℝ => x) := by
  refine ⟨detAssoc (fun β => β), fun x β hβ => ⟨β, ?_, hβ⟩⟩
  rw [appK_detAssoc (fun α y => ⟨y + 1, fun α' h => h y (by omega)⟩) β]
  exact Part.mem_some β

/-- Every constant function is computable. -/
theorem isComputableFun_const (c : ℝ) : IsComputableFun (fun _ : ℝ => c) := by
  obtain ⟨γ, hγ⟩ := exists_fastName c
  refine ⟨detAssoc (fun _ => γ), fun x β _ => ⟨γ, ?_, hγ.isName⟩⟩
  rw [appK_detAssoc (cont_const γ) β]
  exact Part.mem_some γ

end KleeneTwo

end Realizability
