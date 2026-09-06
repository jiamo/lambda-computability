/-
**Specker's theorem: the limit of a computable monotone bounded sequence need not be computable.**

`Start/Specker.lean` builds a computable, nondecreasing, bounded sequence of rationals
`Lambda.speckerVal` with no computable modulus of convergence.  This module takes its limit
`Lambda.speckerReal` — the supremum of the sequence in `ℝ` — and shows that this real number is
**not computable**: no computable `f : ℕ → ℕ` approximates it by the dyadic rationals
`f m / 2 ^ m` to within `2 ^ (-m)`.

Since the limit is nonnegative (`Lambda.speckerReal_nonneg`), restricting the numerators to `ℕ`
is no loss of generality: a nonnegative real is approximated by `⌊x · 2 ^ m⌋ / 2 ^ m`, whose
numerator is already a natural number.

* `Lambda.speckerReal` — the limit, with `Lambda.speckerVal_le_speckerReal`,
  `Lambda.speckerReal_le_one` and `Lambda.exists_speckerVal_gt`;
* `Lambda.specker_limit_not_computable` — **the limit is not a computable real**.
-/

import Start.Specker
import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

/-! ### The limit -/

theorem speckerVal_bddAbove : BddAbove (Set.range fun n : ℕ => ((speckerVal n : ℚ) : ℝ)) := by
  refine ⟨1, ?_⟩
  rintro x ⟨n, rfl⟩
  change ((speckerVal n : ℚ) : ℝ) ≤ 1
  exact_mod_cast (speckerVal_lt_one n).le

/-- **The limit of the Specker sequence**, as a real number. -/
noncomputable def speckerReal : ℝ := ⨆ n : ℕ, ((speckerVal n : ℚ) : ℝ)

theorem speckerVal_le_speckerReal (n : ℕ) : ((speckerVal n : ℚ) : ℝ) ≤ speckerReal :=
  le_ciSup speckerVal_bddAbove n

theorem speckerReal_nonneg : 0 ≤ speckerReal := by
  have h := speckerVal_le_speckerReal 0
  simpa [speckerVal] using h

theorem speckerReal_le_one : speckerReal ≤ 1 :=
  ciSup_le fun n => by
    change ((speckerVal n : ℚ) : ℝ) ≤ 1
    exact_mod_cast (speckerVal_lt_one n).le

/-- The sequence really does converge to `Lambda.speckerReal`. -/
theorem speckerVal_tendsto_speckerReal :
    Filter.Tendsto (fun n : ℕ => ((speckerVal n : ℚ) : ℝ)) Filter.atTop (nhds speckerReal) := by
  refine tendsto_atTop_ciSup ?_ speckerVal_bddAbove
  intro a b hab
  change ((speckerVal a : ℚ) : ℝ) ≤ ((speckerVal b : ℚ) : ℝ)
  exact_mod_cast speckerVal_monotone hab

theorem exists_speckerVal_gt {r : ℝ} (h : r < speckerReal) :
    ∃ s, r < ((speckerVal s : ℚ) : ℝ) :=
  exists_lt_of_lt_ciSup h

/-! ### Dyadic comparisons -/

/-- Comparing a dyadic rational with a stage of the Specker sequence is a comparison of natural
numbers. -/
theorem dyadic_lt_speckerVal_iff (a s m : ℕ) :
    (a : ℝ) / 2 ^ m - 1 / 2 ^ m < ((speckerVal s : ℚ) : ℝ) ↔
      a * 2 ^ s < speckerNum s * 2 ^ m + 2 ^ s := by
  have hval : ((speckerVal s : ℚ) : ℝ) = (speckerNum s : ℝ) / 2 ^ s := by
    rw [speckerVal_eq]
    push_cast
    ring
  rw [hval, div_sub_div_same, div_lt_div_iff₀ (by positivity : (0:ℝ) < 2 ^ m)
    (by positivity : (0:ℝ) < 2 ^ s)]
  constructor
  · intro h
    have h' : ((a : ℝ) * 2 ^ s) < (speckerNum s : ℝ) * 2 ^ m + 2 ^ s := by nlinarith [h]
    exact_mod_cast h'
  · intro h
    have h' : ((a : ℝ) * 2 ^ s) < (speckerNum s : ℝ) * 2 ^ m + 2 ^ s := by exact_mod_cast h
    nlinarith [h']

/-! ### The limit is not computable -/

/-- The search predicate: at precision `k + 4`, stage `s` already exceeds the lower bound
`f (k + 4) / 2 ^ (k + 4) - 1 / 2 ^ (k + 4)` supplied by the approximation `f`. -/
def speckerFound (f : ℕ → ℕ) (k s : ℕ) : Bool :=
  decide (f (k + 4) * 2 ^ s < speckerNum s * 2 ^ (k + 4) + 2 ^ s)

theorem computable_speckerFound {f : ℕ → ℕ} (hf : Computable f) :
    Computable₂ (speckerFound f) := by
  have hnatpow : Primrec₂ (· ^ · : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hm : Computable fun p : ℕ × ℕ => p.1 + 4 :=
    (Primrec.succ.comp (Primrec.succ.comp (Primrec.succ.comp
      (Primrec.succ.comp Primrec.fst)))).to_comp
  have hpowsnd : Computable fun p : ℕ × ℕ => 2 ^ p.2 :=
    (hnatpow.comp (Primrec.const 2) Primrec.snd).to_comp
  have hpowm : Computable fun p : ℕ × ℕ => 2 ^ (p.1 + 4) :=
    (hnatpow.comp (Primrec.const 2)
      (Primrec.succ.comp (Primrec.succ.comp (Primrec.succ.comp
        (Primrec.succ.comp Primrec.fst))))).to_comp
  have hlhs : Computable fun p : ℕ × ℕ => f (p.1 + 4) * 2 ^ p.2 :=
    (Primrec₂.to_comp Primrec.nat_mul).comp (hf.comp hm) hpowsnd
  have hrhs : Computable fun p : ℕ × ℕ => speckerNum p.2 * 2 ^ (p.1 + 4) + 2 ^ p.2 :=
    (Primrec₂.to_comp Primrec.nat_add).comp
      ((Primrec₂.to_comp Primrec.nat_mul).comp
        (computable_speckerNum.comp Primrec.snd.to_comp) hpowm) hpowsnd
  obtain ⟨_, hltP⟩ := (Primrec.nat_lt : PrimrecRel (fun a b : ℕ => a < b))
  have hcmp : Computable₂ (fun a b : ℕ => decide (a < b)) := by
    refine (Primrec.to_comp hltP).of_eq ?_
    intro p
    simp
  exact hcmp.comp hlhs hrhs

/-- **Specker's theorem.**  The limit of the computable, nondecreasing, bounded rational sequence
`Lambda.speckerVal` is not a computable real number: there is no computable `f : ℕ → ℕ` with
`|speckerReal - f m / 2 ^ m| < 2 ^ (-m)` for every `m`.  (Since the limit is nonnegative,
natural-number numerators are no restriction.) -/
theorem specker_limit_not_computable :
    ¬ ∃ f : ℕ → ℕ, Computable f ∧
      ∀ m, |speckerReal - (f m : ℝ) / 2 ^ m| < 1 / 2 ^ m := by
  rintro ⟨f, hf, happ⟩
  classical
  -- the search always succeeds
  have hex : ∀ k, ∃ s, speckerFound f k s = Bool.true := by
    intro k
    have h := happ (k + 4)
    rw [abs_lt] at h
    have hlow : (f (k + 4) : ℝ) / 2 ^ (k + 4) - 1 / 2 ^ (k + 4) < speckerReal := by
      linarith [h.1]
    obtain ⟨s, hs⟩ := exists_speckerVal_gt hlow
    refine ⟨s, ?_⟩
    simpa [speckerFound, decide_eq_true_eq] using
      (dyadic_lt_speckerVal_iff (f (k + 4)) s (k + 4)).1 hs
  -- the value found is a good stage: the remaining tail is smaller than `2 ^ (-(k+3))`
  have hgood : ∀ k s, speckerFound f k s = Bool.true →
      speckerReal - ((speckerVal s : ℚ) : ℝ) < 1 / 2 ^ (k + 3) := by
    intro k s hs
    have h := happ (k + 4)
    rw [abs_lt] at h
    have hlt : (f (k + 4) : ℝ) / 2 ^ (k + 4) - 1 / 2 ^ (k + 4) < ((speckerVal s : ℚ) : ℝ) :=
      (dyadic_lt_speckerVal_iff (f (k + 4)) s (k + 4)).2 (by
        simpa [speckerFound, decide_eq_true_eq] using hs)
    set e : ℝ := 1 / 2 ^ (k + 4) with he
    have htwo : (1 : ℝ) / 2 ^ (k + 3) = e + e := by
      rw [he, pow_succ]
      ring
    rw [htwo]
    linarith [h.2]
  -- a good stage decides the halting set
  have hdec : ∀ k s, speckerFound f k s = Bool.true → (HaltK k ↔ entered k s = Bool.true) := by
    intro k s hs
    constructor
    · intro hk
      by_contra hne
      rw [Bool.not_eq_true] at hne
      obtain ⟨s0, hs0⟩ := (haltK_iff_entered k).1 hk
      set s' := max (max s0 s) (k + 1) with hs'def
      have h1 : entered k s' = Bool.true :=
        entered_mono (le_trans (le_max_left _ _) (le_max_left _ _)) hs0
      have h2 : s ≤ s' := le_trans (le_max_right _ _) (le_max_left _ _)
      have h3 : k < s' := lt_of_lt_of_le (by omega) (le_max_right _ _)
      have hjump : speckerVal s + 1 / 2 ^ (k + 1) ≤ speckerVal s' :=
        speckerVal_jump h2 h3 hne h1
      have hjumpR : ((speckerVal s : ℚ) : ℝ) + 1 / 2 ^ (k + 1) ≤ ((speckerVal s' : ℚ) : ℝ) := by
        have hc := (Rat.cast_le (K := ℝ)).2 hjump
        push_cast at hc
        linarith
      have hle := speckerVal_le_speckerReal s'
      have hbound := hgood k s hs
      have hpow : (1 : ℝ) / 2 ^ (k + 3) < 1 / 2 ^ (k + 1) := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        have hlt2 : (2 : ℝ) ^ (k + 1) < 2 ^ (k + 3) :=
          pow_lt_pow_right₀ (by norm_num) (by omega)
        linarith
      linarith
    · intro h
      exact (haltK_iff_entered k).2 ⟨_, h⟩
  -- hence the halting set is decidable, a contradiction
  have hpartrec : Partrec fun k : ℕ =>
      Part.map (fun s => entered k s) (Nat.rfind fun s => Part.some (speckerFound f k s)) :=
    (Partrec.rfind (computable_speckerFound hf).partrec₂).map
      ((Primrec₂.to_comp primrec_entered).comp Computable.fst Computable.snd)
  have heq : ∀ k : ℕ,
      Part.map (fun s => entered k s) (Nat.rfind fun s => Part.some (speckerFound f k s))
        = Part.some (decide (HaltK k)) := by
    intro k
    obtain ⟨s0, hs0⟩ := hex k
    obtain ⟨n, hn, -⟩ := Nat.rfind_min' (p := fun s => speckerFound f k s) hs0
    have hspec : speckerFound f k n = Bool.true := by
      have h := Nat.rfind_spec hn
      simpa using h
    refine Part.eq_some_iff.2 ((Part.mem_map_iff _).2 ⟨n, hn, ?_⟩)
    by_cases hk : HaltK k
    · simp [hk, (hdec k n hspec).1 hk]
    · have hnk : entered k n = Bool.false := by
        rcases Bool.eq_false_or_eq_true (entered k n) with h | h
        · exact absurd ((hdec k n hspec).2 h) hk
        · exact h
      simp [hk, hnk]
  have hcomp : ComputablePred HaltK :=
    ComputablePred.computable_iff.2
      ⟨fun k => decide (HaltK k), hpartrec.of_eq heq, by funext k; simp⟩
  exact not_rePred_not_haltK (ComputablePred.to_re hcomp.not)

end Lambda
