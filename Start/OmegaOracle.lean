/-
# `Ω` as a halting oracle, and the irrationality of `Ω`

`Start/OmegaUncomputable.lean` shows that Chaitin's constant is not a computable real.  Its proof
already contains the quantitative heart of the matter, and this file draws out the two classical
consequences that the proof is really about.

* **Finitely many bits of `Ω` decide the halting problem.**  `Lambda.omegaBits n = ⌊Ω · 2 ^ n⌋` is
  the number formed by the first `n` binary digits of `Ω`.  There is one partial recursive
  procedure `Lambda.oracleRun` which, fed the number `omegaBits n` together with `n` and any code
  `c` whose associated closed program has at most `n - 2` bits, terminates and returns the correct
  answer to "does `c` have a normal form?".  So the first `n` bits of `Ω` settle the halting
  problem for all programs of at most `n - 2` bits.

* **`Ω` is irrational.**  Rational numbers are computable reals, so this is immediate from
  `Lambda.not_realComputable_chaitinOmega`.

This is the classical "`Ω` is an algorithmically random halting oracle" package minus the
Martin-Löf randomness statement itself, which needs the machine-existence (Kraft–Chaitin) theorem
and is not formalized here.
-/

import Start.OmegaUncomputable

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

noncomputable section

------------------------------------------------------------------------
-- The bits of `Ω`
------------------------------------------------------------------------

/-- The first `n` binary digits of `Ω`, read as a natural number: `⌊Ω · 2 ^ n⌋`. -/
def omegaBits (n : ℕ) : ℕ := ⌊chaitinOmega * 2 ^ n⌋₊

theorem omegaBits_le (n : ℕ) : (omegaBits n : ℝ) / 2 ^ n ≤ chaitinOmega := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have h : (omegaBits n : ℝ) ≤ chaitinOmega * 2 ^ n :=
    Nat.floor_le (le_of_lt (by have := chaitinOmega_pos; positivity))
  rw [div_le_iff₀ hp]
  exact h

theorem lt_omegaBits_add_one (n : ℕ) :
    chaitinOmega < ((omegaBits n : ℝ) + 1) / 2 ^ n := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have h : chaitinOmega * 2 ^ n < (omegaBits n : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [lt_div_iff₀ hp]
  exact h

theorem omegaBits_spec (n : ℕ) :
    |chaitinOmega - (omegaBits n : ℝ) / 2 ^ n| ≤ 1 / 2 ^ n := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have h1 := omegaBits_le n
  have h2 := lt_omegaBits_add_one n
  rw [lt_div_iff₀ hp] at h2
  rw [abs_le]
  constructor
  · have : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
    linarith
  · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hp]
    linarith

/-- Truncating the binary expansion: the first `m` bits are read off the first `n` bits. -/
theorem omegaBits_shift {m n : ℕ} (h : m ≤ n) : omegaBits m = omegaBits n / 2 ^ (n - m) := by
  have hsplit : chaitinOmega * 2 ^ m = chaitinOmega * 2 ^ n / ((2 ^ (n - m) : ℕ) : ℝ) := by
    have hp : (0 : ℝ) < 2 ^ (n - m) := by positivity
    rw [eq_div_iff (by positivity)]
    push_cast
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  rw [omegaBits, hsplit, Nat.floor_div_natCast, omegaBits]

------------------------------------------------------------------------
-- The decider depends on `Ω` only through one value
------------------------------------------------------------------------

theorem omegaTest_congr {g₁ g₂ : ℕ → ℕ} {c : ℕ} (h : g₁ (precIdx c) = g₂ (precIdx c)) (k : ℕ) :
    omegaTest g₁ c k = omegaTest g₂ c k := by
  simp [omegaTest, h]

theorem haltRun_congr {g₁ g₂ : ℕ → ℕ} {c : ℕ} (h : g₁ (precIdx c) = g₂ (precIdx c)) :
    haltRun g₁ c = haltRun g₂ c := by
  have hf : (fun k => Part.some (cond (is_valid_code c) (omegaTest g₁ c k) Bool.true))
      = (fun k => Part.some (cond (is_valid_code c) (omegaTest g₂ c k) Bool.true)) := by
    funext k
    rw [omegaTest_congr h]
  simp only [haltRun, hf]

------------------------------------------------------------------------
-- The oracle procedure
------------------------------------------------------------------------

/-- Reading the first `m` bits off a number `a` that holds the first `n` bits. -/
def prefixOracle (a n : ℕ) : ℕ → ℕ := fun m => a / 2 ^ (n - m)

/-- The halting decider driven by a finite prefix of the binary expansion of `Ω`. -/
def oracleRun (a n c : ℕ) : Part Bool := haltRun (prefixOracle a n) c

theorem partrec_oracleRun : Partrec fun p : ℕ × ℕ × ℕ => oracleRun p.1 p.2.1 p.2.2 := by
  have ha : Primrec (fun q : (ℕ × ℕ × ℕ) × ℕ => q.1.1) := Primrec.fst.comp Primrec.fst
  have hn : Primrec (fun q : (ℕ × ℕ × ℕ) × ℕ => q.1.2.1) :=
    (Primrec.fst.comp Primrec.snd).comp Primrec.fst
  have hc : Primrec (fun q : (ℕ × ℕ × ℕ) × ℕ => q.1.2.2) :=
    (Primrec.snd.comp Primrec.snd).comp Primrec.fst
  have hpi : Primrec (fun q : (ℕ × ℕ × ℕ) × ℕ => precIdx q.1.2.2) := precIdx_primrec.comp hc
  have hg : Primrec (fun q : (ℕ × ℕ × ℕ) × ℕ => q.1.1 / 2 ^ (q.1.2.1 - precIdx q.1.2.2)) :=
    Primrec.nat_div.comp ha (primrec_two_pow.comp (Primrec.nat_sub.comp hn hpi))
  have hA : Primrec (fun q : (ℕ × ℕ × ℕ) × ℕ => 2 ^ (4 * q.2 + 2)) :=
    primrec_two_pow.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) Primrec.snd) (Primrec.const 2))
  have hB : Primrec (fun q : (ℕ × ℕ × ℕ) × ℕ => 2 ^ precIdx q.1.2.2) := primrec_two_pow.comp hpi
  have hN : Primrec (fun q : (ℕ × ℕ × ℕ) × ℕ => omegaNum q.2) := omegaNum_primrec.comp Primrec.snd
  have hlhs := Primrec.nat_mul.comp hg hA
  have hrhs := Primrec.nat_add.comp (Primrec.nat_mul.comp hN hB)
    (Primrec.nat_mul.comp (Primrec.const 3) hA)
  obtain ⟨_inst, hlt⟩ := (Primrec.nat_lt : PrimrecRel (fun a b : ℕ => a < b))
  have htest : Computable₂ (fun (p : ℕ × ℕ × ℕ) (k : ℕ) =>
      omegaTest (prefixOracle p.1 p.2.1) p.2.2 k) :=
    ((hlt.comp (Primrec.pair hlhs hrhs)).to_comp).of_eq
      (fun q => by
        simp only [omegaTest, prefixOracle]
        exact decide_eq_decide.mpr Iff.rfl)
  have hv : Computable (fun p : ℕ × ℕ × ℕ => is_valid_code p.2.2) :=
    (Lambda.is_valid_code_primrec.comp (Primrec.snd.comp Primrec.snd)).to_comp
  have hstop : Computable₂ (fun (p : ℕ × ℕ × ℕ) (k : ℕ) =>
      cond (is_valid_code p.2.2) (omegaTest (prefixOracle p.1 p.2.1) p.2.2 k) Bool.true) :=
    Computable.cond (hv.comp Computable.fst) htest (Computable.const Bool.true)
  have hval : Computable₂ (fun (p : ℕ × ℕ × ℕ) (k : ℕ) =>
      cond (is_valid_code p.2.2)
        (decide (closure_code p.2.2 ≤ k) && haltsBy_code (closure_code p.2.2) k) Bool.false) := by
    refine Computable.cond (hv.comp Computable.fst) ?_ (Computable.const Bool.false)
    have hcl : Primrec (fun q : (ℕ × ℕ × ℕ) × ℕ => closure_code q.1.2.2) :=
      closure_code_primrec.comp hc
    have h1 : Primrec (fun q : (ℕ × ℕ × ℕ) × ℕ => decide (closure_code q.1.2.2 ≤ q.2)) := by
      obtain ⟨_inst, hle⟩ := (Primrec.nat_le : PrimrecRel (fun a b : ℕ => a ≤ b))
      exact (hle.comp (Primrec.pair hcl Primrec.snd)).of_eq (fun q => by congr)
    have h2 : Primrec (fun q : (ℕ × ℕ × ℕ) × ℕ => haltsBy_code (closure_code q.1.2.2) q.2) :=
      haltsBy_code_primrec.comp hcl Primrec.snd
    exact (Primrec.and.comp h1 h2).to_comp
  exact Partrec.map (Partrec.rfind hstop) hval

/-- Fed the first `n` bits of `Ω`, the procedure decides halting for every code whose closed
program has at most `n - 2` bits. -/
theorem oracleRun_spec {c n : ℕ} (h : precIdx c ≤ n) :
    ∃ b : Bool, oracleRun (omegaBits n) n c = Part.some b ∧
      (b = Bool.true ↔ CodeHasNormalForm c) := by
  have hval : prefixOracle (omegaBits n) n (precIdx c) = omegaBits (precIdx c) := by
    rw [prefixOracle, omegaBits_shift h]
  refine ⟨haltDecide omegaBits c, ?_, (haltDecide_iff omegaBits_spec c).symm⟩
  rw [oracleRun, haltRun_congr hval]
  exact haltRun_eq omegaBits_spec c

/-- **The first `n` bits of `Ω` decide the halting problem for all programs of at most `n - 2`
bits.**  One partial recursive procedure, uniform in everything, does the job. -/
theorem chaitinOmega_prefix_decides_halting :
    (Partrec fun p : ℕ × ℕ × ℕ => oracleRun p.1 p.2.1 p.2.2) ∧
      ∀ n c : ℕ, precIdx c ≤ n →
        ∃ b : Bool, oracleRun (omegaBits n) n c = Part.some b ∧
          (b = Bool.true ↔ CodeHasNormalForm c) :=
  ⟨partrec_oracleRun, fun _ _ h => oracleRun_spec h⟩

------------------------------------------------------------------------
-- Irrationality
------------------------------------------------------------------------

theorem primrec_natCast_int : Primrec (fun n : ℕ => (n : ℤ)) := by
  have h : Primrec (fun n : ℕ => Denumerable.ofNat ℤ (2 * n)) :=
    (Primrec.ofNat ℤ).comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
  refine h.of_eq (fun n => ?_)
  have h1 : Equiv.intEquivNat (Int.ofNat n) = 2 * n := rfl
  have h2 : Denumerable.ofNat ℤ (2 * n) = Equiv.intEquivNat.symm (2 * n) := rfl
  rw [h2, ← h1, Equiv.symm_apply_apply]
  rfl

theorem realComputable_of_eq_div {x : ℝ} {a b : ℕ} (hb : 0 < b) (hx : x = (a : ℝ) / b) :
    RealComputable x := by
  refine ⟨fun n => ((a * 2 ^ n / b : ℕ) : ℤ), ?_, fun n => ?_⟩
  · exact (primrec_natCast_int.comp ((Primrec.nat_div.comp
      (Primrec.nat_mul.comp (Primrec.const a) primrec_two_pow) (Primrec.const b)))).to_comp
  · have hB : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    have hP : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hdm : b * (a * 2 ^ n / b) + a * 2 ^ n % b = a * 2 ^ n := Nat.div_add_mod _ _
    have hdmR : (b : ℝ) * ((a * 2 ^ n / b : ℕ) : ℝ) + ((a * 2 ^ n % b : ℕ) : ℝ)
        = (a : ℝ) * 2 ^ n := by exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hdm
    have hrlt : ((a * 2 ^ n % b : ℕ) : ℝ) < (b : ℝ) := by
      exact_mod_cast Nat.mod_lt _ hb
    have hrnn : (0 : ℝ) ≤ ((a * 2 ^ n % b : ℕ) : ℝ) := by positivity
    have hcast : (((a * 2 ^ n / b : ℕ) : ℤ) : ℝ) = ((a * 2 ^ n / b : ℕ) : ℝ) := by
      exact_mod_cast rfl
    have hkey : x - (((a * 2 ^ n / b : ℕ) : ℤ) : ℝ) / 2 ^ n
        = ((a * 2 ^ n % b : ℕ) : ℝ) / ((b : ℝ) * 2 ^ n) := by
      have h3 : (a : ℝ) * 2 ^ n - (b : ℝ) * ((a * 2 ^ n / b : ℕ) : ℝ)
          = ((a * 2 ^ n % b : ℕ) : ℝ) := by linarith
      rw [hx, hcast, div_sub_div _ _ (ne_of_gt hB) (ne_of_gt hP), ← h3]
    rw [hkey, abs_of_nonneg (by positivity)]
    rw [div_le_div_iff₀ (by positivity) hP]
    nlinarith [hrlt, hP.le]

/-- **Chaitin's constant is irrational**: rationals are computable reals. -/
theorem irrational_chaitinOmega : Irrational chaitinOmega := by
  rintro ⟨q, hq⟩
  have hqpos : 0 < q := by
    have := chaitinOmega_pos
    rw [← hq] at this
    exact_mod_cast this
  have hnum : 0 < q.num := Rat.num_pos.2 hqpos
  have hnc : ((q.num.toNat : ℕ) : ℝ) = ((q.num : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hnum.le)
  have hx : chaitinOmega = ((q.num.toNat : ℕ) : ℝ) / ((q.den : ℕ) : ℝ) := by
    rw [← hq, Rat.cast_def, hnc]
  exact not_realComputable_chaitinOmega (realComputable_of_eq_div q.pos hx)

end

end Lambda
