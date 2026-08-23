/-
# Chaitin's constant is not a computable real

`Start/ChaitinOmega.lean` builds the halting probability

  `Ω = ∑ { 2 ^ (-|bits t|) : t closed and normalizing }`

and stops at its convergence (`0 < Ω < 1`).  This file proves the classical next theorem:

  `Lambda.not_realComputable_chaitinOmega : ¬ RealComputable chaitinOmega`,

where `Lambda.RealComputable x` is the standard notion "some computable function produces dyadic
rationals `f n / 2 ^ n` approximating `x` to within `2 ^ (-n)`".

The proof is Chaitin's.  The halting set is computably enumerable, so `Ω` is a computable
*supremum*: the stage-`k` approximation

  `Ω_k = ∑ { 2 ^ (-|bits t|) : encode t ≤ k, t closed, t normal after k leftmost steps }`

is a primitive recursive dyadic rational (`Lambda.omegaNum`) and increases to `Ω`.  If moreover a
computable *upper* estimate for `Ω` is available, the two can be played against each other: to
decide whether a closed term `u` with `L = |bits u|` bits halts, approximate `Ω` to within
`2 ^ (-L-2)` and enumerate stages until `Ω_k` exceeds `Ω - 2 ^ (-L)`.  At that stage every halting
program of length `L` must already have been found, since otherwise its weight `2 ^ (-L)` would
still be missing from `Ω_k`.  So halting becomes decidable, contradicting
`Lambda.not_computablePred_codeHasNormalForm`.

Arbitrary terms are reduced to closed ones by `Lambda.closure`, whose code-level version is the
primitive recursive `Lambda.closure_code`.
-/

import Start.ChaitinOmega
import Start.PlainVsPrefix
import Start.KolmogorovHalting

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

open scoped BigOperators

------------------------------------------------------------------------
-- A primitive recursive `Int.toNat`
------------------------------------------------------------------------

theorem ofNat_int_toNat (n : ℕ) :
    (Denumerable.ofNat ℤ n).toNat = if n.bodd then 0 else n.div2 := by
  change ((Equiv.intEquivNat.symm n : ℤ)).toNat = _
  simp only [Equiv.intEquivNat, Equiv.trans, Equiv.symm, Equiv.coe_fn_mk,
    Equiv.natSumNatEquivNat, Equiv.intEquivNatSumNat, Equiv.boolProdNatEquivNat,
    Equiv.boolProdEquivSum, Function.comp_apply]
  cases n.bodd <;> simp

theorem primrec_int_toNat : Primrec (fun z : ℤ => z.toNat) := by
  have h : Primrec (fun n : ℕ => if n.bodd then 0 else n.div2) :=
    (Primrec.cond Primrec.nat_bodd (Primrec.const 0) Primrec.nat_div2).of_eq
      (fun n => by cases n.bodd <;> simp)
  refine (h.comp (Primrec.encode (α := ℤ))).of_eq (fun z => ?_)
  rw [← ofNat_int_toNat, Denumerable.ofNat_encode]

------------------------------------------------------------------------
-- Valid codes
------------------------------------------------------------------------

/-- Unfolding lemma for `Lambda.is_valid_code`. -/
theorem is_valid_code_eq (n : ℕ) :
    is_valid_code n =
      (match _h : n.unpair with
       | (0, _) => Bool.true
       | (1, m) =>
         match _hm : m.unpair with
         | (c₁, c₂) => is_valid_code c₁ && is_valid_code c₂
       | (2, m) => is_valid_code m
       | _ => Bool.false) := by
  conv_lhs => rw [Lambda.is_valid_code, Nat.strongRecOn_eq]
  congr! 2

@[simp] theorem is_valid_code_pair_zero (i : ℕ) :
    is_valid_code (Nat.pair 0 i) = Bool.true := by
  rw [is_valid_code_eq]; split <;> simp_all

@[simp] theorem is_valid_code_pair_one (a b : ℕ) :
    is_valid_code (Nat.pair 1 (Nat.pair a b)) = (is_valid_code a && is_valid_code b) := by
  rw [is_valid_code_eq]
  split <;>
    (simp_all only [Nat.unpair_pair, Prod.mk.injEq, one_ne_zero, OfNat.one_ne_ofNat, false_and,
        true_and, implies_true, imp_false, forall_eq']
     all_goals (subst_vars; simp))

@[simp] theorem is_valid_code_pair_two (a : ℕ) :
    is_valid_code (Nat.pair 2 a) = is_valid_code a := by
  rw [is_valid_code_eq]; split <;> simp_all

@[simp] theorem is_valid_code_encode (t : Lambda) :
    is_valid_code (Lambda.encode t) = Bool.true := by
  induction t with
  | var i => simp [Lambda.encode]
  | app a b iha ihb => simp [Lambda.encode, iha, ihb]
  | lam u ih => simp [Lambda.encode, ih]

theorem exists_encode_of_is_valid_code :
    ∀ (c : ℕ), is_valid_code c = Bool.true → ∃ t : Lambda, Lambda.encode t = c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
      intro hc
      rw [is_valid_code_eq] at hc
      split at hc
      · next m hu =>
          exact ⟨Lambda.var m, by rw [Lambda.encode, ← Nat.pair_unpair c, hu]⟩
      · next m hu =>
          split at hc
          next c₁ c₂ hm =>
            have h1 : c₁ < c := Lambda.decode_lt_1 hu hm
            have h2 : c₂ < c := Lambda.decode_lt_2 hu hm
            rw [Bool.and_eq_true] at hc
            obtain ⟨t₁, ht₁⟩ := ih c₁ h1 hc.1
            obtain ⟨t₂, ht₂⟩ := ih c₂ h2 hc.2
            have hm' : Nat.pair c₁ c₂ = m := by rw [← Nat.pair_unpair m, hm]
            have hu' : Nat.pair 1 m = c := by rw [← Nat.pair_unpair c, hu]
            exact ⟨Lambda.app t₁ t₂, by rw [Lambda.encode, ht₁, ht₂, hm', hu']⟩
      · next m hu =>
          obtain ⟨u, hu'⟩ := ih m (Lambda.decode_lt_3 hu) hc
          exact ⟨Lambda.lam u, by rw [Lambda.encode, hu', ← Nat.pair_unpair c, hu]⟩
      · exact absurd hc (by simp)

theorem is_valid_code_iff (c : ℕ) :
    is_valid_code c = Bool.true ↔ ∃ t : Lambda, Lambda.encode t = c :=
  ⟨exists_encode_of_is_valid_code c, fun ⟨t, ht⟩ => ht ▸ is_valid_code_encode t⟩

/-- The total decoding function: junk codes are sent to `var 0`. -/
def decodeD (c : ℕ) : Lambda := (Lambda.decode c).getD (Lambda.var 0)

@[simp] theorem decodeD_encode (t : Lambda) : decodeD (Lambda.encode t) = t := by
  simp [decodeD, Lambda.decode_encode]

theorem encode_decodeD {c : ℕ} (h : is_valid_code c = Bool.true) :
    Lambda.encode (decodeD c) = c := by
  obtain ⟨t, rfl⟩ := (is_valid_code_iff c).1 h
  simp

------------------------------------------------------------------------
-- The bit length of a code
------------------------------------------------------------------------

/-- The code-level version of `fun t => (bits t).length`. -/
def bitsLen_code : ℕ → ℕ :=
  codeFold (fun i => i + 2) (fun a b => a + b + 2) (fun a => a + 2)

@[simp] theorem bitsLen_code_correct (t : Lambda) :
    bitsLen_code (Lambda.encode t) = (bits t).length := by
  have key : ∀ u : Lambda,
      termFold (fun i => i + 2) (fun a b => a + b + 2) (fun a => a + 2) u = (bits u).length := by
    intro u
    induction u with
    | var i => simp [termFold]
    | app a b iha ihb => simp [termFold, iha, ihb]
    | lam v ih => simp [termFold, ih]
  rw [bitsLen_code, codeFold_correct, key]

theorem bitsLen_code_primrec : Primrec bitsLen_code := by
  refine codeFold_primrec ?_ ?_ ?_
  · exact Primrec.nat_add.comp Primrec.id (Primrec.const 2)
  · exact Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd) (Primrec.const 2)
  · exact Primrec.nat_add.comp Primrec.id (Primrec.const 2)

theorem bitsLen_code_le (c : ℕ) (h : is_valid_code c = Bool.true) : bitsLen_code c ≤ 4 * c + 2 := by
  obtain ⟨t, rfl⟩ := (is_valid_code_iff c).1 h
  rw [bitsLen_code_correct]
  exact bits_length_le_encode t

------------------------------------------------------------------------
-- Closing a code off
------------------------------------------------------------------------

/-- The code-level version of `fun t => closure (freeMax t) t`. -/
def closure_code (c : ℕ) : ℕ := lam_code^[freeMax_code c] c

theorem lam_code_iterate (n : ℕ) (t : Lambda) :
    lam_code^[n] (Lambda.encode t) = Lambda.encode (closure n t) := by
  induction n with
  | zero => simp [closure]
  | succ n ih => rw [Function.iterate_succ_apply', ih, closure, Lambda.encode, lam_code]

theorem closure_code_correct (t : Lambda) :
    closure_code (Lambda.encode t) = Lambda.encode (closure (freeMax t) t) := by
  rw [closure_code, freeMax_code_correct, lam_code_iterate]

theorem lam_code_iterate_primrec : Primrec₂ (fun c n : ℕ => lam_code^[n] c) := by
  have hstep : Primrec₂ (fun (_ : ℕ) (p : ℕ × ℕ) => lam_code p.2) :=
    Lambda.lam_code_primrec.comp (Primrec.snd.comp Primrec.snd)
  have h := Primrec.nat_rec (f := fun c : ℕ => c) (g := fun (_ : ℕ) (p : ℕ × ℕ) => lam_code p.2)
    Primrec.id hstep
  refine h.of_eq (fun c n => ?_)
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ← ih]

theorem closure_code_primrec : Primrec closure_code := by
  have h := Primrec₂.comp lam_code_iterate_primrec Primrec.id freeMax_code_primrec
  exact h

/-- The closed term attached to a term. -/
def closeTerm (t : Lambda) : Lambda := closure (freeMax t) t

theorem isClosed_closeTerm (t : Lambda) : IsClosed (closeTerm t) := isClosed_closure t

theorem hasNormalForm_closeTerm (t : Lambda) : HasNormalForm (closeTerm t) ↔ HasNormalForm t :=
  hasNormalForm_closure_iff _ t

theorem halts_closeTerm_iff (t : Lambda) : Halts (closeTerm t) ↔ HasNormalForm t :=
  ⟨fun h => (hasNormalForm_closeTerm t).1 h.2,
   fun h => ⟨isClosed_closeTerm t, (hasNormalForm_closeTerm t).2 h⟩⟩

------------------------------------------------------------------------
-- The stage approximations of `Ω`
------------------------------------------------------------------------

/-- `stageHalt k c` tests whether the code `c` is a closed program that is already normal after
`k` leftmost steps. -/
def stageHalt (k c : ℕ) : Bool := is_valid_code c && isClosed_code c && haltsBy_code c k

theorem stageHalt_primrec : Primrec₂ stageHalt := by
  have h1 : Primrec (fun p : ℕ × ℕ => is_valid_code p.2) :=
    Lambda.is_valid_code_primrec.comp Primrec.snd
  have h2 : Primrec (fun p : ℕ × ℕ => isClosed_code p.2) :=
    isClosed_code_primrec.comp Primrec.snd
  have h3 : Primrec (fun p : ℕ × ℕ => haltsBy_code p.2 p.1) :=
    haltsBy_code_primrec.comp Primrec.snd Primrec.fst
  exact (Primrec.and.comp (Primrec.and.comp h1 h2) h3)

theorem stageHalt_encode (k : ℕ) (t : Lambda) :
    stageHalt k (Lambda.encode t) = Bool.true ↔ IsClosed t ∧ is_normal (nstep^[k] t) := by
  simp [stageHalt, isClosed_code_correct, haltsBy_code_correct]

/-- The numerator of the stage-`k` approximation, over the denominator `2 ^ (4 * k + 2)`. -/
def omegaPartial (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | (c + 1) => omegaPartial k c + cond (stageHalt k c) (2 ^ (4 * k + 2 - bitsLen_code c)) 0

/-- The stage-`k` approximation of `Ω`, as a numerator over `2 ^ (4 * k + 2)`. -/
def omegaNum (k : ℕ) : ℕ := omegaPartial k (k + 1)

theorem primrec_two_pow : Primrec (fun n : ℕ => 2 ^ n) := by
  have h := Primrec.nat_rec' (f := fun n : ℕ => n) (g := fun _ : ℕ => 1)
    (h := fun (_ : ℕ) (q : ℕ × ℕ) => 2 * q.2) Primrec.id (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))
  refine h.of_eq (fun n => ?_)
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; ring

theorem omegaPartial_primrec : Primrec₂ omegaPartial := by
  have hcond : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ) => stageHalt x.1.1 x.2.1) :=
    stageHalt_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have hpow : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      2 ^ (4 * x.1.1 + 2 - bitsLen_code x.2.1)) :=
    primrec_two_pow.comp (Primrec.nat_sub.comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4) (Primrec.fst.comp Primrec.fst))
        (Primrec.const 2))
      (bitsLen_code_primrec.comp (Primrec.fst.comp Primrec.snd)))
  have hval : Primrec₂ (fun (p : ℕ × ℕ) (q : ℕ × ℕ) =>
      q.2 + cond (stageHalt p.1 q.1) (2 ^ (4 * p.1 + 2 - bitsLen_code q.1)) 0) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.cond hcond hpow (Primrec.const 0))
  have h := Primrec.nat_rec' (f := fun p : ℕ × ℕ => p.2) (g := fun _ : ℕ × ℕ => (0 : ℕ))
    (h := fun (p : ℕ × ℕ) (q : ℕ × ℕ) =>
      q.2 + cond (stageHalt p.1 q.1) (2 ^ (4 * p.1 + 2 - bitsLen_code q.1)) 0)
    Primrec.snd (Primrec.const 0) hval
  refine h.of_eq (fun p => ?_)
  obtain ⟨k, m⟩ := p
  induction m with
  | zero => rfl
  | succ m ih => simp only [omegaPartial, ← ih]

theorem omegaNum_primrec : Primrec omegaNum := by
  have h := Primrec₂.comp omegaPartial_primrec Primrec.id Primrec.succ
  exact h

/-- The codes counted at stage `k`. -/
def stageCodes (k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter (fun c => stageHalt k c = Bool.true)

theorem mem_stageCodes {k c : ℕ} :
    c ∈ stageCodes k ↔ c ≤ k ∧ stageHalt k c = Bool.true := by
  simp [stageCodes]

/-- The stage-`k` approximation of `Ω`, as a real number. -/
def omegaApprox (k : ℕ) : ℝ := ∑ c ∈ stageCodes k, ((2 : ℝ)⁻¹) ^ (bitsLen_code c)

theorem two_pow_mul_inv_pow {b n : ℕ} (h : b ≤ n) :
    (2 : ℝ) ^ n * ((2 : ℝ)⁻¹) ^ b = 2 ^ (n - b) := by
  have hsplit : (2 : ℝ) ^ n = 2 ^ (n - b) * 2 ^ b := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, mul_assoc, ← mul_pow]
  norm_num

theorem omegaPartial_eq_sum (k : ℕ) :
    ∀ m ≤ k + 1, (omegaPartial k m : ℝ) =
      2 ^ (4 * k + 2) *
        ∑ c ∈ (Finset.range m).filter (fun c => stageHalt k c = Bool.true),
          ((2 : ℝ)⁻¹) ^ (bitsLen_code c) := by
  intro m
  induction m with
  | zero => simp [omegaPartial]
  | succ m ih =>
      intro hm
      have hmk : m ≤ k := by omega
      have ihm := ih (by omega)
      rw [Finset.range_add_one, Finset.filter_insert]
      rcases hb : stageHalt k m with _ | _
      · simp only [Bool.false_eq_true, if_false]
        simp only [omegaPartial, hb, cond_false, Nat.add_zero]
        exact ihm
      · have hnotmem : m ∉ (Finset.range m).filter
            (fun c => stageHalt k c = Bool.true) := by simp
        have hvalid : is_valid_code m = Bool.true := by
          have := hb
          simp only [stageHalt, Bool.and_eq_true] at this
          exact this.1.1
        have hle : bitsLen_code m ≤ 4 * k + 2 := by
          have := bitsLen_code_le m hvalid
          omega
        rw [if_pos rfl, Finset.sum_insert hnotmem]
        simp only [omegaPartial, hb, cond_true]
        push_cast
        rw [ihm, mul_add, two_pow_mul_inv_pow hle]
        ring

theorem omegaApprox_eq_div (k : ℕ) :
    omegaApprox k = (omegaNum k : ℝ) / 2 ^ (4 * k + 2) := by
  have h := omegaPartial_eq_sum k (k + 1) le_rfl
  rw [omegaNum, h, omegaApprox, stageCodes]
  field_simp

------------------------------------------------------------------------
-- The stage approximations converge to `Ω` from below
------------------------------------------------------------------------

/-- The halting weight, as a function on all terms. -/
def haltWeight : Lambda → ℝ :=
  Set.indicator {t : Lambda | Halts t} (fun t => ((2 : ℝ)⁻¹) ^ (bits t).length)

theorem haltWeight_nonneg (t : Lambda) : 0 ≤ haltWeight t :=
  Set.indicator_nonneg (fun _ _ => by positivity) t

theorem haltWeight_of_halts {t : Lambda} (h : Halts t) :
    haltWeight t = ((2 : ℝ)⁻¹) ^ (bits t).length :=
  Set.indicator_of_mem (show t ∈ {t : Lambda | Halts t} from h) _

theorem haltWeight_of_not_halts {t : Lambda} (h : ¬ Halts t) : haltWeight t = 0 :=
  Set.indicator_of_notMem (show t ∉ {t : Lambda | Halts t} from h) _

theorem summable_haltWeight : Summable haltWeight :=
  summable_subtype_iff_indicator.1 summable_haltingWeight

theorem tsum_haltWeight : ∑' t : Lambda, haltWeight t = chaitinOmega :=
  (tsum_subtype {t : Lambda | Halts t} (fun t => ((2 : ℝ)⁻¹) ^ (bits t).length)).symm

open Classical in
/-- The terms counted at stage `k`. -/
def stageTerms (k : ℕ) : Finset Lambda := (stageCodes k).image decodeD

theorem valid_of_mem_stageCodes {k c : ℕ} (hc : c ∈ stageCodes k) :
    is_valid_code c = Bool.true := by
  have h := (mem_stageCodes.1 hc).2
  simp only [stageHalt, Bool.and_eq_true] at h
  exact h.1.1

theorem mem_stageTerms {k : ℕ} {t : Lambda} :
    t ∈ stageTerms k ↔ Lambda.encode t ∈ stageCodes k := by
  classical
  constructor
  · intro h
    rw [stageTerms, Finset.mem_image] at h
    obtain ⟨c, hc, hct⟩ := h
    rw [← hct, encode_decodeD (valid_of_mem_stageCodes hc)]
    exact hc
  · intro h
    rw [stageTerms, Finset.mem_image]
    exact ⟨Lambda.encode t, h, by simp⟩

theorem halts_of_mem_stageTerms {k : ℕ} {t : Lambda} (h : t ∈ stageTerms k) : Halts t := by
  have h2 := (mem_stageCodes.1 (mem_stageTerms.1 h)).2
  simp only [stageHalt, Bool.and_eq_true] at h2
  obtain ⟨⟨-, hcl⟩, hhb⟩ := h2
  refine ⟨(isClosed_code_correct t).1 hcl, ?_⟩
  exact (hasNormalForm_iff_exists_normal_iterate t).2 ⟨k, (haltsBy_code_correct t k).1 hhb⟩

theorem sum_stageTerms (k : ℕ) : ∑ t ∈ stageTerms k, haltWeight t = omegaApprox k := by
  classical
  have hinj : Set.InjOn decodeD ↑(stageCodes k) := by
    intro c hc c' hc' hcc
    rw [← encode_decodeD (valid_of_mem_stageCodes hc),
      ← encode_decodeD (valid_of_mem_stageCodes hc'), hcc]
  rw [stageTerms, omegaApprox, Finset.sum_image hinj]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  have hv := valid_of_mem_stageCodes hc
  have hhalts : Halts (decodeD c) :=
    halts_of_mem_stageTerms (mem_stageTerms.2 (by rw [encode_decodeD hv]; exact hc))
  rw [haltWeight_of_halts hhalts, ← bitsLen_code_correct, encode_decodeD hv]

theorem omegaApprox_le (k : ℕ) : omegaApprox k ≤ chaitinOmega := by
  rw [← sum_stageTerms k, ← tsum_haltWeight]
  exact summable_haltWeight.sum_le_tsum _ (fun i _ => haltWeight_nonneg i)

/-- A halting program that has *not* been found at stage `k` still contributes its own weight. -/
theorem omegaApprox_add_le {k : ℕ} {t : Lambda} (ht : Halts t) (hnot : t ∉ stageTerms k) :
    omegaApprox k + ((2 : ℝ)⁻¹) ^ (bits t).length ≤ chaitinOmega := by
  classical
  have hsum : ∑ u ∈ insert t (stageTerms k), haltWeight u
      = omegaApprox k + ((2 : ℝ)⁻¹) ^ (bits t).length := by
    rw [Finset.sum_insert hnot, sum_stageTerms, haltWeight_of_halts ht]
    ring
  rw [← hsum, ← tsum_haltWeight]
  exact summable_haltWeight.sum_le_tsum _ (fun i _ => haltWeight_nonneg i)

/-- The stage approximations get arbitrarily close to `Ω`. -/
theorem exists_omegaApprox_gt {x : ℝ} (hx : x < chaitinOmega) : ∃ k, x < omegaApprox k := by
  classical
  have hs : HasSum haltWeight chaitinOmega := by
    rw [← tsum_haltWeight]
    exact summable_haltWeight.hasSum
  have hev : ∀ᶠ A in (Filter.atTop : Filter (Finset Lambda)), x < ∑ u ∈ A, haltWeight u :=
    (tendsto_order.1 hs).1 x hx
  obtain ⟨A, hA⟩ := hev.exists
  refine ⟨A.sup (fun t => max (Lambda.encode t) (haltTime t)), ?_⟩
  set k := A.sup (fun t => max (Lambda.encode t) (haltTime t)) with hk
  have hsub : A.filter (fun t => Halts t) ⊆ stageTerms k := by
    intro t htmem
    rw [Finset.mem_filter] at htmem
    obtain ⟨hAmem, hht⟩ := htmem
    have hb : max (Lambda.encode t) (haltTime t) ≤ k := by
      rw [hk]
      exact Finset.le_sup (f := fun t => max (Lambda.encode t) (haltTime t)) hAmem
    refine mem_stageTerms.2 (mem_stageCodes.2 ⟨by omega, ?_⟩)
    simp only [stageHalt, Bool.and_eq_true]
    refine ⟨⟨is_valid_code_encode t, (isClosed_code_correct t).2 hht.1⟩, ?_⟩
    rw [haltsBy_code_correct]
    have hnorm := is_normal_nstep_haltTime hht.2
    rw [nstep_iterate_stable hnorm (by omega)]
    exact hnorm
  have h1 : ∑ u ∈ A.filter (fun t => Halts t), haltWeight u = ∑ u ∈ A, haltWeight u := by
    refine Finset.sum_filter_of_ne (fun u _ hne => ?_)
    by_contra hcon
    exact hne (haltWeight_of_not_halts hcon)
  have h2 : ∑ u ∈ A.filter (fun t => Halts t), haltWeight u ≤ ∑ u ∈ stageTerms k, haltWeight u :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => haltWeight_nonneg i)
  rw [sum_stageTerms] at h2
  rw [← h1] at hA
  linarith

------------------------------------------------------------------------
-- Computable reals
------------------------------------------------------------------------

/-- A real number is *computable* when some computable function produces dyadic rationals
`f n / 2 ^ n` approximating it to within `2 ^ (-n)`. -/
def RealComputable (x : ℝ) : Prop :=
  ∃ f : ℕ → ℤ, Computable f ∧ ∀ n : ℕ, |x - (f n : ℝ) / 2 ^ n| ≤ 1 / 2 ^ n

/-- For a positive real, the approximations may be taken natural. -/
theorem exists_nat_approx {x : ℝ} (hx : 0 < x) (h : RealComputable x) :
    ∃ g : ℕ → ℕ, Computable g ∧ ∀ n : ℕ, |x - (g n : ℝ) / 2 ^ n| ≤ 1 / 2 ^ n := by
  obtain ⟨f, hf, hfa⟩ := h
  refine ⟨fun n => (f n).toNat, primrec_int_toNat.to_comp.comp hf, fun n => ?_⟩
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hnn : 0 ≤ f n := by
    by_contra hcon
    push Not at hcon
    have hle : (f n : ℝ) + 1 ≤ 0 := by
      have h1 : f n ≤ -1 := by omega
      have h2 : (f n : ℝ) ≤ -1 := by exact_mod_cast h1
      linarith
    have h2' := (abs_le.1 (hfa n)).2
    have hmul : (x - (f n : ℝ) / 2 ^ n) * 2 ^ n ≤ (1 / 2 ^ n) * 2 ^ n :=
      mul_le_mul_of_nonneg_right h2' hp.le
    have hexp : (x - (f n : ℝ) / 2 ^ n) * 2 ^ n = x * 2 ^ n - (f n : ℝ) := by
      field_simp
    have hone : (1 / 2 ^ n : ℝ) * 2 ^ n = 1 := by field_simp
    rw [hexp, hone] at hmul
    nlinarith
  have hz : ((f n).toNat : ℤ) = f n := Int.toNat_of_nonneg hnn
  have hcast : (((f n).toNat : ℕ) : ℝ) = (f n : ℝ) := by exact_mod_cast hz
  rw [hcast]
  exact hfa n

------------------------------------------------------------------------
-- The halting decider built from an approximation of `Ω`
------------------------------------------------------------------------

theorem is_valid_code_of_codeHasNormalForm {c : ℕ} (h : CodeHasNormalForm c) :
    is_valid_code c = Bool.true := by
  obtain ⟨t, ht, -⟩ := (codeHasNormalForm_iff c).1 h
  rw [← ht]
  simp

theorem codeHasNormalForm_iff_decodeD {c : ℕ} (hc : is_valid_code c = Bool.true) :
    CodeHasNormalForm c ↔ HasNormalForm (decodeD c) := by
  rw [codeHasNormalForm_iff]
  constructor
  · rintro ⟨t, ht, hnf⟩
    rw [← ht]
    simpa using hnf
  · intro h
    exact ⟨decodeD c, encode_decodeD hc, h⟩

section Decider

variable (g : ℕ → ℕ)

/-- The precision index used for the code `c`: two more than the number of bits of the closed
term attached to `c`. -/
def precIdx (c : ℕ) : ℕ := bitsLen_code (closure_code c) + 2

theorem precIdx_primrec : Primrec precIdx :=
  Primrec.nat_add.comp (bitsLen_code_primrec.comp closure_code_primrec) (Primrec.const 2)

/-- The stage test: `Ω_k` has passed the estimate `(g n - 3) / 2 ^ n`. -/
def omegaTest (c k : ℕ) : Bool :=
  decide (g (precIdx c) * 2 ^ (4 * k + 2) <
    omegaNum k * 2 ^ (precIdx c) + 3 * 2 ^ (4 * k + 2))

theorem omegaTest_iff (c k : ℕ) :
    omegaTest g c k = Bool.true ↔
      (g (precIdx c) : ℝ) / 2 ^ (precIdx c) - 3 / 2 ^ (precIdx c) < omegaApprox k := by
  rw [omegaTest, decide_eq_true_iff, omegaApprox_eq_div, div_sub_div_same]
  have hp : (0 : ℝ) < 2 ^ (precIdx c) := by positivity
  have hq : (0 : ℝ) < 2 ^ (4 * k + 2) := by positivity
  rw [div_lt_div_iff₀ hp hq]
  constructor
  · intro h
    have h' : ((g (precIdx c) : ℝ)) * 2 ^ (4 * k + 2) <
        (omegaNum k : ℝ) * 2 ^ (precIdx c) + 3 * 2 ^ (4 * k + 2) := by exact_mod_cast h
    linarith
  · intro h
    have h' : ((g (precIdx c) : ℝ)) * 2 ^ (4 * k + 2) <
        (omegaNum k : ℝ) * 2 ^ (precIdx c) + 3 * 2 ^ (4 * k + 2) := by linarith
    exact_mod_cast h'

theorem omegaTest_primrec (hg : Computable g) : Computable₂ (omegaTest g) := by
  have hA : Computable (fun p : ℕ × ℕ => 2 ^ (4 * p.2 + 2)) :=
    (primrec_two_pow.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) Primrec.snd) (Primrec.const 2))).to_comp
  have hB : Computable (fun p : ℕ × ℕ => 2 ^ precIdx p.1) :=
    (primrec_two_pow.comp (precIdx_primrec.comp Primrec.fst)).to_comp
  have hG : Computable (fun p : ℕ × ℕ => g (precIdx p.1)) :=
    hg.comp (precIdx_primrec.comp Primrec.fst).to_comp
  have hN : Computable (fun p : ℕ × ℕ => omegaNum p.2) :=
    (omegaNum_primrec.comp Primrec.snd).to_comp
  have hlhs : Computable (fun p : ℕ × ℕ => g (precIdx p.1) * 2 ^ (4 * p.2 + 2)) :=
    (Primrec₂.to_comp Primrec.nat_mul).comp hG hA
  have hrhs : Computable (fun p : ℕ × ℕ =>
      omegaNum p.2 * 2 ^ precIdx p.1 + 3 * 2 ^ (4 * p.2 + 2)) :=
    (Primrec₂.to_comp Primrec.nat_add).comp ((Primrec₂.to_comp Primrec.nat_mul).comp hN hB)
      ((Primrec₂.to_comp Primrec.nat_mul).comp (Computable.const 3) hA)
  obtain ⟨_inst, hlt⟩ := (Primrec.nat_lt : PrimrecRel (fun a b : ℕ => a < b))
  exact ((hlt.to_comp).comp (Computable.pair hlhs hrhs)).of_eq (fun p => by simp [omegaTest])

/-- The partial halting decider driven by the approximation `g` of `Ω`. -/
def haltRun (c : ℕ) : Part Bool :=
  (Nat.rfind fun k => Part.some (cond (is_valid_code c) (omegaTest g c k) Bool.true)).map
    (fun k => cond (is_valid_code c)
      (decide (closure_code c ≤ k) && haltsBy_code (closure_code c) k) Bool.false)

theorem haltRun_partrec (hg : Computable g) : Partrec (haltRun g) := by
  have hv : Computable (fun c : ℕ => is_valid_code c) := Lambda.is_valid_code_primrec.to_comp
  have hstop : Computable₂ (fun (c : ℕ) (k : ℕ) =>
      cond (is_valid_code c) (omegaTest g c k) Bool.true) :=
    Computable.cond (hv.comp Computable.fst) (omegaTest_primrec g hg) (Computable.const Bool.true)
  have hval : Computable₂ (fun (c : ℕ) (k : ℕ) =>
      cond (is_valid_code c)
        (decide (closure_code c ≤ k) && haltsBy_code (closure_code c) k) Bool.false) := by
    refine Computable.cond (hv.comp Computable.fst) ?_ (Computable.const Bool.false)
    have hcl : Primrec (fun p : ℕ × ℕ => closure_code p.1) :=
      closure_code_primrec.comp Primrec.fst
    have h1 : Primrec (fun p : ℕ × ℕ => decide (closure_code p.1 ≤ p.2)) := by
      obtain ⟨_inst, hle⟩ := (Primrec.nat_le : PrimrecRel (fun a b : ℕ => a ≤ b))
      exact (hle.comp (Primrec.pair hcl Primrec.snd)).of_eq (fun p => by congr)
    have h2 : Primrec (fun p : ℕ × ℕ => haltsBy_code (closure_code p.1) p.2) :=
      haltsBy_code_primrec.comp hcl Primrec.snd
    exact (Primrec.and.comp h1 h2).to_comp
  have hsearch : Partrec (fun c : ℕ =>
      Nat.rfind fun k => Part.some (cond (is_valid_code c) (omegaTest g c k) Bool.true)) :=
    Partrec.rfind hstop
  exact Partrec.map hsearch hval

open Classical in
/-- The total halting decider. -/
def haltDecide (c : ℕ) : Bool :=
  if h : (haltRun g c).Dom then (haltRun g c).get h else Bool.false

variable {g}

theorem haltRun_of_invalid {c : ℕ} (h : is_valid_code c = Bool.false) :
    haltRun g c = Part.some Bool.false := by
  have hrf : (Nat.rfind fun _ : ℕ => (Part.some Bool.true : Part Bool)) = Part.some 0 :=
    Part.eq_some_iff.2 (Nat.mem_rfind.2 ⟨Part.mem_some _, fun {m} hm => absurd hm (by omega)⟩)
  simp only [haltRun, h, cond_false, hrf, Part.map_some]

/-- The search terminates: some stage passes the estimate. -/
theorem exists_omegaTest (hg : ∀ n : ℕ, |chaitinOmega - (g n : ℝ) / 2 ^ n| ≤ 1 / 2 ^ n) (c : ℕ) :
    ∃ k, omegaTest g c k = Bool.true := by
  have h2 := abs_le.1 (hg (precIdx c))
  have h3 : (0 : ℝ) < 3 / 2 ^ (precIdx c) - 1 / 2 ^ (precIdx c) := by
    have h4 : (3 : ℝ) - 1 = 2 := by norm_num
    rw [div_sub_div_same, h4]
    positivity
  have hlt : (g (precIdx c) : ℝ) / 2 ^ (precIdx c) - 3 / 2 ^ (precIdx c) < chaitinOmega := by
    linarith [h2.1]
  obtain ⟨k, hk⟩ := exists_omegaApprox_gt hlt
  exact ⟨k, (omegaTest_iff g c k).2 hk⟩

/-- At a stage that has passed the estimate, every halting program of the relevant length has
already been found. -/
theorem halts_iff_of_omegaTest (hg : ∀ n : ℕ, |chaitinOmega - (g n : ℝ) / 2 ^ n| ≤ 1 / 2 ^ n)
    {c k : ℕ} (hc : is_valid_code c = Bool.true) (hk : omegaTest g c k = Bool.true) :
    HasNormalForm (decodeD c) ↔
      (closure_code c ≤ k ∧ haltsBy_code (closure_code c) k = Bool.true) := by
  have hcu : closure_code c = Lambda.encode (closeTerm (decodeD c)) := by
    conv_lhs => rw [← encode_decodeD hc]
    rw [closure_code_correct]
    rfl
  set u := closeTerm (decodeD c) with hudef
  have hclosed : IsClosed u := isClosed_closeTerm _
  have hnfu : HasNormalForm u ↔ HasNormalForm (decodeD c) := hasNormalForm_closeTerm _
  constructor
  · intro hnf
    have hhalts : Halts u := ⟨hclosed, hnfu.2 hnf⟩
    by_contra hcon
    have hnotmem : u ∉ stageTerms k := by
      intro hmem
      have hmc := mem_stageTerms.1 hmem
      rw [← hcu] at hmc
      obtain ⟨hle, hsh⟩ := mem_stageCodes.1 hmc
      simp only [stageHalt, Bool.and_eq_true] at hsh
      exact hcon ⟨hle, hsh.2⟩
    have hineq := omegaApprox_add_le hhalts hnotmem
    have hn : precIdx c = (bits u).length + 2 := by
      rw [precIdx, hcu, bitsLen_code_correct]
    have h1 : (g (precIdx c) : ℝ) / 2 ^ (precIdx c) - 3 / 2 ^ (precIdx c) < omegaApprox k :=
      (omegaTest_iff g c k).1 hk
    have h2 := abs_le.1 (hg (precIdx c))
    have hinv : ((2 : ℝ)⁻¹) ^ (bits u).length = 1 / 2 ^ (bits u).length := by
      rw [inv_pow, one_div]
    have hsplit : (2 : ℝ) ^ (precIdx c) = 4 * 2 ^ (bits u).length := by
      rw [hn, pow_add]
      ring
    rw [hinv] at hineq
    rw [hsplit] at h1
    have h2' := h2.2
    rw [hsplit] at h2'
    have hkey : (1 : ℝ) / (4 * 2 ^ (bits u).length) + 3 / (4 * 2 ^ (bits u).length)
        = 1 / 2 ^ (bits u).length := by
      have hx : (0 : ℝ) < 2 ^ (bits u).length := by positivity
      field_simp
      ring
    linarith
  · rintro ⟨-, hhb⟩
    rw [hcu] at hhb
    exact hnfu.1 ((hasNormalForm_iff_exists_normal_iterate u).2
      ⟨k, (haltsBy_code_correct u k).1 hhb⟩)

theorem haltRun_spec (hg : ∀ n : ℕ, |chaitinOmega - (g n : ℝ) / 2 ^ n| ≤ 1 / 2 ^ n) (c : ℕ) :
    ∃ b, haltRun g c = Part.some b ∧ (CodeHasNormalForm c ↔ b = Bool.true) := by
  rcases hv : is_valid_code c with _ | _
  · refine ⟨Bool.false, haltRun_of_invalid hv, ?_⟩
    constructor
    · intro h
      rw [is_valid_code_of_codeHasNormalForm h] at hv
      exact Bool.noConfusion hv
    · intro h
      exact Bool.noConfusion h
  · obtain ⟨m, hm⟩ := exists_omegaTest hg c
    set q : ℕ → Bool := fun k => cond (is_valid_code c) (omegaTest g c k) Bool.true with hqdef
    have hpm : q m = Bool.true := by
      simp only [hqdef, hv, cond_true]
      exact hm
    obtain ⟨k, hk, -⟩ := Nat.rfind_min' hpm
    have hcoe : ((q : ℕ →. Bool)) = fun k => Part.some (q k) := rfl
    rw [hcoe] at hk
    have hqk : q k = Bool.true := (Part.mem_some_iff.1 (Nat.rfind_spec hk)).symm
    have hspec : omegaTest g c k = Bool.true := by
      rw [hqdef] at hqk
      simpa [hv] using hqk
    have hrf : (Nat.rfind fun k => Part.some (q k)) = Part.some k :=
      Part.eq_some_iff.2 hk
    refine ⟨decide (closure_code c ≤ k) && haltsBy_code (closure_code c) k, ?_, ?_⟩
    · simp only [haltRun, hqdef] at hrf ⊢
      rw [hrf]
      simp only [Part.map_some, hv, cond_true]
    · rw [codeHasNormalForm_iff_decodeD hv,
        halts_iff_of_omegaTest hg hv hspec, Bool.and_eq_true, decide_eq_true_eq]

theorem haltRun_eq (hg : ∀ n : ℕ, |chaitinOmega - (g n : ℝ) / 2 ^ n| ≤ 1 / 2 ^ n) (c : ℕ) :
    haltRun g c = Part.some (haltDecide g c) := by
  classical
  obtain ⟨b, hb, -⟩ := haltRun_spec hg c
  have hdom : (haltRun g c).Dom := by rw [hb]; trivial
  rw [hb, haltDecide, dif_pos hdom]
  congr 1
  exact (Part.get_eq_iff_eq_some.2 hb).symm

theorem haltDecide_iff (hg : ∀ n : ℕ, |chaitinOmega - (g n : ℝ) / 2 ^ n| ≤ 1 / 2 ^ n) (c : ℕ) :
    CodeHasNormalForm c ↔ haltDecide g c = Bool.true := by
  obtain ⟨b, hb, hiff⟩ := haltRun_spec hg c
  have heq := haltRun_eq hg c
  rw [hb, Part.some_inj] at heq
  rw [← heq]
  exact hiff

theorem computable_haltDecide (hgc : Computable g)
    (hg : ∀ n : ℕ, |chaitinOmega - (g n : ℝ) / 2 ^ n| ≤ 1 / 2 ^ n) :
    Computable (haltDecide g) :=
  Partrec.of_eq (haltRun_partrec g hgc) (haltRun_eq hg)

end Decider

------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------

/-- **Chaitin's constant is not computable.** -/
theorem not_realComputable_chaitinOmega : ¬ RealComputable chaitinOmega := by
  intro h
  obtain ⟨g, hgc, hg⟩ := exists_nat_approx chaitinOmega_pos h
  refine not_computablePred_codeHasNormalForm ?_
  refine ComputablePred.computable_iff.2 ⟨haltDecide g, computable_haltDecide hgc hg, ?_⟩
  funext c
  simpa using propext (haltDecide_iff hg c)

end Lambda

end
