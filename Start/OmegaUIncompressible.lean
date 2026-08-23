/-
# Chaitin incompressibility of `Ω` for the universal prefix machine

`Start/KCMachine.lean` builds a universal prefix machine `KC.U` by Kraft–Chaitin allocation and
its halting probability `KC.Omega`.  This file defines the binary expansion `KC.omegaSeq` of
`KC.Omega` and proves the classical incompressibility theorem

* `KC.exists_const_le_KU_omegaPrefix : ∃ c, ∀ n, n ≤ KU ⌜Ω ↾ n⌝ + c`.

The argument is the usual "dodging" one.  From the first `n` bits of `Ω`, read as the number
`a = omegaBits n`, one searches for a stage `T` of the allocation at which the allocated weight
already exceeds `(a - 1) / 2 ^ n`.  Since `Ω < (a + 1) / 2 ^ n`, at most `2 / 2 ^ n` weight is
left, so every slot allocated from stage `T` on has length at least `n`.  Hence every number of
complexity below `n` is the output of a slot allocated before `T`, and `KC.dodgeMax n T + 1` is
not among them: it has complexity at least `n`, while it is computed from the first `n` bits
of `Ω`.
-/

import Start.KCMachine
import Start.KCComputable
import Start.MartinLof

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace KC

------------------------------------------------------------------------
-- The bits of `Ω`
------------------------------------------------------------------------

/-- The first `n` binary digits of `Ω`, read as a natural number. -/
noncomputable def omegaBits (n : ℕ) : ℕ := ⌊Omega * 2 ^ n⌋₊

/-- The binary expansion of `Ω` as an element of Cantor space. -/
noncomputable def omegaSeq (n : ℕ) : Bool := decide (omegaBits (n + 1) % 2 = 1)

theorem omegaBits_le (n : ℕ) : (omegaBits n : ℝ) / 2 ^ n ≤ Omega := by
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have h : (omegaBits n : ℝ) ≤ Omega * 2 ^ n :=
    Nat.floor_le (mul_nonneg Omega_pos.le (by positivity))
  rw [div_le_iff₀ hpos]
  exact h

theorem lt_omegaBits_succ (n : ℕ) : Omega < ((omegaBits n : ℝ) + 1) / 2 ^ n := by
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have h : Omega * 2 ^ n < (omegaBits n : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [lt_div_iff₀ hpos]
  exact h

theorem omegaBits_lt (n : ℕ) : omegaBits n < 2 ^ n := by
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hlt : Omega * 2 ^ n < ((2 ^ n : ℕ) : ℝ) := by
    push_cast
    have : Omega ≤ 1 / 2 := Omega_le_half
    nlinarith
  exact (Nat.floor_lt (mul_nonneg Omega_pos.le (by positivity))).2 hlt

theorem omegaBits_mono : Monotone omegaBits := by
  intro m n h
  refine Nat.floor_mono ?_
  have h2 : (2 : ℝ) ^ m ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h
  have hΩ : 0 ≤ Omega := le_of_lt Omega_pos
  exact mul_le_mul_of_nonneg_left h2 hΩ

theorem omegaBits_div_two (n : ℕ) : omegaBits (n + 1) / 2 = omegaBits n := by
  have h : Omega * 2 ^ (n + 1) = (Omega * 2 ^ n) * ((2 : ℕ) : ℝ) := by push_cast; ring
  unfold omegaBits
  rw [h, Nat.mul_cast_floor_div_cancel (by norm_num)]

/-- The first `n` bits of `Ω`, as a bit string, are the binary expansion of `omegaBits n`. -/
theorem prefixList_omegaSeq (n : ℕ) :
    Lambda.prefixList omegaSeq n = BitStr.ofNat n (omegaBits n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hpre : Lambda.prefixList omegaSeq (n + 1)
          = Lambda.prefixList omegaSeq n ++ [omegaSeq n] := by
        simp [Lambda.prefixList, List.range_succ]
      rw [hpre, ih, BitStr.ofNat_succ, omegaBits_div_two]
      rfl

theorem toNat_prefixList_omegaSeq (n : ℕ) :
    BitStr.toNat (Lambda.prefixList omegaSeq n) = omegaBits n := by
  rw [prefixList_omegaSeq, BitStr.toNat_ofNat, Nat.mod_eq_of_lt (omegaBits_lt n)]

------------------------------------------------------------------------
-- Approximating `Ω` from below
------------------------------------------------------------------------

/-- One step of the approximation of `Ω`. -/
def omegaApproxStep (q : ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  match slot q.1 with
  | none => q.2
  | some (_, L, _) => addPow q.2 L

/-- The allocated weight after `T` steps, as a dyadic pair. -/
def omegaApprox (T : ℕ) : ℕ × ℕ :=
  Nat.rec (motive := fun _ => ℕ × ℕ) (0, 0) (fun k IH => omegaApproxStep (k, IH)) T

theorem omegaApprox_succ (T : ℕ) : omegaApprox (T + 1) = omegaApproxStep (T, omegaApprox T) := rfl

theorem dyadic_omegaApprox (T : ℕ) :
    dyadic (omegaApprox T) = ∑ t ∈ Finset.range T, omegaW t := by
  induction T with
  | zero => simp [omegaApprox, dyadic]
  | succ T ih =>
      rw [Finset.sum_range_succ, ← ih, omegaApprox_succ, omegaApproxStep]
      cases h : slot T with
      | none => simp [omegaW, h]
      | some p =>
          obtain ⟨m, L, x⟩ := p
          simp [omegaW, h, dyadic_addPow]

/-- The test used to search for a stage at which the remaining weight of `Ω` is small. -/
def stageOk (n a T : ℕ) : Bool :=
  decide ((a - 1) * 2 ^ (omegaApprox T).2 < (omegaApprox T).1 * 2 ^ n)

theorem stageOk_iff {n a : ℕ} (ha : 1 ≤ a) (T : ℕ) :
    stageOk n a T = true ↔ ((a : ℝ) - 1) / 2 ^ n < ∑ t ∈ Finset.range T, omegaW t := by
  rw [← dyadic_omegaApprox]
  have h1 : (0 : ℝ) < 2 ^ n := by positivity
  have h2 : (0 : ℝ) < 2 ^ (omegaApprox T).2 := by positivity
  have hcast : (((a - 1 : ℕ)) : ℝ) = (a : ℝ) - 1 := by
    have := Nat.cast_sub (R := ℝ) ha
    simpa using this
  unfold stageOk dyadic
  rw [decide_eq_true_eq, div_lt_div_iff₀ h1 h2, ← hcast]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

theorem exists_stageOk {n : ℕ} (hn : 1 ≤ omegaBits n) : ∃ T, stageOk n (omegaBits n) T = true := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ T, ∑ t ∈ Finset.range T, omegaW t ≤ ((omegaBits n : ℝ) - 1) / 2 ^ n := by
    intro T
    by_contra hlt
    exact hcon T ((stageOk_iff hn T).2 (lt_of_not_ge hlt))
  have hΩ : Omega ≤ ((omegaBits n : ℝ) - 1) / 2 ^ n :=
    Real.tsum_le_of_sum_range_le omegaW_nonneg hle
  have hsub : ((omegaBits n : ℝ) - 1) / 2 ^ n = (omegaBits n : ℝ) / 2 ^ n - 1 / 2 ^ n := by ring
  have hpos : (0 : ℝ) < 1 / 2 ^ n := by positivity
  have := omegaBits_le n
  linarith

/-- After a stage witnessing `stageOk`, every allocated slot is long. -/
theorem le_length_of_stageOk {n T t m L x : ℕ} (hn : 1 ≤ omegaBits n)
    (hT : stageOk n (omegaBits n) T = true) (ht : T ≤ t) (hs : slot t = some (m, L, x)) :
    n ≤ L := by
  by_contra hcon
  push Not at hcon
  have hw : omegaW t = wt L := by unfold omegaW; rw [hs]
  have hnotmem : t ∉ Finset.range T := by simp; omega
  have hsum := summable_omegaW.sum_le_tsum (insert t (Finset.range T))
    (fun i _ => omegaW_nonneg i)
  rw [Finset.sum_insert hnotmem, hw] at hsum
  have hstage := (stageOk_iff hn T).1 hT
  have hup := lt_omegaBits_succ n
  have hle : (2 : ℝ) / 2 ^ n ≤ wt L := by
    rw [wt_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hL1 : L + 1 ≤ n := by omega
    have h2 : (2 : ℝ) ^ (L + 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hL1
    rw [one_mul]
    calc (2 : ℝ) * 2 ^ L = 2 ^ (L + 1) := by ring
      _ ≤ 2 ^ n := h2
  have hid : (2 : ℝ) / 2 ^ n + ((omegaBits n : ℝ) - 1) / 2 ^ n = ((omegaBits n : ℝ) + 1) / 2 ^ n :=
    by ring
  have hΩ : ∑' t : ℕ, omegaW t = Omega := rfl
  rw [hΩ] at hsum
  linarith [hsum, hstage, hup, hle, hid]

------------------------------------------------------------------------
-- Dodging all short programs
------------------------------------------------------------------------

/-- One step of the search for a number that no short program produces. -/
def dodgeStep (n : ℕ) (q : ℕ × ℕ) : ℕ :=
  match slot q.1 with
  | none => q.2
  | some (_, L, y) => if L < n then max y q.2 else q.2

/-- The largest output of a slot of length below `n` allocated before stage `T`. -/
def dodgeMax (n T : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k IH => dodgeStep n (k, IH)) T

theorem dodgeMax_succ (n T : ℕ) : dodgeMax n (T + 1) = dodgeStep n (T, dodgeMax n T) := rfl

theorem dodgeMax_le_succ (n T : ℕ) : dodgeMax n T ≤ dodgeMax n (T + 1) := by
  rw [dodgeMax_succ, dodgeStep]
  cases h : slot T with
  | none => exact le_rfl
  | some p =>
      obtain ⟨m, L, y⟩ := p
      by_cases hL : L < n <;> simp [hL]

theorem le_dodgeMax {n T t m L x : ℕ} (ht : t < T) (hs : slot t = some (m, L, x)) (hL : L < n) :
    x ≤ dodgeMax n T := by
  induction T with
  | zero => omega
  | succ T ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h | rfl
      · exact le_trans (ih h) (dodgeMax_le_succ n T)
      · rw [dodgeMax_succ, dodgeStep, hs]
        simp [hL]

/-- From the first `n` bits of `Ω` one computes a number that no short program produces. -/
def dodge (p : ℕ) : Part ℕ :=
  (Nat.rfind fun T => (Part.some (stageOk p.unpair.1 p.unpair.2 T))).map fun T =>
    dodgeMax p.unpair.1 T + 1

theorem exists_mem_dodge {n : ℕ} (hn : 1 ≤ omegaBits n) :
    ∃ y, y ∈ dodge (Nat.pair n (omegaBits n)) ∧ n ≤ KU y := by
  obtain ⟨T, hT⟩ := exists_stageOk hn
  have hdom : (Nat.rfind fun T' =>
      (Part.some (stageOk (Nat.pair n (omegaBits n)).unpair.1
        (Nat.pair n (omegaBits n)).unpair.2 T'))).Dom := by
    refine Nat.rfind_dom.2 ⟨T, ?_, fun _ => trivial⟩
    simp [Nat.unpair_pair, hT]
  obtain ⟨T₀, hT₀⟩ := Part.dom_iff_mem.1 hdom
  refine ⟨dodgeMax n T₀ + 1, ?_, ?_⟩
  · have := Part.mem_map (fun T => dodgeMax (Nat.pair n (omegaBits n)).unpair.1 T + 1) hT₀
    simpa [dodge, Nat.unpair_pair] using this
  · have hstage : stageOk n (omegaBits n) T₀ = true := by
      have := Nat.rfind_spec hT₀
      simpa [Nat.unpair_pair] using this
    by_contra hcon
    push Not at hcon
    obtain ⟨σ, hlen, hmem⟩ := KU_spec (dodgeMax n T₀ + 1)
    obtain ⟨t, hslot⟩ := mem_U_iff.1 hmem
    have hσn : σ.length < n := by omega
    rcases Nat.lt_or_ge t T₀ with hlt | hle
    · have := le_dodgeMax hlt hslot hσn
      omega
    · have := le_length_of_stageOk hn hstage hle hslot
      omega

------------------------------------------------------------------------
-- Computability of the dodge
------------------------------------------------------------------------

theorem primrec_omegaApproxStep : Primrec omegaApproxStep := by
  have hslot : Primrec fun z : ℕ × (ℕ × ℕ) => slot z.1 := slot_primrec.comp Primrec.fst
  have hih : Primrec fun z : ℕ × (ℕ × ℕ) => z.2 := Primrec.snd
  have hg : Primrec₂ fun (z : ℕ × (ℕ × ℕ)) (p : ℕ × ℕ × ℕ) => addPow z.2 p.2.1 :=
    primrec_addPow.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  refine (Primrec.option_casesOn hslot hih hg).of_eq fun z => ?_
  unfold omegaApproxStep
  cases slot z.1 with
  | none => rfl
  | some p => obtain ⟨m, L, x⟩ := p; rfl

theorem primrec_omegaApprox : Primrec omegaApprox :=
  Primrec.nat_rec' Primrec.id (Primrec.const ((0, 0) : ℕ × ℕ))
    (primrec_omegaApproxStep.comp Primrec.snd).to₂

theorem primrec_stageOk : Primrec fun q : ℕ × ℕ × ℕ => stageOk q.1 q.2.1 q.2.2 := by
  have hap : Primrec fun q : ℕ × ℕ × ℕ => omegaApprox q.2.2 :=
    primrec_omegaApprox.comp (Primrec.snd.comp Primrec.snd)
  have hlhs : Primrec fun q : ℕ × ℕ × ℕ => (q.2.1 - 1) * 2 ^ (omegaApprox q.2.2).2 :=
    Primrec.nat_mul.comp
      (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
      (primrec_two_pow.comp (Primrec.snd.comp hap))
  have hrhs : Primrec fun q : ℕ × ℕ × ℕ => (omegaApprox q.2.2).1 * 2 ^ q.1 :=
    Primrec.nat_mul.comp (Primrec.fst.comp hap) (primrec_two_pow.comp Primrec.fst)
  exact (Primrec.nat_lt.comp hlhs hrhs).decide.of_eq fun q => rfl

theorem primrec_dodgeStep : Primrec₂ dodgeStep := by
  have hslot : Primrec fun z : ℕ × (ℕ × ℕ) => slot z.2.1 :=
    slot_primrec.comp (Primrec.fst.comp Primrec.snd)
  have hih : Primrec fun z : ℕ × (ℕ × ℕ) => z.2.2 := Primrec.snd.comp Primrec.snd
  have hL : Primrec fun y : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ × ℕ) => y.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hy : Primrec fun y : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ × ℕ) => y.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hq2 : Primrec fun y : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ × ℕ) => y.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hn : Primrec fun y : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ × ℕ) => y.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hcond : PrimrecPred fun y : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ × ℕ) => y.2.2.1 < y.1.1 :=
    Primrec.nat_lt.comp hL hn
  have hg : Primrec₂ fun (z : ℕ × (ℕ × ℕ)) (p : ℕ × ℕ × ℕ) =>
      (if p.2.1 < z.1 then max p.2.2 z.2.2 else z.2.2 : ℕ) :=
    Primrec.ite hcond (Primrec.nat_max.comp hy hq2) hq2
  refine (Primrec.option_casesOn hslot hih hg).of_eq ?_
  rintro ⟨n, q⟩
  change _ = dodgeStep n q
  unfold dodgeStep
  cases slot q.1 with
  | none => rfl
  | some p => obtain ⟨m, L, y⟩ := p; rfl

theorem primrec_dodgeMax : Primrec₂ dodgeMax :=
  Primrec.nat_rec (Primrec.const 0) primrec_dodgeStep

theorem partrec_dodge : Partrec dodge := by
  have hpred : Computable₂ fun (p : ℕ) (T : ℕ) => stageOk p.unpair.1 p.unpair.2 T :=
    (primrec_stageOk.comp ((Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)).pair
      ((Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)).pair Primrec.snd))).to_comp
  have hrf : Partrec fun p : ℕ =>
      Nat.rfind fun T => (Part.some (stageOk p.unpair.1 p.unpair.2 T)) :=
    Partrec.rfind hpred.partrec₂
  have hmap : Computable₂ fun (p : ℕ) (T : ℕ) => dodgeMax p.unpair.1 T + 1 :=
    (Primrec.succ.comp (primrec_dodgeMax.comp
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)) Primrec.snd)).to_comp
  exact hrf.map hmap

/-- The dodge, read off a coded bit string rather than a coded pair. -/
def dodgeStr (z : ℕ) : Part ℕ :=
  dodge (Nat.pair ((Encodable.decode (α := List Bool) z).getD []).length
    (BitStr.toNat ((Encodable.decode (α := List Bool) z).getD [])))

theorem partrec_dodgeStr : Partrec dodgeStr := by
  have hdec : Primrec fun z : ℕ => (Encodable.decode (α := List Bool) z).getD [] :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const [])
  have hcomp : Computable fun z : ℕ =>
      Nat.pair ((Encodable.decode (α := List Bool) z).getD []).length
        (BitStr.toNat ((Encodable.decode (α := List Bool) z).getD [])) :=
    Primrec.to_comp (Primrec₂.natPair.comp (Primrec.list_length.comp hdec)
      (BitStr.primrec_toNat.comp hdec))
  exact partrec_dodge.comp hcomp

------------------------------------------------------------------------
-- The incompressibility theorem
------------------------------------------------------------------------

theorem exists_omegaBits_pos : ∃ n, 1 ≤ omegaBits n := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / Omega) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, ?_⟩
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have h1 : (1 : ℝ) ≤ Omega * 2 ^ n := by
    rw [div_lt_iff₀ Omega_pos] at hn
    nlinarith [Omega_pos]
  unfold omegaBits
  exact Nat.le_floor (by exact_mod_cast h1)

/-- **Chaitin incompressibility of `Ω`**: the first `n` bits of `Ω` need a program of `n - O(1)`
bits. -/
theorem exists_const_le_KU_omegaPrefix :
    ∃ c : ℕ, ∀ n : ℕ, n ≤ KU (Encodable.encode (Lambda.prefixList omegaSeq n)) + c := by
  obtain ⟨c₁, hc₁⟩ := exists_const_KU_comp partrec_dodgeStr
  obtain ⟨n₀, hn₀⟩ := exists_omegaBits_pos
  refine ⟨c₁ + n₀, fun n => ?_⟩
  rcases lt_or_ge n n₀ with hsmall | hbig
  · omega
  · have hn : 1 ≤ omegaBits n := le_trans hn₀ (omegaBits_mono hbig)
    obtain ⟨y, hy, hKU⟩ := exists_mem_dodge hn
    set z := Encodable.encode (Lambda.prefixList omegaSeq n) with hz
    have hdec : (Encodable.decode (α := List Bool) z).getD [] = Lambda.prefixList omegaSeq n := by
      rw [hz, Encodable.encodek]
      rfl
    have hy' : y ∈ dodgeStr z := by
      unfold dodgeStr
      rw [hdec, Lambda.prefixList_length, toNat_prefixList_omegaSeq]
      exact hy
    have := hc₁ z y hy'
    omega

end KC
