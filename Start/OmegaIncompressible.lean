/-
# Chaitin's incompressibility theorem for `Ω`

`Start/OmegaOracle.lean` shows that the first `n` bits of Chaitin's constant decide the halting
problem for all programs of at most `n - 2` bits.  This file draws the quantitative consequence
which is the heart of the algorithmic randomness of `Ω`:

  `Lambda.exists_const_le_kolmP_omegaPrefix :
      ∃ c, ∀ n, n ≤ kolmP (omegaPrefix n) + c`,

where `Lambda.omegaPrefix n = ⟨n, ⌊Ω · 2 ^ n⌋⟩` packages the first `n` bits of `Ω` together with
their number.  In words: **the first `n` bits of `Ω` cannot be described by a self-delimiting
program of fewer than `n - O(1)` bits.**

The proof is Chaitin's Berry-style argument.  From `omegaPrefix n` one partial recursive procedure
`Lambda.dodge` computes a number that no program of at most `n - 2` bits produces:

* the oracle search finds a stage `k` by which every program of at most `n - 2` bits that halts
  at all has already halted (`Lambda.StageOk`);
* only finitely many values are produced by codes below `Lambda.encBound n` within `k` leftmost
  steps (`Lambda.Forbidden`), so the least value avoiding all of them exists and, by construction,
  has no program of `≤ n - 2` bits.

Prefixing a shortest program for `omegaPrefix n` with a fixed realizer of `Lambda.dodge` costs
only a constant number of bits — this is where the *self-delimiting* coding is used — so a short
program for `omegaPrefix n` would give a short program for a number that has none.
-/

import Start.OmegaOracle
import Start.PlainVsPrefix

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

noncomputable section

------------------------------------------------------------------------
-- Bounded quantifiers with an arbitrary parameter
------------------------------------------------------------------------

section Bounded

variable {β : Type} [Primcodable β] {R : ℕ → β → Prop} {N : β → ℕ}

theorem primrecPred_exists_lt (hR : PrimrecRel R) (hN : Primrec N) :
    PrimrecPred fun b : β => ∃ a < N b, R a b :=
  ((PrimrecRel.exists_mem_list hR).comp (Primrec.list_range.comp hN) Primrec.id).of_eq
    fun b => by simp

theorem primrecPred_forall_lt (hR : PrimrecRel R) (hN : Primrec N) :
    PrimrecPred fun b : β => ∀ a < N b, R a b :=
  ((PrimrecRel.forall_mem_list hR).comp (Primrec.list_range.comp hN) Primrec.id).of_eq
    fun b => by simp

end Bounded

------------------------------------------------------------------------
-- The two tests
------------------------------------------------------------------------

/-- The first `n` bits of `Ω`, tagged with `n`. -/
def omegaPrefix (n : ℕ) : ℕ := Nat.pair n (omegaBits n)

/-- The stage test of `Start/OmegaUncomputable.lean`, with the oracle `Lambda.prefixOracle`
spelled out: at stage `j` the approximation `Ω_j` has passed the estimate provided by the first
`n` bits `a` of `Ω`. -/
def OTest (a n c j : ℕ) : Prop :=
  a / 2 ^ (n - precIdx c) * 2 ^ (4 * j + 2) <
    omegaNum j * 2 ^ precIdx c + 3 * 2 ^ (4 * j + 2)

instance (a n c j : ℕ) : Decidable (OTest a n c j) := by unfold OTest; infer_instance

theorem oTest_iff (a n c j : ℕ) :
    OTest a n c j ↔ omegaTest (prefixOracle a n) c j = Bool.true := by
  simp only [OTest, omegaTest, prefixOracle]
  exact ⟨fun h => decide_eq_true h, fun h => of_decide_eq_true h⟩

/-- `k` is a stage by which every program of at most `n - 2` bits that halts has been found,
according to the oracle value `a`; here `m` packages `n` and `a`. -/
def StageOk (m k : ℕ) : Prop :=
  ∀ c < encBound m.unpair.1 + 1, precIdx c ≤ m.unpair.1 →
    ∃ j < k + 1, OTest m.unpair.2 m.unpair.1 c j

/-- `s` is the value of some code below `Lambda.encBound n` after at most `k` leftmost steps. -/
def Forbidden (n k s : ℕ) : Prop :=
  ∃ c < encBound n + 1, ∃ j < k + 1,
    nstep_code^[j] (closure_code c) = Lambda.church_code s

instance (m k : ℕ) : Decidable (StageOk m k) := by unfold StageOk; infer_instance

instance (n k s : ℕ) : Decidable (Forbidden n k s) := by unfold Forbidden; infer_instance

------------------------------------------------------------------------
-- Computability of the two tests
------------------------------------------------------------------------

theorem primrec_OTest :
    PrimrecRel fun (j : ℕ) (q : ℕ × ℕ × ℕ) => OTest q.1.unpair.2 q.1.unpair.1 q.2.1 j := by
  have hm : Primrec fun p : ℕ × ℕ × ℕ × ℕ => p.2.1 := Primrec.fst.comp Primrec.snd
  have ha : Primrec fun p : ℕ × ℕ × ℕ × ℕ => p.2.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hm)
  have hn : Primrec fun p : ℕ × ℕ × ℕ × ℕ => p.2.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hm)
  have hc : Primrec fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hpi : Primrec fun p : ℕ × ℕ × ℕ × ℕ => precIdx p.2.2.1 := precIdx_primrec.comp hc
  have hA : Primrec fun p : ℕ × ℕ × ℕ × ℕ => 2 ^ (4 * p.1 + 2) :=
    primrec_two_pow.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) Primrec.fst) (Primrec.const 2))
  have hlhs : Primrec fun p : ℕ × ℕ × ℕ × ℕ =>
      p.2.1.unpair.2 / 2 ^ (p.2.1.unpair.1 - precIdx p.2.2.1) * 2 ^ (4 * p.1 + 2) :=
    Primrec.nat_mul.comp
      (Primrec.nat_div.comp ha (primrec_two_pow.comp (Primrec.nat_sub.comp hn hpi))) hA
  have hrhs : Primrec fun p : ℕ × ℕ × ℕ × ℕ =>
      omegaNum p.1 * 2 ^ precIdx p.2.2.1 + 3 * 2 ^ (4 * p.1 + 2) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (omegaNum_primrec.comp Primrec.fst) (primrec_two_pow.comp hpi))
      (Primrec.nat_mul.comp (Primrec.const 3) hA)
  exact (PrimrecRel.comp Primrec.nat_lt hlhs hrhs).primrecRel

theorem primrec_stageOk : PrimrecRel StageOk := by
  have hex : PrimrecPred fun q : ℕ × ℕ × ℕ =>
      ∃ j < q.2.2 + 1, OTest q.1.unpair.2 q.1.unpair.1 q.2.1 j :=
    primrecPred_exists_lt primrec_OTest
      (Primrec.nat_add.comp (Primrec.snd.comp (Primrec.snd)) (Primrec.const 1))
  have hB : PrimrecPred fun r : ℕ × ℕ × ℕ =>
      ∃ j < r.2.2 + 1, OTest r.2.1.unpair.2 r.2.1.unpair.1 r.1 j :=
    hex.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd)))
  have hA : PrimrecPred fun r : ℕ × ℕ × ℕ => precIdx r.1 ≤ r.2.1.unpair.1 :=
    PrimrecRel.comp Primrec.nat_le (precIdx_primrec.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd)))
  have himp : PrimrecPred fun r : ℕ × ℕ × ℕ =>
      precIdx r.1 ≤ r.2.1.unpair.1 →
        ∃ j < r.2.2 + 1, OTest r.2.1.unpair.2 r.2.1.unpair.1 r.1 j :=
    (hA.not.or hB).of_eq fun r => by tauto
  have hall : PrimrecPred fun p : ℕ × ℕ =>
      ∀ c < encBound p.1.unpair.1 + 1, precIdx c ≤ p.1.unpair.1 →
        ∃ j < p.2 + 1, OTest p.1.unpair.2 p.1.unpair.1 c j :=
    primrecPred_forall_lt himp.primrecRel
      (Primrec.nat_add.comp
        (encBound_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)))
        (Primrec.const 1))
  exact hall.primrecRel

theorem primrec_forbidden : PrimrecPred fun p : (ℕ × ℕ) × ℕ => Forbidden p.1.1 p.1.2 p.2 := by
  have h1 : PrimrecRel fun (j : ℕ) (q : (ℕ × ℕ) × ℕ) =>
      nstep_code^[j] (closure_code q.1.1) = Lambda.church_code q.2 :=
    (PrimrecRel.comp Primrec.eq
      (nstep_code_iterate_primrec.comp
        (closure_code_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        Primrec.fst)
      (Lambda.church_code_primrec.comp (Primrec.snd.comp Primrec.snd))).primrecRel
  have hex : PrimrecPred fun q : (ℕ × ℕ) × ℕ =>
      ∃ j < q.1.2 + 1, nstep_code^[j] (closure_code q.1.1) = Lambda.church_code q.2 :=
    primrecPred_exists_lt h1
      (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1))
  -- reshuffle `(c, ((n, k), s))` into `((c, k), s)`
  have hB : PrimrecPred fun r : ℕ × (ℕ × ℕ) × ℕ =>
      ∃ j < r.2.1.2 + 1, nstep_code^[j] (closure_code r.1) = Lambda.church_code r.2.2 :=
    hex.comp (Primrec.pair
      (Primrec.pair Primrec.fst (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd))
  have hall : PrimrecPred fun p : (ℕ × ℕ) × ℕ =>
      ∃ c < encBound p.1.1 + 1, ∃ j < p.1.2 + 1,
        nstep_code^[j] (closure_code c) = Lambda.church_code p.2 :=
    primrecPred_exists_lt hB.primrecRel
      (Primrec.nat_add.comp (encBound_primrec.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.const 1))
  exact hall

/-- Fed the first `n` bits of `Ω`, this procedure returns a number that no closed program of at
most `n - 2` bits computes. -/
def dodge (m : ℕ) : Part ℕ :=
  (Nat.rfind fun k => Part.some (decide (StageOk m k))).bind fun k =>
    Nat.rfind fun s => Part.some (decide (¬ Forbidden m.unpair.1 k s))

theorem partrec_dodge : Partrec dodge := by
  have hsearch : Partrec fun m : ℕ => Nat.rfind fun k => Part.some (decide (StageOk m k)) :=
    Partrec.rfind primrec_stageOk.decide.to_comp
  have hfb : Computable₂ fun (p : ℕ × ℕ) (s : ℕ) =>
      decide (¬ Forbidden p.1.unpair.1 p.2 s) := by
    have h : PrimrecPred fun q : (ℕ × ℕ) × ℕ => ¬ Forbidden q.1.1.unpair.1 q.1.2 q.2 :=
      (primrec_forbidden.comp (Primrec.pair
        (Primrec.pair (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp Primrec.fst)) Primrec.snd)).not
    exact h.primrecRel.decide.to_comp
  exact Partrec.bind hsearch (Partrec.rfind hfb)

------------------------------------------------------------------------
-- The oracle search terminates
------------------------------------------------------------------------

@[simp] theorem unpair_omegaPrefix_fst (n : ℕ) : (omegaPrefix n).unpair.1 = n := by
  simp [omegaPrefix]

@[simp] theorem unpair_omegaPrefix_snd (n : ℕ) : (omegaPrefix n).unpair.2 = omegaBits n := by
  simp [omegaPrefix]

/-- Fed the true first `n` bits, the stage test is passed by some stage, for every program of at
most `n - 2` bits. -/
theorem exists_oTest {n c : ℕ} (h : precIdx c ≤ n) : ∃ j, OTest (omegaBits n) n c j := by
  obtain ⟨j, hj⟩ := exists_omegaTest omegaBits_spec c
  refine ⟨j, (oTest_iff _ _ _ _).2 ?_⟩
  have hval : prefixOracle (omegaBits n) n (precIdx c) = omegaBits (precIdx c) := by
    rw [prefixOracle, omegaBits_shift h]
  rw [omegaTest_congr hval j]
  exact hj

theorem exists_stageOk (n : ℕ) : ∃ k, StageOk (omegaPrefix n) k := by
  classical
  set f : ℕ → ℕ := fun c =>
    if h : ∃ j, OTest (omegaBits n) n c j then h.choose else 0 with hf
  refine ⟨(Finset.range (encBound n + 1)).sup f, ?_⟩
  intro c hc hpi
  simp only [unpair_omegaPrefix_fst, unpair_omegaPrefix_snd] at hc hpi ⊢
  have hex : ∃ j, OTest (omegaBits n) n c j := exists_oTest hpi
  have hle : f c ≤ (Finset.range (encBound n + 1)).sup f :=
    Finset.le_sup (Finset.mem_range.mpr hc)
  refine ⟨f c, by omega, ?_⟩
  have : f c = hex.choose := by rw [hf]; exact dif_pos hex
  rw [this]
  exact hex.choose_spec

------------------------------------------------------------------------
-- Every short program is caught
------------------------------------------------------------------------

/-- At a stage certified by the oracle, the value of every closed program of at most `n - 2`
bits has already been produced. -/
theorem forbidden_of_isProgramFor {n k s : ℕ} {t : Lambda} (hk : StageOk (omegaPrefix n) k)
    (ht : IsProgramFor t s) (hb : (bits t).length + 2 ≤ n) : Forbidden n k s := by
  obtain ⟨hclosed, hred⟩ := ht
  set c : ℕ := Lambda.encode t with hc
  -- the term is its own closure
  have hfree : freeMax t = 0 := (isClosed_iff_freeMax_eq_zero t).1 hclosed
  have hclos : closure_code c = c := by
    rw [hc, closure_code_correct, hfree, closure]
  -- the code is small
  have hsize : size t ≤ n := le_trans (le_trans (size_le_bits_length t) (by omega)) le_rfl
  have hcb : c ≤ encBound n := encode_le_encBound t n hsize
  -- and its precision index is at most `n`
  have hprec : precIdx c ≤ n := by
    rw [precIdx, hclos, hc, bitsLen_code_correct]
    omega
  -- the oracle stage has already found it
  obtain ⟨j, hjk, hj⟩ :=
    (by simpa using hk c (by simpa using Nat.lt_succ_of_le hcb) (by simpa using hprec) :
      ∃ j < k + 1, OTest (omegaBits n) n c j)
  have hjt : omegaTest omegaBits c j = Bool.true := by
    have hval : prefixOracle (omegaBits n) n (precIdx c) = omegaBits (precIdx c) := by
      rw [prefixOracle, omegaBits_shift hprec]
    rw [← omegaTest_congr hval j]
    exact (oTest_iff _ _ _ _).1 hj
  -- so it has halted by stage `j`
  have hvalid : is_valid_code c = Bool.true := by rw [hc]; exact is_valid_code_encode t
  have hdec : decodeD c = t := by
    apply Lambda.encode_injective
    rw [encode_decodeD hvalid]
  have hnf : HasNormalForm t := ⟨Lambda.church s, hred, Lambda.church_normal s⟩
  have hhalt := (halts_iff_of_omegaTest omegaBits_spec hvalid hjt).1 (by rw [hdec]; exact hnf)
  have hby : haltsBy_code c j = Bool.true := by
    have := hhalt.2
    rwa [hclos] at this
  have hnormal : Lambda.is_normal (nstep^[j] t) := (haltsBy_code_correct t j).1 hby
  -- and its normal form is the Church numeral of `s`
  have hnft : nf t = Lambda.church s := nf_eq_of_reduces_normal hred (Lambda.church_normal s)
  have hstable : nstep^[j] t = nf t :=
    nstep_iterate_stable (is_normal_nstep_haltTime hnf) (haltTime_le hnormal)
  refine ⟨c, by omega, j, hjk, ?_⟩
  rw [hclos, hc, nstep_code_iterate, hstable, hnft, encode_church_eq_church_code]

------------------------------------------------------------------------
-- Only finitely many values are caught
------------------------------------------------------------------------

theorem church_code_injective : Function.Injective Lambda.church_code := by
  intro s₁ s₂ h
  rw [← encode_church_eq_church_code, ← encode_church_eq_church_code] at h
  exact Lambda.church_injective (Lambda.encode_injective h)

theorem exists_not_forbidden (n k : ℕ) : ∃ s, ¬ Forbidden n k s := by
  classical
  set T : Finset ℕ :=
    ((Finset.range (encBound n + 1)) ×ˢ (Finset.range (k + 1))).image
      (fun p => nstep_code^[p.2] (closure_code p.1)) with hT
  have hmem : ∀ s, Forbidden n k s → Lambda.church_code s ∈ T := by
    rintro s ⟨c, hc, j, hj, hval⟩
    rw [hT]
    exact Finset.mem_image.2 ⟨(c, j), Finset.mem_product.2
      ⟨Finset.mem_range.2 hc, Finset.mem_range.2 hj⟩, hval⟩
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hle : (Finset.range (T.card + 1)).card ≤ T.card :=
    Finset.card_le_card_of_injOn Lambda.church_code (fun s _ => hmem s (hcon s))
      (fun a _ b _ h => church_code_injective h)
  simp only [Finset.card_range] at hle
  omega

------------------------------------------------------------------------
-- The dodging value
------------------------------------------------------------------------

/-- **The value computed from the first `n` bits of `Ω` has no short program.** -/
theorem dodge_spec (n : ℕ) :
    ∃ x, dodge (omegaPrefix n) = Part.some x ∧
      ∀ t : Lambda, IsProgramFor t x → n ≤ (bits t).length + 2 := by
  classical
  -- the stage search
  obtain ⟨k₀, hk₀⟩ := exists_stageOk n
  set q₀ : ℕ → Bool := fun k => decide (StageOk (omegaPrefix n) k) with hq₀
  have hpm₀ : q₀ k₀ = Bool.true := by simp [hq₀, hk₀]
  obtain ⟨k, hk, -⟩ := Nat.rfind_min' hpm₀
  have hcoe₀ : ((q₀ : ℕ →. Bool)) = fun k => Part.some (q₀ k) := rfl
  rw [hcoe₀] at hk
  have hrf₁ : (Nat.rfind fun k => Part.some (q₀ k)) = Part.some k := Part.eq_some_iff.2 hk
  have hStage : StageOk (omegaPrefix n) k := by
    have hqk : q₀ k = Bool.true := (Part.mem_some_iff.1 (Nat.rfind_spec hk)).symm
    rw [hq₀] at hqk
    exact of_decide_eq_true hqk
  -- the value search
  obtain ⟨s₀, hs₀⟩ := exists_not_forbidden n k
  set q₁ : ℕ → Bool := fun s => decide (¬ Forbidden (omegaPrefix n).unpair.1 k s) with hq₁
  have hpm₁ : q₁ s₀ = Bool.true := by simp [hq₁, hs₀]
  obtain ⟨x, hx, -⟩ := Nat.rfind_min' hpm₁
  have hcoe₁ : ((q₁ : ℕ →. Bool)) = fun s => Part.some (q₁ s) := rfl
  rw [hcoe₁] at hx
  have hrf₂ : (Nat.rfind fun s => Part.some (q₁ s)) = Part.some x := Part.eq_some_iff.2 hx
  have hxnot : ¬ Forbidden n k x := by
    have hqx : q₁ x = Bool.true := (Part.mem_some_iff.1 (Nat.rfind_spec hx)).symm
    rw [hq₁] at hqx
    have := of_decide_eq_true hqx
    simpa using this
  refine ⟨x, ?_, ?_⟩
  · rw [dodge, hrf₁, Part.bind_some, hrf₂]
  · intro t ht
    by_contra hcon
    exact hxnot (forbidden_of_isProgramFor hStage ht (by omega))

------------------------------------------------------------------------
-- Chaitin's incompressibility theorem
------------------------------------------------------------------------

/-- **The prefixes of `Ω` are incompressible**: no self-delimiting program of fewer than
`n - O(1)` bits describes the first `n` bits of Chaitin's constant. -/
theorem exists_const_le_kolmP_omegaPrefix : ∃ c : ℕ, ∀ n : ℕ, n ≤ kolmP (omegaPrefix n) + c := by
  obtain ⟨F, hFc, hF⟩ := lambdaComputable_of_partrec_closed partrec_dodge
  refine ⟨(bits F).length + 4, fun n => ?_⟩
  obtain ⟨x, hxval, hxshort⟩ := dodge_spec n
  obtain ⟨t, ht, hlen⟩ := exists_program_of_kolmP (omegaPrefix n)
  have hu : IsProgramFor (Lambda.app F t) x := by
    refine ⟨Lambda.IsClosed_app hFc ht.1, ?_⟩
    exact Lambda.reduces_trans (Lambda.reduces_app_right ht.2) ((hF _ x).1 hxval)
  have h := hxshort _ hu
  have hbits : (bits (Lambda.app F t)).length = (bits F).length + (bits t).length + 2 := by
    simp [bits_app]
  omega

end

end Lambda
