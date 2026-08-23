/-
# The Levin–Schnorr theorem

`Start/MartinLof.lean` proves the *easy* half of the Levin–Schnorr theorem for the prefix
complexity `Lambda.kolmP` of the binary lambda-calculus machine: a Martin-Löf random sequence has
incompressible prefixes.  The converse is false for that machine, because it is not additively
optimal (see the discussion at the top of `Start/MartinLof.lean`).

For the Kraft–Chaitin universal prefix machine `KC.U` of `Start/KCMachine.lean`, which *is*
additively optimal, both halves hold, and this file proves them:

* `KC.mlRandom_of_exists_const_le_KU` (proved in `Start/OmegaURandom.lean`) — **the converse
  half**: if the prefixes of `X` are incompressible, `∃ c, ∀ n, n ≤ KU ⌜X ↾ n⌝ + c`, then `X` is
  Martin-Löf random.  Its proof is the machine-existence argument that turns a Martin-Löf test
  into a computably enumerated stream of requests of finite total weight; the randomness of `Ω`
  (`KC.mlRandom_omegaSeq`) is its special case for Chaitin incompressibility.
* `KC.exists_const_le_KU_prefix_of_mlRandom` — **the easy half** for `KU`: the strings that `KU`
  compresses by more than `c` bits form the `c`-th level of a Martin-Löf test `KC.kuTest`, whose
  measure bound is Kraft's inequality `KC.kraft_KU`.
* `KC.mlRandom_iff_exists_const_le_KU` — **the Levin–Schnorr theorem**: for the universal prefix
  machine, Martin-Löf randomness *is* incompressibility of all prefixes.
-/

import Start.OmegaURandom

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace KC

open MeasureTheory Lambda

------------------------------------------------------------------------
-- The compression test of the universal prefix machine
------------------------------------------------------------------------

/-- The allocation step `t` witnesses that `σ` is compressible by more than `c` bits: it hands
out a program of length `L` for the code of `σ`, with `L + c < |σ|`. -/
def kuFound (c : ℕ) (σ : List Bool) (t : ℕ) : Bool :=
  ((slot t).map fun p =>
    decide (p.2.2 = Encodable.encode σ ∧ p.2.1 + c < σ.length)).getD Bool.false

/-- One step of the enumeration `KC.kuEnter`. -/
def kuStep (c : ℕ) (σ : List Bool) (q : ℕ × Bool) : Bool := q.2 || kuFound c σ q.1

/-- The compression test of `KC.U`: level `c` collects the strings compressible by more than `c`
bits, enumerated by the stage at which their short program is allocated. -/
def kuEnter (c : ℕ) (σ : List Bool) (j : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) Bool.false (fun k IH => kuStep c σ (k, IH)) j

theorem kuEnter_eq_true_iff (c : ℕ) (σ : List Bool) (j : ℕ) :
    kuEnter c σ j = Bool.true ↔ ∃ t < j, kuFound c σ t = Bool.true := by
  induction j with
  | zero => simp [kuEnter]
  | succ j ih =>
      have hstep : kuEnter c σ (j + 1) = (kuEnter c σ j || kuFound c σ j) := rfl
      rw [hstep, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨t, ht, h⟩ | h)
        · exact ⟨t, by omega, h⟩
        · exact ⟨j, Nat.lt_succ_self j, h⟩
      · rintro ⟨t, ht, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with hlt | rfl
        · exact Or.inl ⟨t, hlt, h⟩
        · exact Or.inr h

theorem primrec_kuFound :
    Primrec fun p : ℕ × (ℕ × List Bool) => kuFound p.2.1 p.2.2 p.1 := by
  have hslot : Primrec fun p : ℕ × (ℕ × List Bool) => slot p.1 := slot_primrec.comp Primrec.fst
  have hbody : Primrec₂ fun (p : ℕ × (ℕ × List Bool)) (q : ℕ × ℕ × ℕ) =>
      decide (q.2.2 = Encodable.encode p.2.2 ∧ q.2.1 + p.2.1 < p.2.2.length) := by
    have hA : PrimrecPred fun y : (ℕ × (ℕ × List Bool)) × (ℕ × ℕ × ℕ) =>
        y.2.2.2 = Encodable.encode y.1.2.2 :=
      PrimrecRel.comp (Primrec.eq (α := ℕ))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.encode.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    have hB : PrimrecPred fun y : (ℕ × (ℕ × List Bool)) × (ℕ × ℕ × ℕ) =>
        y.2.2.1 + y.1.2.1 < y.1.2.2.length :=
      PrimrecRel.comp Primrec.nat_lt
        (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    exact (hA.and hB).decide
  exact (Primrec₂.comp Primrec.option_getD (Primrec.option_map hslot hbody)
    (Primrec.const Bool.false)).of_eq fun p => rfl

/-- `KC.kuFound` as a computable function of an arbitrary computable triple of arguments. -/
theorem comp_kuFound {α : Type} [Primcodable α] {f : α → ℕ} {g : α → List Bool} {h : α → ℕ}
    (hf : Computable f) (hg : Computable g) (hh : Computable h) :
    Computable fun a => kuFound (f a) (g a) (h a) :=
  ((Primrec.to_comp primrec_kuFound).comp (hh.pair (hf.pair hg))).of_eq fun _ => rfl

theorem computable₂_kuEnter :
    Computable₂ fun (p : ℕ × List Bool) (j : ℕ) => kuEnter p.1 p.2 j := by
  have hstep : Computable₂ fun (p : (ℕ × List Bool) × ℕ) (q : ℕ × Bool) =>
      kuStep p.1.1 p.1.2 q := by
    have hprev : Computable fun x : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) => x.2.2 :=
      Computable.snd.comp Computable.snd
    have hc : Computable fun x : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) => x.1.1.1 :=
      Computable.fst.comp (Computable.fst.comp Computable.fst)
    have hσ : Computable fun x : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) => x.1.1.2 :=
      Computable.snd.comp (Computable.fst.comp Computable.fst)
    have hk : Computable fun x : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) => x.2.1 :=
      Computable.fst.comp Computable.snd
    exact (comp_or hprev (comp_kuFound hc hσ hk)).of_eq fun x => rfl
  exact (Computable.nat_rec Computable.snd (Computable.const Bool.false) hstep).of_eq fun p => rfl

theorem computable_kuEnter :
    Computable fun p : ℕ × List Bool × ℕ => kuEnter p.1 p.2.1 p.2.2 := by
  have harg : Computable fun p : ℕ × List Bool × ℕ => ((p.1, p.2.1) : ℕ × List Bool) :=
    Computable.fst.pair (Computable.fst.comp Computable.snd)
  have hj : Computable fun p : ℕ × List Bool × ℕ => p.2.2 := Computable.snd.comp Computable.snd
  exact (Computable₂.comp computable₂_kuEnter harg hj).of_eq fun p => rfl

theorem exists_kuEnter_iff (c : ℕ) (σ : List Bool) :
    (∃ j, kuEnter c σ j = Bool.true) ↔ KU (Encodable.encode σ) + c < σ.length := by
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨t, -, ht⟩ := (kuEnter_eq_true_iff c σ j).1 hj
    unfold kuFound at ht
    cases hs : slot t with
    | none => rw [hs] at ht; simp at ht
    | some p =>
        obtain ⟨m, L, x⟩ := p
        rw [hs] at ht
        simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at ht
        obtain ⟨hx, hlt⟩ := ht
        have hKU : KU x ≤ L := KU_le_of_slot hs
        rw [hx] at hKU
        omega
  · intro hlt
    obtain ⟨τ, hlen, hmem⟩ := KU_spec (Encodable.encode σ)
    obtain ⟨t, ht⟩ := mem_U_iff.1 hmem
    refine ⟨t + 1, (kuEnter_eq_true_iff c σ (t + 1)).2 ⟨t, Nat.lt_succ_self t, ?_⟩⟩
    unfold kuFound
    rw [ht]
    simp only [Option.map_some, Option.getD_some, decide_eq_true_eq, true_and]
    omega

/-- **Kraft's inequality for `KU`, in `ℝ≥0∞`.** -/
theorem kraft_KU_ennreal : ∑' x : ℕ, (2 : ENNReal)⁻¹ ^ KU x ≤ 1 := by
  simp only [ennreal_two_inv_pow]
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
  refine ENNReal.ofReal_le_one.2 ?_
  simpa [wt] using kraft_KU F

theorem cantorMeasure_kuEnter_le (c : ℕ) :
    cantorMeasure (openOf {σ | ∃ j, kuEnter c σ j = Bool.true}) ≤ (2 : ENNReal)⁻¹ ^ c := by
  have hset : {σ : List Bool | ∃ j, kuEnter c σ j = Bool.true}
      = {σ : List Bool | KU (Encodable.encode σ) + c < σ.length} := by
    ext σ
    exact exists_kuEnter_iff c σ
  rw [hset]
  set W : Set (List Bool) := {σ : List Bool | KU (Encodable.encode σ) + c < σ.length} with hW
  refine le_trans (cantorMeasure_openOf_le W) ?_
  have hterm : ∀ σ : W, (2 : ENNReal)⁻¹ ^ (σ : List Bool).length ≤
      (2 : ENNReal)⁻¹ ^ (c + 1) * (2 : ENNReal)⁻¹ ^ KU (Encodable.encode (σ : List Bool)) := by
    intro τ
    have h : KU (Encodable.encode (τ : List Bool)) + c < (τ : List Bool).length := τ.2
    rw [← pow_add]
    exact pow_le_pow_right_of_le_one' (by norm_num) (by omega)
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  rw [ENNReal.tsum_mul_left]
  have hinj : Function.Injective fun σ : W => Encodable.encode (σ : List Bool) :=
    fun _ _ h => Subtype.ext (Encodable.encode_injective h)
  have hsum : ∑' σ : W, (2 : ENNReal)⁻¹ ^ KU (Encodable.encode (σ : List Bool)) ≤ 1 :=
    le_trans (ENNReal.tsum_comp_le_tsum_of_injective hinj fun x => (2 : ENNReal)⁻¹ ^ KU x)
      kraft_KU_ennreal
  calc (2 : ENNReal)⁻¹ ^ (c + 1) *
        ∑' σ : W, (2 : ENNReal)⁻¹ ^ KU (Encodable.encode (σ : List Bool))
      ≤ (2 : ENNReal)⁻¹ ^ (c + 1) * 1 := by gcongr
    _ ≤ (2 : ENNReal)⁻¹ ^ c := by
        rw [mul_one]
        exact pow_le_pow_right_of_le_one' (by norm_num) (by omega)

/-- The Martin-Löf test built from compressibility by the universal prefix machine. -/
def kuTest : MLTest where
  enter := kuEnter
  enter_computable := computable_kuEnter
  measure_le := cantorMeasure_kuEnter_le

------------------------------------------------------------------------
-- The easy half, and the theorem
------------------------------------------------------------------------

/-- **The easy half of the Levin–Schnorr theorem** for the universal prefix machine: a
Martin-Löf random sequence has `KU`-incompressible prefixes. -/
theorem exists_const_le_KU_prefix_of_mlRandom {X : ℕ → Bool} (h : MLRandom X) :
    ∃ c : ℕ, ∀ n : ℕ, n ≤ KU (Encodable.encode (prefixList X n)) + c := by
  obtain ⟨c, hc⟩ := h kuTest
  refine ⟨c, fun n => ?_⟩
  by_contra hcon
  refine hc (mem_openOf.2 ⟨prefixList X n, ?_, mem_cylinder_prefixList X n⟩)
  change ∃ j, kuEnter c (prefixList X n) j = Bool.true
  refine (exists_kuEnter_iff c (prefixList X n)).2 ?_
  rw [prefixList_length]
  omega

/-- **The Levin–Schnorr theorem.**  For the Kraft–Chaitin universal prefix machine, a sequence is
Martin-Löf random if and only if its prefixes are incompressible up to an additive constant. -/
theorem mlRandom_iff_exists_const_le_KU {X : ℕ → Bool} :
    MLRandom X ↔ ∃ c : ℕ, ∀ n : ℕ, n ≤ KU (Encodable.encode (prefixList X n)) + c :=
  ⟨exists_const_le_KU_prefix_of_mlRandom, mlRandom_of_exists_const_le_KU⟩

end KC
