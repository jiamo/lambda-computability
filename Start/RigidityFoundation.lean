/-
**The foundations of the rigidity development, unified with the host oracle machines** —
milestone M26 (`M26-UNIFY-RIGIDITY-FOUNDATION`).

`Start/RigidityBridge.lean` identifies the degrees of the absorbed rigidity development with the
host's degrees of sets.  The absorbed development also keeps its own oracle programs
(`TuringRigidity.OracleCode`, `Start/RigidityOracleCode.lean`) and its own jump
(`TuringRigidity.OracleJump.jump`, `iterate`; `Start/RigidityOracleJump.lean`), while the host has
the oracle machines `Lambda.Oracle.Phi` (`Start/OracleMachine.lean`) and the jump
`Lambda.Oracle.jumpChar` (`Start/OracleJump.lean`).  This module identifies both.

* `Lambda.Oracle.exists_index_param` — **relativised s-m-n**: a function recursive in `A` with a
  parameter has a computable family of indices `k v` with `Φ^A_{k v}(y) = g v`;
  `Lambda.Oracle.dom_turingReducible_jumpChar` — so the domain of every function recursive in `A`
  is decidable relative to the host jump of `A`;
* **`Lambda.Oracle.jumpChar_reduces_jump`**, **`Lambda.Oracle.jump_reduces_jumpChar`** — the host
  jump and the upstream jump of every oracle are Turing equivalent;
  **`Lambda.Oracle.hostIterate_equiv`** — and so are their `n`-th iterates, for every `n`;
* **`Lambda.Oracle.exists_index_of_code`** — every upstream oracle program has one host index
  computing the same partial function **relative to every oracle**;
* **`Lambda.Oracle.exists_code_of_index`** — conversely every host index has one upstream program
  computing the same partial function relative to every oracle (`Lambda.Oracle.phiCode`, an
  explicit program: read the oracle segment by primitive recursion with queries, search for a
  converging stage, read off the value).
-/

import Start.RigidityOracleCode
import Start.RigidityJumpProperties
import Start.OracleUniversal
import Start.JumpSigmaOne

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda.Oracle

open TuringRigidity
open Nat.Partrec (Code)
open Encodable Denumerable

/-! ### Relativised s-m-n and the host jump -/

/-- **Relativised s-m-n.** -/
theorem exists_index_param {A : ℕ → Bool} {g : ℕ →. ℕ} (hg : RecursiveIn {oracleFun A} g) :
    ∃ k : ℕ → ℕ, Computable k ∧ ∀ v y, Phi A (k v) y = g v := by
  obtain ⟨F, hF, hs⟩ := exists_simulates_of_recursiveIn hg
  let G : ℕ →. ℕ := fun z => F (Nat.pair (Nat.unpair (Nat.unpair z).2).1 (Nat.unpair z).1)
  have hG : Nat.Partrec G := by
    have hp : Primrec fun z : ℕ => Nat.pair (Nat.unpair (Nat.unpair z).2).1 (Nat.unpair z).1 :=
      Primrec₂.natPair.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
        (Primrec.fst.comp Primrec.unpair)
    exact Partrec.nat_iff.1 ((Partrec.nat_iff.2 hF).comp hp.to_comp)
  obtain ⟨cG, hcG⟩ := Code.exists_code.1 hG
  refine ⟨fun v => encode (Code.curry cG v),
    (Primrec.encode.comp (Code.primrec₂_curry.comp (Primrec.const cG) Primrec.id)).to_comp,
    fun v y => ?_⟩
  have hsim : Simulates A (Code.eval (Code.curry cG v)) (fun _ => g v) := by
    refine ⟨fun x y' s t hst h => ?_, fun x y' => ?_⟩
    · rw [Code.eval_curry, hcG] at h ⊢
      simp only [G, Nat.unpair_pair] at h ⊢
      exact hs.1 v y' s t hst h
    · rw [hs.2 v y']
      simp only [Code.eval_curry, hcG, G, Nat.unpair_pair]
  rw [Phi_encode, evalOracle_eq_of_simulates hsim]

/-- **The domain of a function recursive in `A` is decidable relative to the jump of `A`.** -/
theorem dom_turingReducible_jumpChar {A : ℕ → Bool} {g : ℕ →. ℕ}
    (hg : RecursiveIn {oracleFun A} g) :
    TuringReducible (oracleFun (charOracle fun v => (g v).Dom)) (oracleFun (jumpChar A)) := by
  obtain ⟨k, hk, hspec⟩ := exists_index_param hg
  have hJ : ∀ v, Jump A (k v) ↔ (g v).Dom := fun v => by
    unfold Jump
    rw [hspec]
  have horacle : RecursiveIn {oracleFun (jumpChar A)} (oracleFun (jumpChar A)) :=
    RecursiveIn.oracle _ (by simp)
  have hidx : RecursiveIn {oracleFun (jumpChar A)} (fun n => (k n : Part ℕ)) :=
    RecursiveIn.iff_nat.mpr (Nat.Partrec.recursiveIn (Partrec.nat_iff.1 hk.partrec))
  have hcomp := recIn_comp horacle hidx
  have hEq : (fun n => ((k n : ℕ) : Part ℕ) >>= oracleFun (jumpChar A)) =
      oracleFun (charOracle fun v => (g v).Dom) := by
    funext n
    have hb : ((k n : ℕ) : Part ℕ) >>= oracleFun (jumpChar A)
        = oracleFun (jumpChar A) (k n) := Part.bind_some _ _
    rw [hb]
    have hval : jumpChar A (k n) = charOracle (fun v => (g v).Dom) n := by
      by_cases hn : (g n).Dom
      · simp [jumpChar_eq_true_iff.2 ((hJ n).2 hn), charOracle, hn]
      · simp [jumpChar_eq_false_iff.2 (fun h => hn ((hJ n).1 h)), charOracle, hn]
    simp only [oracleFun, hval]
  rwa [hEq] at hcomp

/-! ### The two jumps -/

/-- **The host jump is computable in the upstream jump.** -/
theorem jumpChar_reduces_jump (A : ℕ → Bool) : Reduces (jumpChar A) (OracleJump.jump A) := by
  classical
  obtain ⟨j, hj⟩ := jump_re_in A
  have hf : Nat.RecursiveIn {oracleFunction A} (Phi A j) :=
    RecursiveIn.iff_nat.mp (recursiveIn_Phi A j)
  have hd := OracleJump.domain_recursive_jump hf
  unfold ArithmeticHierarchy.RecursivePred at hd
  apply RecursiveIn.iff_nat.mpr
  refine hd.of_eq fun x => ?_
  by_cases h : Jump A x
  · simp [oracleFunction, jumpChar_eq_true_iff.2 h, (hj x).1 h]
  · simp [oracleFunction, jumpChar_eq_false_iff.2 h, mt (hj x).2 h]

/-- **The upstream jump is computable in the host jump.** -/
theorem jump_reduces_jumpChar (A : ℕ → Bool) : Reduces (OracleJump.jump A) (jumpChar A) := by
  classical
  obtain ⟨Q, hQ, hPQ⟩ := OracleJump.halts_sigma A
  have hQ' : Nat.RecursiveIn {oracleFunction A} (fun z => Part.some (if Q z then 1 else 0)) := by
    simpa [ArithmeticHierarchy.Form, ArithmeticHierarchy.RecursivePred] using hQ
  have hsub : Nat.Partrec fun m : ℕ => (Part.some (1 - m) : Part ℕ) :=
    Partrec.nat_iff.1 (Primrec.nat_sub.comp (Primrec.const 1) Primrec.id).to_comp.partrec
  have hflip : Nat.RecursiveIn {oracleFunction A} (fun z => Part.some (if Q z then 0 else 1)) :=
    (Nat.RecursiveIn.comp (Nat.Partrec.recursiveIn hsub) hQ').of_eq fun z => by
      by_cases h : Q z <;> simp [h]
  let g : ℕ →. ℕ := fun v => Nat.rfind fun a =>
    (fun m => decide (m = 0)) <$> (Part.some (if Q (Nat.pair v a) then 0 else 1) : Part ℕ)
  have hg : Nat.RecursiveIn {oracleFunction A} g := Nat.RecursiveIn.rfind hflip
  have hdom : ∀ v, (g v).Dom ↔ OracleJump.Halts A (Nat.unpair v).1 (Nat.unpair v).2 := by
    intro v
    have h1 := hPQ v
    simp only [ArithmeticHierarchy.Quant, ite_true] at h1
    rw [h1]
    simp only [g]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      by_contra hn
      simp [hn] at ha
    · rintro ⟨a, ha⟩
      exact ⟨a, by simp [ha]⟩
  have hred := dom_turingReducible_jumpChar (A := A) (RecursiveIn.iff_nat.mpr hg)
  have heq : charOracle (fun v => (g v).Dom) = OracleJump.jump A := by
    funext v
    by_cases h : OracleJump.Halts A (Nat.unpair v).1 (Nat.unpair v).2
    · simp [charOracle, OracleJump.jump, h, (hdom v).2 h]
    · simp [charOracle, OracleJump.jump, h, mt (hdom v).1 h]
  rw [heq] at hred
  exact hred

/-- The host's iterated jumps. -/
def hostIterate (A : ℕ → Bool) : ℕ → (ℕ → Bool)
  | 0 => A
  | n + 1 => jumpChar (hostIterate A n)

/-- **The iterated jumps agree up to Turing equivalence**, for every oracle and every `n`. -/
theorem hostIterate_equiv (A : ℕ → Bool) (n : ℕ) :
    Reduces (hostIterate A n) (OracleJump.iterate A n) ∧
      Reduces (OracleJump.iterate A n) (hostIterate A n) := by
  induction n with
  | zero => exact ⟨TuringReducible.refl _, TuringReducible.refl _⟩
  | succ n ih =>
      refine ⟨TuringReducible.trans (jumpChar_reduces_jump (hostIterate A n))
        (OracleJump.jump_mono ih.1), TuringReducible.trans (OracleJump.jump_mono ih.2)
          (jump_reduces_jumpChar (hostIterate A n))⟩

/-! ### Upstream programs as host indices -/

theorem exists_uniform_simulates (c : OracleCode) :
    ∃ F, Nat.Partrec F ∧ ∀ A, Simulates A F (OracleCode.eval (oracleFunction A) c) := by
  induction c with
  | zero => exact ⟨liftFun fun _ => 0, partrec_liftFun Nat.Partrec.zero,
      fun A => simulates_liftFun A _⟩
  | succ => exact ⟨liftFun Nat.succ, partrec_liftFun Nat.Partrec.succ,
      fun A => simulates_liftFun A _⟩
  | left => exact ⟨liftFun fun n => (Nat.unpair n).1, partrec_liftFun Nat.Partrec.left,
      fun A => simulates_liftFun A _⟩
  | right => exact ⟨liftFun fun n => (Nat.unpair n).2, partrec_liftFun Nat.Partrec.right,
      fun A => simulates_liftFun A _⟩
  | query => exact ⟨queryFun, partrec_queryFun, fun A => simulates_queryFun A⟩
  | pair c d ih₁ ih₂ =>
      obtain ⟨F₁, hF₁, hs₁⟩ := ih₁
      obtain ⟨F₂, hF₂, hs₂⟩ := ih₂
      exact ⟨fun z => Nat.pair <$> F₁ z <*> F₂ z, Nat.Partrec.pair hF₁ hF₂,
        fun A => (hs₁ A).pairing (hs₂ A)⟩
  | comp c d ih₁ ih₂ =>
      obtain ⟨F₁, hF₁, hs₁⟩ := ih₁
      obtain ⟨F₂, hF₂, hs₂⟩ := ih₂
      refine ⟨fun z => (F₂ z).bind fun v => F₁ (Nat.pair z.unpair.1 v), ?_,
        fun A => (hs₁ A).composition (hs₂ A)⟩
      refine Partrec.nat_iff.1 (Partrec.bind (Partrec.nat_iff.2 hF₂) ?_)
      exact (Partrec.nat_iff.2 hF₁).comp
        (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
          Primrec.snd).to_comp
  | prec c d ih₁ ih₂ =>
      obtain ⟨F₁, hF₁, hs₁⟩ := ih₁
      obtain ⟨F₂, hF₂, hs₂⟩ := ih₂
      exact ⟨precFun F₁ F₂, partrec_precFun hF₁ hF₂, fun A => (hs₁ A).precn (hs₂ A)⟩
  | find c ih =>
      obtain ⟨F₁, hF₁, hs₁⟩ := ih
      exact ⟨rfindFun F₁, partrec_rfindFun hF₁, fun A => (hs₁ A).rfindn⟩

/-- **Every upstream oracle program is a host index**, one index for all oracles. -/
theorem exists_index_of_code (c : OracleCode) :
    ∃ e : ℕ, ∀ A : ℕ → Bool, Phi A e = OracleCode.eval (oracleFunction A) c := by
  obtain ⟨F, hF, hs⟩ := exists_uniform_simulates c
  obtain ⟨cF, hcF⟩ := Code.exists_code.1 hF
  refine ⟨encode cF, fun A => funext fun x => ?_⟩
  rw [Phi_encode]
  exact congrFun (evalOracle_eq_of_simulates (by rw [hcF]; exact hs A)) x

/-! ### Host indices as upstream programs -/

/-- A partial recursive function is computed by a query-free upstream program, for every oracle. -/
theorem exists_qfree {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    ∃ c : OracleCode, ∀ g, OracleCode.eval g c = f := by
  induction hf with
  | zero => exact ⟨.zero, fun _ => rfl⟩
  | succ => exact ⟨.succ, fun _ => rfl⟩
  | left => exact ⟨.left, fun _ => rfl⟩
  | right => exact ⟨.right, fun _ => rfl⟩
  | pair _ _ ih₁ ih₂ =>
      obtain ⟨c, hc⟩ := ih₁
      obtain ⟨d, hd⟩ := ih₂
      exact ⟨.pair c d, fun g => by simp only [OracleCode.eval, hc, hd]; rfl⟩
  | comp _ _ ih₁ ih₂ =>
      obtain ⟨c, hc⟩ := ih₁
      obtain ⟨d, hd⟩ := ih₂
      exact ⟨.comp c d, fun g => by simp only [OracleCode.eval, hc, hd]; rfl⟩
  | prec _ _ ih₁ ih₂ =>
      obtain ⟨c, hc⟩ := ih₁
      obtain ⟨d, hd⟩ := ih₂
      exact ⟨.prec c d, fun g => by simp only [OracleCode.eval, hc, hd]; rfl⟩
  | rfind _ ih =>
      obtain ⟨c, hc⟩ := ih
      exact ⟨.find c, fun g => by simp only [OracleCode.eval, hc]; rfl⟩

theorem partrec_segAppendPair :
    Nat.Partrec fun w : ℕ => (Part.some (segAppend (Nat.unpair w).1 (Nat.unpair w).2) : Part ℕ) :=
  Partrec.nat_iff.1 (primrec_segAppend.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)).to_comp.partrec

/-- A query-free program for `segAppend` on pairs. -/
def appCode : OracleCode := (exists_qfree partrec_segAppendPair).choose

theorem eval_appCode (g : ℕ →. ℕ) (w : ℕ) :
    OracleCode.eval g appCode w = Part.some (segAppend (Nat.unpair w).1 (Nat.unpair w).2) := by
  rw [appCode, (exists_qfree partrec_segAppendPair).choose_spec g]

/-- The identity program. -/
def idCode : OracleCode := .pair .left .right

theorem eval_idCode (g : ℕ →. ℕ) (n : ℕ) : OracleCode.eval g idCode n = Part.some n := by
  simp [idCode, OracleCode.eval, Seq.seq, Nat.pair_unpair]

theorem zero_part : (0 : Part ℕ) = Part.some 0 := rfl

@[simp] theorem some_bind' (a : ℕ) (f : ℕ →. ℕ) : (Part.some a >>= f) = f a :=
  Part.bind_some a f

theorem bind_pfun (x : Part ℕ) (f : ℕ →. ℕ) : (x >>= f) = x.bind f := rfl

theorem eval_comp (g : ℕ →. ℕ) (c d : OracleCode) (n : ℕ) :
    OracleCode.eval g (.comp c d) n = OracleCode.eval g d n >>= OracleCode.eval g c := rfl

theorem eval_pair_some (g : ℕ →. ℕ) (c d : OracleCode) (n a b : ℕ)
    (ha : OracleCode.eval g c n = Part.some a) (hb : OracleCode.eval g d n = Part.some b) :
    OracleCode.eval g (.pair c d) n = Part.some (Nat.pair a b) := by
  simp [OracleCode.eval, ha, hb, Seq.seq]

theorem eval_find (g : ℕ →. ℕ) (c : OracleCode) (a : ℕ) :
    OracleCode.eval g (.find c) a =
      Nat.rfind fun n => (fun m => decide (m = 0)) <$> OracleCode.eval g c (Nat.pair a n) := rfl

theorem eval_prec_zero (g : ℕ →. ℕ) (c d : OracleCode) (a : ℕ) :
    OracleCode.eval g (.prec c d) (Nat.pair a 0) = OracleCode.eval g c a := by
  simp [OracleCode.eval]

theorem eval_prec_succ (g : ℕ →. ℕ) (c d : OracleCode) (a n : ℕ) :
    OracleCode.eval g (.prec c d) (Nat.pair a (n + 1)) =
      OracleCode.eval g (.prec c d) (Nat.pair a n) >>= fun i =>
        OracleCode.eval g d (Nat.pair a (Nat.pair n i)) := by
  simp [OracleCode.eval]

/-- One step of reading the oracle: from `⟨a, ⟨y, σ⟩⟩`, append the answer at `y` to `σ`. -/
def segStep : OracleCode :=
  .comp appCode (.pair (.comp .right .right) (.comp .query (.comp .left .right)))

theorem eval_segStep (A : ℕ → Bool) (a y i : ℕ) :
    OracleCode.eval (oracleFunction A) segStep (Nat.pair a (Nat.pair y i)) =
      Part.some (segAppend i (if A y then 1 else 0)) := by
  rw [segStep, eval_comp, eval_pair_some _ _ _ _ i (if A y then 1 else 0), some_bind', eval_appCode]
  · simp
  · simp [OracleCode.eval]
  · simp [OracleCode.eval, oracleFunction]

/-- **The oracle segment of length `s`**, by primitive recursion with queries. -/
def segCode : OracleCode := .comp (.prec .zero segStep) (.pair .zero idCode)

theorem segNum_zero (A : ℕ → Bool) : segNum A 0 = 0 := rfl

theorem eval_segPrec (A : ℕ → Bool) (s : ℕ) :
    OracleCode.eval (oracleFunction A) (.prec .zero segStep) (Nat.pair 0 s) =
      Part.some (segNum A s) := by
  induction s with
  | zero => rw [eval_prec_zero]; rfl
  | succ s ih =>
      rw [eval_prec_succ, ih, Part.bind_eq_bind, Part.bind_some, eval_segStep, segNum_succ]

theorem eval_segCode (A : ℕ → Bool) (s : ℕ) :
    OracleCode.eval (oracleFunction A) segCode s = Part.some (segNum A s) := by
  have hpre : OracleCode.eval (oracleFunction A) (.pair .zero idCode) s =
      Part.some (Nat.pair 0 s) := by
    exact eval_pair_some _ _ _ _ _ _ zero_part (eval_idCode _ s)
  rw [segCode, eval_comp, hpre, some_bind', eval_segPrec]

/-- The test of a stage: from `⟨⟨x, s⟩, σ⟩`, `0` if the machine `e` converges at stage `s` on the
segment `σ`, else `1`. -/
def phiTest (e : ℕ) : ℕ →. ℕ := fun w =>
  Part.some (bif (Code.evaln (Nat.unpair (Nat.unpair (Nat.unpair w).1).2).1 (ofNat Code e)
    (Nat.pair (Nat.unpair w).2 (Nat.unpair (Nat.unpair w).1).1)).isSome then 0 else 1)

/-- The value at a stage. -/
def phiVal (e : ℕ) : ℕ →. ℕ := fun w =>
  Part.some ((Code.evaln (Nat.unpair (Nat.unpair (Nat.unpair w).1).2).1 (ofNat Code e)
    (Nat.pair (Nat.unpair w).2 (Nat.unpair (Nat.unpair w).1).1)).getD 0)

theorem primrec_stage (e : ℕ) : Primrec fun w : ℕ =>
    Code.evaln (Nat.unpair (Nat.unpair (Nat.unpair w).1).2).1 (ofNat Code e)
      (Nat.pair (Nat.unpair w).2 (Nat.unpair (Nat.unpair w).1).1) := by
  have h1 : Primrec fun w : ℕ => (Nat.unpair w).1 := Primrec.fst.comp Primrec.unpair
  have h2 : Primrec fun w : ℕ => (Nat.unpair w).2 := Primrec.snd.comp Primrec.unpair
  exact Code.primrec_evaln.comp (Primrec.pair (Primrec.pair (h1.comp (h2.comp h1))
    (Primrec.const _)) (Primrec₂.natPair.comp h2 (h1.comp h1)))

theorem partrec_phiTest (e : ℕ) : Nat.Partrec (phiTest e) :=
  Partrec.nat_iff.1 (Primrec.cond (Primrec.option_isSome.comp (primrec_stage e))
    (Primrec.const 0) (Primrec.const 1)).to_comp.partrec

theorem partrec_phiVal (e : ℕ) : Nat.Partrec (phiVal e) :=
  Partrec.nat_iff.1 (Primrec.option_getD.comp (primrec_stage e) (Primrec.const 0)).to_comp.partrec

/-- From `⟨x, s⟩`, the pair `⟨⟨x, s⟩, σ⟩` with `σ` the oracle segment read at stage `s`. -/
def withSeg (c : OracleCode) : OracleCode :=
  .comp c (.pair idCode (.comp segCode (.comp .right .right)))

theorem eval_withSeg (A : ℕ → Bool) {c : OracleCode} {f : ℕ →. ℕ}
    (hc : ∀ g, OracleCode.eval g c = f) (x s : ℕ) :
    OracleCode.eval (oracleFunction A) (withSeg c) (Nat.pair x s) =
      f (Nat.pair (Nat.pair x s) (segNum A (Nat.unpair s).2)) := by
  have hσ : OracleCode.eval (oracleFunction A) (.comp segCode (.comp .right .right)) (Nat.pair x s)
      = Part.some (segNum A (Nat.unpair s).2) := by
    rw [eval_comp, eval_comp]
    simp [OracleCode.eval, eval_segCode, some_bind']
  rw [withSeg, eval_comp, eval_pair_some _ _ _ _ _ _ (eval_idCode _ _) hσ, some_bind', hc]

/-- **The upstream program of the host machine `e`.** -/
def phiCode (e : ℕ) : OracleCode :=
  .comp (withSeg (exists_qfree (partrec_phiVal e)).choose)
    (.pair idCode (.find (withSeg (exists_qfree (partrec_phiTest e)).choose)))

/-- **Every host index is an upstream program**, one program for all oracles. -/
theorem eval_phiCode (e : ℕ) (A : ℕ → Bool) :
    OracleCode.eval (oracleFunction A) (phiCode e) = Phi A e := by
  funext x
  have hv := (exists_qfree (partrec_phiVal e)).choose_spec
  have ht := (exists_qfree (partrec_phiTest e)).choose_spec
  have hpred : (fun n => (fun m => decide (m = 0)) <$> OracleCode.eval (oracleFunction A)
      (withSeg (exists_qfree (partrec_phiTest e)).choose) (Nat.pair x n)) =
        fun n => Part.some (oracleStep A (ofNat Code e) x n).isSome := by
    funext n
    rw [eval_withSeg A ht]
    simp only [phiTest, Nat.unpair_pair, oracleStep]
    cases (Code.evaln (Nat.unpair n).1 (ofNat Code e)
      (Nat.pair (segNum A (Nat.unpair n).2) x)).isSome <;> rfl
  have hpair : OracleCode.eval (oracleFunction A)
      (.pair idCode (.find (withSeg (exists_qfree (partrec_phiTest e)).choose))) x =
        (Nat.rfind fun n => Part.some (oracleStep A (ofNat Code e) x n).isSome).map
          (Nat.pair x) := by
    simp only [OracleCode.eval, eval_idCode, hpred, Seq.seq]
    simp
  rw [phiCode, eval_comp, hpair, Phi, evalOracle, Nat.rfindOpt]
  apply Part.ext
  intro y
  rw [bind_pfun]
  constructor
  · intro hy
    obtain ⟨w, hw, hy⟩ := Part.mem_bind_iff.1 hy
    obtain ⟨s, hs, rfl⟩ := (Part.mem_map_iff _).1 hw
    refine Part.mem_bind_iff.2 ⟨s, hs, ?_⟩
    have hsome := Nat.rfind_spec hs
    rw [Part.mem_some_iff] at hsome
    rw [eval_withSeg A hv] at hy
    simp only [phiVal, Nat.unpair_pair, Part.mem_some_iff] at hy
    obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.1 hsome.symm
    simp only [oracleStep] at hv' ⊢
    rw [hv'] at hy ⊢
    simp only [Option.getD_some] at hy
    subst hy
    simp
  · intro hy
    obtain ⟨s, hs, hy⟩ := Part.mem_bind_iff.1 hy
    refine Part.mem_bind_iff.2 ⟨Nat.pair x s, (Part.mem_map_iff _).2 ⟨s, hs, rfl⟩, ?_⟩
    rw [eval_withSeg A hv]
    simp only [phiVal, Nat.unpair_pair, Part.mem_some_iff]
    simp only [oracleStep] at hy
    cases hst : Code.evaln (Nat.unpair s).1 (ofNat Code e) (Nat.pair (segNum A (Nat.unpair s).2) x)
      with
    | none => rw [hst] at hy; simp at hy
    | some v =>
        rw [hst] at hy
        simp only [Option.getD_some]
        have hy' : y ∈ Part.some v := by simpa using hy
        exact Part.mem_some_iff.1 hy'

theorem exists_code_of_index (e : ℕ) :
    ∃ c : OracleCode, ∀ A : ℕ → Bool, OracleCode.eval (oracleFunction A) c = Phi A e :=
  ⟨phiCode e, eval_phiCode e⟩

end Lambda.Oracle
