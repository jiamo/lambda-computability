/-
**The Turing jump.**

With the indexing `Φ_e^A` of `Start/OracleMachine.lean` and its completeness
(`Start/OracleSim.lean`) in place, the diagonal set

```
A' = { e | Φ_e^A(e) halts }
```

is the *Turing jump* of `A`.  This file proves the two theorems that make it a jump: `A'` is not
computable relative to `A` (a relativised halting problem), while `A` is computable relative to
`A'`.  Together they give a strictly increasing operator on the Turing degrees, i.e. the degrees
have no maximum, and every degree carries a strictly harder problem above it.

* `Lambda.Oracle.Jump`, `Lambda.Oracle.jumpChar` — the jump as a predicate and as an oracle;
* `Lambda.Oracle.not_recursiveIn_jumpChar` — **the relativised halting problem**: `A'` is not
  computable in `A`;
* `Lambda.Oracle.queryIndex` — a computable index of the machine that queries the oracle at a
  fixed place and diverges if the answer is negative, the reduction underlying:
* `Lambda.Oracle.recursiveIn_jumpChar` — `A` is computable in `A'`;
* `Lambda.Oracle.turingReducible_jumpChar`, `Lambda.Oracle.not_turingReducible_jumpChar` — the two
  statements in mathlib's `≤ᵀ` notation, and
* `Lambda.Oracle.turingDegree_lt_jump` — the degree of `A'` is strictly above the degree of `A`.
-/

import Start.OracleSim

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Oracle

open Encodable Denumerable
open Nat.Partrec (Code)
open scoped Computability

/-- The **Turing jump** of `A`: the set of indices `e` such that the `e`-th machine with oracle
`A` halts on its own index. -/
def Jump (A : ℕ → Bool) (e : ℕ) : Prop := (Phi A e e).Dom

/-- The jump of `A`, as an oracle. -/
noncomputable def jumpChar (A : ℕ → Bool) : ℕ → Bool := fun e =>
  haveI := Classical.dec (Jump A e)
  decide (Jump A e)

@[simp] theorem jumpChar_eq_true_iff {A : ℕ → Bool} {e : ℕ} : jumpChar A e = true ↔ Jump A e := by
  simp [jumpChar]

theorem jumpChar_eq_false_iff {A : ℕ → Bool} {e : ℕ} : jumpChar A e = false ↔ ¬ Jump A e := by
  rw [Bool.eq_false_iff, ne_eq, jumpChar_eq_true_iff]

/-! ## The jump is not computable in the oracle -/

/-- Searching for a zero of a constant function halts exactly when the constant is zero. -/
theorem rfind_const_dom {c : ℕ} :
    (Nat.rfind fun _ => (fun m => decide (m = 0)) <$> (Part.some c : Part ℕ)).Dom ↔ c = 0 := by
  constructor
  · intro h
    have hmem : (Nat.rfind fun _ => (fun m => decide (m = 0)) <$> (Part.some c : Part ℕ)).get h ∈
        Nat.rfind fun _ => (fun m => decide (m = 0)) <$> (Part.some c : Part ℕ) :=
      Part.get_mem h
    have := (mem_rfind_iff (g := fun _ => (Part.some c : Part ℕ))).1 hmem
    simpa [eq_comm] using this.1
  · rintro rfl
    exact Part.dom_iff_mem.2 ⟨0, (mem_rfind_iff (g := fun _ => (Part.some 0 : Part ℕ))).2
      ⟨Part.mem_some 0, fun m hm => absurd hm (Nat.not_lt_zero m)⟩⟩

/-- **The relativised halting problem.**  The jump of `A` is not computable relative to `A`. -/
theorem not_recursiveIn_jumpChar (A : ℕ → Bool) :
    ¬ RecursiveIn {oracleFun A} (oracleFun (jumpChar A)) := by
  intro h
  set f : ℕ →. ℕ := oracleFun (jumpChar A) with hf
  -- the machine that halts exactly on the indices *not* in the jump
  have hcomp : RecursiveIn {oracleFun A} fun n => (((Nat.unpair n).1 : ℕ) : Part ℕ) >>= f :=
    recIn_comp h recIn_left
  have hrfind := recIn_rfind hcomp
  have hEq : (fun a => Nat.rfind fun n =>
        (fun m => decide (m = 0)) <$> ((((Nat.unpair (Nat.pair a n)).1 : ℕ) : Part ℕ) >>= f)) =
      fun a => Nat.rfind fun _ => (fun m => decide (m = 0)) <$> f a := by
    funext a
    have hb : (Part.some a >>= f) = f a :=
      (Part.bind_eq_bind (Part.some a) f).trans (Part.bind_some a f)
    simp [hb]
  rw [hEq] at hrfind
  obtain ⟨e, he⟩ := exists_index_of_recursiveIn hrfind
  have hdom : Jump A e ↔ ¬ Jump A e := by
    have hval : Phi A e e = Nat.rfind fun _ => (fun m => decide (m = 0)) <$> f e :=
      congrFun he e
    have hfe : f e = Part.some (if jumpChar A e then 1 else 0) := rfl
    constructor
    · intro hj
      have : (Phi A e e).Dom := hj
      rw [hval, hfe] at this
      have h0 := rfind_const_dom.1 this
      have : jumpChar A e = false := by
        by_cases hb : jumpChar A e = true
        · simp [hb] at h0
        · simpa using Bool.eq_false_iff.2 hb
      exact absurd hj (jumpChar_eq_false_iff.1 this)
    · intro hj
      have : jumpChar A e = false := jumpChar_eq_false_iff.2 hj
      have hdom' : (Nat.rfind fun _ => (fun m => decide (m = 0)) <$> f e).Dom := by
        rw [hfe, this]
        exact rfind_const_dom.2 rfl
      change (Phi A e e).Dom
      rw [hval]
      exact hdom'
  by_cases hj : Jump A e
  · exact (hdom.1 hj) hj
  · exact hj (hdom.2 hj)

/-! ## The oracle is computable in its jump -/

/-- The master machine behind the reduction of `A` to its jump: given `n`, an oracle segment and
an input, it halts with value `0` if the oracle says `true` at `n`, and diverges otherwise. -/
def queryMaster : ℕ →. ℕ := fun z =>
  (((segQuery z.unpair.2.unpair.1 z.unpair.1).bind fun b => if b then some 0 else none :
    Option ℕ) : Part ℕ)

theorem partrec_queryMaster : Nat.Partrec queryMaster := by
  have hq : Primrec fun z : ℕ => segQuery z.unpair.2.unpair.1 z.unpair.1 :=
    primrec_segQuery.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.fst.comp Primrec.unpair)
  have hmain : Computable fun z : ℕ =>
      (segQuery z.unpair.2.unpair.1 z.unpair.1).bind fun b => if b then some 0 else none :=
    Primrec.to_comp <| Primrec.option_bind hq
      (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const true))
        (Primrec.const (some 0)) (Primrec.const none)).to₂
  exact Partrec.nat_iff.1 (Computable.ofOption hmain)

/-- A code for the master machine. -/
noncomputable def queryCode : Code := (Code.exists_code.1 partrec_queryMaster).choose

theorem eval_queryCode : Code.eval queryCode = queryMaster :=
  (Code.exists_code.1 partrec_queryMaster).choose_spec

/-- The index of the machine that queries the oracle at `n` and diverges on a negative answer. -/
noncomputable def queryIndex (n : ℕ) : ℕ := encode (Code.curry queryCode n)

/-- The partial function that the `n`-th query machine computes with oracle `A`. -/
def queryTarget (A : ℕ → Bool) (n : ℕ) : ℕ →. ℕ := fun _ =>
  if A n then Part.some 0 else Part.none

theorem simulates_queryCurry (A : ℕ → Bool) (n : ℕ) :
    Simulates A (Code.eval (Code.curry queryCode n)) (queryTarget A n) := by
  have hval : ∀ s x, Code.eval (Code.curry queryCode n) (Nat.pair (segNum A s) x) =
      (((segQuery (segNum A s) n).bind fun b => if b then some 0 else none : Option ℕ) :
        Part ℕ) := by
    intro s x
    rw [Code.eval_curry, eval_queryCode]
    simp [queryMaster]
  constructor
  · intro x y s t hst hy
    rw [hval] at hy ⊢
    simp only [Part.mem_coe, Option.mem_def, Option.bind_eq_some_iff] at hy ⊢
    obtain ⟨b, hb, hy⟩ := hy
    exact ⟨b, segQuery_mono hst hb, hy⟩
  · intro x y
    constructor
    · intro hy
      refine ⟨n + 1, ?_⟩
      rw [hval]
      simp only [queryTarget] at hy
      by_cases hA : A n
      · simp only [hA, if_true] at hy
        have hy0 : y = 0 := by simpa using hy
        simp [segQuery_segNum_of_lt (Nat.lt_succ_self n), hA, hy0]
      · simp [hA] at hy
    · rintro ⟨s, hs⟩
      rw [hval] at hs
      simp only [Part.mem_coe, Option.mem_def, Option.bind_eq_some_iff] at hs
      obtain ⟨b, hb, hy⟩ := hs
      rw [segQuery_segNum] at hb
      by_cases hns : n < s
      · simp only [hns, if_true, Option.some_inj] at hb
        subst hb
        by_cases hA : A n
        · simp only [hA, if_true, Option.some_inj] at hy
          simp [queryTarget, hA, ← hy]
        · simp [hA] at hy
      · simp [hns] at hb

theorem phi_queryIndex (A : ℕ → Bool) (n x : ℕ) :
    Phi A (queryIndex n) x = queryTarget A n x := by
  have h := evalOracle_eq_of_simulates (simulates_queryCurry A n)
  rw [queryIndex, Phi_encode]
  exact congrFun h x

/-- The `n`-th query machine halts on its own index exactly when `n` belongs to the oracle. -/
theorem jumpChar_queryIndex (A : ℕ → Bool) (n : ℕ) : jumpChar A (queryIndex n) = A n := by
  have hdom : Jump A (queryIndex n) ↔ A n = true := by
    unfold Jump
    rw [phi_queryIndex]
    by_cases hA : A n
    · simp [queryTarget, hA]
    · simp [queryTarget, hA]
  by_cases hA : A n
  · simp [jumpChar_eq_true_iff, hdom.2 hA, hA]
  · have : ¬ Jump A (queryIndex n) := fun h => by simp [hdom.1 h] at hA
    simp [jumpChar_eq_false_iff.2 this, Bool.eq_false_iff.2 hA]

theorem computable_queryIndex : Computable queryIndex := by
  have : Primrec fun n : ℕ => Code.curry queryCode n :=
    Primrec₂.comp Code.primrec₂_curry (Primrec.const queryCode) Primrec.id
  exact (Primrec.encode.comp this).to_comp

/-- **The oracle is computable in its jump.** -/
theorem recursiveIn_jumpChar (A : ℕ → Bool) :
    RecursiveIn {oracleFun (jumpChar A)} (oracleFun A) := by
  have horacle : RecursiveIn {oracleFun (jumpChar A)} (oracleFun (jumpChar A)) :=
    RecursiveIn.oracle _ (by simp)
  have hidx : RecursiveIn {oracleFun (jumpChar A)} (fun n => (queryIndex n : Part ℕ)) :=
    RecursiveIn.iff_nat.mpr
      (Nat.Partrec.recursiveIn (Partrec.nat_iff.1 computable_queryIndex.partrec))
  have hcomp := recIn_comp horacle hidx
  have hEq : (fun n => ((queryIndex n : ℕ) : Part ℕ) >>= oracleFun (jumpChar A)) =
      oracleFun A := by
    funext n
    have hb : ((queryIndex n : ℕ) : Part ℕ) >>= oracleFun (jumpChar A)
        = oracleFun (jumpChar A) (queryIndex n) := Part.bind_some _ _
    rw [hb]
    simp [oracleFun, jumpChar_queryIndex]
  rwa [hEq] at hcomp

/-! ## The jump in the language of Turing degrees -/

/-- `A ≤ᵀ A'`. -/
theorem turingReducible_jumpChar (A : ℕ → Bool) : oracleFun A ≤ᵀ oracleFun (jumpChar A) :=
  recursiveIn_jumpChar A

/-- `A' ≰ᵀ A`. -/
theorem not_turingReducible_jumpChar (A : ℕ → Bool) :
    ¬ (oracleFun (jumpChar A) ≤ᵀ oracleFun A) :=
  not_recursiveIn_jumpChar A

/-- **The jump theorem**: the Turing degree of the jump is strictly above the degree of the
oracle, so there is no greatest Turing degree. -/
theorem turingDegree_lt_jump (A : ℕ → Bool) :
    toAntisymmetrization TuringReducible (oracleFun A) <
      toAntisymmetrization TuringReducible (oracleFun (jumpChar A)) := by
  rw [lt_iff_le_and_ne]
  constructor
  · exact toAntisymmetrization_le_toAntisymmetrization_iff.2 (turingReducible_jumpChar A)
  · intro hEq
    have hle : oracleFun (jumpChar A) ≤ᵀ oracleFun A :=
      toAntisymmetrization_le_toAntisymmetrization_iff.1 (le_of_eq hEq.symm)
    exact not_turingReducible_jumpChar A hle

end Oracle
end Lambda
