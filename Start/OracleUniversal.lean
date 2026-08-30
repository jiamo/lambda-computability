/-
**The relativised enumeration theorem.**

There is a single machine that runs all of them: the partial function

```
(e, x) ↦ Φ_e^A(x)
```

is itself recursive in `A` (`Lambda.Oracle.recursiveIn_universal`), so the indexing `Φ^A` of
`Start/OracleMachine.lean` has a universal machine relative to `A`
(`Lambda.Oracle.exists_universal_index`).

The proof is the one of `Start/OracleSound.lean`, carried out uniformly in the code: the stage
function now reads the code off its input, which is harmless because `Code.evaln` is primitive
recursive in the code as well as in the fuel and the input.

The immediate consequence is that the Turing jump is *recursively enumerable in* its oracle
(`Lambda.Oracle.jump_re_in`): there is one index `j` with `A' = { e | Φ_j^A(e) ↓ }`.  Together with
`Lambda.Oracle.not_recursiveIn_jumpChar` this is the relativised halting theorem: `A'` is r.e. in
`A` but not computable in `A`.
-/

import Start.OracleJump
import Start.OracleSound

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Oracle

open Encodable Denumerable
open Nat.Partrec (Code)
open scoped Computability

/-- The stage function of the universal machine: on input `Nat.pair (Nat.pair e x) s` it runs one
stage of the `e`-th machine on `x`. -/
noncomputable def ustageFun (A : ℕ → Bool) : ℕ →. ℕ := fun w =>
  Part.some (optEnc (oracleStep A (ofNat Code w.unpair.1.unpair.1) w.unpair.1.unpair.2 w.unpair.2))

theorem recursiveIn_ustageFun (A : ℕ → Bool) : RecursiveIn {oracleFun A} (ustageFun A) := by
  have hseg : RecursiveIn {oracleFun A} fun w : ℕ =>
      (Part.some (segNum A w.unpair.2.unpair.2) : Part ℕ) :=
    recursiveIn_compPartrec (recursiveIn_segNum A)
      (Primrec.to_comp (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp Primrec.unpair))))
  have hpost : Nat.Partrec fun u : ℕ =>
      (Part.some (optEnc (Code.evaln u.unpair.1.unpair.2.unpair.1
        (ofNat Code u.unpair.1.unpair.1.unpair.1)
        (Nat.pair u.unpair.2 u.unpair.1.unpair.1.unpair.2))) : Part ℕ) := by
    have hfuel : Primrec fun u : ℕ => u.unpair.1.unpair.2.unpair.1 :=
      Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
    have hcode : Primrec fun u : ℕ => ofNat Code u.unpair.1.unpair.1.unpair.1 :=
      (Primrec.ofNat Code).comp (Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
    have hinp : Primrec fun u : ℕ => Nat.pair u.unpair.2 u.unpair.1.unpair.1.unpair.2 :=
      Primrec₂.natPair.comp (Primrec.snd.comp Primrec.unpair)
        (Primrec.snd.comp (Primrec.unpair.comp
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
    have harg : Primrec fun u : ℕ =>
        ((u.unpair.1.unpair.2.unpair.1, ofNat Code u.unpair.1.unpair.1.unpair.1),
          Nat.pair u.unpair.2 u.unpair.1.unpair.1.unpair.2) :=
      Primrec.pair (Primrec.pair hfuel hcode) hinp
    exact Partrec.nat_iff.1
      (Primrec.to_comp (primrec_optEnc.comp (Code.primrec_evaln.comp harg))).partrec
  exact recursiveIn_of_eq (recursiveIn_bindPair (recursiveIn_of_partrec hpost) hseg)
    fun w => by simp [ustageFun, oracleStep]

/-- The search predicate of the universal machine. -/
noncomputable def usearchFun (A : ℕ → Bool) : ℕ →. ℕ := fun w =>
  Part.some (if optEnc (oracleStep A (ofNat Code w.unpair.1.unpair.1) w.unpair.1.unpair.2
    w.unpair.2) = 0 then 1 else 0)

/-- The value read off a stage of the universal machine. -/
noncomputable def uvalFun (A : ℕ → Bool) : ℕ →. ℕ := fun w =>
  Part.some (optEnc (oracleStep A (ofNat Code w.unpair.1.unpair.1) w.unpair.1.unpair.2
    w.unpair.2) - 1)

theorem recursiveIn_usearchFun (A : ℕ → Bool) : RecursiveIn {oracleFun A} (usearchFun A) := by
  have hpost : Nat.Partrec fun u : ℕ =>
      (Part.some (if u.unpair.2 = 0 then 1 else 0) : Part ℕ) :=
    Partrec.nat_iff.1 (Primrec.to_comp (Primrec.ite
      (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 0))
      (Primrec.const 1) (Primrec.const 0))).partrec
  exact recursiveIn_of_eq
    (recursiveIn_bindPair (recursiveIn_of_partrec hpost) (recursiveIn_ustageFun A))
    fun w => by simp [ustageFun, usearchFun]

theorem recursiveIn_uvalFun (A : ℕ → Bool) : RecursiveIn {oracleFun A} (uvalFun A) := by
  have hpost : Nat.Partrec fun u : ℕ => (Part.some (u.unpair.2 - 1) : Part ℕ) :=
    Partrec.nat_iff.1 (Primrec.to_comp
      (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1))).partrec
  exact recursiveIn_of_eq
    (recursiveIn_bindPair (recursiveIn_of_partrec hpost) (recursiveIn_ustageFun A))
    fun w => by simp [ustageFun, uvalFun]

/-- **The relativised enumeration theorem.**  Running the `e`-th machine with oracle `A` on the
input `x` is, uniformly in `e` and `x`, a computation recursive in `A`. -/
theorem recursiveIn_universal (A : ℕ → Bool) :
    RecursiveIn {oracleFun A} fun v : ℕ => Phi A v.unpair.1 v.unpair.2 := by
  have hsearch := recIn_rfind (recursiveIn_usearchFun A)
  have h := recursiveIn_bindPair (recursiveIn_uvalFun A) hsearch
  refine recursiveIn_of_eq h fun v => ?_
  have hp : ∀ n : ℕ, ((fun m => decide (m = 0)) <$> usearchFun A (Nat.pair v n)) =
      Part.some (decide (oracleStep A (ofNat Code v.unpair.1) v.unpair.2 n ≠ none)) := by
    intro n
    cases hstep : oracleStep A (ofNat Code v.unpair.1) v.unpair.2 n with
    | none => simp [usearchFun, hstep]
    | some z => simp [usearchFun, hstep]
  ext y
  simp only [Phi]
  rw [Part.mem_bind_iff, mem_evalOracle_iff]
  constructor
  · rintro ⟨w, hw, hy⟩
    have hw' := Nat.mem_rfind.mp hw
    have h1 : true ∈
        Part.some (decide (oracleStep A (ofNat Code v.unpair.1) v.unpair.2 w ≠ none)) :=
      hp w ▸ hw'.1
    have hwsome : oracleStep A (ofNat Code v.unpair.1) v.unpair.2 w ≠ none :=
      of_decide_eq_true (Part.mem_some_iff.mp h1).symm
    have hval : uvalFun A (Nat.pair v w) =
        Part.some (optEnc (oracleStep A (ofNat Code v.unpair.1) v.unpair.2 w) - 1) := by
      simp only [uvalFun, Nat.unpair_pair]
    have hy' : y = optEnc (oracleStep A (ofNat Code v.unpair.1) v.unpair.2 w) - 1 :=
      Part.mem_some_iff.mp (hval ▸ hy)
    refine ⟨w, ?_, ?_⟩
    · cases hstep : oracleStep A (ofNat Code v.unpair.1) v.unpair.2 w with
      | none => exact absurd hstep hwsome
      | some z =>
          rw [hstep] at hy'
          simp only [optEnc_some, Nat.add_sub_cancel] at hy'
          exact congrArg some hy'.symm
    · intro m hm
      have h2 : false ∈
          Part.some (decide (oracleStep A (ofNat Code v.unpair.1) v.unpair.2 m ≠ none)) :=
        hp m ▸ hw'.2 (m := m) hm
      by_contra hne
      simp [hne] at h2
  · rintro ⟨s, hs, hlt⟩
    refine ⟨s, Nat.mem_rfind.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [hp]; simp [hs]
    · intro m hm
      rw [hp]; simp [hlt m hm]
    · simp only [uvalFun, Nat.unpair_pair, hs, optEnc_some, Nat.add_sub_cancel]
      exact Part.mem_some y

/-- There is a universal index: one machine that, given `Nat.pair e x`, simulates the `e`-th
machine on `x`. -/
theorem exists_universal_index (A : ℕ → Bool) :
    ∃ u : ℕ, ∀ e x : ℕ, Phi A u (Nat.pair e x) = Phi A e x := by
  obtain ⟨u, hu⟩ := exists_index_of_recursiveIn (recursiveIn_universal A)
  exact ⟨u, fun e x => by rw [hu]; simp only [Nat.unpair_pair]⟩

/-- **The jump is recursively enumerable in its oracle**: a single machine with oracle `A`
enumerates `A'`. -/
theorem jump_re_in (A : ℕ → Bool) : ∃ j : ℕ, ∀ e : ℕ, Jump A e ↔ (Phi A j e).Dom := by
  have hdiag : RecursiveIn {oracleFun A} fun e => Phi A e e := by
    refine recursiveIn_of_eq (recursiveIn_compPartrec (recursiveIn_universal A)
      (Primrec.to_comp (Primrec₂.natPair.comp Primrec.id Primrec.id))) fun e => ?_
    simp
  obtain ⟨j, hj⟩ := exists_index_of_recursiveIn hdiag
  exact ⟨j, fun e => by rw [Jump, hj]⟩

end Oracle
end Lambda
