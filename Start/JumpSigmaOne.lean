/-
**The jump is `Σ₁`-hard, uniformly in the oracle.**

`Start/OracleJump.lean` proves the two halves of the jump theorem: `A'` is not computable in `A`,
while `A` is computable in `A'`.  This file adds the third basic property of the jump, the one that
makes `∅'` *the* halting problem: every recursively enumerable predicate is many-one reducible to
`A'`, for **every** oracle `A`, and therefore is decidable relative to `A'`.

The reduction is the relativised `s-m-n` construction of `Start/OracleJump.lean`, but with the
oracle ignored altogether: given a partial recursive `f`, the machine `constMaster f` runs `f` on
the parameter that `Code.curry` has baked into it, no matter what oracle segment and input it is
handed.  Hence its index `k x` satisfies `Φ_{k x}^A(y) = f x` for every oracle `A` and every input
`y`, and in particular `k x ∈ A'` exactly when `f x` converges.

* `Lambda.Oracle.exists_index_const` — a computable indexing of the constant machines;
* `Lambda.Oracle.exists_index_repred` — for an r.e. predicate `P`, a computable `k` with
  `P x ↔ Jump A (k x)`;
* `Lambda.Oracle.manyOneReducible_jump` — `P ≤₀ A'`;
* `Lambda.Oracle.charOracle` — the characteristic function of a predicate;
* `Lambda.Oracle.turingReducible_jumpChar_of_repred` — `P ≤ᵀ A'`: an r.e. predicate is decidable
  relative to the jump of any oracle, in particular relative to `∅'`
  (`Lambda.Oracle.turingReducible_haltingOracle_of_repred`).
-/

import Start.OracleJump
import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Oracle

open Encodable Denumerable
open Nat.Partrec (Code)
open scoped Computability

/-! ## Machines that ignore their oracle and their input -/

/-- The master machine of a parametrised computation: on input `Nat.pair x w` it runs `f` on the
parameter `x`, ignoring `w` — which, in the coding of `Start/OracleMachine.lean`, carries both the
oracle segment and the real input. -/
def constMaster (f : ℕ →. ℕ) : ℕ →. ℕ := fun z => f z.unpair.1

theorem partrec_constMaster {f : ℕ →. ℕ} (hf : Nat.Partrec f) : Nat.Partrec (constMaster f) := by
  have : Partrec fun z : ℕ => f z.unpair.1 :=
    (Partrec.nat_iff.2 hf).comp (Primrec.fst.comp Primrec.unpair).to_comp
  exact Partrec.nat_iff.1 this

/-- **A computable indexing of the constant machines.**  For a partial recursive `f` there is a
computable `k` such that the machine `k x` computes the constant function `f x`, with any oracle
and on any input. -/
theorem exists_index_const {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    ∃ k : ℕ → ℕ, Computable k ∧ ∀ (A : ℕ → Bool) (x y : ℕ), Phi A (k x) y = f x := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 (partrec_constMaster hf)
  refine ⟨fun x => encode (Code.curry c x), ?_, ?_⟩
  · have : Primrec fun x : ℕ => Code.curry c x :=
      Primrec₂.comp Code.primrec₂_curry (Primrec.const c) Primrec.id
    exact (Primrec.encode.comp this).to_comp
  · intro A x y
    have hev : ∀ w, Code.eval (Code.curry c x) w = f x := by
      intro w
      rw [Code.eval_curry, hc]
      simp [constMaster]
    have hsim : Simulates A (Code.eval (Code.curry c x)) (fun _ => f x) := by
      constructor
      · intro w z s t _ hz
        rw [hev] at hz ⊢
        exact hz
      · intro w z
        constructor
        · intro hz
          exact ⟨0, by rw [hev]; exact hz⟩
        · rintro ⟨s, hs⟩
          rw [hev] at hs
          exact hs
    rw [Phi_encode]
    exact congrFun (evalOracle_eq_of_simulates hsim) y

/-! ## Every r.e. predicate reduces to the jump -/

/-- A recursively enumerable predicate is the domain of a partial recursive function. -/
theorem exists_partrec_dom {P : ℕ → Prop} (hP : REPred P) :
    ∃ f : ℕ →. ℕ, Nat.Partrec f ∧ ∀ x, (f x).Dom ↔ P x := by
  refine ⟨fun x => (Part.assert (P x) fun _ => Part.some 0), ?_, fun x =>
    ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩⟩
  have : Partrec fun x : ℕ => (Part.assert (P x) fun _ => Part.some (0 : ℕ)) := by
    have h := hP.map (f := fun x => Part.assert (P x) fun _ => Part.some ())
      (g := fun (_ : ℕ) (_ : Unit) => (0 : ℕ)) (Computable.const 0).to₂
    refine h.of_eq fun x => ?_
    apply Part.ext
    intro y
    simp [Part.assert]
  exact Partrec.nat_iff.1 this

/-- **The jump is `Σ₁`-hard.**  Every r.e. predicate is many-one reducible to the jump of *any*
oracle, by a reduction that does not depend on the oracle. -/
theorem exists_index_repred {P : ℕ → Prop} (hP : REPred P) :
    ∃ k : ℕ → ℕ, Computable k ∧ ∀ (A : ℕ → Bool) (x : ℕ), (P x ↔ Jump A (k x)) := by
  obtain ⟨f, hf, hdom⟩ := exists_partrec_dom hP
  obtain ⟨k, hk, hphi⟩ := exists_index_const hf
  refine ⟨k, hk, fun A x => ?_⟩
  have : Jump A (k x) ↔ (f x).Dom := by
    unfold Jump
    rw [hphi A x (k x)]
  rw [this, hdom]

/-- `P ≤₀ A'` for every r.e. predicate `P` and every oracle `A`. -/
theorem manyOneReducible_jump {P : ℕ → Prop} (hP : REPred P) (A : ℕ → Bool) :
    P ≤₀ Jump A := by
  obtain ⟨k, hk, hspec⟩ := exists_index_repred hP
  exact ⟨k, hk, fun x => hspec A x⟩

/-! ## Decidability relative to the jump -/

/-- The characteristic function of a predicate, as an oracle. -/
noncomputable def charOracle (P : ℕ → Prop) : ℕ → Bool := fun x =>
  haveI := Classical.dec (P x)
  decide (P x)

@[simp] theorem charOracle_eq_true_iff {P : ℕ → Prop} {x : ℕ} :
    charOracle P x = true ↔ P x := by
  simp [charOracle]

/-- **An r.e. predicate is decidable relative to the jump of any oracle.** -/
theorem turingReducible_jumpChar_of_repred {P : ℕ → Prop} (hP : REPred P) (A : ℕ → Bool) :
    oracleFun (charOracle P) ≤ᵀ oracleFun (jumpChar A) := by
  obtain ⟨k, hk, hspec⟩ := exists_index_repred hP
  have horacle : RecursiveIn {oracleFun (jumpChar A)} (oracleFun (jumpChar A)) :=
    RecursiveIn.oracle _ (by simp)
  have hidx : RecursiveIn {oracleFun (jumpChar A)} (fun n => (k n : Part ℕ)) :=
    RecursiveIn.iff_nat.mpr (Nat.Partrec.recursiveIn (Partrec.nat_iff.1 hk.partrec))
  have hcomp := recIn_comp horacle hidx
  have hEq : (fun n => ((k n : ℕ) : Part ℕ) >>= oracleFun (jumpChar A)) =
      oracleFun (charOracle P) := by
    funext n
    have hb : ((k n : ℕ) : Part ℕ) >>= oracleFun (jumpChar A)
        = oracleFun (jumpChar A) (k n) := Part.bind_some _ _
    rw [hb]
    have hval : jumpChar A (k n) = charOracle P n := by
      by_cases hPn : P n
      · have : Jump A (k n) := (hspec A n).1 hPn
        simp [jumpChar_eq_true_iff.2 this, charOracle, hPn]
      · have : ¬ Jump A (k n) := fun h => hPn ((hspec A n).2 h)
        simp [jumpChar_eq_false_iff.2 this, charOracle, hPn]
    simp only [oracleFun, hval]
  rwa [hEq] at hcomp

/-- The halting oracle `∅'`: the jump of the empty oracle. -/
noncomputable def haltingOracle : ℕ → Bool := jumpChar (fun _ => false)

/-- **Every r.e. predicate is decidable relative to `∅'`.** -/
theorem turingReducible_haltingOracle_of_repred {P : ℕ → Prop} (hP : REPred P) :
    oracleFun (charOracle P) ≤ᵀ oracleFun haltingOracle :=
  turingReducible_jumpChar_of_repred hP _

end Oracle
end Lambda
