/-
**The join of two oracles.**

The *join* `A ⊕ B` of two oracles interleaves them, `A` on the even positions and `B` on the odd
ones (`Lambda.Oracle.joinOracle`).  It is an upper bound of both in the Turing ordering
(`Lambda.Oracle.turingReducible_joinOracle_left`, `…_right`) and the least one
(`Lambda.Oracle.joinOracle_least`), so the Turing degrees form an upper semilattice
(`Lambda.Oracle.turingDegree_isLUB_join`).

Together with `Start/KleenePost.lean` — where two incomparable degrees are built — this says that
the degrees are a genuinely branching, non-linear order with binary suprema.
-/

import Start.OracleSound

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Oracle

open scoped Computability

/-- The join `A ⊕ B` of two oracles: `A` on the even positions, `B` on the odd ones. -/
def joinOracle (A B : ℕ → Bool) : ℕ → Bool := fun n => if n % 2 = 0 then A (n / 2) else B (n / 2)

@[simp] theorem joinOracle_two_mul (A B : ℕ → Bool) (n : ℕ) :
    joinOracle A B (2 * n) = A n := by
  have h1 : (2 * n) % 2 = 0 := by omega
  have h2 : (2 * n) / 2 = n := by omega
  simp [joinOracle, h1, h2]

@[simp] theorem joinOracle_two_mul_succ (A B : ℕ → Bool) (n : ℕ) :
    joinOracle A B (2 * n + 1) = B n := by
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  simp [joinOracle, h1, h2]

theorem turingReducible_joinOracle_left (A B : ℕ → Bool) :
    oracleFun A ≤ᵀ oracleFun (joinOracle A B) := by
  refine recursiveIn_of_eq (recursiveIn_compPartrec (recursiveIn_oracleFun (A := joinOracle A B))
    (Primrec.to_comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))) fun n => ?_
  simp [oracleFun]

theorem turingReducible_joinOracle_right (A B : ℕ → Bool) :
    oracleFun B ≤ᵀ oracleFun (joinOracle A B) := by
  refine recursiveIn_of_eq (recursiveIn_compPartrec (recursiveIn_oracleFun (A := joinOracle A B))
    (Primrec.to_comp (Primrec.succ.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)))) fun n => ?_
  simp [oracleFun]

/-- **The join is the least upper bound.**  Any oracle computing both `A` and `B` computes their
join. -/
theorem joinOracle_least {A B : ℕ → Bool} {f : ℕ →. ℕ} (hA : oracleFun A ≤ᵀ f)
    (hB : oracleFun B ≤ᵀ f) : oracleFun (joinOracle A B) ≤ᵀ f := by
  have hhalf : Computable fun n : ℕ => n / 2 :=
    Primrec.to_comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
  have hA' : RecursiveIn {f} fun n => oracleFun A (n / 2) :=
    recursiveIn_compPartrec hA hhalf
  have hB' : RecursiveIn {f} fun n => oracleFun B (n / 2) :=
    recursiveIn_compPartrec hB hhalf
  have hpair := recIn_pair hA' hB'
  have hsel : Nat.Partrec fun w : ℕ =>
      (Part.some (if w.unpair.1 % 2 = 0 then w.unpair.2.unpair.1 else w.unpair.2.unpair.2) :
        Part ℕ) := by
    refine Partrec.nat_iff.1 (Primrec.to_comp (Primrec.ite ?_ ?_ ?_)).partrec
    · exact Primrec.eq.comp
        (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 2))
        (Primrec.const 0)
    · exact Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
    · exact Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  refine recursiveIn_of_eq (recursiveIn_bindPair (recursiveIn_of_partrec hsel) hpair) fun n => ?_
  simp only [oracleFun, Seq.seq, Part.map_some, Nat.unpair_pair, joinOracle]
  by_cases h : n % 2 = 0 <;> simp [h]

/-- The degree of the join is the least upper bound of the two degrees. -/
theorem turingDegree_isLUB_join (A B : ℕ → Bool) :
    IsLUB {toAntisymmetrization TuringReducible (oracleFun A),
        toAntisymmetrization TuringReducible (oracleFun B)}
      (toAntisymmetrization TuringReducible (oracleFun (joinOracle A B))) := by
  constructor
  · rintro d (rfl | rfl)
    · exact toAntisymmetrization_le_toAntisymmetrization_iff.2
        (turingReducible_joinOracle_left A B)
    · exact toAntisymmetrization_le_toAntisymmetrization_iff.2
        (turingReducible_joinOracle_right A B)
  · rintro d hd
    induction d using Quotient.inductionOn with
    | h f =>
        have hA : oracleFun A ≤ᵀ f := toAntisymmetrization_le_toAntisymmetrization_iff.1
          (hd (Set.mem_insert _ _))
        have hB : oracleFun B ≤ᵀ f := toAntisymmetrization_le_toAntisymmetrization_iff.1
          (hd (Set.mem_insert_of_mem _ rfl))
        exact toAntisymmetrization_le_toAntisymmetrization_iff.2 (joinOracle_least hA hB)

end Oracle
end Lambda
