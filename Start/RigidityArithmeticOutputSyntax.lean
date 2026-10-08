import Start.RigidityExtensionArithmeticRepresentative
import Start.RigidityArithmeticRelations
import Start.RigidityArithmeticSetSyntax

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Computability/ArithmeticOutputSyntax.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.ExtensionArithmeticRepresentative
open OracleJump UniformArithmetic CommonIdeal IndexMatrix TableIndices BoundedSetTheory Encodable
open PersistentRestrictions

theorem fixed_output_arithmetic (d k : ℕ) :
    Arith (fun O _ => Represents (iterate (join (O 0) (O 1)) k) (machine d) (O 2)) :=
  represents_arith (parameter_arith 2)
    (iterate_arith (join_arith (parameter_arith 0) (parameter_arith 1)) k) (Primrec.const d)

theorem fixed_output_bounded (d k : ℕ) :
    ∃ φ : Formula, DefinesArithmetic.{0} φ
      (fun O _ => Represents (iterate (join (O 0) (O 1)) k) (machine d) (O 2)) :=
  arithmetic_bounded_definition (fixed_output_arithmetic d k)

theorem extension_table_program (I J : CountableIdeal)
    (hIJ : I.carrier ⊆ J.carrier) (ρ : I ≃o I) (σ : J ≃o J)
    (he : Extends hIJ ρ σ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (A R : Oracle) (hA : degree A ∈ J.carrier)
    (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero),hz⟩).val) :
    ∃ X : Oracle, degree X = (σ ⟨degree A,hA⟩).val ∧
      ∃ d : ℕ, Represents (iterate (join A R) 5) (machine d) X := by
  obtain ⟨X,hX,hred,_⟩ := extension_literal_join_program I J hIJ ρ σ he hz A R hA hR
  obtain ⟨c,hc⟩ := (TableIndices.reduces_iff_represents X _).mp hred
  exact ⟨X,hX,encode c,by simpa only [machine_encode] using hc⟩

end TuringRigidity.ExtensionArithmeticRepresentative

