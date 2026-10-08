import Start.RigidityGenericTruth
import Start.RigidityGenericFiberIdeal
import Start.RigiditySourceIdentity

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Representation/GenericSourceTransfer.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.GenericSourceTransfer
open FiniteShuffle ShuffleRequirements PairGenericSelection GenericFactor GenericIdentity Set

@[simp] theorem triple_join (Y Z : Oracle) :
    GenericTruth.triple (join Y Z) = (Y,column false Z,column true Z) := by
  have hl : column false (join Y Z) = Y := by funext n; simp [column]
  have hr : column true (join Y Z) = Z := by funext n; simp [column]
  simp [GenericTruth.triple,hl,hr]

theorem selected_borel_truth (p : OracleCode) (P : Oracle)
    (E : ℕ → List Bool → Prop) (hE : ∀ n, DenseOpen (E n)) :
    ∃ U : Set Oracle, IsOpen U ∧
    ∃ F : ℕ → List Bool → Prop, (∀ n, DenseOpen (F n)) ∧
    ∃ Z : {Y : Oracle // GenericFor F Y} → Oracle, Measurable Z ∧
      (∀ Y b, GenericFor E (column b (Z Y)) ∧ GenericCoding.InfiniteOdd (column b (Z Y)) ∧
        ∀ X, GenericFor E (GenericCoding.code X (column b (Z Y)))) ∧
      (∀ Y a, a ≤ degree Y.val ↔
        a ≤ degree (join Y.val (column false (Z Y))) ∧
        a ≤ degree (join Y.val (column true (Z Y)))) ∧
      ∀ Y, SourceEquation p P (Y.val,column false (Z Y),column true (Z Y)) ↔
        join Y.val (Z Y) ∈ U := by
  obtain ⟨U,hU,D,hD,htruth⟩ := GenericTruth.sourceEquation_generic_truth p P
  obtain ⟨hF,Z,hZ,hjoint,hgen,hI⟩ := borel_joint_ideal_selection D E hD hE
  refine ⟨U,hU,FirstFamily D,hF,Z,hZ,hgen,hI,?_⟩
  intro Y
  simpa only [triple_join] using htruth (join Y.val (Z Y)) (hjoint Y)

theorem recover_at (π : Degree ≃o Degree) (p : OracleCode) (P Y G0 G1 : Oracle)
    (hG0 : RepresentsAt π p P G0) (hG1 : RepresentsAt π p P G1)
    (hC0 : RepresentsAt π p P (GenericCoding.code Y G0))
    (hC1 : RepresentsAt π p P (GenericCoding.code Y G1))
    (hi0 : GenericCoding.InfiniteOdd G0) (hi1 : GenericCoding.InfiniteOdd G1)
    (hI : PrincipalIntersection Y (join Y G0) (join Y G1))
    (he : SourceEquation p P (Y,G0,G1)) : RepresentsAt π p P Y :=
  (source_5_5_iff π p P Y G0 G1 hG0 hG1 hC0 hC1 hi0 hi1 hI).mp he

end TuringRigidity.GenericSourceTransfer

