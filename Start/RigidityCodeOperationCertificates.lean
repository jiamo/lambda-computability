import Start.RigiditySumCertificates

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/OrdinalCodes/CodeOperationCertificates.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem codePowerAt_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (y x : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hc : OmegaPowerCertificates M (e x)) (hy : e y = (Ordinal.omega0 ^ (e x).rank).toZFSet) :
    (codePowerAt y x).Sat (M : Set ZFSet) e := by
  rw [codePowerAt,SentenceForm.sat_rename]
  exact omegaPowerSentence_of_certificates M hM hω _ (fun i => he _) hc hy

theorem codeSumAt_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (c a b : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (α β : Ordinal.{u}) (ha : e a = α.toZFSet) (hb : e b = β.toZFSet)
    (hc : SumCertificates M α β) (hy : e c = (α+β).toZFSet) :
    (codeSumAt c a b).Sat (M : Set ZFSet) e := by
  rw [codeSumAt,SentenceForm.sat_rename]
  exact sumSentence_of_certificates M hM hω _ (fun i => he _) α β ha hb hc hy


theorem codeScaleAt_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (twice : Bool) (y x : ℕ)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a : Ordinal.{u}) (ha : e x = a.toZFSet)
    (hc : twice = true → SumCertificates M a a) (hy : e y = (codeScale twice a).toZFSet) :
    (codeScaleAt twice y x).Sat (M : Set ZFSet) e := by
  cases twice with
  | false => exact hy.trans ha.symm
  | true =>
    change (doubleSentence.rename (fun i => if i = 0 then y else x)).Sat (M : Set ZFSet) e
    rw [SentenceForm.sat_rename]
    rw [doubleSentence,SentenceForm.sat_rename]
    exact sumSentence_of_certificates M hM hω
      (fun i => e (if (if i = 0 then 0 else 1) = 0 then y else x))
      (fun i => he _) a a ha ha (hc rfl)
      (by simpa only [codeScale,↓reduceIte,Ordinal.mul_two] using hy)

end TuringRigidity.OrdinalCoding

