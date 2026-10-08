import Start.RigidityMain
import Start.OracleDegreeBridge

/-!
# Rigidity of the degrees of sets, in this library's names

This module is this library's own.  `Start/Rigidity*.lean` absorb the upstream
`DegreeRigidity` development (family 241, "Rigidity of the Turing degrees"), whose end result is
`TuringRigidity.ManuscriptMain.rigidity : TuringRigidity.MainTheorem`.

`Start/OracleDegreeBridge.lean` had restated the upstream model as `Lambda.Oracle.SetDegree`
and the upstream main theorem as the proposition `Lambda.Oracle.SetDegreeRigidity`, without a
proof.  Here the two quotients are identified (`setDegreeOrderIso`, the identity on the
underlying type: both are `Antisymmetrization (ℕ → Bool) _` of the same relation), and
`setDegreeRigidity` proves `SetDegreeRigidity`.  Through the order embedding
`SetDegree.toTuringDegree` it is a statement about the degrees of sets inside mathlib's
`TuringDegree`.
-/

namespace Lambda
namespace Oracle

/-- The degrees of sets of `Start/OracleDegreeBridge.lean` are the upstream `Degree`; the two
quotients coincide definitionally. -/
def setDegreeOrderIso : SetDegree ≃o TuringRigidity.Degree where
  toEquiv := Equiv.refl _
  map_rel_iff' := Iff.rfl

/-- **Rigidity of the degrees of sets**: every order automorphism of the Turing degrees of
subsets of `ℕ` is the identity.  Proved from the absorbed upstream theorem
`TuringRigidity.ManuscriptMain.rigidity`. -/
theorem setDegreeRigidity : SetDegreeRigidity := by
  intro π a
  have h := TuringRigidity.ManuscriptMain.rigidity
    (setDegreeOrderIso.symm.trans (π.trans setDegreeOrderIso)) (setDegreeOrderIso a)
  simpa using h

end Oracle
end Lambda
