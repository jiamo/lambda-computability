import Start.OracleSim

/-
**Two presentations of the Turing degrees, side by side.**

github.com/openai/math (commit adc7f1241, Apache-2.0), directory
`lean/OAI/Computability/DegreeRigidity/Model.lean`, family 241, paper "Rigidity of the Turing
degrees", defines

```
abbrev Oracle := ℕ → Bool
def oracleFunction (A : Oracle) : ℕ →. ℕ := fun n => Part.some (if A n then 1 else 0)
def Reduces (A B : Oracle) : Prop := TuringReducible (oracleFunction A) (oracleFunction B)
def Degree := Antisymmetrization Oracle Reduces
def MainTheorem : Prop := ∀ π : Degree ≃o Degree, ∀ a : Degree, π a = a
```

This library (`Start/OracleSim.lean` and its users) works with
`Lambda.Oracle.oracleFun (A : ℕ → Bool) : ℕ →. ℕ := fun n => Part.some (if A n then 1 else 0)`
and states degree results in mathlib's `TuringDegree = Antisymmetrization (ℕ →. ℕ) TuringReducible`.

The definitions below restate the openai/math model (only its five definitions, not its proofs;
see `NOTICE`) under the names `SetReduces`, `SetDegree`, `SetDegreeRigidity`, and settle how the
two relate:

* `oracleFunction_eq` — their `oracleFunction` *is* our `oracleFun` (`rfl`);
* `setReduces_iff` — their `Reduces` is our `TuringReducible` on `oracleFun`, by unfolding;
* `SetDegree.toTuringDegree` — their `Degree` is **not** mathlib's `TuringDegree` but a different
  quotient (of total `0/1` oracles instead of partial functions); it maps into it by an order
  embedding, so neither type is a wrapper of the other: theirs is the sub-order of the degrees
  of sets.
-/

set_option autoImplicit false

namespace Lambda
namespace Oracle

/-- The openai/math `oracleFunction`, restated. -/
def oracleFunctionOAI (A : ℕ → Bool) : ℕ →. ℕ := fun n => Part.some (if A n then 1 else 0)

theorem oracleFunction_eq : oracleFunctionOAI = oracleFun := rfl

/-- The openai/math `Reduces`: Turing reducibility between sets. -/
def SetReduces (A B : ℕ → Bool) : Prop := TuringReducible (oracleFun A) (oracleFun B)

theorem setReduces_iff (A B : ℕ → Bool) :
    SetReduces A B ↔ TuringReducible (oracleFun A) (oracleFun B) := Iff.rfl

instance : IsPreorder (ℕ → Bool) SetReduces where
  refl _ := TuringReducible.refl _
  trans _ _ _ h k := TuringReducible.trans h k

/-- The openai/math `Degree`: the Turing degrees *of sets*. -/
def SetDegree := Antisymmetrization (ℕ → Bool) SetReduces

instance : PartialOrder SetDegree :=
  @instPartialOrderAntisymmetrization (ℕ → Bool)
    { le := SetReduces
      lt A B := SetReduces A B ∧ ¬ SetReduces B A
      le_refl _ := TuringReducible.refl _
      le_trans _ _ _ h k := TuringReducible.trans h k }

/-- The openai/math `MainTheorem` (rigidity), restated as a proposition.  It is proved in
`Start/RigidityBridge.lean` (`setDegreeRigidity`) from the absorbed upstream development. -/
def SetDegreeRigidity : Prop := ∀ π : SetDegree ≃o SetDegree, ∀ a : SetDegree, π a = a

/-- The degree of a set in the openai/math quotient. -/
def setDegree (A : ℕ → Bool) : SetDegree := toAntisymmetrization SetReduces A

/-- The map from degrees of sets to mathlib's Turing degrees, `deg A ↦ deg (oracleFun A)`. -/
def SetDegree.toTuringDegreeFun : SetDegree → TuringDegree :=
  Quotient.lift (fun A => toAntisymmetrization TuringReducible (oracleFun A))
    (fun _ _ h => Quotient.sound h)

@[simp] theorem SetDegree.toTuringDegreeFun_mk (A : ℕ → Bool) :
    SetDegree.toTuringDegreeFun (setDegree A) =
      toAntisymmetrization TuringReducible (oracleFun A) := rfl

theorem SetDegree.toTuringDegreeFun_le_iff (a b : SetDegree) :
    a.toTuringDegreeFun ≤ b.toTuringDegreeFun ↔ a ≤ b := by
  induction a using Quotient.inductionOn with
  | h A =>
    induction b using Quotient.inductionOn with
    | h B => exact Iff.rfl

/-- **The degrees of sets embed into mathlib's Turing degrees as an order.** -/
def SetDegree.toTuringDegree : SetDegree ↪o TuringDegree :=
  OrderEmbedding.ofMapLEIff SetDegree.toTuringDegreeFun SetDegree.toTuringDegreeFun_le_iff

/-- The range of the embedding is exactly the set of degrees containing a `0/1` oracle. -/
theorem SetDegree.range_toTuringDegree :
    Set.range SetDegree.toTuringDegree =
      {d | ∃ A : ℕ → Bool, d = toAntisymmetrization TuringReducible (oracleFun A)} := by
  ext d
  constructor
  · rintro ⟨a, rfl⟩
    induction a using Quotient.inductionOn with
    | h A => exact ⟨A, rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨setDegree A, rfl⟩

end Oracle
end Lambda
