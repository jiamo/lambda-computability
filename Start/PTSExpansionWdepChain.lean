import Start.PTSExpansionBeyondPoll

/-!
# Series V, round 1, part B: the dependent rule of `Wdep` reaches non-normalizing `o`-types

`Wdep` adds the rule `(o, t, t)` to `W`.  In the Stage B induction (`Stratification.core_aux`)
this rule gives exactly two calls that go down a level: the domain of a product `Π x:A. B : t`
with `A : o`, and the argument of an application whose head has such a product type.  The
object-erasure strategy would treat those subjects (`o`-types and objects) by a separate inner
induction.  `Wdep_typeA_domain` records why an inner induction cannot be bought from
normalization: the closed `o`-type `typeA` (Hurkens' term applied to `o`), which has no normal
form, is the domain of a well-typed `(o, t, t)`-product.
-/

set_option autoImplicit false

namespace PureTypeSystem

namespace BeyondPoll

theorem typeA_typed_Wdep : HasType Wdep ([]) typeA (.sort .o) :=
  typeA_typed.monotone (fun _ _ h => h) (fun _ _ _ h => Or.inl h)

/-- **A non-normalizing `o`-type is the domain of a dependent product of `Wdep`**:
`⊢ Π x : typeA. o : t` through the rule `(o, t, t)`, and `typeA` has no normal form. -/
theorem Wdep_typeA_domain :
    HasType Wdep ([]) (.pi typeA (.sort .o)) (.sort .t) ∧ ¬ WeaklyNormalizing typeA := by
  refine ⟨?_, W_type_not_wn.2⟩
  have hax : HasType Wdep ([]) (.sort .o) (.sort .t) := .ax (Or.inl ⟨rfl, rfl⟩)
  have hB : HasType Wdep (typeA :: ([] : List (Expr WSort))) (.sort .o) (.sort .t) := by
    have := HasType.weaken hax typeA_typed_Wdep
    simpa [Expr.rename] using this
  exact .product typeA_typed_Wdep hB (Or.inr ⟨rfl, rfl, rfl⟩)

end BeyondPoll

end PureTypeSystem
