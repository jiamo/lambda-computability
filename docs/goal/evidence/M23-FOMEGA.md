# M23-FOMEGA — classification of kinds and constructors (partial; row stays open)

Module: `Start/PTSFOmegaKinds.lean` (new; imports `Start.PTSCube`).

```lean
theorem PureTypeSystem.not_hasType_conv_box (f : CubeFeatures) {Γ A s}
    (hA : HasType (cubeSpec f) Γ A (.sort s)) (hc : Converts A (.sort .box)) : False
inductive PureTypeSystem.IsKind : Expr Srt → Prop   -- ∗ | Π K₁ K₂
theorem PureTypeSystem.isKind_of_hasType_box (f : CubeFeatures) (hdep : f.dep = false)
    {Γ K} (h : HasType (cubeSpec f) Γ K (.sort .box)) : IsKind K
theorem PureTypeSystem.hasType_box_iff_isKind {Γ} (hΓ : ValidContext (cubeSpec systemFOmega) Γ)
    (K : Expr Srt) : HasType (cubeSpec systemFOmega) Γ K (.sort .box) ↔ IsKind K
inductive PureTypeSystem.IsConstr : (Nat → Prop) → Expr Srt → Prop
  -- type variables, arrows, ∀ over kinds, λ over kinds, applications
theorem PureTypeSystem.isConstr_of_hasType (f : CubeFeatures) (hdep : f.dep = false)
    (hops : f.ops = true) {Γ M T} (h : HasType (cubeSpec f) Γ M T) :
    HasType (cubeSpec f) Γ T (.sort .box) → IsConstr (kindMask Γ) M
theorem PureTypeSystem.systemFOmega_constr {Γ A K}
    (hA : HasType (cubeSpec systemFOmega) Γ A K)
    (hK : HasType (cubeSpec systemFOmega) Γ K (.sort .box)) :
    IsKind K ∧ IsConstr (kindMask Γ) A
```

Strong normalization of `F^ω` is **not** proved; the row stays `TODO_READY`. The next missing
construction (named in the row's open boundary) is the interpretation of kinds as candidate
spaces and of constructors under kind-respecting valuations.
