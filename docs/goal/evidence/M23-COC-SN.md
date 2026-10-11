# M23-COC-SN — strong normalization of the calculus of constructions

Modules (new): `Start/CoCModel.lean` (syntactic model), `Start/CoCSN.lean` (typing side and
terminal theorems).  Both are imported by `Start.lean` and registered in `Start/Capstones.lean`.

Route: Geuvers' saturated-set model ("A short and flexible proof of strong normalization for the
calculus of constructions").  Not the Geuvers–Nederhof translation.

## Terminal statements

```lean
theorem PureTypeSystem.coc_stronglyNormalizing : SystemStronglyNormalizing (cubeSpec coc)
theorem PureTypeSystem.cube_stronglyNormalizing (f : CubeFeatures) :
    SystemStronglyNormalizing (cubeSpec f)          -- cube_sn_mono (le_coc f)
theorem PureTypeSystem.systemFOmega_stronglyNormalizing :
    SystemStronglyNormalizing (cubeSpec systemFOmega)
theorem PureTypeSystem.coc_consistent :
    ¬ ∃ M, HasType (cubeSpec coc) ([]) M (.pi (.sort .star) (.var 0))
```

`#print axioms`: `coc_stronglyNormalizing`, `cube_stronglyNormalizing`,
`systemFOmega_stronglyNormalizing`: `[propext, Quot.sound]`; `coc_consistent`:
`[propext, Classical.choice, Quot.sound]`.  No hypothesis, no structure field, no use of
`SystemWeaklyNormalizing` or `weak_implies_strong`; `Start/PTSBasic.lean` is unchanged.

## Structure of the proof

* (a) candidate spaces: `CoC.Sk` (kind skeletons `∗`, `arrO k` for a product over a type,
  `arr a k` for a product over a kind), `CoC.V`, `CoC.Sat` (saturated sets for the PTS's own
  `Beta`, which also reduces annotations and products), `CoC.Cand`, valuations `CoC.Val`,
  `CoC.interp` with `interp_rename`, `interp_subst`, `interp_agree`, `interp_cand`.
* (c) classification: syntactic classifier `CoC.cl` (kind / constructor / object, with skeletons),
  `cl_subst` (purely syntactic), `CoC.type_unique` (uniqueness of types in every corner),
  `CoC.kind_cl`, `CoC.not_kind`, `CoC.kind_conv`, `CoC.classify`
  (`Γ ⊢ M : T`, `T ≠ □` ⟹ `cl M = bindC (cl T)`), `CoC.cl_beta`, `CoC.wc_of_hasType`.
  Kinds such as `Π x:A. K` are read through their skeleton (`arrO`).
* invariance: `CoC.interp_beta`, `CoC.interp_conv`.
* (b)/(d) `CoC.fundamental`: `Γ ⊢ M : T`, `SemCtx Γ σ ξ` ⟹ `M[σ] ∈ ⟦T⟧ξ`, for every legal
  judgement (kinds, constructors and objects; `⟦□⟧` is the set of strongly normalizing
  expressions), hence `CoC.sn_of_hasType` and `CoC.systemStronglyNormalizing`.
* (e) consistency from SN and `no_normal_closed_bot`.

## Not done

(f) decidable type checking for coc is not started; the row's open boundary names the first
missing piece.
