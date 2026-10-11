# M23-FOMEGA — System F-omega is strongly normalizing

```lean
theorem PureTypeSystem.systemFOmega_stronglyNormalizing :
    SystemStronglyNormalizing (cubeSpec systemFOmega)       -- Start/CoCSN.lean
```

Proved from `coc_stronglyNormalizing` by `cube_sn_mono` (the route sanctioned by the task
instruction for Geuvers' model).  The model of `Start/CoCModel.lean` is a reducibility-candidate
model indexed by kinds: candidate spaces `V k` over kind skeletons (saturated sets at `∗`,
functions between candidate spaces at products of kinds), kind-respecting valuations, and the
interpretation of constructors with its substitution lemma (`interp_subst`) and its invariance
under conversion (`interp_conv`).  See `docs/goal/evidence/M23-COC-SN.md`.

`#print axioms PureTypeSystem.systemFOmega_stronglyNormalizing`: `[propext, Quot.sound]`.

The earlier classification of `Start/PTSFOmegaKinds.lean` (`hasType_box_iff_isKind`,
`isConstr_of_hasType`, `systemFOmega_constr`) is unchanged.
