# M23-PTS — the lambda cube as one family of pure type systems

**Status:** DONE_STRONG.

Foundation: the pure type system framework absorbed from openai/math (family 245,
`Start/PTSBasic.lean`, `Start/PTSTyping.lean`, `Start/PTSSubstitution.lean`,
`Start/PTSReduction.lean`; see `NOTICE`), which supplies the generic typing judgement,
substitution, confluence and subject reduction (`PureTypeSystem.HasType.subject_reduction`).

This library's own contributions:

* `Start/PTSCube.lean` — `PureTypeSystem.CubeFeatures` (three Booleans: polymorphism,
  dependency, type operators), `PureTypeSystem.cubeSpec : CubeFeatures → Specification Srt` and
  the eight corners `lambdaArrow, systemF, lambdaOmegaBar, systemFOmega, lambdaP, lambdaP2,
  lambdaPOmegaBar, coc` as instances of the one family; `HasType.mono`, `cube_inclusion`
  (adding product rules preserves derivations), `cube_sn_mono` (strong normalization descends);
  functionality of axioms and rules; `not_hasType_box`; `lambdaPiSpec_eq_cube` (the library's
  `λΠ` specification is the `λP` corner), `cube_lambdaP_toTyping` (a derivation translation into
  `LambdaPi.Typing`), `cube_lambdaP_sn`, `cube_lambdaArrow_sn` (the latter two via the
  independent `LambdaPiSN` development, which is preserved).
* `Start/PTSSystemFElab.lean` — the derivation-directed elaboration of Curry-style System F
  (`SystemF.Typing`) into annotated `systemF`-corner terms: `FElab.elaborate` builds, by
  induction on the Curry derivation, an annotated term `M` with
  `HasType F Δ M (tr θ A)` and `erase m M = t`; `FElab.elaborate_ctx` (closed form with the
  canonical context) and `FElab.elaborate_corner` (every corner above `systemF`).
* `Start/PTSCheck.lean` — a verified fuel-bounded type inference procedure for arbitrary
  specifications with decidable axioms/rules (`Check.infer_sound`), used for concrete checks.

Classical: the cube (Barendregt) and the PTS presentation.  New here: the parameterised family,
the inclusion/transport lemmas, the elaboration with its erasure theorem, the verified checker.
