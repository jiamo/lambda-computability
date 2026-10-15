/-
**Expansion postponement for the dependent corners of the lambda cube: reduction to one lemma
(M29-EP-CUBE).**

Expansion postponement for the dependent corners (λP, λP2, λPω̲, λC) is *not* proved here.

* `cube_expansionPostponement_iff_productNormalizationR`: for every corner `f` of the cube,
  `ExpansionPostponement (cubeSpec f) ↔ ProductNormalizationR (cubeSpec f)`.  The proof uses
  strong normalization of the cube (`cube_stronglyNormalizing`), and only in one place: in the
  abstraction case, to reduce the type of the body to its normal form
  (`expansionPostponement_of_productNormalizationR`).
* `cube_expansionPostponement_of_productNormalizationR`: the direction that remains open for
  `f.dep = true`.  The first missing lemma, for λP, is
  `theorem lambdaP_productNormalizationR : ProductNormalizationR (cubeSpec lambdaP)`.
* `cube_productNormalizationR`: product normalization for the corners without `(∗,□)`.
-/

import Start.PTSExpansionPoll
import Start.PTSExpansionLevels
import Start.CoCSN

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

/-- For every corner of the cube, expansion postponement is equivalent to product
normalization.  Uses strong normalization of the cube. -/
theorem cube_expansionPostponement_iff_productNormalizationR (f : CubeFeatures) :
    ExpansionPostponement (cubeSpec f) ↔ ProductNormalizationR (cubeSpec f) :=
  expansionPostponement_iff_productNormalizationR
    (fun Γ hΓ M hM => weaklyNormalizing_of_stronglyNormalizing
      (cube_stronglyNormalizing f Γ hΓ M hM))

theorem cube_expansionPostponement_of_productNormalizationR (f : CubeFeatures)
    (h : ProductNormalizationR (cubeSpec f)) : ExpansionPostponement (cubeSpec f) :=
  (cube_expansionPostponement_iff_productNormalizationR f).2 h

/-- For the corners without the dependent rule, product normalization holds (through the
stratified case `cube_expansionPostponement`). -/
theorem cube_productNormalizationR (f : CubeFeatures) (hf : f.dep = false) :
    ProductNormalizationR (cubeSpec f) :=
  (cube_expansionPostponement_iff_productNormalizationR f).1 (cube_expansionPostponement f hf)

end PureTypeSystem
