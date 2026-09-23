# M18-PCA-LATTICE — the order of partial combinatory algebras

**Status:** DONE_WEAK (the order, its degeneracy, the informative refinement and the separation
`K₁ < K₂` are proved; the question about realizability toposes is recorded as open).

`Start/PCAOrder.lean` formalizes the order of partial combinatory algebras under applicative
morphisms, on top of `Start/PCAMorphism.lean` and `Start/KleeneNoRetraction.lean`.

## The plain order, and why it is not the right one

* `Realizability.PCALe A B` — there is an applicative morphism `A → B`;
* `Realizability.pcaLe_refl`, `Realizability.pcaLe_trans` — it is a preorder (identity morphism,
  composition of morphisms);
* `Realizability.PCAEquiv` with `pcaEquiv_refl`, `PCAEquiv.symm`, `PCAEquiv.trans` — the induced
  equivalence;
* `Realizability.pcaLe_trivial`, `Realizability.pcaEquiv_of_any` — **the plain order is
  degenerate**: the trivial morphism of `Start/KleeneNoRetraction.lean` (every element of the
  target represents every element of the source) makes any two algebras equivalent. Nothing can
  be separated in it — the same phenomenon that forced `no_separatesBits_morphism` to assume that
  the target reads something back.

## The informative order

* `Realizability.AppMorphism.Decides γ` — one element of the target recovers, from any
  representative, whether the element represented is the combinator `k` or the combinator `k i`;
* `Realizability.AppMorphism.decides_id` — the identity morphism decides, by `i`;
* `Realizability.AppMorphism.decides_step`, `Realizability.AppMorphism.Decides.comp` — decidable
  morphisms compose: the composite decider reads its argument through the realizer of the second
  morphism applied to a representative of the first decider, and then through the second decider;
* `Realizability.PCALeD` with `pcaLeD_refl`, `pcaLeD_trans` — hence a preorder again, and
  `Realizability.pcaLe_of_pcaLeD` places it below the plain one.

## `K₁ < K₂`

* `Realizability.KleeneTwo.selEl`, `selAssoc`, `appK_selAssoc` — the continuous test "is the value
  read at `0` equal to `n₀`?", as an element of `K₂`;
* `Realizability.KleeneTwo.kOneToTwo_decides` — the morphism `K₁ → K₂` decides, since a
  representative is the constant function naming the number; so `K₁ ⪯ K₂`
  (`Realizability.KleeneTwo.pcaLeD_kleene`);
* `Realizability.KleeneTwo.separatesBits_of_decides` — a decision of the two combinators already
  separates bits: `selAssoc 0` turns the constant function `0` into `k` and the constant function
  `1` into `k i`, and a partial recursive code turns the decider's answer back into the bit;
* `Realizability.KleeneTwo.not_decides`, `not_pcaLeD_kleene` — hence no applicative morphism
  `K₂ → K₁` decides, by `no_separatesBits_morphism`;
* `Realizability.KleeneTwo.kleene_strict` — **`K₁ < K₂`** in the informative order.

## Open

The third exit criterion — whether two partial combinatory algebras with equivalent realizability
toposes are equivalent — is **recorded as open**: the library has no construction of the
realizability topos of an algebra (only the assemblies and their exact completion,
`Start/AsmExReg*.lean`), so the statement cannot even be phrased here yet. Which further algebras
are comparable is likewise not settled in the literature.

## Gates

`lake build` (whole tree, no errors and no new warnings), `scripts/check_sorry.py`,
`scripts/check_closure.py`, `scripts/goal_state.py validate`. `#print axioms` on the results above
reports only `propext`, `Classical.choice`, `Quot.sound`.
