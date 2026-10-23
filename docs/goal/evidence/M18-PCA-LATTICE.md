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

## Big round 2, run 1

Closed as DONE_STRONG: the exit criteria are met as written.

* "Applicative morphisms are preordered by existence, and the induced equivalence is defined." —
  `Realizability.PCALe`, `Realizability.PCAEquiv`, `pcaLe_refl`, `pcaLe_trans`
  (Start/PCAOrder.lean).
* "K1 < K2 is proved strict, extending Start/KleeneNoRetraction.lean." —
  `Realizability.KleeneTwo.kleene_strict : PCALeD ℕ (ℕ → ℕ) ∧ ¬ PCALeD (ℕ → ℕ) ℕ`, in the order of
  decidable applicative morphisms.  In the plain existence preorder no strict comparison is
  possible at all: `Realizability.pcaEquiv_of_any` proves every two algebras equivalent (the
  trivial morphism), so the decidable refinement is the order in which this criterion can hold,
  and it is proved there.
* "The statement that two PCAs with equivalent realizability toposes are equivalent is either
  proved or recorded as open." — recorded as open (the library has assemblies and their exact
  completion, not the realizability topos of an algebra); see the earlier sections.

## Big round 2, run 6 (restoration after the move to a new project)

The big round 2 sections of this note (runs 1 to 3) were lost with the old project and were recreated
in run 6 from its command logs, which record the text that was appended; the Lean modules they cite
were restored from the old project's export, rebuilt with `lake build --wfail`, and their axioms
regenerated (`docs/goal/evidence/*-axioms.txt`, section "Big round 2, run 6").

## Big round 2, run 7 (restoration after the export of run 6)

The platform's export of run 6's project dropped this note; it was put back from the copy of before big round 2 (our tree at ce8fe5e), and the
big round 2 sections that run 6 had restored were added again in run 7 from the command logs of
runs 1 to 3 (the appended text is recorded there verbatim). The axioms files of the big round 2 rows
were regenerated with `#print axioms` in run 7 (section "Big round 2, run 7").
