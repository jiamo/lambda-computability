# M10-LAMBDAPI-SELF-INITIAL

**Status:** DONE_STRONG

Module `Start/LambdaPiSelfMor.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry`; `#print axioms` on the headline declarations
reports only `propext`, `Classical.choice`, `Quot.sound`.

`M10-CWA-BICATEGORY` left the *existence* half of bi-initiality open: a 1-cell out of the syntactic
model of λΠ was known to be isomorphic to the canonical interpretation exactly when 2-cells exist
in both directions, but no 2-cell was produced.  This task produces it, for the 1-cells that come
from a **morphism of models of λΠ** — the restriction is necessary, since
`LambdaPiBiInitial.not_biInitial_syntacticCModel` shows the syntactic model is not bi-initial among
all coherent models (a model need not have any types at all).

## Reading a morphism of the syntactic category off its representative

* `LambdaPiSelf.hom_eq_of_out_conv` — two morphisms of the syntactic category with convertible
  representatives at every variable of the target context are equal;
* `LambdaPiSelf.subI_out_conv` — **a morphism of the syntactic model carrying a substitution is
  that substitution**, up to conversion: the value it gives to a variable is, by
  `LambdaPiSelf.tmI_rep_conv`, the raw term it is supposed to carry;
* `LambdaPiSelf.ctxConvOk_length_le`, `LambdaPiSelf.objCtx_length` — a conversion of contexts does
  not change the length, so the object interpreting a context has a context of the same length;
* `LambdaPiSelf.comp_ids_out_conv`, `LambdaPiSelf.extendQ_objIso_out_conv` — a composite of
  morphisms carried by the identity substitution is carried by it, and so is the action of the
  comparison on an extended context.

## The self-interpretation is the identity

Building on `LambdaPiSelf.objIso Γ : obj Γ ≅ Γ` of `Start/LambdaPiSelfIso.lean`:

* `LambdaPiSelf.objIso_naturality` — the comparison is natural in the context: both sides carry the
  raw substitution `σ`, so they are equal;
* `LambdaPiSelf.tySubQ_objIso` — the interpretation of a type in the syntactic model is that type;
* `LambdaPiSelf.extend_objIso` — the comparison commutes with the comparisons of extended contexts;
* **`LambdaPiSelf.selfTwoCell : Cwa.TwoCell (LambdaPiInitial.mor syntacticModel_piInj)
  (Cwa.Mor.id syntactic)`**, invertible (`isIso_selfTwoCell`), giving
  **`LambdaPiSelf.selfIso`** — the syntax interprets itself by the identity.

## Every morphism of models out of the syntax is the interpretation

Composing the naturality 2-cell of `Start/LambdaPiInitialNatural.lean` with the whiskering of
`selfIso`:

* `LambdaPiSelf.isIso_whiskerRight_selfTwoCell` — the whiskered 2-cell is invertible;
* **`LambdaPiSelf.isoModelHom`** — for a model `M` with injective products and a morphism of models
  `H : ModelHom syntacticModel M`, the canonical interpretation `LambdaPiInitial.mor` is isomorphic
  to `H.mor` as a morphism of categories with attributes;
* `LambdaPiSelf.twoCell_of_modelHom` — in particular the missing 2-cell exists;
* `LambdaPiSelf.isoModelHom_modelHom` — any two morphisms of models out of the syntax are
  isomorphic;
* **`LambdaPiSelf.nonempty_unique_twoCell_modelHom`** — and there is *exactly one* 2-cell between
  them, uniqueness being the rigidity `LambdaPiBiInitial.subsingleton_twoCell` applied to the
  terminality of the image of the empty context.

This is contractibility of the hom-category, restricted to the 1-cells underlying morphisms of
models of λΠ: the precise sense in which the syntax of λΠ is bi-initial.

## Gates

```
python3 scripts/goal_state.py validate
python3 scripts/check_closure.py
lake build
```

all pass; `lake build` reports no `sorry` and no linter warning for the new module.

## Boundary

The statement is about 1-cells that preserve the structure of a model of λΠ (`LambdaPi.ModelHom`);
for a bare morphism of categories with attributes nothing of the sort can hold.  The pseudofunctors
between models with Π and locally cartesian closed categories are still not constructed.
