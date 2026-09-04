# M10-LAMBDAPI-MODELHOM

**Status:** DONE_STRONG

Modules `Start/LambdaPiInitialApp.lean` and `Start/LambdaPiInitialModelHom.lean`, both imported by
`Start.lean` and registered in `Start/Capstones.lean`.  They build without `sorry`; `#print axioms`
on the headline declarations reports only `propext`, `Classical.choice`, `Quot.sound`.

`M10-LAMBDAPI-SELF-INITIAL` proved the *uniqueness* side of bi-initiality for the syntactic model of
λΠ, but only for a hypothetical morphism of models `H : ModelHom syntacticModel M`: nothing said
that such a morphism exists.  The comparison morphism `LambdaPiInitial.mor` was known to preserve
the universe, the products over the small types, their codes and abstraction; the one clause of
`LambdaPi.ModelHom` still missing was preservation of **application**.  This task supplies it and
packages the result.

## Application is preserved

The syntactic application is taken in the generic-argument form: the representative of
`smallPi.app f` is `f` weakened past the new variable, applied to the variable `0`
(`LambdaPiUniv.rep_appQ`).  The semantic content is therefore the "weaken, then instantiate at the
generic argument" law.

* `LambdaPi.tmCast_extHom_var` — the section defined by the generic argument undoes the action of
  the display map on extended contexts: composing the two gives the identity;
* `LambdaPi.val_app_weaken` — applying the weakening of `f` to the generic argument returns the
  generic application of `f`, compared as a value (type and term together).  This is naturality of
  application (`LambdaPi.Model.app_sub`) followed by functoriality of substitution on values;
* `LambdaPi.TmI.app_shift_var` — hence the raw term `(shift t) (var 0)` denotes the generic
  application of whatever `t` denotes: weakening of the interpretation, the variable rule, the
  application rule of the interpretation, and the value computation above;
* **`LambdaPiInitial.tmMap_appQ`** — application is preserved by the comparison morphism: the image
  of the generic application of `f`, read in the compared extended context, is the generic
  application of the image of `f`.  As for abstraction, the proof is uniqueness of the
  interpretation applied to the two readings of the same raw term.

## The interpretation is a morphism of models

* `LambdaPiInitial.tmCast_of_val_eq` — a value equality determines the transported term;
* `LambdaPiInitial.tmMap_lam_cast` — abstraction preserved, in the transported form the structure
  asks for;
* `LambdaPiInitial.obj_empty` — the empty context is interpreted by the empty context of the model,
  so its image is terminal;
* **`LambdaPiInitial.modelHom`** — the comparison morphism, with all six clauses, is a
  `LambdaPi.ModelHom syntacticModel M` for every model `M` with injective products, and
  `LambdaPiInitial.nonempty_modelHom` is the corresponding existence statement (weak initiality).

## Bi-initiality

* **`LambdaPiInitial.biInitial_syntacticModel`** — into every model of λΠ with injective products
  there is a morphism of models, and between the 1-cells underlying any two of them there is
  exactly one 2-cell.  Existence is `modelHom`; contractibility is
  `LambdaPiSelf.nonempty_unique_twoCell_modelHom`.

## Gates

```
python3 scripts/goal_state.py validate
python3 scripts/check_closure.py
lake build Start.LambdaPiInitialApp Start.LambdaPiInitialModelHom
lake build
```

all pass; the full `lake build` reports no error and no linter warning.

## Boundary

Bi-initiality is claimed among *models of λΠ* with injective products, that is for 1-cells
underlying a `LambdaPi.ModelHom`; among all coherent models it is false
(`LambdaPiBiInitial.not_biInitial_syntacticCModel`).  The pseudofunctors between models with Π and
locally cartesian closed categories are still not constructed.
