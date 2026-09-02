# M10-LAMBDAPI-INTERP-NATURAL

**Status:** DONE_STRONG

Modules `Start/LambdaPiModelHom.lean`, `Start/CwaMorVal.lean` and
`Start/LambdaPiInterpTransport.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  They build without `sorry` and without linter warnings.

## What the task asked

`Start/LambdaPiInitial.lean` interprets `λΠ` in a model and packages the interpretation as a
morphism of categories with attributes out of the syntactic model.  What was missing is
*naturality in the model*: a structure-preserving morphism between two models should carry the
interpretation in the source to the interpretation in the target.

## What is proved

* `LambdaPi.ModelHom` — a **morphism of models of `λΠ`**: a morphism of the underlying categories
  with attributes which preserves the universe and its decoding, the products over the small
  types, the codes for those products, abstraction and application, and which sends the
  interpretation of the empty context to a terminal object.
* `LambdaPi.ModelHom.semCtx`, `.semObj`, `.semIso` — the image of a semantic context, the object
  of the target it lives over, and the comparison of the image of the object with the object
  built by iterated extension; `Cwa.extendIso` — extending a context along an isomorphism is an
  isomorphism.
* `Cwa.Mor.valMap`, `Cwa.Mor.valMap_sub`, `Cwa.Mor.valMap_var` — the action of a morphism of
  categories with attributes on *values* (a type together with a term of it), its compatibility
  with substitution, and the fact that the generic term is carried to the generic term along the
  comparison of extended contexts.
* `LambdaPi.ModelHom.varVal_map` — the image of a semantic context reads its de Bruijn variables
  as the images of what they read in the source.
* `LambdaPi.ModelHom.semTy_U`, `.semTy_El`, `.semTy_Pi` — the universe, the decoding of a code and
  a dependent product are carried to the universe, the decoding of the image of the code and the
  dependent product of the images, the body being read through the comparison
  `LambdaPi.ModelHom.consMor` of extended contexts.
* `LambdaPi.ModelHom.val_sub_valMap_U`, `.val_sub_valMap_cons`, `.val_sub_valMap_lam`,
  `.val_sub_valMap_app`, `.tmCast_consMor` — the value-level computations the term cases need:
  the image of a value of the universe is the image of the code it is; the image of a value of an
  extended context is its image substituted along `consMor`; the image of an abstraction, resp. of
  the generic application, is the abstraction, resp. the generic application, of the image; and
  the section of the image of a term followed by `consMor` is the image of its section.
* `LambdaPi.TyI.map`, `LambdaPi.TmI.map` — **the interpretation of a type, resp. of a term,
  commutes with a morphism of models**, proved by mutual induction on the interpretation
  relations; `LambdaPi.CtxI.map` — hence the image of an interpretation of a syntactic context is
  one.

## Boundary

The statement is about the *interpretation relations* `TyI`, `TmI`, `CtxI` of
`Start/LambdaPiInterp.lean`, i.e. about what a raw expression denotes in a semantic context.  It
is not phrased as a 2-categorical universal property of the syntactic model; that is the separate,
partly open task `M10-CWA-BICATEGORY`.

## Gates

* `lake build Start.CwaMorVal Start.LambdaPiModelHom Start.LambdaPiInterpTransport` — no error and
  no warning.
* `python3 scripts/check_closure.py`.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: `LambdaPi.TyI.map`, `LambdaPi.TmI.map`, `LambdaPi.CtxI.map` and
  `LambdaPi.ModelHom.varVal_map` depend only on `propext`, `Classical.choice` and `Quot.sound`.
