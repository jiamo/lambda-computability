# M10-CWA-STRICT-FUNCTOR

**Status:** DONE_STRONG

Module `Start/CwaStrictFunctor.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings; `#print axioms` on
the headline declarations reports only `propext`, `Classical.choice`, `Quot.sound`.

## What was missing

`Start/CwaLocalUniverse.lean` strictifies a category with pullbacks into a model of a dependent
type theory (`Cwa.ofPullbacks`), and `Start/CwaMor.lean` turns a pullback-preserving functor into a
morphism of the resulting models (`Cwa.morOfPullbackPreserving`).  Nothing related the two: it was
not recorded that the identity functor induces the identity morphism, nor that a composite induces
the composite, so strictification was a construction on objects and arrows but not a functor.

## What is proved

All the data of the induced morphism except one field is strictly functorial for free: the functor
on contexts is the given functor, and a type — a local universe `⟨base, total, proj, cls⟩` — is
transported componentwise.  The single non-formal field is the comparison isomorphism `luExtIso` of
an extended context, which is the canonical map between two pullbacks.  It is therefore pinned down
by the two legs of the pullback square (`LuTy.isPullback_gen`), which gives

* `Cwa.luExtIso_id` — the comparison of the identity functor is the identity;
* `Cwa.luExtIso_comp` — the comparison of `F ⋙ G` is `G.map (luExtIso F A).hom ≫
  luExtIso G (luMap F A)`.

With `Cwa.Mor.ext` (a morphism of models is determined by its functor, its action on types and its
comparison) these upgrade to equalities of morphisms of models:

* **`Cwa.morOfPreservesPullbacks_id`** — `morOfPreservesPullbacks (𝟭 C) = Mor.id (Cwa.ofPullbacks C)`;
* **`Cwa.morOfPreservesPullbacks_comp`** — `morOfPreservesPullbacks (F ⋙ G) =
  (morOfPreservesPullbacks F).comp (morOfPreservesPullbacks G)`.

Finally the source of the functor is built:

* `Cwa.PbCat` — a bundled category with pullbacks, with `Cwa.PbCat.Hom` a functor preserving
  pullbacks, and `Cwa.PbCat.instCategory` the resulting category (the laws hold because the
  preservation hypothesis is a proposition and composition of functors is strictly associative and
  unital);
* **`Cwa.strictification : PbCat ⥤ Cwa.Model`** — the strictification functor, with `map_id` and
  `map_comp` exactly the two theorems above.

This is the 1-categorical skeleton of the passage from locally cartesian closed categories to
models of `λΠ`: on the semantic side an LCCC is in particular a category with pullbacks, so it has
a strictified model, and now that assignment is functorial in the pullback-preserving functors.

## Gates

```
python3 scripts/goal_state.py validate
python3 scripts/check_closure.py
lake build
```

all pass.

## Boundary

Only pullbacks are transported here: a functor is not asked to preserve the dependent products, so
the induced morphism of models is not claimed to preserve a Π-structure, and the pseudofunctor
relating models with Π to locally cartesian closed categories, together with its inverse up to
equivalence, is still not constructed (see `M9-LAMBDAPI-LCCC` and `M10-CWA-BICATEGORY`).
