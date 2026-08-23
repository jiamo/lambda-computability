# M9-STLC-CCC

**Status:** DONE_STRONG

Modules `Start/Stlc.lean`, `Start/StlcCcc.lean` and `Start/CccModel.lean`, all imported by
`Start.lean`.  They build without `sorry` and without linter warnings; `#print axioms` on the
headline declarations reports only `propext`, `Classical.choice`, `Quot.sound`.

These files formalize the Lambek half of the Curry–Howard–Lambek correspondence in both
directions: the syntax of the simply typed lambda calculus is a cartesian closed category, and
every cartesian closed category is a model of that syntax.

## Syntax — `Start/Stlc.lean`

An intrinsically typed presentation: `Ty` (base type, unit, binary products, function types),
`Ctx = List Ty`, de Bruijn variables `Var`, terms `Tm Γ A`, renamings `Ren` with `ren`,
substitutions `Sub` with `sub`, and the full complement of laws (`ren_id`, `ren_ren`, `sub_ren`,
`ren_sub`, `sub_id`, `sub_sub`, `inst_wk`, `sub_single`, `wk_sub`).  `Conv` is βη-conversion: β and
η for functions, the projection and surjective-pairing rules for products, terminality for the
unit type, congruences, and the equivalence-relation rules.  `Conv.sub`, `Conv.ren` and
`Conv.subCongr` record its compatibility with substitution.

## The syntactic category is cartesian closed — `Start/StlcCcc.lean`

Morphisms `A ⟶ B` are terms `Tm [A] B` modulo conversion (`Hom`, `hom`, `hom_eq`, `Hom.ind`),
composition is substitution (`cmp`, `cmp_id_left`, `cmp_id_right`, `cmp_assoc`, `cmp_congr`),
giving `Stlc.category`.

* `isTerminalUnit`, `terminalCone` — the unit type is terminal (by the η-rule for `unit`);
* `projFst`, `projSnd`, `pairHom`, `prodCone` — the product type is a binary product (by the
  projection rules and surjective pairing);
* `Stlc.cartesianMonoidal` — the resulting `CartesianMonoidalCategory` structure;
* `expFunctor` — the functor `X ⇒ -`, with `expTm_id` and `expTm_comp` proved by η;
* `curryTm`/`uncurryTm` and `uncurry_curry`/`curry_uncurry` — currying is a bijection
  `Hom (X × Y) Z ≃ Hom Y (X ⇒ Z)`, by β and η;
* `Stlc.closed`, `Stlc.monoidalClosed` — the bijection is natural, so `- ⊗ X ⊣ X ⇒ -`.

In this Mathlib version "cartesian closed" is `CartesianMonoidalCategory C` together with
`MonoidalClosed C`; both instances are provided for `Stlc.Ty`.

## Every cartesian closed category is a model — `Start/CccModel.lean`

For a category `C` with `CartesianMonoidalCategory C` and `MonoidalClosed C` and a chosen object
`S` interpreting the base type:

* `tyObj`, `ctxObj` — types as objects and contexts as iterated products;
* `varMor`, `tmMor` — variables as projections, terms as morphisms `⟦Γ⟧ ⟶ ⟦A⟧`;
* `renMor`, `subMor` with `tmMor_ren`, `tmMor_wk`, `tmMor_sub`, `tmMor_inst` — the substitution
  lemma: syntactic substitution is composition;
* **`tmMor_conv`** — soundness: convertible terms have equal interpretations;
* `interpTm`, `interpTm_id`, `interpTm_cmp`, **`interpFunctor`** — hence a functor from the
  syntactic category to `C` sending the type `A` to `⟦A⟧`;
* `interpFunctor_obj_unit`, `interpFunctor_obj_prod`, `interpFunctor_obj_arrow`,
  `interpFunctor_map_projFst`, `interpFunctor_map_projSnd`, `interpFunctor_map_pairHom`,
  `interpFunctor_map_curryHom` — the functor preserves the cartesian closed structure: the
  terminal object, the products with their projections and pairing, and the exponentials with
  their currying.

## Boundary

Freeness of the syntactic category in the strict sense — uniqueness of the structure-preserving
functor out of it, i.e. the full 2-categorical statement of the correspondence — is not claimed
here.  What is proved is that the syntactic category is cartesian closed, that every cartesian
closed category receives an interpretation functor from it, and that this functor preserves the
cartesian closed structure.
