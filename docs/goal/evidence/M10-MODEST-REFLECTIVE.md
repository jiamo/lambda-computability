# M10-MODEST-REFLECTIVE

**Status:** DONE_STRONG

`Start/ModestReflect.lean` — the modest assemblies are a reflective subcategory of the assemblies.

## What is proved

* `Realizability.Assembly.ShareRealizer` — two elements share a realizer when some element of the
  algebra realizes both; a modest assembly is exactly one for which this relation is equality.
* `Realizability.Assembly.modestQuot`, `.modest_modestQuot` — the quotient by that relation, with
  the realizers of the representatives, is an assembly, and it **is modest**: two classes realized
  by the same element have representatives sharing that realizer.
* `Realizability.Assembly.modestUnit` — the projection, tracked by the identity combinator: no
  computation happens, only the identification of elements.
* `Realizability.Assembly.apply_eq_of_shareRealizer` — a morphism into a modest assembly cannot
  separate two elements sharing a realizer: its tracker computes a single value on the common
  realizer, and that value realizes both images.
* `Realizability.Assembly.modestLift`, `.modestUnit_comp_modestLift`, `.modestLift_uniq` — the
  induced morphism out of the quotient, tracked by the same element, and its uniqueness.
* `Realizability.Modest.reflector`, `.reflectorAdj` — **the quotient is left adjoint to the
  inclusion**, and `Realizability.Modest.instReflective` records that the modest assemblies are a
  reflective subcategory of `Asm(A)`.
* `Realizability.PER.reflector`, `.reflectorAdj` — the same adjunction transported along the
  equivalence of `Start/ModestEquiv.lean`: the PERs are reflective in the assemblies.

## Gates

```
lake build Start.ModestReflect      # no error, no warning
python3 scripts/check_closure.py    # OK: 336 modules, all in the import closure and all registered
python3 scripts/goal_state.py validate
```

The module contains no `sorry` and no `axiom`, and is registered in `Start/Capstones.lean`.
