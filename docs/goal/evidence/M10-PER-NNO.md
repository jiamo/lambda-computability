# M10-PER-NNO

**Status:** DONE_STRONG

`Start/PERNNO.lean` — an equivalence of categories preserves natural numbers objects, so the
partial equivalence relations have one.

## What is proved

* `CategoryTheory.Limits.IsNNO.ofEquivalence` — **an equivalence of categories preserves natural
  numbers objects** (for Lawvere's universal property as stated in `Start/AssemblyNNO.lean`): the
  image of the terminal object is terminal, and a recursion datum `(X, q, f)` in the target is
  pulled back along the counit isomorphism `e.functor.obj (e.inverse.obj X) ≅ X` using fullness,
  solved in the source, and pushed forward again; uniqueness follows from faithfulness.
* `Realizability.PER.natPER`, `unitOfModest`, `natZeroPER`, `natSuccPER` — the natural numbers,
  their terminal source, zero and successor as partial equivalence relations, the images of the
  modest assembly of natural numbers under `Realizability.perEquivModest`.
* `Realizability.PER.isNNO_natPER` — **the partial equivalence relations have a natural numbers
  object** over an algebra with more than one element.

## Scope

`[Nontrivial A]`, inherited from `M10-MODEST-NNO`: over a one-element algebra the assembly of
natural numbers is not modest.

## Gates

```
lake build Start.PERNNO             # no error, no warning
python3 scripts/check_closure.py
python3 scripts/goal_state.py validate
```

`#print axioms` on the headline results reports only `propext`, `Classical.choice` and
`Quot.sound`.  The module contains no `sorry` and no `axiom`, and is registered in
`Start/Capstones.lean`.
