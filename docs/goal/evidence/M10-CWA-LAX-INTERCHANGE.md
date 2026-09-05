# M10-CWA-LAX-INTERCHANGE

**Status:** DONE_STRONG

Module `Start/CwaLaxInterchange.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warning; `#print axioms` on
the headline declarations reports only `propext`, `Classical.choice`, `Quot.sound`.

## The statement

`M10-CWA-LAX-WHISKER` built the two whiskerings of a lax 2-cell by a morphism of models and proved
each functorial in the 2-cell; it left the interchange law unclaimed, and expected it to fail.
This task proves it, for arbitrary lax 2-cells on both sides:

* **`Cwa.LaxTwoCell.whisker_exchange`** — for `θ : LaxTwoCell F G` with `F G : Mor T S` and
  `ψ : LaxTwoCell K L` with `K L : Mor S R`, the vertical composite of `whiskerLeft F ψ` with
  `whiskerRight θ L` equals that of `whiskerRight θ K` with `whiskerLeft G ψ`.

## Why it holds

By `M10-CWA-LAX-RIGID` a lax 2-cell is determined by its natural transformation
(`Cwa.LaxTwoCell.ext_of_nat`), and the comparisons play no part in the equation: on natural
transformations the identity is the ordinary exchange law of `CategoryTheory.NatTrans`, which the
whiskerings implement (`whiskerLeft_nat`, `whiskerRight_nat`).  So no naturality of the comparison
in the other 2-cell has to be assumed — the comparison has no freedom left to be natural in.

## The mixed case

The special case in which one of the two 2-cells is a strict 2-cell embedded into the lax ones
along `Cwa.TwoCell.toLax` is recorded separately, since it is the case a strictification argument
meets:

* `Cwa.LaxTwoCell.whisker_exchange_strict_left`, `Cwa.LaxTwoCell.whisker_exchange_strict_right`.

Both are corollaries of the general law rather than substitutes for it.

## Whiskering and the classification

* `Cwa.LaxTwoCell.whiskerLeft_ofNat`, `Cwa.LaxTwoCell.whiskerRight_ofNat` — whiskering the lax
  2-cell attached to a natural transformation gives the lax 2-cell attached to the whiskered
  natural transformation.

## Gates

```
python3 scripts/goal_state.py validate
python3 scripts/check_closure.py
lake build Start.CwaLaxInterchange
lake build
```

all pass; the full `lake build` reports no error and no linter warning.

## Boundary

None.
