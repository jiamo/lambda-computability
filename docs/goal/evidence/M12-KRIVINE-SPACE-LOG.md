# M12-KRIVINE-SPACE-LOG — the collected state written with binary pointers

`Krivine.Impl.encState` (`Start/KrivineHeapCost.lean`) writes addresses in unary.  That is fine
for the time bound it serves — a pass over the state costs its length — and useless for a space
bound: it charges one bit per *unit* of address instead of one bit per *bit* of address.

`Start/KrivineSpaceLog.lean` writes a state in fixed-width binary fields.

## The encoding

* `Krivine.Impl.bitsOf`, `Krivine.Impl.numOf` — a number on `w` bits, least significant bit
  first, and the number a word denotes; `Krivine.Impl.numOf_bitsOf` computes the round trip as a
  residue and `Krivine.Impl.numOf_bitsOf_of_lt` closes it below `2 ^ w`.
* `Krivine.Impl.encPtrBin`, `Krivine.Impl.encCellBin`, `Krivine.Impl.encStateBin` — a pointer
  (tag bit and address), a cell (tag bit, address, pointer) and a state: code, environment
  pointer, stack preceded by its height, heap preceded by its size.

## Faithfulness

`Krivine.Impl.decStateBin` is a decoder, and `Krivine.Impl.decStateBin_encStateBin` proves it
recovers any state all of whose fields fit in `w` bits (`Krivine.Impl.FitsIn`); hence
`Krivine.Impl.encStateBin_inj`, the state is determined by its word.  Nothing is hidden in the
encoding: it is not merely a length measure.

## The logarithmic overhead

* `Krivine.Impl.encStateBin_length` — the exact length,
  `4·w + 1 + |stack|·w + |heap|·(2w+2)`.
* `Krivine.Impl.widthOf tab s = Nat.size (|tab| + |stack| + space s)` — the width a collected
  state needs, that is the number of bits of the largest number it mentions.
* `Krivine.Impl.fitsIn_gcState` — a collected state does fit in that width: its code address is
  an address of the table, and every pointer of it is the rank of a live cell, hence below
  `Krivine.Impl.space` (`Krivine.Impl.cellFits_gcState`).
* `Krivine.Impl.encStateBin_gcState_length_le` — **the overhead is logarithmic**: the collected
  state occupies at most `(4 + |stack| + 3 · space s) · (w + 1)` bits.
* `Krivine.Impl.space_le_encStateBin_gcState_length` — conversely the word is at least `space s`
  bits long, so counting cells and counting bits agree up to that factor.
* `Krivine.Impl.gcState_encoded_log` — the two statements together, at `w = widthOf tab s`.

## Boundary

This is the cost of *one* state.  The space of a whole run is `M12-KRIVINE-SPACE-INVARIANCE`.
