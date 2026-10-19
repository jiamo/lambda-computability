# M28-STARHEIGHT-CORE-MOD-TWO: computations (Python, not Lean-verified)

- `autosearch.py` (the search of the brief, verbatim except the timing column, which is dropped so
  that the output is reproducible):
  - `python3 autosearch.py aabb 7 > autosearch_aabb_7_output.txt` (about 4 minutes): `H-states 8192
    paired 8192`; for `n = 2..7` good automata `3, 10, 39, 171, 830, 4503`, hits 0 each time.
  - `python3 autosearch.py abab 5 > autosearch_abab_5_output.txt` (positive control): `paired 0`,
    every good automaton is a hit.
- `order8_table.py > order8_table_output.txt`: the order-8 cores as central extensions of `V4` by
  `Z2` (element orders), the mod-2 identity `Q8 = D4 + Z4xZ2` on random words, `Z2WrZ2` is `D4`,
  and the `Z8` expansion `s = R + 4C` on all 128 cases.
- `derived_table.py > derived_table_output.txt`: for the 15 classes of words of length 4, the
  transition group `G(w) <= UT5(F2)` of the mod-2 counting automaton: `|G|, |G'|, |G''|, |Z|`,
  whether rows/columns span `F2^5`, and the central involutions flipping the count (R2, R3 (c)).
