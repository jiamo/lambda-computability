# M28-STARHEIGHT-Z4-MOD-TWO: computations (Python, not Lean-verified)

- `wreath_facts.py` -> `wreath_facts_output.txt` (`python3 wreath_facts.py > wreath_facts_output.txt`):
  `Z2 wr Z4` (same multiplication as the Lean `Z2WrZ4`): order 64, lower central series
  `64, 8, 4, 2, 1` (class 4), Frattini subgroup of order 16, non-abelian; 3 subgroups of index 2,
  none abelian; element orders and centre.
- `r3_span.py` -> `r3_span_output.txt`
  (`(python3 r3_span.py 8; python3 r3_span.py 16) > r3_span_output.txt`): for R3, whether a
  letter-in-state count is an F2- (or Z/4-) linear combination of the proved pieces, computed
  exactly on weight functions over the torus `(Z/M)^alphabet`, `M = 8` and `M = 16` (see the
  docstring for why this is exact).  Positive control: `Z4Rot2Abc` modulo 2 with the R1 pieces
  removed has deficiency 0 (that is the R1 identity).
