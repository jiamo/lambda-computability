# Search scripts for S4 over three letters (Python 3, no dependencies)

Run each script from any directory: it finds its siblings through its own path.  Letters are
tables in Lean's convention (images of `0 1 2 3`); `r2obs.user_class` converts the board's
right-action tuples.

M28-STARHEIGHT-S4-THREE (R1):
- `s4three.py`: S4 tables, classes of generating triples, coset automata, the `D` computation.
- `gen.py`, `data.py`: per-class automaton families and stage witnesses for the Lean files.
- `emit_certs.py`: writes `Start/StarHeightS4ThreeCertsA.lean`–`E`.
- `emit_glue.py` with `glue_template.lean`: writes `Start/StarHeightS4ThreeLetters.lean`.
  Both reproduce the committed files byte for byte.
- `rss.py`: `python3 rss.py lake env lean <file>` prints the max RSS in MiB.

M28-STARHEIGHT-S4-DOUBLE-TRANSPOSITION (R2):
- `r2.py`: the 19 double-transposition classes, letter-cycle automata, and `W_of` (the
  `V4`-part of the values of words returning a family to its bases).
- `r2a.py` (singles; loops to n = 5, reported up to n = 4), `r2b.py` (all pairs, n ≤ 3), `r2c.py <seed> <seconds>` (random
  families of 2–3 automata on 2–7 states).
- `r2obs.py`: good automata, and the observers (markers, Transfer counters, off-base counters).
- `r2exp1.py`–`r2exp4.py`: the observer experiments; `r2exp2.py single|transfer|marker|rev|
  markerpair ...`.  `r2exp4.py` checks the left-coset form of the `V4` part.
- `candidate_check.py`: checks the regular expressions for the candidate language.

These are computations, not Lean proofs.
