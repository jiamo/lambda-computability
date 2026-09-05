# M11-THREE-SAT-NPC

**Status:** DONE_STRONG

The library had two NP-complete problems, `SAT` (`Start/CookLevinNPHard.lean`) and `CIRCUIT-SAT`
(`M11-CIRCUIT-SAT-NPC`).  It now has the *bounded width* one as well: **`k`-SAT** for every
`k ≥ 3`, the words that decode to a satisfiable conjunctive normal form all of whose clauses have
at most `k` literals, and **3-SAT** as the case `k = 3`.

Module: `Start/ThreeSat.lean`, imported by `Start.lean` and registered in `Start/Capstones.lean`.
It builds with no `sorry` and no linter warning, and `Complexity.npComplete_KSAT` and
`Complexity.npComplete_ThreeSAT` depend only on `propext`, `Classical.choice`, `Quot.sound`.

## The Tseitin translation has width three (first exit criterion)

A gate definition is a conjunction of implications of width two, plus one clause of width three
for the binary gates, and the output assertion is a unit clause:

* `Complexity.Tseitin.length_le_three_of_mem_gateCnf`,
* `Complexity.Tseitin.length_le_three_of_mem_defsCnf`,
* `Complexity.Tseitin.length_le_three_of_mem_toCnf` — **every clause of `toCnf C` has at most
  three literals**, for every list of gates `C`.

## Recognising a code of a CNF of width `w` (second exit criterion)

The token reader of `Start/Sat.lean` scans a word from the right through the phases
`main`/`esc`/`esc2`, pushing a literal on the clause being read and, at a separator, pushing that
clause on the list of clauses already read.  Whether every *completed* clause is narrow is
therefore a finite-state property: the automaton needs the phase, the number of literals of the
clause being read capped at `w + 1`, and a dead state entered when a completed clause was too
wide.

* `Complexity.Sat.tstep`, `Complexity.Sat.tenc`, `Complexity.Sat.tdec`, `Complexity.Sat.tdelta` —
  the automaton and its transition function on the `3 * (w + 2) + 1` state codes;
* `Complexity.Sat.abst` — the state code of a decoder state;
* `Complexity.Sat.tdelta_abst`, `Complexity.Sat.rst_tdelta` — **the automaton simulates the
  decoder**: `rst (tdelta w) 0 u = abst w (drun u)`;
* `Complexity.Sat.widthTerm` and `Complexity.Sat.eval_widthTerm` — the Cobham term obtained from
  the automaton by `Complexity.eval_fstStTerm` of `Start/CobhamTransducer.lean`, accepting exactly
  the words that decode to a CNF of width at most `w`;
* `Complexity.Sat.inP_KCnfWord : ∀ w, InP (KCnfWord w)`.

## `k`-SAT is in NP (third exit criterion)

* `Complexity.InNP.inter_inP` — **`NP` is closed under intersection with `P`**: run the verifier
  and the decision procedure on the same input and take the conjunction, with the same witness
  bound;
* `Complexity.Sat.KSAT k : Language := fun u => SAT u ∧ KCnfWord k u`, with
  `Complexity.Sat.ThreeSAT` the case `k = 3`;
* `Complexity.Sat.inNP_KSAT` and `Complexity.Sat.inNP_ThreeSAT`, from `Complexity.Sat.inNP_SAT`
  and the previous item.

## `k`-SAT is NP-hard, hence NP-complete (fourth exit criterion)

The reduction is the one already in the library: `Complexity.CircCode.tseitinTerm`, which computes
`encCnf (toCnf (gatesOf x))` on every word, now lands in `k`-SAT because of the width bound.

* `Complexity.Sat.KSAT_encCnf` — a code of a CNF of width at most `k` is in `KSAT k` exactly when
  that CNF is satisfiable;
* `Complexity.polyManyOne_CSAT_KSAT : 3 ≤ k → CSAT ≤ₘᵖ Sat.KSAT k`;
* `Complexity.npHard_KSAT`, from `Complexity.npHard_CSAT`;
* `Complexity.npComplete_KSAT : 3 ≤ k → NPComplete (Sat.KSAT k)`, and
  `Complexity.npComplete_ThreeSAT : NPComplete Sat.ThreeSAT`.

## Gates

* `python3 scripts/goal_state.py validate`
* `python3 scripts/check_closure.py`
* `lake build Start.ThreeSat`
