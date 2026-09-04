# M11-CIRCUIT-SAT-NPC

**Status:** DONE_STRONG

Before this task the library had exactly one NP-complete problem, `SAT`
(`Start/CookLevinNPHard.lean`).  It now has a second one, `CIRCUIT-SAT`, together with
polynomial-time reductions in **both** directions, so the two are interreducible and the
NP-hardness of `SAT` transfers.

Modules: `Start/CircuitSystem.lean`, `Start/CircuitSatLang.lean`, `Start/SatToCircuit.lean`,
`Start/SatToCircuitCob.lean`, all imported by `Start.lean` and registered in
`Start/Capstones.lean`.  They build without `sorry`, and `Complexity.npComplete_CSAT` depends only
on `propext`, `Classical.choice`, `Quot.sound`.

## The language (first two exit criteria)

A decision problem is a set of *arbitrary* words, so the definition has to say what an arbitrary
word means as a circuit.  Two steps make that harmless.

`Start/CircuitSystem.lean` gives a list of gates an **equation semantics** that needs no
well-formedness: `Tseitin.gateValFn`, `Tseitin.Consistent` and

* `Tseitin.esat C` — there is an assignment of a Boolean to every wire that satisfies every gate
  equation and makes the output wire true;
* `Tseitin.esat_iff_sat_toCnf` — for **every** list of gates, `esat` is the satisfiability of the
  Tseitin translation;
* `Tseitin.esat_iff_csat` — on a well-formed circuit, `esat` is ordinary circuit satisfiability.

`Start/CircuitSatLang.lean` reads gates off any word with the finite-state control of
`Start/CircuitCode.lean` (`CircCode.gatesOf`) and defines

* `Complexity.CSAT : Language := fun x => Tseitin.esat (gatesOf x)`,
* `Complexity.CSAT_encCirc_wf` — on the code of a well-formed circuit this **is** circuit
  satisfiability.

## CIRCUIT-SAT is in NP (third exit criterion)

`CircCode.brun_gblk_gatesOf` and `CircCode.eval_tseitinTerm_word` extend the block-emitting
recursion of `Start/CircuitCode.lean` from codes to arbitrary words, so the Tseitin term computes
the translation of `gatesOf x` for every `x`.  Hence

* `Complexity.polyManyOne_CSAT_SAT : CSAT ≤ₘᵖ Sat.SAT`,
* `Complexity.inNP_CSAT`.

## SAT reduces to CIRCUIT-SAT, semantically (fourth exit criterion)

`Start/SatToCircuit.lean` builds the circuit of a word by the *same* right-to-left token scan that
`Start/Sat.lean` uses to decode and evaluate a CNF: four gates per position (`Sat.satBlk`), on top
of the two constant gates that start the accumulators (`Sat.satC`).  The two top wires of the
block at a position carry exactly the two accumulators of the evaluator — "every clause read so far
is satisfied" and "the clause being read is already satisfied":

* `Sat.wf_satC` — the circuit is well formed;
* `Sat.vals_satC` — the wires carry the accumulators of `Sat.mrun`;
* `Sat.out_satC` — its output is the truth value of the decoded CNF;
* `Sat.csat_satC_iff` — it is satisfiable exactly when the word is in `SAT`;
* `Sat.CSAT_encCirc_satC`.

## The reduction is a Cobham term (fifth exit criterion)

`Start/SatToCircuitCob.lean` exhibits `u ↦ encCirc (satC u)` as a Cobham (polynomial-time) term by
running the block recursion of `Start/CobhamBlock.lean` with a three-state phase automaton:

* `Sat.pdelta`, `Sat.pinc`, with `Sat.rst_pdelta` (the automaton computes the phase of the decoder)
  and `Sat.rcnt_pinc` (four gates per position);
* `Sat.tickT` and `Sat.eval_tickT` — the number of ticks since the last token, that is the variable
  index of a literal, is recovered by running the CNF evaluator against the all-ones assignment and
  measuring how far the assignment pointer moved;
* `Sat.tokT`, `Sat.eval_tokT` — a gate token as a term;
* `Sat.blkT`, `Sat.eval_blkT`, `Sat.length_cirBlk` — the block and its length bound;
* `Sat.satCircTerm` and `Sat.eval_satCircTerm` — **the term computes the code of the circuit**.

## Conclusion (sixth exit criterion)

* `Complexity.polyManyOne_SAT_CSAT : Sat.SAT ≤ₘᵖ CSAT`;
* `Complexity.npHard_CSAT`, from `Complexity.npHard_SAT` by transitivity of `≤ₘᵖ`;
* `Complexity.npComplete_CSAT : NPComplete CSAT`.

## Gates

* `python3 scripts/goal_state.py validate`
* `python3 scripts/check_closure.py`
* `lake build Start.CircuitSatLang`, `lake build Start.SatToCircuitCob`
