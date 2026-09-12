# M13-QBF-SPACE — quantified Boolean formulas, evaluated in bounded memory

`Start/Qbf.lean`.  `TQBF` is the standard complete problem for polynomial space; this task is the
easy half of that statement — that deciding a closed quantified Boolean formula costs memory
polynomial in the formula — in the cost model of `M13-SAVITCH-VM`.

## Formulas

* `Complexity.Qbf.QBF` — variables, negation, conjunction, disjunction, and the two quantifiers,
  each binding a variable index.
* `Complexity.Qbf.QBF.eval` — the value under an assignment; a quantifier evaluates its body with
  the bound variable set to each of the two values.
* `Complexity.Qbf.QBF.height`, `.size`, `.varBound`, `.free`, `.Closed` — the measures the memory
  bound is stated in, and the free variables.
* `Complexity.Qbf.QBF.eval_congr` — the value depends only on the free variables; hence
  `Complexity.Qbf.QBF.eval_closed`, and `Complexity.Qbf.TQBF` is well defined.

## The evaluator

* `Complexity.Qbf.Cont` — an activation record: which connective or quantifier is pending, the
  subformula still to be evaluated, the value already obtained, and, for a quantifier, the value
  the bound variable had before the quantifier was entered.
* `Complexity.Qbf.step` — the deterministic transition, with short-circuiting conjunction and
  disjunction.
* `Complexity.Qbf.Trace B s t` — a run all of whose states carry at most `B` records.
* `Complexity.Qbf.trace_eval` — **the theorem**: started on `p` with an assignment and a stack, the
  machine reaches the answer `eval σ p` with *the same assignment and the same stack*, and never
  holds more than `height p` records above the stack it started with.  The restoration of the
  assignment is what makes the induction go through under quantifiers.
* `Complexity.Qbf.memBits`, `.tqbf_memBits_le`, `.tqbf_memBits_le_size` — the memory of a state in
  bits, and the bounds `varBound p + (height p + 1) · (2 w + 2)` and, with a pointer wide enough
  to address the formula, a bound quadratic in `size p`.

## Honest boundary

As in `Start/SavitchVM.lean`, memory is *counted* rather than encoded: the machine's states hold
subformulas, and `memBits` charges `w` bits for each, `w` being the width of a pointer into the
formula.  What is proved is the shape of the bound — one record per level of the formula, one bit
per variable.  The hard half of the PSPACE-completeness of `TQBF`, a generic reduction from a
space-bounded machine to a quantified Boolean formula, is not formalized.

## Gates

`lake build`, `python3 scripts/check_closure.py`, `python3 scripts/goal_state.py validate`.
