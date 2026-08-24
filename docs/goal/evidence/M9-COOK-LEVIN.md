# M9-COOK-LEVIN

**Status:** BACKEND_PARTIAL

Modules `Start/Sat.lean`, `Start/Tseitin.lean`, `Start/CookLevin.lean`, all imported by
`Start.lean`.  They build without `sorry` and without linter warnings.

Two of the three exit criteria are met unconditionally: Boolean formulas and satisfiability are
encoded as a language over binary words, and **SAT is proved to be in NP**.  The third — that
every language in `NP` reduces to SAT — is *not* proved; what is proved is that it follows from a
single precisely stated compilation hypothesis, together with the Tseitin translation, which is
formalized in full.

## Formulas as a language over binary words (first exit criterion)

`Start/Sat.lean`.  A CNF is a list of clauses, a clause a list of literals, a literal a pair
`(sign, index)`; `Complexity.Sat.cnfVal σ F` is the truth value of `F` under the assignment `σ`,
a binary word whose missing bits read `false`.

Words encode CNFs by a prefix-free token code that is read **from the right**, which is the
direction in which Cobham's bounded recursion on notation consumes its argument:

* `1` — a tick, incrementing the variable index of the literal being read;
* `0 1` — a negative literal on the current tick count, `0 0 1` — a positive literal;
* `0 0 0` — a clause separator.

`encLit`, `encClause`, `encCnf` write the code; the decoder `decode : Word → Cnf` is a total,
junk-tolerant automaton (`DSt`, `dstep`, `drun`), so every word denotes some CNF.
`decode_encCnf` proves that decoding inverts the encoding.  `SAT` is the language
`{u | ∃ σ, cnfVal σ (decode u) = true}`, and `SAT_encCnf`, `SAT_encCnf_nil`,
`not_SAT_encCnf_empty_clause` show it is neither empty nor everything.

## SAT is in NP (second exit criterion)

`Complexity.Sat.inNP_SAT`.  The verifier is an explicit Cobham term.

* `MSt`/`mstep`/`mrun` is a second automaton that reads the same token code while *evaluating* it
  against an assignment `σ`, carrying only four items of state: the truth of the clauses read so
  far, the truth of the clause being read, the unread suffix of `σ`, and a two-bit phase.
  `mrun_eq` proves it simulates the decoder: its state is always the truth value of the decoded
  data.
* `satMachine` implements that automaton as a Cobham term by bounded recursion on notation, with
  the state packed into a word `allSat :: curSat :: phase bits :: assignment pointer`;
  `eval_satMachine` proves `satMachine.eval [u, σ] = encMSt (mrun σ u)`.  The bound needed by
  `bRec` is `boundT`, and `length_boundT`/`mrun_ptr_length` supply the length inequality that
  makes the truncation harmless.
* `satVerifier` runs the machine and reads its `allSat` bit, after checking with `Cob.dropU` that
  the witness is not longer than the input; `eval_satVerifier` characterizes when it accepts.
* The witness bound is the identity: `litVal_take`, `clauseVal_take`, `cnfVal_take` and the index
  bound `drun_bounded` show that a satisfying assignment may always be truncated to the length of
  the input, since a word of length `n` decodes to a CNF whose variables are all `< n`.

Reusable Cobham gadgets added on the way: `bw`, `Cob.iteC`, `Cob.dropU` (drop `|u|` bits),
`Cob.tailN`, `Cob.nthBit`, `Cob.andT/orT/notT/iteT/consT`.

## The Tseitin translation (part of the third exit criterion)

`Start/Tseitin.lean`.  A circuit is a straight-line program `Circuit = List Gate`, written output
first, in which a gate may refer only to the gates after it in the list; the identifier of a gate
is the number of gates below it, so identifiers are stable under passing to a suffix, which makes
both the evaluator (`vals`, `out`) and the translation structurally recursive.  `csat C` says some
input word makes the output true.

`toCnf` is the Tseitin translation: the CNF variable `2 * j + 1` stands for the gate `j` and
`2 * i` for the circuit input `i`, and the clauses assert the defining equivalence of every gate
plus the truth of the output gate.

* `cnfValF_defsCnf` — the canonical assignment (input bits on the even variables, gate values on
  the odd ones) satisfies the defining clauses;
* `vals_of_cnfValF` — conversely, *every* satisfying assignment computes the gate values of the
  circuit run on the input it describes;
* `csat_iff_sat_toCnf` — **the translation preserves satisfiability**;
* `length_toCnf_le` — it has linear size, at most `3 * |C| + 1` clauses.

The bridge between the two notions of assignment (a word, as `SAT` uses, and a function, as the
induction uses) is `cnfVal_eq_cnfValF` together with `cnfVal_map_range` and the variable bound
`toCnf_vars`.

## What remains, and its exact statement

`Start/CookLevin.lean` isolates the missing step as

```lean
def CircuitCompilable (v : Cob) : Prop :=
  ∃ (cc : Word → Tseitin.Circuit) (gen : Cob),
    (∀ x, Tseitin.wf (cc x)) ∧
    (∀ x, Tseitin.csat (cc x) ↔ ∃ w : Word, v.eval [x, w] ≠ []) ∧
    (∀ x, gen.eval [x] = Sat.encCnf (Tseitin.toCnf (cc x)))
```

— an arbitrary Cobham verifier compiles, uniformly in the input, into a Boolean circuit whose
satisfying inputs are its accepted witnesses, the translation being produced by a Cobham term.
Granted it:

* `npHard_SAT_of_circuitCompilable` — **SAT is NP-hard**;
* `npComplete_SAT_of_circuitCompilable` — **SAT is NP-complete**;
* `peqNP_iff_inP_SAT_of_circuitCompilable` — `P = NP` iff `SAT ∈ P`.

The hypothesis is never assumed: it occurs only as an antecedent, and no other module mentions it.

Unconditionally, `polyManyOne_SAT_of_inP` shows that every language in `P` reduces to SAT (the
reduction decides the language and returns a fixed satisfiable or unsatisfiable formula), so the
reduction apparatus around `SAT` is not vacuous.

## Boundary

* **The compilation step is not formalized.**  Because polynomial time for functions is defined
  syntactically à la Cobham rather than by machines, compiling a verifier means a structural
  recursion over the Cobham term: values become fixed-width bit blocks with a monotone presence
  prefix, `comp`/`proj`/`app` are wiring, `take` is a pointwise conjunction, `smash` needs an
  addition chain for unary multiplication, and `bRec` unrolls into a chain of conditional steps —
  a constant number of nestings, hence polynomial size, but a large formalization.  On top of it
  the *emitter* `gen` must itself be a Cobham term, which requires writing the clause generator as
  nested bounded recursions with unary index arithmetic.
* Consequently `NPHard` is still not known to be inhabited, and `PeqNP` is neither proved nor
  refuted.
* Cobham's theorem (that `Cob` is exactly polynomial-time Turing computability) remains
  unformalized, as recorded in `M9-COMPLEXITY-CLASSES`; nothing here depends on it.
