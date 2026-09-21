# M14-QBF-STEP-FORMULA

**Status:** DONE_STRONG

The configuration graph of a space-bounded machine is written as quantified Boolean formulas:
configurations become words of a fixed width, one transition becomes a formula of size linear in
that width times the number of situations of the machine, and the whole reduction becomes a
*closed* formula that is true exactly when the machine accepts its input.  This is the machine
half of the PSPACE-hardness of `TQBF` except for one thing, recorded under Boundary: that the map
from an input to its formula is computable in polynomial time.

## What is built

### `Start/SpacePadded.lean` — configurations of a fixed width

The work tape of `Start/SpaceMachine.lean` grows as the machine writes, so two configurations with
the same contents may have tapes of different lengths.  `Complexity.Space.padTape` keeps the first
`s` cells and `Complexity.Space.pad` applies that to a configuration;
`Complexity.Space.Fits M x s` recognises the configurations whose state is one of the machine's,
whose input head is on the input or its end marker, whose tape has exactly `s` cells and whose
work head stands on one of them; `Complexity.Space.padStep` is the one-step relation between such
configurations.

Padding commutes with writing inside the bound (`padTape_writeAt`), so it is a bisimulation:
`padStep_pad` pads a step of the machine, `exists_step_of_padStep` un-pads one, and hence
`steps_padStep_of_steps` and `exists_steps_of_steps_padStep` transport whole runs.  Combining this
with the configuration count of `Start/SpaceConfigCount.lean` gives

* `Complexity.Space.accepts_iff_padStep` — acceptance is reachability in the padded graph;
* `Complexity.Space.accepts_iff_reachLe_padStep` — and reachability there within
  `2 ^ savitchDepth M x s` steps, which is the shape the midpoint recursion consumes.

### `Start/QbfCfgWord.lean` — a configuration as a word

`Complexity.Qbf.cfgWidth M x s = q + (n + 1) + s + s` and `Complexity.Qbf.cfgWord` write a
configuration in four blocks: the control state in unary, the position of the input head in unary,
the `s` cells of the work tape bit by bit, and the position of the work head in unary.  Unary
positions are what keep a transition *local*: a head moves by shifting a single `true`.

* `blockVal_eq_cfgWord_iff` — a block of an assignment carries the word of a configuration exactly
  when it carries its bits;
* `tapeOf_eq_tape` — then its tape block is that configuration's tape;
* `cfgWord_injective` — the encoding is faithful on configurations of width `s`;
* `WordStep`, `wordStep_length`, `reachLe_wordStep_iff` — the one-step relation read on words,
  and the fact that bounded reachability of words is bounded reachability of configurations.

### `Start/QbfMachine.lean` — the formulas

`QBF.litF`, `QBF.ff`, `QBF.disjAny` are a literal, the false formula and a disjunction over a
list, with their evaluation and size lemmas.  On top of them:

* `QBF.cfgF M x s a q i j` — block `a` carries the word of the configuration with state `q`,
  input head `i`, work head `j` and the tape the block itself carries (`QBF.eval_cfgF`);
* `QBF.tgtF` — the target block carries the new state, the new head positions, the bit written
  under the old work head and every other cell copied from the source block (`QBF.eval_tgtF`);
* `QBF.caseList` — every *situation* of the machine (state, both head positions, the bit read)
  together with the instructions available in it that stay inside the state set and inside the
  space bound (`QBF.mem_caseList`);
* `QBF.stepF M x s a b` — the disjunction over those cases of `cfgF ∧ literal ∧ tgtF`.

The three results about the step formula:

* `Complexity.Qbf.QBF.eval_stepF` — **it expresses one step**: it holds under an assignment
  exactly when the words in blocks `a` and `b` are the words of two configurations related by
  `padStep`, i.e. exactly `WordStep`;
* `Complexity.Qbf.QBF.size_stepF_le` — its size is at most
  `q · (n+1) · s · 2 · (18 q) · (15 · width + 13) + 4`: polynomial in `q`, `n` and `s`, with no
  hypothesis on the machine, because the cases run over the instructions a situation can possibly
  offer (`Complexity.Qbf.QBF.allInstr`, `Complexity.Qbf.QBF.length_allInstr`) rather than over the
  transition function's own list;
* `Complexity.Qbf.QBF.length_caseList_le` — the count of situations behind that bound.

Feeding the step formula to `Complexity.Qbf.QBF.reachF` and quantifying over the two endpoint
blocks gives the closed formula `Complexity.Qbf.QBF.machineF M x s`, with

* `Complexity.Qbf.QBF.eval_machineF` — **the reduction is correct**: for a well-formed machine
  running in space `s ≥ 1` on the input `x`, the formula is true (under any assignment, being
  closed in the two endpoint blocks) exactly when the machine accepts `x`;
* `Complexity.Qbf.QBF.size_machineF_le` — its size is bounded by the step-formula bound plus
  `savitchDepth · (43 · width + 21)` plus a fixed multiple of `width`, `s` and
  `q · (n+1) · s · width`, hence polynomial in `q`, `n` and `s`.

## Boundary

What is still missing for `TQBF` to be proved PSPACE-hard is that the map `x ↦ machineF M x s`
is computed from `x` in polynomial time: a syntactic transducer writing the formula, analysed in
the time model of `Start/ComplexityClasses.lean`.  Until then the statement above is a
polynomial-size reduction of acceptance to a true closed quantified Boolean formula, and the
hardness of `TQBF` is not claimed.  That remains the open task `M14-TQBF-PSPACE-HARD`.

## Gates

```
lake build                        # Build completed successfully, 0 errors
python3 scripts/check_sorry.py    # OK: no sorry/admit
python3 scripts/check_closure.py  # OK: all modules in the import closure and registered
python3 scripts/goal_state.py validate
python3 scripts/check_manifest.py
```
