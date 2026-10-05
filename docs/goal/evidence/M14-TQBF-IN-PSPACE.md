# M14-TQBF-IN-PSPACE — TQBF lies in PSPACE, hence TQBF is PSPACE-complete

**Status:** DONE_STRONG (together with `M14-QBF-STEP-PROG` and `M14-TQBF-PSPACE-HARD`)

## Terminal statements

```lean
theorem Complexity.Qbf.tqbf_pspace : Complexity.Space.PSPACE Complexity.Qbf.tqbfLang
theorem Complexity.Space.pspaceComplete_tqbfLang :
    Complexity.Space.PSPACEComplete Complexity.Qbf.tqbfLang
theorem Complexity.Qbf.pspaceComplete_TQBF :
    Complexity.Space.PSPACEComplete Complexity.Qbf.tqbfLang
```

(`Start/QbfEvalCob.lean`; `#print axioms Complexity.Space.pspaceComplete_tqbfLang` gives
`propext, Classical.choice, Quot.sound`.)

`Complexity.Space.PSPACE` is membership in `DSPACE s` for a polynomial `s`, on the offline machine
of `Start/SpaceMachine.lean`; `Complexity.Space.PSPACEComplete L` is `PSPACE L ∧ PSPACEHard L`, and
the hardness half is the existing `Complexity.Space.pspaceHard_tqbfLang'` (`Start/QbfHard.lean`).

## The route

`M14-SPACE-COMPILE` left one gap: the step of the QBF evaluator had to be carried out by a tape
program on an encoding of its state (`M14-QBF-STEP-PROG`).  The route taken writes the step as
**Cobham terms** and lets the verified Cobham-to-tape compiler of `M21-COBHAM-TO-SPACE` produce the
tape program, instead of writing the tape program for the step by hand.

1. **A word evaluator** — `Start/QbfEvalMachine.lean`.  `Complexity.Qbf.EvalW.QS` is a state made
   of six words (the code still to be read, a stack of 7-field records written as unary fields,
   the mode, the assignment, the binding flags, a halting flag) and `Complexity.Qbf.EvalW.qstep`
   is its step, a case distinction on `Complexity.Qbf.EvalW.caseNum`.
   * `Complexity.Qbf.EvalW.halts` — from the initial state the machine halts on every word;
   * `Complexity.Qbf.EvalW.accepts_iff` — it halts accepting exactly on the words of
     `Complexity.Qbf.tqbfLang`;
   * `Complexity.Qbf.EvalW.inv_iterate`, `.length_fieldsWord_le` — every reachable state satisfies
     an invariant bounding each component by `regBound n = ((2n+10)^2 + 7)(n+5) + n + 1`.
2. **Iterating Cobham terms on a tape** — `Start/CobhamIterate.lean`.
   `Complexity.Space.iterDecider` is a tape program that computes an initial state with Cobham
   terms `init`, and then, while a designated register is non-empty, replaces the state by the
   values of Cobham terms `step` (`Complexity.Space.iterBody`, whose bridge lemma is
   `Complexity.Space.runs_iterBody`).  `Complexity.Space.pspace_of_cobIter`: if the stages of the
   iteration have polynomially bounded words, a halting stage is reached, and a designated word of
   that stage is non-empty exactly on `L`, then `PSPACE L` — however many rounds are needed.
3. **The step as Cobham terms** — `Start/QbfEvalCob.lean`.  `Complexity.Qbf.EvalW.caseT` computes
   the case number in unary, `Complexity.Qbf.EvalW.stepTs c` computes each case, and
   `Complexity.Qbf.EvalW.stepT` selects among them with `Complexity.Cob.tableSel`.
   * `Complexity.Qbf.EvalW.eval_caseT`, `.eval_stepTs` — correct on every state;
   * `Complexity.Qbf.EvalW.eval_stepT` — **the six terms compute the step of the evaluator**;
   * `Complexity.Qbf.EvalW.cobIter_eq` — the iteration of the terms is the run of the evaluator.

   General term combinators added on the way: `Complexity.Cob.takeBy`, `.dropBy`, `.setBy`
   (setting the bit of a word at a unary index), `.zerosT`, `.onesOf`, and total versions of the
   field accessors (`Complexity.Cob.eval_fieldTerm'`, `.eval_dropFieldsT'`).
4. `Complexity.Qbf.tqbf_pspace` instantiates `pspace_of_cobIter` with these terms, the halting time
   from `halts`, the acceptance from `accepts_iff` and the bound from the invariant.

## About `M14-QBF-STEP-PROG`

Its original exit criteria asked for the step as a hand-written tape program and the bridge lemma
of `Complexity.Space.Prog.realizes_loop`.  The tape program for one step that the proof uses is
`Complexity.Space.iterBody K 6 Complexity.Qbf.EvalW.stepT` — the compiled step terms followed by
the copy-back — with bridge lemma `Complexity.Space.runs_iterBody`, and the outer loop is
`Complexity.Space.Tracks.runs_whileNE` rather than `realizes_loop`.  The task-board row has been
rewritten to record this route; the deliverable it was opened for (`M14-TQBF-IN-PSPACE`) is met.

## Gates

```
lake build                        # Build completed successfully
python3 scripts/check_sorry.py
python3 scripts/check_closure.py
python3 scripts/goal_state.py validate
python3 scripts/check_manifest.py
scripts/pack_gate.sh HEAD
```
