# M14-TQBF-PSPACE-HARD

**Status:** DONE_WEAK — `TQBF` is proved `PSPACE`-hard; the membership `TQBF ∈ PSPACE`, and hence
the completeness statement, is the separate open task `M14-TQBF-IN-PSPACE`.

This note also records the evidence for the chain of tasks that produce the reduction:
`M14-QBF-COB-STEPCASE`, `M14-QBF-COB-STEP`, `M14-QBF-COB-INITACC`, `M14-QBF-COB-LEVELS`,
`M14-QBF-COB-MACHINE`, `M14-QBF-COB-REDUCTION`.

## The headline

`Complexity.Qbf.QBF.pspaceHard_tqbfLang` (`Start/QbfCobReduction.lean`):

```lean
theorem pspaceHard_tqbfLang {L : Complexity.Space.Language} (h : Complexity.Space.PSPACE L) :
    Complexity.PolyManyOne L tqbfLang
```

and its nondeterministic strengthening `Complexity.Qbf.QBF.npspaceHard_tqbfLang`: **every language
decided in polynomial space — even nondeterministically — is many-one reducible to `TQBF` by a map
of words computed in polynomial time**, polynomial time being Cobham's class
(`Complexity.Cob`) as used everywhere in this library, and `tqbfLang` the language of binary codes
of true closed quantified Boolean formulas.

## How it is built

* `Start/CobhamCond.lean` — the arithmetic the compiler needs: the normalised truth value of a
  term (`Complexity.Cob.eval_boolT`), comparison of two unary numbers (`.eval_ltU`, `.eval_leU`,
  `.eval_eqU`) and reading the bit of a word at a unary position (`.eval_bitU`).
* `Start/CobhamUnary.lean` — unary successor, predecessor, sum and minimum, and the assembly of a
  parameter word from the terms of its fields (`Complexity.Cob.eval_fieldsT`).
* `Start/CobhamFieldsApp.lean` — parameter words that carry a word (the input of the simulated
  machine) after their unary fields (`Complexity.Cob.eval_fieldTerm_app`, `.eval_tailWord`).
* `Start/QbfMachineDepth.lean` — the reduction formula at an arbitrary depth of the midpoint
  recursion: correctness at every depth at or above `savitchDepth`
  (`Complexity.Qbf.QBF.eval_machineFk`), closedness (`.closed_machineFk`) and
  `Complexity.Qbf.QBF.tqbf_machineFk_iff`, which is the statement the reduction needs.
* `Start/QbfCobCfg.lean` — the configuration-block formulas `cfgF` and `tgtF`
  (`Complexity.Qbf.QBF.enc_cfgF_eval`, `.enc_tgtF_eval`).
* `Start/QbfCobStepCase.lean` — one case of the step formula and its guard
  (`Complexity.Qbf.QBF.eval_stepCaseTerm`, `.eval_guardT`, `.eval_caseTerm`).
* `Start/QbfCobStep.lean` — the two sweeps over the head positions assemble the step formula
  (`Complexity.Qbf.QBF.enc_stepF_eval`).
* `Start/QbfCobInitAcc.lean` — the initial and accepting constraints
  (`Complexity.Qbf.QBF.enc_initF_eval`, `.enc_accF_eval`).
* `Start/QbfCobLevels.lean` — the sweep over the levels of the midpoint recursion, whose fields are
  affine in the level (`Complexity.Qbf.QBF.eval_levelsT`).
* `Start/QbfCobMachine.lean` — the concatenation of every piece: the code of the reduction formula
  is the value of one Cobham term at the input and a parameter word
  (`Complexity.Qbf.QBF.enc_machineFk_eval`).
* `Start/QbfCobReduction.lean` — the parameter word is removed: unary polynomials of the length of
  the input are Cobham functions (`Complexity.Cob.eval_onesT`, `.eval_powT`, `.eval_nsmulT`), so
  the reduction is one term of the input alone (`Complexity.Qbf.QBF.redTerm`,
  `.eval_redTerm`), and the hardness theorems follow from
  `Complexity.Qbf.QBF.tqbf_machineFk_iff` and the Savitch depth bound of `Start/QbfPspace.lean`.

In every one of these terms the padding constants are independent of the instance, so a single
term serves every machine, width, block index and level — which is what uniformity of the
reduction means.

## Boundary

`Complexity.Qbf.pspaceComplete_TQBF` is *not* available: the library has the easy half of
membership as a memory bound on the evaluating stack machine
(`Complexity.Qbf.tqbf_memBits_le_size`, quadratic in the size of the formula) but not yet a machine
of `Start/SpaceMachine.lean` deciding `tqbfLang` within a polynomial space bound, which is the
open task `M14-TQBF-IN-PSPACE`.  Until that is closed the completeness statement cannot be
formed, and this task stays `DONE_WEAK` with hardness proved.

## Gates

```
lake build                        # Build completed successfully (9179 jobs), 0 errors
python3 scripts/check_sorry.py    # OK: no sorry/admit in 460 modules
python3 scripts/check_closure.py  # OK: 459 modules, all in the import closure and all registered
python3 scripts/goal_state.py validate
python3 scripts/check_manifest.py
```

`#print axioms Complexity.Qbf.QBF.pspaceHard_tqbfLang` → `[propext, Classical.choice, Quot.sound]`.

## Addendum: hardness as a property of a language (`M14-PSPACE-HARDNESS-USE`)

`Start/QbfHard.lean` names the property and draws the consequences: `Complexity.Space.PSPACEHard`,
`.NPSPACEHard` and `.PSPACEComplete`; `Complexity.Space.pspaceHard_tqbfLang'` and
`.npspaceHard_tqbfLang'` restate the reduction theorems in that vocabulary;
`Complexity.Space.PSPACEHard.of_reduction` transports hardness along a reduction; and
`Complexity.Space.PSPACEHard.inP_of_inP`, `Complexity.Space.pspace_inP_of_tqbf_inP`,
`Complexity.Space.pspace_inNP_of_tqbf_inNP` and `Complexity.Space.tqbf_not_inP` say what a hard
problem is good for: a polynomial-time algorithm for `TQBF` would decide every language of
polynomial space in polynomial time, and one such language outside `P` keeps `TQBF` outside `P`.
`Complexity.Space.PSPACEComplete Complexity.Qbf.tqbfLang` remains unproved, for the reason recorded
above.
