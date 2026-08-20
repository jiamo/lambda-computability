# M4-SELF-INTERPRETER — a self-interpreter for the lambda calculus

## What was added

`Start/SelfInterpreter.lean` (imported by `Start.lean`).

The arithmetized evaluator `Lambda.eval_gk` works on codes: it maps the code of a term to the code
of its normal form.  What is added here is the lambda-level statement — Barendregt's *enumerator*:

- `Lambda.exists_self_interpreter` — there is a **closed** term `E` such that for every closed term
  `M`,
  `E (church (encode M))` **reduces to** `M` (not merely: is beta convertible with `M`).
- `Lambda.not_exists_quote` — the converse fails: no term `Q` satisfies `Q M ↠ church (encode M)`
  for every closed `M`.  Reduction cannot separate a term from its reducts, but the code can
  (`I` and `I I`).
- `Lambda.exists_self_interpreter_church` — non-vacuity check: on the code of `church k` the
  interpreter returns `church k`.

Supporting development, all proved:

- `Lambda.freeBelow`, `Lambda.subst_ne_self_of_not_freeBelow`, `Lambda.freeBelow_of_isClosedAt` —
  a structural rendering of the repository's substitution-based closedness predicate, together with
  the previously missing inversion direction.
- `Lambda.substEnv` / `Lambda.envCons` — parallel substitution of a family of terms for the free de
  Bruijn variables, with `Lambda.substEnv_var_id`, `Lambda.substEnv_congr` and
  `Lambda.substEnv_of_isClosed`.
- `Lambda.reduces_lift` — reduction is preserved by lifting (a reusable congruence that the
  repository did not have).
- `Lambda.zeroBranch` with `Lambda.zeroBranch_zero` / `Lambda.zeroBranch_succ` — the numeric
  two-way branch used by the interpreter.
- `Lambda.tagOf`, `Lambda.argOf`, `Lambda.leftOf`, `Lambda.rightOf` — the numeric destructors of
  `Lambda.encode`, with their computability and their values on codes of variables, applications
  and abstractions.
- `Lambda.evStep`, `Lambda.selfEval = Theta (evStep …)`, `Lambda.envExt`, and the unfolding lemma
  `Lambda.selfEval_unfold`.
- `Lambda.selfEval_correct` — the interpreter run on the code of an arbitrary term `t` in an
  environment term realizing `u` reduces to `substEnv u t`.  The abstraction case reduces under the
  binder, which is why the environment argument (rather than closed terms only) is needed.

The four destructors are computable, so `Lambda.exists_realizer_of_computable` supplies the closed
lambda terms the interpreter needs; no new assumption is introduced.

## Verification

- `lake build` succeeds, no errors and no linter warnings; no `sorry` in `Start/SelfInterpreter.lean`.
- `#print axioms Lambda.exists_self_interpreter` and `#print axioms Lambda.selfEval_correct`:
  only `propext, Classical.choice, Quot.sound`.
