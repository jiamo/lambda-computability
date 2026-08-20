# M2-STYLE-RESIDUE

Clear the residual style warnings that need per-proof restructuring

Strategy: work module by module, restructuring the affected proofs. No linter was disabled and no
`set_option linter.* false` / `nolint` was added.

Result: the three remaining warning classes are now empty. `lake build` emits no `linter.*`
warning at all.

| class | before | after |
|---|---:|---:|
| `linter.style.longLine` | 89 | 0 |
| `linter.flexible` | 83 | 0 |
| `linter.style.multiGoal` | 57 | 0 |

(The counts above are the ones recorded on the task board, which include duplicate reports for the
same source position; the number of distinct positions was 89 / 43 / 57.)

Per-module distinct warnings before the work:

| module | before | after |
|---|---:|---:|
| `Start/CodeOps.lean` | 54 | 0 |
| `Start/CodePrimrec.lean` | 46 | 0 |
| `Start/Computability.lean` | 17 | 0 |
| `Start/Pairing.lean` | 17 | 0 |
| `Start/EvalSound.lean` | 12 | 0 |
| `Start/Sqrt.lean` | 11 | 0 |
| `Start/Combinators.lean` | 9 | 0 |
| `Start/Reduction.lean` | 8 | 0 |
| `Start/Arithmetic.lean` | 8 | 0 |
| `Start/Encoding.lean` | 3 | 0 |
| `Start/Syntax.lean` | 2 | 0 |
| `Start/Church.lean` | 1 | 0 |
| `Start/Recursion.lean` | 1 | 0 |

What was done:

* `linter.flexible`: every non-terminal `simp` / `simp_all` was replaced by the explicit
  `simp only [...]` / `simp_all only [...]` set it actually used, so the proof no longer depends on
  the ambient simp set at that point.
* `linter.style.multiGoal`: tactic sequences that silently relied on several goals being in flight
  were focused with `·` bullets, or replaced by a single term-level `exact` / `refine`. In
  particular
  * `Lambda.unpairLeft_step2`, `Lambda.unpairRight_step2` (`Start/Pairing.lean`) are now direct
    congruence proofs built from the new `Lambda.reduces_app` lemma;
  * `LambdaComputable2.mult` and `LambdaComputable.pred` (`Start/Pairing.lean`) now use `use` for
    the witness instead of `constructor` plus a stray `case w`;
  * `Lambda.lift_ecf_primrec`, `Lambda.subst_ecf_primrec` (`Start/CodePrimrec.lean`) and
    `Lambda.subst_code_primrec` (`Start/CodeOps.lean`) are single applications of
    `Primrec.nat_strong_rec`;
  * `Lambda.subst_code_case1_primrec` (`Start/CodeOps.lean`) states its helper before applying
    `Primrec.of_eq`, so the rewrite is a single `refine`.
* `Start/EvalSound.lean`: `Lambda.code_step'_sound_var` now derives `code_step' (encode (var n)) =
  none` as a named `have` and rewrites with it, instead of an `aesop`-driven multi-goal script.
* `linter.style.longLine`: long declarations, comments and proof terms were reflowed at 100
  columns; several inline `match ... with | ... | ...` expressions were rewritten in multi-line
  form.

New reusable lemma:

* `Lambda.reduces_app` (`Start/Reduction.lean`): congruence of `Lambda.reduces` for applications in
  both arguments at once.

Gates:

```
python3 scripts/goal_state.py validate   # OK: 8 tasks validated
lake build                               # Build completed successfully, 0 linter warnings
```

## Re-check after the milestone-3/4 work

The modules that were added later (`Start/Realizer.lean`, `Start/EvalCorrect.lean`,
`Start/Minimization.lean`, `Start/PartrecLambda.lean`) and a handful of pre-existing proofs had
reintroduced 17 warnings in three classes.  They were cleared at their source, again without
disabling any linter:

* `flexible`: the non-terminal `simp_all` calls in `Start/CodeOps.lean` (1031),
  `Start/Computability.lean` (371), `Start/CodePrimrec.lean` (238, 1580, 1613) and
  `Start/EvalSound.lean` (308, 353) were replaced by the explicit `simp_all only [...]` sets they
  actually use;
* `style.show`: the three goal-changing `show` tactics in `Start/Computability.lean` (428, 456)
  and `Start/EvalSound.lean` (69) became `change`;
* `style.longLine`: the reflowed proof lines were kept within 100 columns;
* `unusedSimpArgs`: one unused simp argument in `Start/Minimization.lean` was dropped.

A full rebuild (`rm -rf .lake/build && lake build`) now produces no `linter.*` warning at all.
