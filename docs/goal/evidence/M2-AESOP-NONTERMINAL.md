# M2-AESOP-NONTERMINAL

## Claim

The library must build without any `aesop: failed to prove the goal ...` warning.
Such a warning marks a *non-terminal* `aesop` call: the automation runs, fails to
close the goal, and hands the leftover goals to the following tactics.  Aesop
reports this because relying on the residue of a failed search is fragile.

The fix is a restructuring in every case: the automation is either replaced by
the explicit tactics that carry out the same step, or the surrounding proof is
rewritten so that the remaining automation is terminal.  No aesop option
(`warnOnNonterminal`, `terminal`, …) and no linter has been disabled, and no
`sorry` was introduced.

## Baseline

At the start of the task `lake build` emitted 98 such warnings:

| module | warnings |
| --- | --- |
| `Start/Arithmetic.lean` | 5 |
| `Start/Church.lean` | 1 |
| `Start/CodeOps.lean` | 14 |
| `Start/CodePrimrec.lean` | 31 |
| `Start/Combinators.lean` | 3 |
| `Start/Computability.lean` | 14 |
| `Start/Encoding.lean` | 4 |
| `Start/EvalCorrect.lean` | 1 |
| `Start/EvalSound.lean` | 14 |
| `Start/Pairing.lean` | 10 |
| `Start/Sqrt.lean` | 1 |

## Work done

Fully cleared modules (no `aesop: failed` warning remains):

- `Start/Sqrt.lean`, `Start/Church.lean`, `Start/Encoding.lean`,
  `Start/Combinators.lean`, `Start/Arithmetic.lean`, `Start/Pairing.lean`,
  `Start/EvalCorrect.lean`.

Representative restructurings:

- `LambdaComputable.sqrt`, `LambdaComputable.succ`, `LambdaComputable.zero`,
  `LambdaComputable.unpairLeft/unpairRight`, `LambdaComputable2.pair/add`:
  the `∃ F, ∀ n m, f n = some m ↔ …` goal is now discharged by an explicit
  `refine ⟨F, fun n m => ⟨fun h => ?_, fun h => ?_⟩⟩`, using
  `Part.some_inj` and `Lambda.unique_church_reduct` in the two directions.
- `Lambda.decode_lt_1/2/3` (`Start/Encoding.lean`): the case analysis that
  aesop performed on `Nat.unpair` is now written out with
  `split_ifs` / `Prod.mk.injEq` / `subst`.
- `Start/Pairing.lean`: the four reduction steps for `unpairLeft`/`unpairRight`
  are now congruence proofs built from `Lambda.reduces_app{,_left,_right}`,
  and the `if`-elimination is factored into the new reusable lemma
  `Lambda.ite_lt'_church`.
- `Lambda.code_step_beta` (`Start/EvalCorrect.lean`): the two side conditions
  `c₁ < c`, `c₂ < c` are stated up front, and the match is reduced by
  `simp only [hL, Nat.unpair_pair]` and `rw [if_pos …]`.
- `Start/Combinators.lean`: `Lambda.IsClosedAt_zero_iff_IsClosed` is a plain
  `constructor`; `Lambda.isZero_succ` and `Lambda.false_works` rewrite with the
  relevant equation instead of letting aesop guess it.

Dead code removed along the way: the placeholder definitions
`Lambda.unpairLeft := Lambda.church 0` and `Lambda.unpairRight := Lambda.church 0`
in `Start/Combinators.lean` (superseded by `Lambda.unpairLeft_impl` /
`Lambda.unpairRight_impl` in `Start/Pairing.lean`), and the two `#synth`
diagnostic commands in the same file.

## Tooling

`scripts/aesop_fix.py` reports the non-terminal sites of a module and tries a
list of candidate replacements, accepting one only when the module still
elaborates with no errors and no new warnings.  `scripts/aesop_trace.py` prints
the goals before and after a given site, which is what the manual rewrites are
based on.

## Status

Closed.  A full `lake build` (937 jobs, exit 0) emits **zero**
`aesop: failed to prove the goal` warnings; every module of the library is
clear, including the four that were open before: `Start/CodeOps.lean`,
`Start/CodePrimrec.lean`, `Start/Computability.lean` and
`Start/EvalSound.lean`.

Restructurings used for the last four modules:

- `Start/CodeOps.lean`: the side conditions that aesop was rediscovering in
  every branch (`(Nat.unpair m).1 < n` etc.) are now stated as explicit
  `have`s before the automation, which makes the remaining call terminal; the
  `Nat.unpair` matches are opened with `rcases h : Nat.unpair x with ⟨a, b⟩`
  followed by `obtain _ | _ | _ | k := a`.
- `Start/CodePrimrec.lean`: the `Primrec` scripts that mixed `convert` with a
  non-terminal `aesop`/`bound_nt` residue are replaced by direct term proofs
  built from `Primrec.ite`, `Primrec.option_bind`, `Primrec.option_casesOn`,
  `Primrec.option_getD`, `Primrec.list_getElem?`, `Primrec.nat_rec₁`,
  `Primrec₂.comp₂`, `Primrec.of_eq` and `Primrec.nat_strong_rec`.  The two
  strong-recursion equations are now proved from explicit unfolding lemmas,
  `Lambda.decode_code_eq_step` and the new `Lambda.subst_ecf_eq`, instead of
  by an aesop search through `Nat.strongRecOn_eq`.
- `Start/EvalSound.lean`: the evaluation-step case analyses are done with
  `rcases`/`split_ifs` and closed by `rfl` or by the corresponding
  `eval_ecf_*` equation.

New reusable lemmas introduced along the way, in `Start/Encoding.lean`:
`Lambda.lt_pair_of_pos`, `Lambda.lt_pair_one`, `Lambda.left_lt_app_code`,
`Lambda.right_lt_app_code`.

No aesop option and no linter was disabled, and no `sorry` was introduced.
The only warnings the build still emits are the pre-existing style notices
(`simp_all` flexibility, `show` linter) and the `lake` manifest notice; no new
warning class appeared.
