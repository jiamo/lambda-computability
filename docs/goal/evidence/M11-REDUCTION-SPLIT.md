# M11-REDUCTION-SPLIT

**Status:** DONE_STRONG

`Start/Reduction.lean` had grown into two unrelated developments: the confluence of β-reduction
(the Tait–Martin-Löf parallel reduction argument, now routed through `Start/Rewriting.lean`) and a
collection of λ-term *encodings* — the Church numerals, the standard combinators and the predicate
`LambdaComputable` — that no part of the confluence proof uses and that most of its clients import
only for the encodings.

The encodings now live in `Start/ChurchCombinators.lean`:

* `Lambda.church` — the Church numeral of a natural number;
* `LambdaComputable` — a numeric function computed by a λ-term on the Church numerals;
* `Lambda.I`, `Lambda.K`, `Lambda.S`, `Lambda.pair`, `Lambda.fst`, `Lambda.snd`, `Lambda.succ`,
  `Lambda.fix` — the combinators, with their reduction lemmas.

`Start/Reduction.lean` keeps the confluence development and nothing else.

## What did not change

No declaration was renamed and no statement was weakened: the split is a move, module by
declaration, with `import Start.ChurchCombinators` added next to every `import Start.Reduction` in
the modules that used the moved names (`Start.lean`, `Start/Basic.lean`, `Start/Boundary.lean`,
`Start/Church.lean`, `Start/Computability.lean`, `Start/CodeOps.lean`, `Start/CodePrimrec.lean`,
`Start/LambdaBetaEta.lean`, `Start/ReducesIn.lean`).  Downstream modules are unaffected.

## Gates

* `python3 scripts/goal_state.py validate`
* `python3 scripts/check_closure.py`
* `lake build Start.ChurchCombinators`, `lake build Start.Reduction`
