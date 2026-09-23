# M15-BGS-DIFFERENT — an oracle that separates: `P^B ≠ NP^B`

`Start/BakerGillSolovay.lean` carries out the separating half of Baker–Gill–Solovay on top of the
relativized classes of `Start/OracleClasses.lean`, the counting step of `Start/OracleDiag.lean`
and the enumeration of `Start/OracleEnum.lean`.

## The language

`Complexity.BGS.langB f : Language` is the standard one: `x` is accepted exactly when some word of
length `|x|` lies in the oracle `Complexity.BGS.oracleB f`.

* `Complexity.BGS.inNP_rel_langB` — **the language is in `NP^B`.**  The verifier
  `Complexity.BGS.verifier` checks that the witness has the length of the input
  (`Complexity.BGS.eqLenC`, built from the truncating subtraction `Complexity.Cob.dropN` of
  `Start/CobhamRange.lean`) and asks the oracle about it; the witness bound is the identity.

## The oracle

`Complexity.BGS.stage f : ℕ → List Word × ℕ` is the construction: a finite oracle, as a list of
words, together with a threshold above which everything added later lies.  At stage `e + 1` the
`e`-th term `f e` of the enumeration is run on the unary input `1 ^ n`, where
`n = Complexity.BGS.diagLen f e` is above both the previous threshold and the length from which
`f e` is guaranteed to leave a word of that length unasked
(`Complexity.CobQ.exists_word_not_queried_unary`).

* if the run accepts, nothing is added, and the bookkeeping lemmas
  (`length_le_of_mem_stage`, `mem_stage_of_length_le`, `stage_subset_mono`, `stage_snd_mono`)
  show that no word of length `n` ever enters the oracle — `no_word_of_diagLen`;
* if the run rejects, the unasked word `Complexity.BGS.witness` of length `n` is added.

The new threshold is `max n (qlen (f e) n)`, the polynomial bound of
`Complexity.CobQ.polyQueryLen` on the length of the queries, so that everything the run asked
about is decided at that stage and is never changed afterwards.  That is what
`Complexity.BGS.run_stage_eq` needs: by the use principle `Complexity.CobQ.run_congr`, the run of
`f e` on `1 ^ n` with the finite oracle of stage `e` and with the completed oracle `B` agree.

## The separation

* `Complexity.BGS.not_inP_rel_langB` — for a surjective enumeration `f`, the language is not in
  `P^B`: given a term `t` deciding it, write `t = f e`; on `1 ^ n` the term accepts exactly when no
  word of length `n` is in `B`, a contradiction in both branches.
* `Complexity.bgs_different : ∃ B : Complexity.Oracle, ¬ Complexity.PeqNP_rel B` — **there is an
  oracle with `P^B ≠ NP^B`**, by `Complexity.CobQ.exists_enumeration`.

Note that no separate "uniform time bound in the index" is needed here: the machines are Cobham
terms, so every term of the enumeration is polynomial-time by construction, and the polynomial
bounds `Complexity.CobQ.polyQueryCount` and `.polyQueryLen` are read off the term itself.

## Gates

`lake build` (whole tree, no errors and no new warnings), `python3 scripts/check_sorry.py`,
`python3 scripts/check_closure.py`, `python3 scripts/goal_state.py validate`,
`python3 scripts/check_manifest.py`.
