# M7-OMEGA-ORACLE

**Status:** DONE_STRONG

Module `Start/OmegaOracle.lean`, now imported by `Start.lean` (see
`docs/goal/evidence/M7-VERIFICATION-DEBT.md`: the module did not compile and was not
reachable from any build target until this milestone).

* `Lambda.omegaBits n = ⌊Ω · 2 ^ n⌋` — the number formed by the first `n` binary digits of
  `Ω`, characterised by `Lambda.omegaBits_le`, `Lambda.lt_omegaBits_add_one`,
  `Lambda.omegaBits_spec`, and coherent across lengths (`Lambda.omegaBits_shift`).
* `Lambda.oracleRun` and `Lambda.partrec_oracleRun` — one partial recursive procedure which,
  fed `omegaBits n` together with `n` and a code `c`, terminates and answers halting
  correctly whenever the associated closed program has at most `n - 2` bits
  (`Lambda.oracleRun_spec`, `Lambda.chaitinOmega_prefix_decides_halting`). So finitely many
  bits of `Ω` settle the halting problem for all short programs.
* `Lambda.irrational_chaitinOmega` — a rational is a computable real
  (`Lambda.realComputable_of_eq_div`), so irrationality follows from
  `Lambda.not_realComputable_chaitinOmega`.

Gates: `lake build` succeeds; no `sorry`; no linter warnings.
