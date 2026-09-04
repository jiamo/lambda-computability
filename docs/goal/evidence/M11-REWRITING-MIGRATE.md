# M11-REWRITING-MIGRATE

**Status:** DONE_STRONG

The eight client modules named by the task now obtain their generic rewriting lemmas from
`Start/Rewriting.lean`, each through a single bridging lemma.  Every public declaration name and
statement of those modules is unchanged, so no downstream module was touched; the whole library
builds with no error and no linter warning, and no `sorry` occurs anywhere under `Start/`.

## The bridges

| Module | Bridge | Generic results used |
|---|---|---|
| `Start/Reduction.lean` | `Lambda.reduces_iff_star` | `strip_of_between`, `confluent_of_diamond_of_between` |
| `Start/SystemTConfluence.lean` | `GodelT.reduces_iff_star` | `SN.star`, `confluent_of_sn` (Newman) |
| `Start/SystemFCConfluence.lean` | `SystemFC.reducesC_iff_star` | `strip_of_between`, `confluent_of_diamond_of_between` |
| `Start/LambdaPi.lean` | `LambdaPi.Red.iff_star`, `Pars.iff_star`, `Conv.iff_conv` | `strip`, `confluent_of_diamond`, `confluent_of_diamond_of_between`, `conv_iff_joins_of_confluent` |
| `Start/LambdaBetaEta.lean` | `Lambda.betaEtaTStar.iff_star`, `betaEtaReduces.iff_star`, `betaEtaConv.iff_conv` | `strip`, `confluent_of_diamond`, `conv_iff_joins_of_confluent` |
| `Start/LambdaEtaPostpone.lean` | `Lambda.etaReduces_iff_star` | `postpone_par_star`, `postpones_of_par` |
| `Start/LambdaPiEtaPostpone.lean` | `LambdaPi.EtaRed.iff_star`, `SRed.iff_plus`, `BetaEtaRed.iff_star` | `postpone_par_star`, `postponesPlus_of_par`, `star_alt_iff_of_postpones`, `sn_alt_aux` |
| `Start/LambdaPiEtaConfluent.lean` | `LambdaPi.StepE`/`EtaStepE` with `StepE.of_red`, `EtaStepE.of_etaRed` | `commute_of_stronglyCommute` (Hindley), `confluent_alt_of_commute` (Hindley–Rosen) |

The syntax-specific content — parallel reduction and its diamond property, the substitution
lemmas, the local diagrams, local confluence — stays in the client modules, as planned.

Two statements are worth recording because they are now proved once instead of four or two times:
`LambdaPi.confluent_step` and `Lambda.confluent_betaEtaStep` name the confluence of the respective
step relations in the interface's vocabulary, and `LambdaPi.postponesPlus_etaStep` names
η-postponement in the sharp form that the strong-normalization argument consumes.

## Gates

- `lake build` — success, 0 errors, 0 warnings.
- `python3 scripts/goal_state.py validate` — board validates.
- `python3 scripts/check_closure.py` — all modules in the import closure and all registered.
