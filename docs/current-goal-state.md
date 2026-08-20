# Current goal state

- Active milestone: `M4`

| Rank | ID | Priority | Status | Depends on | Evidence | Open Boundary |
|---:|---|---|---|---|---|---|
| 10 | `M1-BOUNDARY-SORRY-CLOSURE` | `P0` | `DONE_STRONG` | - | docs/goal/evidence/M1-BOUNDARY-SORRY-CLOSURE.md |  |
| 20 | `M1-ENCODING-EXTRACTION-CLOSURE` | `P0` | `DONE_STRONG` | - | docs/goal/evidence/M1-ENCODING-EXTRACTION-CLOSURE.md |  |
| 30 | `M1-COMPUTABILITY-CLOSURE` | `P0` | `DONE_STRONG` | M1-ENCODING-EXTRACTION-CLOSURE | docs/goal/evidence/M1-COMPUTABILITY-CLOSURE.md |  |
| 40 | `M1-MODULAR-ENTRYPOINT-SWITCH` | `P1` | `DONE_STRONG` | M1-BOUNDARY-SORRY-CLOSURE, M1-COMPUTABILITY-CLOSURE | docs/goal/evidence/M1-MODULAR-ENTRYPOINT-SWITCH.md |  |
| 50 | `M1-BASIC-COMPAT-SHIM` | `P1` | `DONE_STRONG` | M1-MODULAR-ENTRYPOINT-SWITCH | docs/goal/evidence/M1-BASIC-COMPAT-SHIM.md |  |
| 60 | `M1-LINTER-HARDENING` | `P2` | `DONE_STRONG` | M1-MODULAR-ENTRYPOINT-SWITCH | docs/goal/evidence/M1-LINTER-HARDENING.md |  |
| 10 | `M2-EVAL-CORRECTNESS-DISCHARGE` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M2-EVAL-CORRECTNESS-DISCHARGE.md |  |
| 20 | `M2-STYLE-RESIDUE` | `P2` | `DONE_STRONG` | - | docs/goal/evidence/M2-STYLE-RESIDUE.md |  |
| 30 | `M2-AESOP-NONTERMINAL` | `P2` | `DONE_STRONG` | - | docs/goal/evidence/M2-AESOP-NONTERMINAL.md |  |
| 40 | `M2-EVAL-NORMALIZATION-HOLDS` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M2-EVAL-NORMALIZATION-HOLDS.md |  |
| 10 | `M3-STANDARDIZATION` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M3-STANDARDIZATION.md |  |
| 20 | `M3-LAMBDA-PREC-COMPILER` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M3-LAMBDA-PREC-COMPILER.md |  |
| 21 | `M3-LAMBDA-MU-CORRECTNESS` | `P1` | `DONE_STRONG` | M3-LAMBDA-PREC-COMPILER | docs/goal/evidence/M3-LAMBDA-MU-CORRECTNESS.md |  |
| 22 | `M3-PARTREC-IMP-LAMBDACOMPUTABLE` | `P1` | `DONE_STRONG` | M3-LAMBDA-PREC-COMPILER, M3-LAMBDA-MU-CORRECTNESS | docs/goal/evidence/M3-PARTREC-IMP-LAMBDACOMPUTABLE.md |  |
| 30 | `M4-CHURCH-TURING-LAMBDA` | `P2` | `DONE_STRONG` | M2-EVAL-NORMALIZATION-HOLDS, M3-PARTREC-IMP-LAMBDACOMPUTABLE | docs/goal/evidence/M4-CHURCH-TURING-LAMBDA.md |  |
| 40 | `M4-TM2-IMP-PARTREC` | `P3` | `DONE_STRONG` | - | docs/goal/evidence/M4-TM2-IMP-PARTREC.md |  |
| 50 | `M4-SCOTT-RICE` | `P3` | `DONE_STRONG` | M4-CHURCH-TURING-LAMBDA | docs/goal/evidence/M4-SCOTT-RICE.md |  |
| 60 | `M4-SMN-UNIFORM` | `P3` | `DONE_STRONG` | - | docs/goal/evidence/M4-SMN-UNIFORM.md |  |
| 70 | `M4-SELF-INTERPRETER` | `P3` | `DONE_STRONG` | M4-CHURCH-TURING-LAMBDA | docs/goal/evidence/M4-SELF-INTERPRETER.md |  |

Next: all tasks in the active milestone are `DONE_STRONG`.
