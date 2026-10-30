# `c/`: a C implementation of the church-turing development

This directory holds a C implementation of the executable objects of the Lean development: the
λ-calculus, Cobham's polynomial-time terms, quantified Boolean formulas and, in later rounds, the
machines (the Krivine machine, multi-tape and space-bounded machines, the register programs). It
rests on a small C runtime of its own, the *base*.

The C code is written and verified by Aristotle (aristotlelib ≥ 3.1). Each C module must agree
with the Lean definitions it implements. Those definitions are restated, verbatim, in
`spec/CTSpec.lean`, which type-checks on its own with `import Mathlib`; that file names the
repository module each one comes from.

## Layout

| path | contents |
|---|---|
| `spec/*.lean` | the reference semantics (Lean), copied from `Start/` |
| `include/ct/*.h` | the public headers, one per module |
| `src/*.c` | the implementation |
| `tests/test_*.c` | executable tests, one program per module, exit status 0 on success |
| `proofs/` | Aristotle's note on its proof artifacts (kept internal by Aristotle; see PROOFS.md) |
| `PROOFS.md` | every verified property: its statement, status and artifact |
| `Makefile` | `make` builds `build/libct.a`; `make test` builds and runs every test |

## Conventions

- C11 (`-std=c11`), compiled with `-Wall -Wextra -Werror -pedantic`, using only the standard
  library (`stdint.h`, `stddef.h`, `stdbool.h`, `stdlib.h`, `string.h`; `stdio.h` in tests).
- No global mutable state. Every public function is reentrant.
- Every public function that can fail returns `ct_status` (`CT_OK`, `CT_ENOMEM`, `CT_EOVERFLOW`,
  `CT_ELIMIT`, `CT_EINVAL`) and writes its results through pointers.
- Lean's `ℕ` is unbounded; in C it is `uint64_t` with checked arithmetic. A function must return
  `CT_EOVERFLOW` instead of wrapping around. **Whenever it returns `CT_OK`, its result equals the
  Lean value.**
- Computations that can grow without bound (substitution, reduction, evaluation of Cobham terms)
  take explicit limits (fuel, maximal number of nodes, maximal word length) and return `CT_ELIMIT`
  when a limit is reached.
- Memory comes from the base's arenas. A module never frees individual objects: the caller
  destroys the arena.
- No undefined behavior on any input that satisfies the documented preconditions.
- Portable C: the code and the tests must also pass on arm64 macOS (Apple clang), where
  `_Alignof(max_align_t)` is 8, not 16 as on x86-64 Linux. Tests must not assume a particular
  alignment, word size beyond C11 guarantees, or `malloc` behavior.

## Modules

### Round 1

| module | C | Lean (`spec/CTSpec.lean`) |
|---|---|---|
| base | `ct_status`, arenas, checked `uint64_t` arithmetic, bit words (`CT.Word = List Bool`), vectors of words | — |
| lambda | terms with de Bruijn indices, `lift`, `subst`, `size`, `church`, equality, leftmost-outermost one-step reduction, normalization with fuel and a step count | `CT.Lambda`, `.lift`, `.subst`, `.size`, `.church`, `.step` |
| cob | Cobham terms and their evaluation on lists of words | `CT.Cob`, `CT.Cob.eval` |
| qbf | quantified Boolean formulas and their evaluation under an assignment | `CT.QBF`, `CT.QBF.eval` |

### Round 2: every executable definition of the development

Round 2 implements, in C, every definition of the Lean development that computes something: the
step functions of machines, evaluators, interpreters, compilers between models, type checkers,
normalizers and decision procedures. The Lean sources are uploaded with the round-2 prompt under
`ref/Start/`: copies of the repository's `Start/` modules on Lean v4.34 and Mathlib v4.34 (CI run
41038371877). They are reference material and not part of this directory.

Each definition that a C module implements is restated, verbatim from `ref/Start/`, in a spec
file of its part (`spec/Machines.lean`, `spec/Programs.lean`, `spec/Types.lean`,
`spec/Complexity.lean`, `spec/Automata.lean`, `spec/Further.lean`), with the same conventions as
`spec/CTSpec.lean`: a namespace `CT`, `import Mathlib` only, and a comment naming the source module.
A spec file must type-check on its own.

| part | modules (C) | Lean sources (`ref/Start/`) |
|---|---|---|
| F machines | `krivine`, `cbv`, `lazy`, `multitape`, `minsky`, `spacemachine`, `kcmachine`, `wlram`, `blc`, `combinators`, `pca` | `KrivineHeap`, `KrivineDecode`, `CbvMachine`, `CbvStepFn`, `LazyStepFn`, `LeftmostRun`, `DepthThreeModel`, `Minsky`, `MinskyCompile`, `SpaceMachine`, `KCMachine`, `WLModel`, `WLRAMInstruction`, `WLInterpreter`, `BLC`, `Combinators`, `PCA` |
| G programs and compilers | `regprog`, `cobcompile`, `oraclecob`, `transducer`, `code`, `pairing` | `CobRegProg`, `CobMultiTape`, `OracleCob`, `CobhamTransducer`, `MacroTransducer`, `CodePrimrec`, `CodeOps`, `Pairing`, `Encoding` |
| H type checkers and normalizers | `stlc`, `systemf`, `systemt`, `hm`, `fsub`, `lambdapi`, `coc`, `pts`, `mltt` | `StlcNbE`, `SystemF`, `SystemT`, `HMAlgorithmW`, `Unification`, `FsubComputable`, `LambdaPiInfer`, `LambdaPiNormalize`, `LambdaPiLFDecide`, `CoCInfer`, `PTSCheck`, `PTSNormalize`, `MLTTCheck`, `MLTTDecide`, `MLTTNormalize` |
| I logic and complexity | `sat`, `tseitin`, `resolution`, `cooklevin`, `qbfmachine`, `savitch`, `sumcheck`, `circuit`, `treeeval` | `Sat`, `ThreeSat`, `Tseitin`, `Resolution`, `CookLevinNPHard`, `QbfLinearize`, `QbfEvalMachine`, `SavitchReach`, `SavitchVM`, `SumCheck`, `ShamirVerifier`, `AC0`, `CircuitBuild`, `TreeEval` |
| J automata and star height | `dfa`, `starheight` | `StarHeightLocalDFA`, `StarHeightDFAReturns`, `StarHeightPSTRecognizer`, `StarHeightTranslation`, `StarHeightCoreClassCheck` |
| K further programs | one module per source | `LogspaceDeterministic`, `LogspaceRecursivePrograms`, `LogspaceQueryPrograms`, `SpaceProgDecide`, `SpaceToLogspaceRun`, `OracleMachine`, `OracleSpace`, `ShamirMachine`, `UniformAuto`, `LevinSearch`, `SizeChange`, `KleeneTwo`, `TM2Partrec`, `EvalGK` |

The module names in the C column are suggestions; one C module may implement several Lean
modules. The rest of `ref/Start/` is there because the listed modules import it.

Outside the scope of any round, because they are not programs: `noncomputable` definitions,
predicates, sets, measures and category-theoretic constructions, and functions that the
development proves uncomputable (the halting set, Kolmogorov complexity, Chaitin's Ω, the busy
beaver function).

## Verification goals

For every public function `f`:

1. **No undefined behavior** (Aristotle property kind `c_function_no_ub`).
2. **Agreement with the Lean definition** (natural-language properties, formalized by Aristotle).
   Whenever `f` returns `CT_OK`, its output encodes the value of the corresponding definition of
   `spec/` on the encoded input. For one-step reduction this means two things:
   - the reported successor `t'` satisfies `CT.Lambda.step t t'`, and the contracted redex is the
     leftmost-outermost one;
   - "normal form" is reported exactly when no `t'` with `CT.Lambda.step t t'` exists.
