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
| `spec/CTSpec.lean` | the reference semantics (Lean), copied from `Start/` |
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

## Modules

### Round 1

| module | C | Lean (`spec/CTSpec.lean`) |
|---|---|---|
| base | `ct_status`, arenas, checked `uint64_t` arithmetic, bit words (`CT.Word = List Bool`), vectors of words | — |
| lambda | terms with de Bruijn indices, `lift`, `subst`, `size`, `church`, equality, leftmost-outermost one-step reduction, normalization with fuel and a step count | `CT.Lambda`, `.lift`, `.subst`, `.size`, `.church`, `.step` |
| cob | Cobham terms and their evaluation on lists of words | `CT.Cob`, `CT.Cob.eval` |
| qbf | quantified Boolean formulas and their evaluation under an assignment | `CT.QBF`, `CT.QBF.eval` |

### Later rounds

- The Krivine machine with a heap (`Start/KrivineHeap.lean`, `Krivine.Impl.hstep`).
- Multi-tape machines (`Start/DepthThreeModel.lean`, `FiniteMultiTapeMachine`, `multiTapeStep`).
- Space-bounded offline machines (`Start/SpaceMachine.lean`).
- Word-register programs and their interpreter (`Start/CobRegProg.lean`, `Start/CobMultiTape.lean`).
- Oracle Cobham terms (`Start/OracleCob.lean`, `CobQ.eval` with an oracle callback).

## Verification goals

For every public function `f`:

1. **No undefined behavior** (Aristotle property kind `c_function_no_ub`).
2. **Agreement with the Lean definition** (natural-language properties, formalized by Aristotle).
   Whenever `f` returns `CT_OK`, its output encodes the value of the corresponding definition of
   `spec/CTSpec.lean` on the encoded input. For one-step reduction this means two things:
   - the reported successor `t'` satisfies `CT.Lambda.step t t'`, and the contracted redex is the
     leftmost-outermost one;
   - "normal form" is reported exactly when no `t'` with `CT.Lambda.step t t'` exists.
