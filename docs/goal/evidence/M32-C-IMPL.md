# M32: a C implementation, written and verified by Aristotle

Requested on 2026-10-30: "就在这个项目引入 c 版本的 这个项目的实现。包括 c 的底座。都让 Aristotle 来写。"

## Why Aristotle, and why C

- aristotlelib 3.1 rejects Lean-only projects. Probe project dcdf2ee8 returned: "Lean-only
  projects aren't supported right now as we focus on verified software and hardware".
- It verifies C, Verilog and, on some accounts, Rust.
  - C properties are either `c_function_no_ub` or natural-language statements.
  - Its proofs are Lean artifacts.
- The project therefore gets a C implementation of its executable objects, verified against the
  Lean definitions.

## Specification

- `c/README.md` gives the layout, the conventions (C11, no UB, checked `uint64_t` for ℕ, arenas,
  explicit limits) and the verification goals.
- `c/spec/CTSpec.lean` holds the reference definitions, copied verbatim from `Start/` into the
  namespace `CT`. It type-checks on its own with `import Mathlib` (Lean v4.33 here; Aristotle uses
  v4.34).

## Rounds

- Round 1 (M32-C-ROUND1): the base, the λ-calculus, Cobham terms, QBF.
- Later rounds: the machines (M32-C-MACHINES) and the register programs and oracle terms
  (M32-C-COBMT).
- M32-C-CI adds the C tests to CI.

## Round 1 result (Aristotle project 19976abc, run 6b89de8c, 2026-10-30)

The run took 08:02–11:00 UTC. It reports Parts A–D implemented and all 64 properties proved: the 48 we asked for
and 16 it added for its static helpers. None was refuted or left open.

**What the repository now holds**
- `c/include/ct/{base,lambda,cob,qbf}.h`, `c/src/{base,lambda,cob,qbf}.c`, `c/tests/test_{base,lambda,cob,qbf}.c`:
  Aristotle's files, byte for byte, except one test line (below).
- `c/PROOFS.md`: the statement and status of every property.
- `c/proofs/README.md`: Aristotle's note that the proof artifacts are kept internal.
- `c/ARISTOTLE_SUMMARY.md`: its report.
- The seven files of the specification commit (`Makefile`, `README.md`, `spec/CTSpec.lean`, …) came back
  unchanged; this was checked with `cmp`.

**Review done here**
- Every function was read against `c/spec/CTSpec.lean`:
  - `lift`; `subst` (it lifts `s` lazily, by `d` under `d` binders);
  - `size` (an index `i` counts `i + 1`); `church` (`f = var 1`, `x = var 0`);
  - the leftmost-outermost step (a redex at the root first, then the function, then the argument);
  - `Cob.eval`: `bRec` from the shortest suffix up, truncated to the length of the bound;
  - `QBF.eval`: quantifiers are a chain of bindings, which plays the role of `Function.update`.
- The code makes no system, file or network calls. It uses only `stdbool/stddef/stdint/stdio/stdlib/string`.
- `make -C c test`, with Apple clang 21 on arm64, `-std=c11 -Wall -Wextra -Werror -pedantic`:
  - all five test programs pass;
  - `test_lambda` reports that `PLUS 2 3` normalizes to `church 5` in 6 steps.
- The four test programs also pass under `-fsanitize=address,undefined`.
- The one change is in `tests/test_base.c`: `ct_arena_alloc(a, 16, 16, &q)` became
  `ct_arena_alloc(a, 16, _Alignof(max_align_t), &q)`.
  - `max_align_t` has alignment 16 on x86-64 Linux, the platform Aristotle assumed, but 8 on arm64 macOS.
  - With alignment 16 on arm64, the library correctly returns `CT_EINVAL`, and that test line failed 1000 times.

**Open (row M32-C-ROUND1-ARTIFACTS)**
- No proof artifact was returned, and every property's `artifact_paths` is empty. The verification is
  therefore Aristotle's report, not something we can re-check.
- The results are partial correctness: they say what holds if a function returns, not that it returns.
  Freedom from memory leaks is not claimed.
