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
