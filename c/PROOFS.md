# PROOFS.md — verified properties (rounds 1 and 2)

This file lists every property of Part E: its statement, its status (**proved** / **refuted** /
**open**) and its artifact. For the nature of the artifacts, see `proofs/README.md`.

## What "proved" means here

- **The C code itself is verified.** Each proof is about the functions in `src/*.c` as written
  (not a model), and the statements use verbatim restatements of the reference definitions of
  `spec/CTSpec.lean` (`CT.Lambda`, `.lift`, `.subst`, `.size`, `.church`, `.step`, `CT.QBF.eval`,
  `CT.Cob.eval`, `CT.Word = List Bool`); `spec/CTSpec.lean` itself is unchanged.
- **Every statement combines the two goals of README.md:** (1) no undefined behavior for every input
  satisfying the stated caller obligations, and (2) agreement with the Lean definition whenever the
  function returns `CT_OK`.
- **Partial correctness.** Each statement says what holds *if* the function returns. Termination
  is not claimed.
- **Error returns.** "An error code" means one of `CT_ENOMEM`, `CT_EOVERFLOW`, `CT_ELIMIT`,
  `CT_EINVAL`. In every error case of a public function, its result parameters (`*out`,
  `*normal`, `*steps`, the buffer of `ct_word_to_string`) are left unchanged. Two exceptions
  concern static helpers only. The counters of the helpers (`budget` in `lambda.c`, `work` in
  `cob.c`) may have been decreased before an error. The flag `*out` of `normal_rec` may have been
  written before it returns `CT_ELIMIT`.
- **Caller obligations.** Every statement below holds under these conditions, in addition to the
  ones listed in its entry. The Properties table repeats them row by row.
  - A *live arena* was returned by `ct_arena_create` and has not been destroyed.
  - A *valid word* is a readable `ct_word` whose `bits` point to `len` readable bytes, each 0 or 1
    (as produced by the word functions). A *valid vector* is a readable `ct_vec` whose `items`
    point to `len` readable valid words.
  - A term or formula *built in a live arena* was returned by the module's constructors (or
    computed by its functions), and its nodes are still allocated and not modified.
  - Limit structures (`ct_lambda_limits`, `ct_cob_limits`) must have initialized fields. The
    counters passed to the static helpers (`budget` in `lambda.c`, `work` in `cob.c`) must point
    to a `uint64_t` holding an initialized value. `assign` in `qbf.c` must hold initialized `bool`s.
  - **Non-overlap.** Every written object (`*out`, `*normal`, `*steps`, a helper's counter, and
    the buffer `buf[0..cap-1]` of `ct_word_to_string`) must be distinct from the other written
    objects. It
    must also not overlap any input object, any memory reachable from the inputs (word bytes,
    vector `items` arrays, term and formula nodes, `assign`, the `gs` array of `ct_cob_comp`, the
    characters of a string), or the arena's internal records. Inputs that are only read may
    overlap each other (for example `u` and `v` of `ct_word_concat` may be the same word).

## Assumptions (the trusted base)

- **C library functions.** The proofs assume the standard C behavior of `malloc` (returns NULL
  or a fresh suitably aligned block), `free`, `memcpy` (copy between non-overlapping buffers),
  `memset` and `strlen`. Their implementations are not verified. Which function relies on which
  is listed below; without these assumptions the affected results are not established.
- **Linking.** `lambda.c`, `qbf.c` and `cob.c` call functions of `base.c` (`ct_arena_alloc`,
  `ct_arena_alloc_array` and the word/vector functions). Those calls are covered by the proofs of
  the `base.c` functions from their bodies; the results hold for any whole program that links
  `base.c` with the calling file. No contract of a `base.c` function is assumed.
- **Platform.** Implementation-defined behavior follows GCC/Clang on x86-64 Linux (`size_t` and
  `uint64_t` are 64-bit, `malloc` alignment is 16).

## Summary

All 48 public functions of Parts A–D (and their static helpers) are **proved**: no undefined
behavior and agreement with `spec/CTSpec.lean`, under the assumptions and caller obligations
above. No property was refuted and none is open. Absence of memory leaks is not
part of the verified claims (in particular, `ct_arena_destroy` is proved free of undefined
behavior, not proved to release every block).

## Properties

Artifact for every entry: *internal machine-checked proof (see `proofs/README.md`)*.

### Part B — λ-calculus (`src/lambda.c`) — priorities 1 and 2

Library functions used (through `ct_arena_alloc`): `malloc`, `free`. `ct_lambda_size` and
`ct_lambda_equal` use none.

| # | Function | Statement | Status |
|---|---|---|---|
| L1 | `ct_lambda_lift(a, n, k, t, lim, out)` | No UB; on `CT_OK`, `*out` is a term equal to `CT.Lambda.lift n k t`; otherwise an error code. Caller: `a` live arena; `t` built in a live arena; `lim` readable with initialized fields; `out` writable and not overlapping `*lim`, the nodes of `t` or the arena's records. | **proved** |
| L2 | `ct_lambda_subst(a, s, x, t, lim, out)` | No UB; on `CT_OK`, `*out` is a term equal to `CT.Lambda.subst s x t`; otherwise an error code. Caller: as L1, with `s`, `t` built in a live arena. | **proved** |
| L3 | `ct_lambda_size(t, max_depth, out)` | No UB; on `CT_OK`, `CT.Lambda.size t` fits in `uint64_t` and `*out` equals it; otherwise an error code. | **proved** |
| L4 | `ct_lambda_church(a, n, lim, out)` | No UB; on `CT_OK`, `*out` is a term equal to `CT.Lambda.church n`; otherwise an error code. | **proved** |
| L5 | `ct_lambda_step(a, t, lim, out, normal)` | No UB; on `CT_OK` either `*normal` is true, `*out == t` and there is **no** `t'` with `CT.Lambda.step t t'`, or `*normal` is false and `*out` is a term `t'` with `CT.Lambda.step t t'` obtained by contracting the **leftmost-outermost** redex (the head redex if `t` is one; otherwise a step in the function part, in the argument only when the function part is normal and not an abstraction, or under the abstraction). Hence "normal" is reported exactly when no `t'` with `CT.Lambda.step t t'` exists. | **proved** |
| L6 | `ct_lambda_normalize(a, t, fuel, lim, out, steps)` | No UB; on `CT_OK`, `*steps ≤ fuel`, `*out` is a term `u` with no `CT.Lambda.step` reduct, and `u` is reached from `t` by exactly `*steps` leftmost-outermost steps. **Fuel bound:** an error other than `CT_ELIMIT` (`CT_ENOMEM`, `CT_EOVERFLOW`) can only arise while computing one of the first `fuel` steps, from a term reached after `i < fuel` steps. No step beyond the first `fuel` is computed, and with `fuel == 0` the result is `CT_OK` or `CT_ELIMIT`. On error `*out` and `*steps` are unchanged. | **proved** |
| L7 | `ct_lambda_var`, `ct_lambda_app`, `ct_lambda_lam` | No UB; on `CT_OK`, `*out` encodes `var i`, `app f x`, `lam body` respectively (sharing the arguments). | **proved** |
| L8 | `ct_lambda_equal(s, t, max_depth, out)` | No UB; on `CT_OK`, `*out` is true exactly when `s` and `t` encode equal `CT.Lambda` values. | **proved** |
| L9 | static helpers `mk_node`, `lift_rec`, `subst_rec`, `size_rec`, `equal_rec`, `step_rec`, `normal_rec` | No UB under their callers' obligations (`budget` points to a `uint64_t` holding an initialized value; `budget` and the outputs are pairwise distinct and do not overlap the input nodes or the arena's records); each computes its part of the above (`subst_rec(…, x, d, …)` computes `subst (lift d 0 s) x t` for `d ≤ x`; `step_rec` computes one leftmost-outermost step or reports that there is none; `normal_rec` decides, without allocating, whether a term has no step, and its only error is `CT_ELIMIT`). | **proved** |

### Part D — QBF (`src/qbf.c`) — priority 3

Library functions used: the constructors use `malloc`, `free` (through `ct_arena_alloc`);
`ct_qbf_eval` uses none.

| # | Function | Statement | Status |
|---|---|---|---|
| Q1 | `ct_qbf_eval(p, assign, n, max_depth, out)` | No UB; on `CT_OK`, `*out == CT.QBF.eval σ p` where `σ i = assign[i]` for `i < n` and `σ i = false` for `i ≥ n`; otherwise an error code; `assign` is unchanged. Caller: `p` built in a live arena; `assign` points to `n` readable, initialized `bool`s (may be NULL if `n == 0`); `out` writable and not overlapping `assign` or the nodes of `p`. | **proved** |
| Q2 | `ct_qbf_var`, `ct_qbf_neg`, `ct_qbf_conj`, `ct_qbf_disj`, `ct_qbf_all`, `ct_qbf_ex` | No UB; on `CT_OK`, `*out` encodes the corresponding `CT.QBF` constructor applied to the arguments. | **proved** |
| Q3 | static helpers `mk_node`, `lookup`, `eval_rec` | No UB; `lookup` returns the value of a variable under the assignment updated by the quantifier bindings; `eval_rec` computes `CT.QBF.eval` under that assignment. | **proved** |

### Part C — Cobham terms (`src/cob.c`) — priority 4

Library functions used: `malloc`, `free` (constructors and evaluation, through the arena),
`memcpy` (`ct_cob_comp`, and `ct_cob_eval` through `ct_word_cons`/`ct_vec_cons`), `memset`
(`ct_cob_eval`, through `ct_word_replicate`).

| # | Function | Statement | Status |
|---|---|---|---|
| C1 | `ct_cob_eval(a, c, args, lim, out)` | No UB; on `CT_OK`, `*out` is the word `CT.Cob.eval c args` and its length is at most `lim->max_len`; otherwise an error code. Caller: `a` live arena; `c` built in a live arena; `args` a valid vector; `lim` readable with initialized fields; `out` writable and not overlapping `*args`, its items or their bytes, `*lim`, the nodes of `c` or the arena's records. | **proved** |
| C2 | static helpers `eval_rec`, `eval_comp`, `eval_brec` | Caller: as C1, with `work` pointing to a `uint64_t` holding an initialized value, distinct from `out`. No UB; on `CT_OK`, `*out` is `CT.Cob.eval c args` for the node `c`, of length at most `max_len`. | **proved** |
| C3 | `ct_cob_proj`, `ct_cob_empty`, `ct_cob_app`, `ct_cob_smash`, `ct_cob_brec` | No UB; on `CT_OK`, `*out` encodes the corresponding `CT.Cob` constructor. | **proved** |
| C4 | `ct_cob_comp(a, f, gs, ngs, out)` | No UB (the array size computation cannot wrap); on `CT_OK`, `*out` encodes `CT.Cob.comp f [gs[0], …, gs[ngs-1]]` (the array is copied). Caller: `gs` points to `ngs` readable pointers (may be NULL if `ngs == 0`). | **proved** |
| C5 | static helper `mk_node` | No UB; on `CT_OK`, `*out` is a fresh node holding the given fields. | **proved** |

Note on the fuel of `ct_lambda_normalize` (L6): once `fuel` steps have been taken, the function
only checks, through `normal_rec`, whether the current term is normal and returns `CT_ELIMIT` if
not. An earlier version of `src/lambda.c` computed one extra step before checking the fuel, so it
could return an error caused by that extra step. L6 covers the current code.

Note on the word-length limit: `lim->max_len` bounds every word computed by `ct_cob_eval`,
including a projection's result. A `proj i` whose argument is longer than `max_len` returns
`CT_ELIMIT` (an earlier version of `src/cob.c` returned such an argument unchanged); C1 covers
the current code.

### Part A — base (`src/base.c`)

Library functions used: `ct_arena_create` (`malloc`), `ct_arena_alloc` / `ct_arena_alloc_array`
(`malloc`, `free`), `ct_arena_destroy` (`free`), `ct_word_cons` / `ct_word_concat` / `ct_vec_cons`
/ `ct_vec_make` (`memcpy`), `ct_word_replicate` (`memset`), `ct_word_from_string` (`strlen`);
every allocating function also relies on `malloc`/`free` through the arena. The checked
arithmetic and the non-allocating word/vector functions use no library function.

| # | Function | Statement | Status |
|---|---|---|---|
| A1 | `ct_arena_create(out)` | No UB; returns `CT_OK` with `*out` a new empty arena, or `CT_ENOMEM` with `*out` unchanged. | **proved** |
| A2 | `ct_arena_alloc(a, size, align, out)` | No UB; for an object of a C type of positive size `size` whose alignment divides 16: on `CT_OK`, `*out` points to a fresh, suitably aligned, uninitialised object owned by the caller until the arena is destroyed; otherwise an error code, nothing changed. A call with `size == 0` returns `CT_EINVAL` without touching memory. | **proved** |
| A3 | `ct_arena_alloc_array(a, count, elem_size, align, out)` | No UB (`count * elem_size` is overflow-checked); on `CT_OK`, `count > 0` and `*out` points to a fresh array of `count` elements; otherwise an error code. A call with `count == 0` or `elem_size == 0` returns `CT_EINVAL` without touching memory. | **proved** |
| A4 | `ct_arena_destroy(a)` | No UB when `a` is NULL, or a live arena whose blocks the caller gives up (neither the arena nor any of its blocks is used afterwards). Not claimed: that every block and the arena are released (absence of memory leaks is not verified). | **proved** |
| A5 | `ct_u64_add`, `ct_u64_sub`, `ct_u64_mul` | No UB; `CT_OK` with the exact mathematical result exactly when it fits in `uint64_t` (for `sub`: when `y ≤ x`); otherwise `CT_EOVERFLOW` with `*out` unchanged. | **proved** |
| A6 | `ct_word_empty`, `ct_word_get`, `ct_word_drop`, `ct_word_take` | No UB; produce `[]`, `w[i]` (`CT_EINVAL` if `i ≥ length`), `w.drop n`, `w.take n`. | **proved** |
| A7 | `ct_word_cons`, `ct_word_replicate` | No UB; on `CT_OK`, produce `b :: w`, `List.replicate n b`; otherwise an error code. | **proved** |
| A8 | `ct_word_length`, `ct_word_tail`, `ct_word_from_string`, `ct_word_to_string`, `ct_word_concat`, `ct_word_equal` | No UB; return `w.length`; produce `w.tail`; parse a `'0'`/`'1'` string (`CT_EINVAL` on other characters); print `w` into a buffer of capacity `cap` when `length + 1 ≤ cap` (`CT_EINVAL` otherwise; the buffer must not overlap `*w` or its bytes); produce `u ++ v`; decide `u = v`. | **proved** |
| A9 | `ct_vec_get`, `ct_vec_tail`, `ct_vec_cons` | No UB; produce `v.getD i []` (missing index reads as the empty word), `v.tail`, `w :: v`. | **proved** |
| A10 | `ct_vec_make`, `ct_vec_length` | No UB; produce `[ws[0], …, ws[n-1]]`; return `v.length`. | **proved** |
| A11 | static helpers `bits_alloc`, `items_alloc` | No UB for positive sizes; fresh arrays from the arena. | **proved** |

---

# Round 2

## Status of the parts

| part | status | C modules written (header, source, test) |
|---|---|---|
| F machines | **partly done** | `krivine`, `cbv`, `lazy`, `leftmost`, `multitape`, `minsky`, `spacemachine` |
| G programs and compilers | not started | — |
| H type checkers and normalizers | not started | — |
| I logic and complexity | not started | — |
| J automata and star height | not started | — |
| K further programs | not started | — |

Part F, in the order of its table:

| Lean source | status | C module |
|---|---|---|
| `KrivineHeap` (with the definitions of `KrivineTable` and `Krivine` it uses) | done (C and tests) | `krivine` |
| `KrivineDecode` | done (C and tests) | `krivine` |
| `CbvMachine`, `CbvStepFn` | done (C and tests) | `cbv` |
| `LazyStepFn` (with the definitions of `LazyMachine` it uses) | done (C and tests) | `lazy` |
| `LeftmostRun` (with `Lambda.step_normal` of `EvalSound`) | partly done: `nstep`, `closure`; the code-level functions `nstep_code`, `isNormal_code`, `haltsBy_code` are not yet written | `leftmost` |
| `DepthThreeModel` | done (C and tests) for every computable definition | `multitape` |
| `Minsky` (with `CMInstr`, `CM`, `CMConf` of `FsubGhelli`) | done (C and tests) | `minsky` |
| `MinskyCompile` | not started | — |
| `SpaceMachine` | done (C and tests) | `spacemachine` |
| `KCMachine` | not started | — |
| `WLModel`, `WLRAMInstruction`, `WLInterpreter` | not started | — |
| `BLC`, `Combinators`, `PCA` | not started | — |

Every definition implemented in round 2 was restated verbatim from `ref/Start/` (namespace `CT`,
`import Mathlib` only, a comment naming the source module before each one) and type-checked on its
own. That formal restatement is kept internal by Aristotle and is not delivered in this
directory (`spec/Machines.lean` is left empty); each entry below names the Lean definition and its
source module in `Start/`, which fix the meaning of the statement.

**Round-1 code.** No round-1 source file was changed in round 2 (no bug was found).
`tests/test_base.c` was replaced by the uploaded version (line 55 requests
`_Alignof(max_align_t)` instead of 16).

## Verification status of round 2

Verification goals (README.md): for every public function, (1) no undefined behavior on every input
satisfying the documented preconditions, and (2) whenever it returns `CT_OK`, its output encodes the
value of the corresponding Lean definition of `Start/` (named in each entry) on the encoded input. For a step function this
means: the reported successor is the Lean successor, and "halted"/"stuck" is reported exactly when
the Lean step function returns `none`.

The caller obligations of round 1 apply (live arenas, terms built in a live arena and not
modified, initialized limit structures, written objects distinct from each other and from the
inputs). In addition, for round 2: arrays passed with a length or capacity have at least that many
elements; enumeration fields (`kind`, moves, labels) hold one of the documented values; the indices
stored in tables, heaps and stacks are in range where the header says so. Assumptions: those of
round 1 (standard behavior of `malloc` and `free`; the same platform).

Proofs were started in the order of the parts. Two properties are **proved**; every other
round-2 property is **open** (not yet proved and not refuted). No round-2 property is refuted.

Artifact for every **proved** entry: *internal machine-checked proof (see `proofs/README.md`)*.
Open entries have no artifact yet.

### Part F — `krivine` (`src/krivine.c`)

| # | Function | Lean definition | Statement (both goals) | Status |
|---|---|---|---|---|
| F1 | `ct_kclos_mk(a, code, env, out)` | `Krivine.Clos.mk` | For a live arena `a`, a term `code` representing `t` and an environment `env` representing `e` (NULL, or nodes built by `ct_kenv_cons` whose closures were built by `ct_kclos_mk`): no UB; on `CT_OK`, `*out` points to a new closure representing `Krivine.Clos.mk t e`; otherwise an error code and `*out` unchanged. | **proved** |
| F2 | `ct_kenv_cons(a, head, tail, out)` | `List.cons` on `Krivine.Env` | For a live arena, a closure `head` representing `c` and an environment `tail` representing `e`: no UB; on `CT_OK`, `*out` points to a new list node representing `c :: e`; otherwise an error code and `*out` unchanged. | **proved** |
| F3 | `ct_krivine_flatten`, `ct_krivine_tab_of` | `Impl.flatten`, `Impl.tabOf`, `Impl.rootOf` | No UB; on `CT_OK` the new table and root are `flatten t tab` (resp. `tabOf t`, `rootOf t`). | open |
| F4 | `ct_krivine_dec_term_f`, `ct_krivine_dec_term` | `Impl.decTermF`, `Impl.decTerm` | No UB; on `CT_OK` the term built is `decTermF tab fuel p` (resp. `decTerm tab p`). | open |
| F5 | `ct_krivine_dec_clos_f`, `ct_krivine_dec_env_f`, `ct_krivine_dec_clos`, `ct_krivine_dec_env` | `Impl.decClF`, `Impl.decEnvF`, `Impl.decClos`, `Impl.decEnvP` | No UB; on `CT_OK` the closure/environment built is the value of the definition. | open |
| F6 | `ct_krivine_env_nth` | `Impl.envNth` | No UB; returns true with `*out = q` iff `envNth heap e n = some q`. | open |
| F7 | `ct_krivine_dec_state`, `ct_krivine_init_state` | `Impl.decState`, `Impl.initState` | No UB; on `CT_OK` the state written is `decState tab s` (resp. `initState t`). | open |
| F8 | `ct_krivine_hstep` | `Impl.hstep` | No UB; on `CT_OK`, `*stuck` is true and the state unchanged iff `hstep tab s = none`; otherwise the label and the new state are those of `hstep tab s = some (l, s')`. `CT_ELIMIT` only when the heap or the stack is full. | open |
| F9 | `ct_krivine_unfold`, `ct_krivine_unfold_env`, `ct_krivine_spine`, `ct_krivine_state_decode` | `Clos.unfold`, `unfoldEnv`, `spine`, `State.decode` | No UB; on `CT_OK` the term built is the value of the definition. | open |

### Part F — `cbv` (`src/cbv.c`)

| # | Function | Lean definition | Statement (both goals) | Status |
|---|---|---|---|---|
| F10 | `ct_cek_cont_arg`, `ct_cek_cont_fn` | `Frame.arg u e :: k`, `Frame.fn c :: k` | No UB; on `CT_OK` the new continuation represents the list. | open |
| F11 | `ct_cek_init` | `CEK.State.init` | No UB; writes `eval t [] []`. | open |
| F12 | `ct_cek_step` | `CEK.stepFn` | No UB; on `CT_OK`, `*halted` iff `stepFn s = none`; otherwise `*out` represents `s'` with `stepFn s = some s'`. | open |
| F13 | `ct_cek_beta_count` | `CEK.Label.betaCount` | No UB; returns the value of the definition. | open |
| F14 | `ct_cek_plug`, `ct_cek_decode` | `CEK.plug`, `CEK.State.decode` | No UB; on `CT_OK` the term built is the value of the definition. | open |
| F15 | `ct_cek_kweight`, `ct_cek_measure` | `CEK.kWeight`, `CEK.measure` | No UB; on `CT_OK` the value is the Lean value (`CT_EOVERFLOW` if it does not fit). | open |

### Part F — `lazy` (`src/lazy.c`)

| # | Function | Lean definition | Statement (both goals) | Status |
|---|---|---|---|---|
| F16 | `ct_lenv_cons`, `ct_lazy_cell_orig`, `ct_lazy_init` | `List.cons`, `Lazy.Cell.orig`, `Lazy.LState.init` | No UB; the result represents the value of the definition. | open |
| F17 | `ct_lazy_beta_count`, `ct_lazy_forced` | `Lazy.LLabel.betaCount`, `Lazy.LLabel.forced` | No UB; the result is the value of the definition. | open |
| F18 | `ct_lazy_step` | `Lazy.lstepFn` | No UB; on `CT_OK`, `*halted` (state unchanged) iff `lstepFn s = none`; otherwise the state now represents `s'` with `lstepFn s = some s'`. `CT_ELIMIT` only when the stack or the heap is full. | open |

### Part F — `leftmost` (`src/leftmost.c`)

| # | Function | Lean definition | Statement (both goals) | Status |
|---|---|---|---|---|
| F19 | `ct_leftmost_step_normal` | `Lambda.step_normal` | No UB; on `CT_OK`, `*none` iff `step_normal t = none`, otherwise `*out` is `t'` with `step_normal t = some t'`. | open |
| F20 | `ct_leftmost_nstep`, `ct_leftmost_closure` | `Lambda.nstep`, `Lambda.closure` | No UB; on `CT_OK` the term is the value of the definition. | open |

### Part F — `multitape` (`src/multitape.c`)

| # | Function | Lean definition | Statement (both goals) | Status |
|---|---|---|---|---|
| F21 | `ct_mt_literal_eval`, `ct_mt_gate_input_eval`, `ct_mt_gate_count` | `Literal.eval`, `GateInput.eval`, `Circuit3.gateCount` | No UB; on `CT_OK` the value is the Lean value (cube `Fin nv → Bool`). | open |
| F22 | `ct_mt_headmove_apply`, `ct_mt_update` | `HeadMove.apply`, `multiTapeUpdate` | No UB; on `CT_OK` the tapes represent the Lean result; `CT_ELIMIT` only when a head would leave its window. | open |
| F23 | `ct_mt_step`, `ct_mt_run_steps` | `FiniteMultiTapeMachine.step` (`multiTapeStep`), `runSteps` | No UB; on `CT_OK`, "halted"/`none` is reported exactly when the Lean result is `none`; otherwise the configuration represents the Lean result. | open |
| F24 | `ct_mt_init` | `FiniteMultiTapeMachine.init` | No UB; on `CT_OK` the configuration represents `M.init input`. | open |

### Part F — `minsky` (`src/minsky.c`)

| # | Function | Lean definition | Statement (both goals) | Status |
|---|---|---|---|---|
| F25 | `ct_minsky_reg`, `ct_minsky_base`, `ct_minsky_godel` | `KInstr.reg`, `base`, `godel` | No UB; on `CT_OK` the value is the Lean value (`CT_EOVERFLOW` when it does not fit). | open |
| F26 | `ct_minsky_inc_f`, `ct_minsky_test_f`, `ct_minsky_exit_l` | `incF`, `testF`, `exitL` | No UB; on `CT_OK` the instruction/label is the Lean value. | open |
| F27 | `ct_minsky_isize`, `ct_minsky_off`, `ct_minsky_block_f` | `isize`, `off`, `blockF` | No UB; on `CT_OK` the value is the Lean value. | open |
| F28 | `ct_minsky_compile`, `ct_minsky_compile_aux` | `compile`, `compileAux` | No UB; on `CT_OK` the output array encodes the two-counter program `compile M` (resp. `compileAux M (M.drop s) s`). | open |
| F29 | `ct_minsky_enc_c` | `encC` | No UB; on `CT_OK` the configuration is `encC M k ⟨pc, r⟩`. | open |

### Part F — `spacemachine` (`src/spacemachine.c`)

| # | Function | Lean definition | Statement (both goals) | Status |
|---|---|---|---|---|
| F30 | `ct_sp_config_space`, `ct_sp_write_at`, `ct_sp_move_work`, `ct_sp_move_in` | `Config.space`, `writeAt`, `moveWork`, `moveIn` | No UB; on `CT_OK` the value is the Lean value (`CT_ELIMIT` if a tape does not fit its buffer). | open |
| F31 | `ct_sp_accept`, `ct_sp_step_list` | `Machine.accept`, `Machine.stepList` | No UB; on `CT_OK` the successors written are, in order, the elements of `M.stepList x c`. | open |
| F32 | `ct_sp_init`, `ct_sp_const_machine` | `init`, `Machine.constMachine` | No UB; the result represents the Lean value. | open |

## Not implemented

Definitions of the round-2 scope that are skipped because they cannot be implemented faithfully
in C (README.md: noncomputable definitions, predicates, unbounded searches):

| Lean source | definitions | reason |
|---|---|---|
| `LeftmostRun` | `haltTime`, `nf` | defined with `sInf` over all natural numbers (an unbounded search for a normal form; noncomputable) |
| `DepthThreeModel` | `RawClause.eval`, `Circuit3.middleEval`, `Circuit3.eval` | `noncomputable` (classical decision over finite sets) |
| `DepthThreeModel` | `Circuit3.Computes`, `MultiTapeHaltsIn` | predicates |
| `CbvMachine` | `IsValue`, `cbvstep`, `CbvNormal`, `cbvIn`, `Trans`, `IsFinal`, `Run`, `Good`, `Frame.Good`, `State.Good`, `Stuck` | predicates and relations |
| `LazyMachine` | `LTrans`, `LStep`, `LFinal`, `LRun` | relations |
| `Minsky` | `KM.Step`, `KM.HaltsFrom`, `KM.Halts`, `RegsBelow` | relations and predicates |
| `SpaceMachine` | `Machine.Deterministic`, `Machine.WellFormed`, `Machine.Step`, `Accepts`, `SpaceBoundedOn`, `SpaceBounded`, `NSPACE`, `DSPACE`, `LOGSPACE`, `PSPACE`, `NPSPACE` | predicates and complexity classes |

Definitions of round-2 sources that are computable but not yet written (remaining work, not
skipped): `nstep_code`, `isNormal_code`, `haltsBy_code` of `LeftmostRun` (they work on the Gödel
codes `Lambda.code_step'` of `EvalSound`), and every definition of the sources marked "not
started" above.
