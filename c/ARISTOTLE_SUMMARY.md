# Summary of changes for run 6b89de8c-9d70-4d0f-a2ff-277e91aa7e08
I've implemented Parts A–D in C, `make test` passes, and every property is proved under the caller obligations and library assumptions below. No property was refuted and none is open. The proof files are not in `proofs/`: they are kept internal, as `proofs/README.md` explains. `PROOFS.md` gives each property's statement, status and artifact.

You mentioned earlier that no files had appeared while credit was being used. All the deliverables listed at the end are now in the project directory and have been published.

**Two fixes to my own code during verification**
- **`ct_lambda_normalize`** used to compute one extra step before checking the fuel. That step could fail and return an error such as `CT_EOVERFLOW` instead of `CT_ELIMIT`.
  - Once `fuel` steps have been taken, it now only checks whether the term is normal, using a new non-allocating helper `normal_rec`, and returns `CT_ELIMIT` if it is not.
  - New tests in `tests/test_lambda.c` cover `fuel == 0`.
- **`ct_cob_eval`**: a `proj` whose argument is longer than `max_len` now returns `CT_ELIMIT`. Previously it returned the argument unchanged.

**What was implemented**
- **Part A** (`include/ct/base.h`, `src/base.c`, `tests/test_base.c`):
  - status codes;
  - arenas (create, aligned allocation with every size overflow-checked, destroy);
  - checked `uint64_t` add/sub/mul;
  - immutable bit words with every operation you listed;
  - word vectors in which a missing index reads as the empty word.
- **Part B** (`lambda.h/.c`, `test_lambda.c`):
  - terms with structural equality;
  - `lift`, `subst`, `size` and `church`;
  - one leftmost-outermost step;
  - normalization with fuel and a step count.
- **Part C** (`cob.h/.c`, `test_cob.c`): Cobham terms and evaluation, with limits on word length, work and depth (`CT_ELIMIT` when one is exceeded). The tests cover proj, empty, app, smash, a composition, identity by recursion on notation, and concatenation.
- **Part D** (`qbf.h/.c`, `test_qbf.c`): formulas and `ct_qbf_eval`; variables ≥ `n` read as false.

**What `make test` printed:** all five test programs built without warnings (`-Wall -Wextra -Werror -pedantic`).
- `test_base`, `test_cob` and `test_qbf` each reported all checks passed.
- `test_lambda` reported that `PLUS 2 3` normalizes to `church 5` in 6 steps, then all checks passed.
- The existing `test_version` printed nothing.
- The run exited with status 0.

**Status of every property (all proved)**
Each statement covers no undefined behavior plus agreement with `spec/CTSpec.lean` on `CT_OK`. These are partial-correctness results: they say what holds if the function returns, not that it returns.
- **λ-calculus, priorities 1 and 2:**
  - `ct_lambda_lift`, `ct_lambda_subst`, `ct_lambda_size` and `ct_lambda_church` compute exactly `CT.Lambda.lift`, `.subst`, `.size` and `.church`.
  - `ct_lambda_step` contracts the leftmost-outermost redex, and reports "normal" exactly when no `CT.Lambda.step` exists.
  - `ct_lambda_normalize`, on `CT_OK`: `*steps ≤ fuel`, and its result is normal and reached from `t` by exactly `*steps` leftmost-outermost steps.
  - `ct_lambda_normalize` fuel bound: an error other than `CT_ELIMIT` can only come from computing one of the first `fuel` steps. With `fuel == 0` the result is `CT_OK` or `CT_ELIMIT`.
  - The constructors, `ct_lambda_equal` and all static helpers, including `normal_rec`, are also proved.
- **QBF, priority 3:** `ct_qbf_eval` returns `CT.QBF.eval σ p`, where `σ i = assign[i]` for `i < n` and false otherwise. The constructors and helpers are also proved.
- **Cobham terms, priority 4:** `ct_cob_eval` returns `CT.Cob.eval c args`, a word of length at most `lim->max_len`. The helpers, all constructors and `mk_node` are also proved.
- **Base:** the arena functions, checked arithmetic, all word and vector functions and the allocation helpers are proved. `ct_arena_alloc` with size 0, and `ct_arena_alloc_array` with `count == 0` or `elem_size == 0`, return `CT_EINVAL` without touching memory.
- **Not claimed:** freedom from memory leaks. `ct_arena_destroy` is proved free of undefined behavior, but it is not proved to release every block.
- **Error returns:** a public function leaves its result parameters unchanged. The static helpers' `budget`/`work` counters may have been decreased, and `normal_rec`'s flag may have been written before it returns `CT_ELIMIT`.

**Caller obligations** (each entry in `PROOFS.md` and the Properties table states its own):
- Arenas are live (created and not yet destroyed).
- Words, vectors, terms and formulas are valid and not modified during the call.
- Limit structures, the `budget`/`work` counters and the `assign` entries hold initialized values.
- Written objects are distinct from one another. They do not overlap the inputs, memory reachable from the inputs (word bytes, item arrays, term nodes, `assign`, `gs`), or the arena's internal records. For example, the buffer passed to `ct_word_to_string` must not overlap the word or its bytes.

**Assumptions**
- **C library:** the standard behavior of `malloc`, `free`, `memcpy`, `memset` and `strlen` is assumed, not verified.
- **Calls into `base.c`:** where `lambda.c`, `qbf.c` and `cob.c` call `base.c` functions, those functions are verified from their own code, not assumed.
- **Platform:** behavior the C standard leaves to the implementation follows GCC/Clang on x86-64 Linux.

`spec/CTSpec.lean`, `Makefile` and `README.md` are unchanged.

Files are in the project directory:
- `PROOFS.md`
- `proofs/README.md`
- `include/ct/base.h`, `include/ct/lambda.h`, `include/ct/cob.h`, `include/ct/qbf.h`
- `src/base.c`, `src/lambda.c`, `src/cob.c`, `src/qbf.c`
- `tests/test_base.c`, `tests/test_lambda.c`, `tests/test_cob.c`, `tests/test_qbf.c`