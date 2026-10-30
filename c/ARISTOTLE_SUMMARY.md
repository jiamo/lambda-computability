# Summary of changes for run 56a7f0de-bf74-4875-ae1b-d10352dae99a
Part F is partly done: I wrote and tested seven new C modules for it. Parts G–K are not started. In this round only `ct_kclos_mk` and `ct_kenv_cons` are verified; every other new function is written and tested, but its proofs are still open. I stopped here because you said credit was nearly used up, which is the round's stop rule; per your follow-ups, I put C code ahead of proofs. The next round can continue from the status recorded in `PROOFS.md`.

**What was implemented, by part** (each module has a header in `include/ct/`, a source in `src/` and a test in `tests/`)
- **Part F, done (C and tests):**
  - `krivine`: the Krivine machine — code table, heap, one step, and decoding a state back to a λ-term.
  - `cbv`: the call-by-value machine — `stepFn`, `plug`, `State.decode`, `kWeight`, `measure`, `Label.betaCount`.
  - `lazy`: the call-by-need machine — `lstepFn`, `Cell.orig`, `LState.init`, label functions.
  - `multitape`: the computable definitions of `DepthThreeModel`, including the multi-tape step, `init` and `runSteps`.
  - `minsky`: counter machines and their compiler to two-counter machines.
  - `spacemachine`: `writeAt`, `moveWork`, `moveIn`, `Config.space`, `stepList`, `init`, `constMachine`.
- **Part F, partly done:** `leftmost` has `step_normal`, `nstep` and `closure`. Still to write: `nstep_code`, `isNormal_code`, `haltsBy_code`, which work on number codes of terms.
- **Part F, not started:** `MinskyCompile`, `KCMachine`, `WLModel`, `WLRAMInstruction`, `WLInterpreter`, `BLC`, `Combinators`, `PCA`.
- **Spec:** I restated every implemented definition word for word, with its source module, and checked that it type-checks on its own. That restatement is kept internal: `spec/Machines.lean` is delivered empty, and each entry in `PROOFS.md` names its Lean definition and source module instead.
- **Round-1 code:** unchanged, since no bug was found. `tests/test_base.c` is now your uploaded version.

**What `make test` printed:** "all checks passed" for `test_base`, `test_cbv`, `test_cob`, `test_krivine`, `test_lambda` (which also prints "PLUS 2 3 normalizes to church 5 in 6 steps"), `test_lazy`, `test_leftmost`, `test_minsky`, `test_multitape`, `test_qbf` and `test_spacemachine`. `test_version` prints nothing when it passes. The run passes with gcc and with clang, and every test also runs clean under AddressSanitizer and UndefinedBehaviorSanitizer. I could not run it on arm64 macOS. The tests compare against hand-computed values and lemmas stated in the Lean sources. The `minsky` test also runs a compiled two-counter program and checks the encoded registers it ends with.

**Status of every property**
- **Round 1:** all 64 entries are still proved, unchanged.
- **Round 2, proved (F1, F2):**
  - `ct_kclos_mk`: no undefined behavior; on `CT_OK`, `*out` represents `Clos.mk t e`; otherwise `*out` is unchanged.
  - `ct_kenv_cons`: no undefined behavior; on `CT_OK`, `*out` represents `c :: e`; otherwise `*out` is unchanged.
  - Both assume standard `malloc`/`free` behavior and say what holds if the function returns. They do not prove termination or absence of memory leaks.
- **Round 2, open (F3–F32):** every other public function of the seven new modules. None is refuted.

**Skipped definitions ("Not implemented" in `PROOFS.md`)**
- `haltTime` and `nf`: they search all natural numbers for a normal form, which cannot be implemented faithfully.
- `RawClause.eval`, `Circuit3.middleEval`, `Circuit3.eval`: declared `noncomputable`.
- Predicates and relations, which are not programs: `cbvstep`, `Trans`, `LTrans`, `KM.Step`, the space-complexity classes, and so on.

**Proof artifacts:** the proofs and the exact Lean statements can't be exported, so `proofs/<module>/` and Lean files under `proofs/statements/` are not provided. `proofs/README.md` and `proofs/statements/README.md` explain this; `PROOFS.md` states every property in precise prose. `ref/` and the archive are not in the result.