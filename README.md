This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# start


This is a Lean 4 + mathlib study project focused on formalizing the untyped lambda calculus. The project uses De Bruijn indices to represent terms and includes definitions and proofs for lifting and substitution, beta reduction and parallel reduction, Church numerals, term encoding/decoding, and computability results related to primitive recursive and partial recursive functions.

## What This Project Covers

- The syntax of the untyped lambda calculus as `Lambda`
- Formalization of `lift`, `subst`, and their core lemmas
- Single-step, parallel, and multi-step reduction
- The diamond property of parallel reduction and confluence of the lambda calculus
- Church numerals, combinators, and basic closed terms
- Encoding and decoding lambda terms as natural numbers
- Evaluation and computability constructions based on term encodings

## Requirements

- Lean toolchain: as pinned in `lean-toolchain` (`leanprover/lean4:v4.33.0`)
- Dependency: `mathlib` (`v4.33.0`, see `lakefile.toml` / `lake-manifest.json`)
- Build tool: `lake`

It is recommended to install `elan` so the toolchain in `lean-toolchain` is selected automatically.

## Quick Start

Build the default target from the repository root:

```bash
lake build
```

This command has been verified against the current repository state. On the first build, Lean will fetch the toolchain and dependencies based on `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

If you only want to check the library entry file, run:

```bash
lake env lean Start.lean
```

## Repository Layout

The development is fully modular; `Start.lean` imports the modules below in dependency order.

### Core layers

- `Start/Tactics.lean`: shared tactic helpers (`bound_nt`)
- `Start/Syntax.lean`: `Lambda` type, `lift`, `subst`, and all lift/subst lemmas
- `Start/Reduction.lean`: `step`, `step_p`, `reduces`, `rho`, diamond property, strip lemma,
  `confluence_theorem`, Church numerals, standard combinators, `LambdaComputable`
- `Start/Church.lean`: `Lambda.iterate`, Church numeral reduction lemmas, `Lambda.succ_correct`
- `Start/Encoding.lean`: `Lambda.encode`, `Lambda.decode`, `Encodable Lambda`

### Arithmetization and computability

- `Start/CodeOps.lean`: code validity, codes for variables/applications/abstractions/Church
  numerals, code-level substitution and beta steps, with their `Primrec` proofs
- `Start/Computability.lean`: `Lambda.eval` (`Partrec`), `Lambda.unchurch_code`,
  `Lambda.compute_fun` and `Lambda.compute_fun_partrec`
- `Start/CodePrimrec.lean`: arithmetized decoder, the `ECF` closure format, `lift_code`,
  `subst_code'`, `step_code'`, `code_step'` and their primitive recursiveness
- `Start/EvalSound.lean`: soundness of the code-level evaluator, normal forms, `Lambda.eval'`
- `Start/Arithmetic.lean`: Church arithmetic (`add`, `mult`), injectivity/normality of Church
  numerals, and the bridge `LambdaComputable_imp_Partrec`
- `Start/GrossKnuth.lean`: normalization of the Gross–Knuth strategy — iterating the complete
  development `Lambda.rho` reaches any normal form of a term
- `Start/EvalGK.lean`: the arithmetized complete development `Lambda.rho_code`, the evaluator
  `Lambda.eval_gk` with its correctness theorem `Lambda.evalCorrectnessGK`, and the unconditional
  bridge `LambdaComputable_imp_Partrec_unconditional`

### Lambda-definable functions

- `Start/Combinators.lean`: booleans, conditionals, pairs, predecessor, subtraction, comparisons,
  and the closed-term API (`Lambda.IsClosed`)
- `Start/Sqrt.lean`: fixed-point recursion (`Lambda.W`, `Lambda.REC_v2`) and integer square root
- `Start/Pairing.lean`: pairing/unpairing terms, `LambdaComputable2`, composition combinators
- `Start/Recursion.lean`: closing terms, primitive recursion (`Lambda.prec`), minimisation
  (`Lambda.mu`)
- `Start/Realizer.lean`: `Lambda.Realizes`, realizer combinators, and the compiler
  `Lambda.exists_realizer_of_primrec` turning every `Nat.Primrec` construction into a closed
  lambda term
- `Start/Minimization.lean`: correctness of the minimisation combinator
  (`Lambda.muCorrectness`) and the analysis of a witnessless search
- `Start/PartrecLambda.lean`: parameterised minimisation, Kleene normal form, the reverse
  direction `lambdaComputable_of_computable` and the capstone equivalence for total functions
  `lambdaComputable_iff_computable`

### Weak head reduction, standardization and the partial capstone

- `Start/WeakHead.lean`: weak head normal forms, the weak head strategy and its optimality
  (`Lambda.whnIn_of_step`)
- `Start/Standardization.lean`: standard reductions, the standardization theorem
  (`Lambda.sred_of_reduces`) and normalization of the weak head strategy
  (`Lambda.hasWhnfEval_of_reduces_whnf`)
- `Start/Divergence.lean`: the divergence half of minimisation (`Lambda.muDivergence`)
- `Start/Leftmost.lean`: the normal order strategy, its normalization, and
  `Lambda.evalNormalization`
- `Start/PartialCapstone.lean`: the strict realizer of a partial function and the capstone
  `lambdaComputable_iff_partrec`

### Machine side

- `Start/TM2Partrec.lean`: arithmetization of a bundled machine `Turing.FinTM2` with finite
  stack alphabets — the one-step transition is primitive recursive, the run is obtained by
  minimisation, and `TM2Partrec.partrec_evalCode` shows the machine computes a partial
  recursive function
- `Start/TM2Restrict.lean`: restriction of a TM2 machine to a finite set of labels it never
  leaves, with a step-by-step simulation
- `Start/TM2Forward.lean`: Mathlib's compiler from partial recursive functions into machines,
  bundled as a `Turing.FinTM2` (`TM2Partrec.trFinTM2_outputs`)
- `Start/TM2Capstone.lean`: the binary encoding on symbol codes and the machine equivalence
  `TM2Partrec.tm2Computable_iff_partrec`

### Further recursion theory, complexity and algorithms (milestone M5)

- `Start/RecursionParams.lean`: Kleene's recursion theorem **with parameters**
  (`Lambda.exists_recursion_with_parameters`) — a primitive recursive `s` with `decode (s y)
  = some X` and `X ↠ F ⌜s y⌝ ⌜y⌝`
- `Start/Encodings.lean`: model equivalences beyond unary functions — the curried binary form
  (`lambdaComputable2_iff_partrec₂`, `lambdaComputable2_iff_tm2Computable`) and computability
  over arbitrary `Primcodable` input types (`LambdaComputableEnc`, `TM2ComputableEnc` and the
  bridges between them)
- `Start/TM2PolyTime.lean`: time-bounded machine runs (`TM2Partrec.HaltsWithin`,
  `TM2ComputableNatInTime`, `TM2ComputableNatInPolyTime`), the resulting partial recursiveness,
  and bridges to Mathlib's `Turing.TM2ComputableInPolyTime`
- `Start/Solvability.lean`: head-solvability (`Lambda.Solvable`), unsolvability of `Ω`
  (`Lambda.not_solvable_omega`), generic reachability of solvable terms
  (`Lambda.exists_args_conv_of_solvable`) and undecidability of solvability
- `Start/AlgorithmRepresentation.lean`: a Dershowitz–Gurevich style *representation* theorem —
  sequential algorithms in bounded-exploration form (`SeqAlgorithm.Algorithm`) have partial
  recursive input-output functions (`SeqAlgorithm.Algorithm.partrec_run`), hence are
  lambda-definable and Turing computable

### Interfaces and compatibility

- `Start/Boundary.lean`: LACI-inspired interface records (`ReductionBoundary`, `EncodingBoundary`,
  `ComputabilityInternalizer`) with concrete adapters — no `sorry`
- `Start/Basic.lean`: compatibility shim that re-exports every module, so `import Start.Basic`
  keeps working
- `Start/Demo.lean`: guided tour of the main results
- `Start.lean`: library entry point

### Other

- `lakefile.toml`: Lake project configuration
- `docs/goal/task-board.yaml`: structured task board (every task is complete)
- `docs/goal/evidence/`: evidence notes backing each completed task
- `scripts/goal_state.py`: lightweight task-board validator / selector
- `scripts/lint_report.py`, `scripts/check_file.sh`: helpers that summarise the linter warnings of
  a build log, or of a single module
- `scratch/`: experimental files kept from earlier exploration (`Check.lean`, `temp.lean`,
  `temp2.lean`, `check_subst.lean`).  They are not part of the library target, are not built by
  `lake build`, and still contain `sorry`s; see `scratch/README.md`

## Current Status

- The default library target `Start` builds successfully with `lake build`, and it now compiles
  every module, including `Start.Boundary`
- The whole development is `sorry`-free
- Every module also builds independently via `lake build Start.Syntax` etc.
- `lake build` emits no `linter.*` warning at all: the surface went from 1072 warnings down to 0
  (see `docs/goal/evidence/M1-LINTER-HARDENING.md` and
  `docs/goal/evidence/M2-STYLE-RESIDUE.md`); no linter is disabled anywhere
- `LambdaComputable f → Partrec f` is proved unconditionally in `Start/EvalGK.lean`
- Both halves of minimisation are proved (`Lambda.muCorrectness`, `Lambda.muDivergence`), so the
  lambda capstone holds for arbitrary partial functions:
  `lambdaComputable_iff_partrec : LambdaComputable f ↔ Partrec f` (`Start/PartialCapstone.lean`);
  the total-function form `lambdaComputable_iff_computable` remains available
- The machine side is closed as well:
  `TM2Partrec.tm2Computable_iff_partrec : TM2ComputableNat f ↔ Partrec f`
  (`Start/TM2Capstone.lean`), and the two models are compared directly in
  `lambdaComputable_iff_tm2Computable`
- Every task on the board is `DONE_STRONG`
- Consequences of the capstone, added on top of the board:
  - `Lambda.Theta_reduces` (`Start/FixedPoint.lean`) — Turing's fixed-point combinator, with the
    fixed-point equation as a reduction;
  - `Lambda.exists_code_fixed_point` (`Start/SecondRecursion.lean`) — Kleene's second recursion
    theorem for the lambda calculus: every closed `F` has an `X` with `X ↠ F ⌜X⌝`;
  - `Lambda.not_computablePred_codeConverges` (`Start/Undecidable.lean`) — no computable predicate
    decides whether a coded term reduces to a Church numeral;
  - `Lambda.not_computablePred_codeHasNormalForm` (`Start/NormalizationUndecidable.lean`) — the
    stronger statement that normalizability is undecidable;
  - `Lambda.scott_theorem` (`Start/Scott.lean`) — Scott's theorem: no closed lambda term decides a
    convertibility-invariant set of terms that has a closed member and a closed non-member;
  - `Lambda.not_computablePred_codeSet` (`Start/Scott.lean`) — Rice's theorem for the lambda
    calculus: the code set of such a set of terms is not computable; the concrete instance
    "convertible with `church 0`" is `Lambda.not_computablePred_codeSet_conv_church_zero`;
  - `Lambda.exists_smn` (`Start/SMN.lean`) — the uniform s-m-n theorem for this coding: fixing a
    parameter of a coded term is primitive recursive;
  - `Lambda.exists_self_interpreter` (`Start/SelfInterpreter.lean`) — a **self-interpreter**
    (Barendregt's enumerator): a single closed term `E` with `E ⌜M⌝ ↠ M` for every closed `M`,
    where `⌜M⌝ = church (encode M)`; the general statement about open terms and environments is
    `Lambda.selfEval_correct`;
  - `Lambda.not_exists_quote` (`Start/SelfInterpreter.lean`) — the converse fails: no term `Q`
    satisfies `Q M ↠ ⌜M⌝` for all closed `M`, so quoting is not lambda-definable.
- `docs/church-turing-discussion.md` records what these results do and do not say about the
  Church–Turing thesis itself.
- Milestone `M5` turned the former "suggested next steps" into five completed board tasks:
  - `M5-RECURSION-PARAMS` — `Lambda.exists_recursion_with_parameters`;
  - `M5-ENCODINGS-MULTIARG` — `lambdaComputable2_iff_partrec₂`,
    `lambdaComputable2_iff_tm2Computable`, `lambdaComputableEnc_iff_tm2ComputableEnc`;
  - `M5-POLYTIME` — `TM2Partrec.lambdaComputable_of_tm2ComputableNatInPolyTime` plus the
    Mathlib bridge `TM2Partrec.partrec_of_tm2ComputableInPolyTime`;
  - `M5-SOLVABILITY` — `Lambda.not_solvable_omega`,
    `Lambda.exists_args_conv_of_solvable`, `Lambda.not_computablePred_codeSet_solvable`;
  - `M5-ALGORITHM-REPRESENTATION` — `SeqAlgorithm.Algorithm.partrec_run` and
    `SeqAlgorithm.Algorithm.lambdaComputable_run`.

- Milestone `M6` adds **Kolmogorov complexity for the lambda calculus**
  (`Start/Kolmogorov.lean`, `Start/KolmogorovBinary.lean`).  Program length is the syntactic size
  `Lambda.size` of a closed term reducing to a Church numeral, and
  `Lambda.kolm s = sInf {size t | t closed, t ↠ church s}`:
  - `Lambda.exists_incompressible` — for every `n` some number has complexity at least `n`
    (counting: `Lambda.finite_setOf_size_le` and `Lambda.finite_setOf_kolm_le`);
  - `Lambda.not_computablePred_kolm_le` — the relation `kolm s ≤ n` is undecidable (Berry's
    paradox, run through the closed form `Lambda.exists_code_fixed_point_closed` of Kleene's
    second recursion theorem), and `Lambda.not_computable_kolm` — `kolm` is not computable;
  - `Lambda.kolm_le_kolmWith` — the invariance theorem: measuring complexity through any fixed
    closed interpreter term changes it by at most an additive constant, and the identity
    interpreter returns `kolm` itself up to `3`;
  - `Lambda.exists_const_kolm_le_of_partrec` / `Lambda.exists_const_kolm_le_of_tm2` — for any
    partial recursive, equivalently Turing machine computable, description system `V` there is a
    constant `c` with `kolm s ≤ 3 * p + c` whenever `V p = s`;
  - `Lambda.binNum` — compact numerals of size `O(log n)` reducing to `church n`, giving the
    logarithmic form `Lambda.exists_const_kolm_le_size`,
    `Lambda.exists_const_kolm_le_size_of_partrec` and `Lambda.exists_const_kolm_le_size_of_tm2`:
    complexity is bounded by a constant multiple of the *bit length* of the description.

- Milestone `M6` is completed by **Kraft's inequality and Chaitin's `Ω`**
  (`Start/Kraft.lean`, `Start/ChaitinOmega.lean`):
  - `Lambda.bits` — the binary lambda calculus coding of a term as a bit string
    (`var i ↦ 1^(i+1) 0`, `lam t ↦ 00 t`, `app a b ↦ 01 a b`), proved self-delimiting
    (`Lambda.bits_append_inj`) and hence prefix free (`Lambda.bits_prefixFree`);
  - `Kraft.tsum_wt_le_one` — Kraft's inequality `∑ 2 ^ (-|c i|) ≤ 1` for an arbitrary prefix free
    coding `c`, by the counting argument on extensions to a common length;
  - `Lambda.kolmP` — prefix complexity, the least *bit* length of a closed program, with
    `Lambda.kraft_kolmP : ∑' s, 2 ^ (-kolmP s) ≤ 1` and `Lambda.kolmP_le_two_mul_kolm`;
  - `Lambda.chaitinOmega` — the halting probability `∑ 2 ^ (-|bits t|)` over the closed terms with
    a normal form: a convergent sum (`Lambda.summable_haltingWeight`) with
    `Lambda.chaitinOmega_mem_Ioo : 0 < Ω < 1`.

## Suggested Next Steps

All board items are now `DONE_STRONG`.  The natural continuation on the complexity side is the
algorithmic randomness of `Ω` — its incompressibility, and the fact that its first `n` bits decide
the halting problem for programs of length at most `n` — which is not proved here.  Other honest
scope limits of milestone `M5`, and the natural continuations from there, are:

- Böhm's separation theorem itself is **not** proved: `Start/Solvability.lean` gives solvability,
  its undecidability and a generic reachability statement, but not the separation of two distinct
  βη-normal forms by a common context;
- the algorithm representation theorem is a theorem about the stated bounded-exploration axioms,
  not a proof of the Church–Turing thesis; widening the axioms (arbitrary finite structures
  instead of naturals in finitely many locations) is a natural next step;
- on the complexity side, only the transfer *out of* polynomial-time machines is formalized; a
  resource-preserving compilation *into* machines, or a cost model for the lambda side, is not.

## Task Workflow

This repository includes a small structured task-board workflow.

```bash
python3 scripts/goal_state.py validate
python3 scripts/goal_state.py next
python3 scripts/goal_state.py render --write docs/current-goal-state.md
```

The tasks live in `docs/goal/task-board.yaml`.
