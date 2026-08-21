This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Building

The project pins Lean `v4.33.0` (`lean-toolchain`) and Mathlib `v4.33.0`
(`lakefile.toml` and `lake-manifest.json`).  These three must agree: if they do not,
`lake` re-resolves the dependencies on every invocation and starts compiling all of
Mathlib from source, which never finishes in reasonable time.

From a fresh clone:

```bash
lake exe cache get   # download prebuilt Mathlib artifacts (do this first!)
lake build           # builds the `Start` library
```

`lake exe cache get` is what keeps `lake build` from recompiling Mathlib itself.

# Scratch files

These files are experiments kept from earlier exploration.  They are **not** part of the
`Start` library target, are not built by `lake build`, and still contain `sorry`s and dead
ends.  Nothing in `Start/` depends on them.

- `temp.lean`, `temp2.lean`: earlier monolithic drafts of the development
- `Check.lean`, `check_subst.lean`: small standalone checks of `Primrec` and substitution

# What is in here

`Start/` is a self-contained formalization of the untyped lambda calculus and its
metatheory, from syntax and confluence up to algorithmic information theory:

- **Syntax, reduction, confluence, standardization** — `Start/Syntax.lean`,
  `Start/Reduction.lean`, `Start/GrossKnuth.lean`, `Start/Standardization.lean`,
  `Start/WeakHead.lean`, `Start/Leftmost.lean`.
- **Church–Turing equivalence** — the lambda calculus computes exactly the partial
  recursive functions (`Start/PartialCapstone.lean`, `Start/PartrecLambda.lean`), which are
  exactly the Turing machine computable ones (`Start/TM2Capstone.lean`), with multi-argument
  and arbitrary-`Primcodable` versions in `Start/Encodings.lean`.
- **Recursion theory** — fixed points (`Start/FixedPoint.lean`), the s-m-n theorem
  (`Start/SMN.lean`), Kleene's second recursion theorem with parameters
  (`Start/SecondRecursion.lean`, `Start/RecursionParams.lean`), a self-interpreter
  (`Start/SelfInterpreter.lean`), Rice's theorem (`Start/Scott.lean`), undecidability of
  convergence, of normalization and of solvability (`Start/Undecidable.lean`,
  `Start/NormalizationUndecidable.lean`, `Start/Solvability.lean`).
- **Algorithmic information theory** — Kolmogorov complexity and Berry's paradox
  (`Start/Kolmogorov.lean`, `Start/KolmogorovBinary.lean`), Kraft's inequality
  (`Start/Kraft.lean`), prefix complexity and Chaitin's `Ω` (`Start/ChaitinOmega.lean`,
  `Start/PlainVsPrefix.lean`), the busy beaver (`Start/BusyBeaver.lean`), the halting/`K`
  bridge (`Start/KolmogorovHalting.lean`), `Ω` as an uncomputable, irrational halting
  oracle (`Start/OmegaUncomputable.lean`, `Start/OmegaOracle.lean`), and Chaitin's
  incompressibility theorem `n ≤ kolmP (omegaPrefix n) + c`
  (`Start/OmegaIncompressible.lean`).
- **Algorithmic randomness** — the uniform measure on Cantor space, Martin-Löf tests and
  Martin-Löf randomness (`Start/MartinLof.lean`): no computable sequence is random, and every
  random sequence has incompressible prefixes (the easy half of the Levin–Schnorr theorem).

`Start/Demo.lean` is a guided tour with `#check`s of the headline statements. The task board
(`docs/goal/task-board.yaml`, rendered to `docs/current-goal-state.md`) tracks every result
with an evidence note in `docs/goal/evidence/`, including the honest open boundaries —
currently the Martin-Löf randomness of `Ω` itself and Böhm's separation theorem.

# License

Apache License 2.0 — see [`LICENSE`](LICENSE).
