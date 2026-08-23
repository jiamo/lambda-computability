This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# lambda-computability

A `sorry`-free Lean 4 formalization of **computability theory and algorithmic information
theory, done inside the untyped lambda calculus**: from de Bruijn syntax and confluence, through
the Church–Turing equivalence with partial recursive functions and Turing machines, up to
Kolmogorov complexity, Chaitin's `Ω`, Martin-Löf randomness and Böhm's separation theorem.

[![CI](../../actions/workflows/lean_action_ci.yml/badge.svg)](../../actions/workflows/lean_action_ci.yml)
![Lean](https://img.shields.io/badge/Lean-v4.33.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.33.0-blue)
![sorry-free](https://img.shields.io/badge/sorry--free-yes-brightgreen)
![tasks](https://img.shields.io/badge/task%20board-51%2F51%20DONE__STRONG-brightgreen)

Everything below is proved in `Start/`; the whole library compiles with `lake build`, contains no
`sorry` and no `axiom`, and the headline results depend only on `propext`, `Classical.choice` and
`Quot.sound`.

## Headline theorems

Signatures below are the actual statements in the library (printed with `#check`; the guided tour
in `Start/Demo.lean` checks them all).

### Church–Turing equivalence

```lean
-- The lambda calculus computes exactly the partial recursive functions.
lambdaComputable_iff_partrec :
    ∀ {f : ℕ →. ℕ}, LambdaComputable f ↔ Partrec f

-- … which are exactly the functions computed by (bundled, finite) TM2 machines.
TM2Partrec.tm2Computable_iff_partrec :
    ∀ {f : ℕ →. ℕ}, TM2Partrec.TM2ComputableNat f ↔ Partrec f

lambdaComputable_iff_tm2Computable :
    ∀ {f : ℕ →. ℕ}, LambdaComputable f ↔ TM2Partrec.TM2ComputableNat f
```

### Recursion theory

```lean
-- Rice/Scott: no closed term decides a nontrivial conversion-invariant set.
Lambda.scott_theorem :
    ∀ {A : Lambda → Prop}, Lambda.ConvInvariant A →
      ∀ {M N : Lambda}, M.IsClosed → N.IsClosed → A M → ¬ A N →
        ∀ {F : Lambda}, F.IsClosed → ¬ F.Decides A

-- s-m-n: fixing a parameter is primitive recursive on codes.
Lambda.exists_smn :
    ∃ s, Primrec₂ s ∧ ∀ (F : Lambda) (n : ℕ),
      Lambda.decode (s F.encode n) = some (F.app (Lambda.church n))

-- A self-interpreter: E ⌜M⌝ ↠ M for every closed M.
Lambda.exists_self_interpreter :
    ∃ E, E.IsClosed ∧ ∀ M : Lambda, M.IsClosed →
      (E.app (Lambda.church M.encode)).reduces M

-- Kleene's second recursion theorem with parameters.
Lambda.exists_recursion_with_parameters :
    ∀ {F : Lambda}, F.IsClosed →
      ∃ s, Primrec s ∧ ∀ y : ℕ, ∃ X, Lambda.decode (s y) = some X ∧
        X.reduces ((F.app (Lambda.church (s y))).app (Lambda.church y))

-- The lambda halting set is one-one complete among r.e. predicates.
Lambda.codeHasNormalForm_one_complete :
    REPred Lambda.CodeHasNormalForm ∧
      ∀ p : ℕ → Prop, REPred p → p ≤₁ Lambda.CodeHasNormalForm
```

### Algorithmic information theory

```lean
-- Berry's paradox: Kolmogorov complexity is not computable, and is unbounded.
Lambda.not_computable_kolm  : ¬ Computable Lambda.kolm
Lambda.exists_incompressible : ∀ n : ℕ, ∃ s, n ≤ Lambda.kolm s

-- Kraft's inequality for a prefix-free code.
Kraft.tsum_wt_le_one :
    ∀ {ι : Type u} {c : ι → List Bool}, Kraft.PrefixFreeCoding c → ∑' i, Kraft.wt (c i) ≤ 1

-- Chaitin's Ω is a genuine probability, uncomputable and irrational.
Lambda.chaitinOmega_mem_Ioo    : Lambda.chaitinOmega ∈ Set.Ioo 0 1
Lambda.irrational_chaitinOmega : Irrational Lambda.chaitinOmega

-- Every Martin-Löf random sequence has incompressible prefixes
-- (the easy half of Levin–Schnorr for the lambda-calculus prefix complexity).
Lambda.exists_const_le_kolmP_prefix_of_mlRandom :
    ∀ {X : ℕ → Bool}, Lambda.MLRandom X →
      ∃ c, ∀ n : ℕ, n ≤ Lambda.kolmP (Encodable.encode (Lambda.prefixList X n)) + c

-- The Levin–Schnorr theorem for the universal prefix machine `KC.KU`:
-- Martin-Löf randomness is exactly incompressibility of every prefix.
KC.mlRandom_iff_exists_const_le_KU :
    ∀ {X : ℕ → Bool},
      Lambda.MLRandom X ↔ ∃ c, ∀ n : ℕ, n ≤ KC.KU (Encodable.encode (Lambda.prefixList X n)) + c

-- The bits of Ω are Martin-Löf random -- now a corollary of the converse half
-- applied to Chaitin's incompressibility theorem for Ω.
KC.mlRandom_omegaSeq : Lambda.MLRandom KC.omegaSeq

-- The Kraft-Chaitin machine is optimal for the lambda prefix machine.
KC.exists_const_KU_le_kolmP : ∃ c, ∀ s, KC.KU s ≤ Lambda.kolmP s + c
```

### Lambda calculus theory

```lean
-- Confluence (Church–Rosser) via parallel reduction.
Lambda.confluence_theorem : Lambda.Confluence

-- Böhm's separation theorem: two closed normal forms whose Böhm trees are not
-- η-equal are separable by one list of closed arguments.
Lambda.separable_toTerm_of_not_tagEq :
    ∀ {x y : Lambda.BohmNF},
      Lambda.BohmNF.FreeVarsBelow 0 x → Lambda.BohmNF.FreeVarsBelow 0 y →
      ¬ Lambda.TagEq 0 (fun _ => 0) x (fun _ => 0) y → x.toTerm.Separable y.toTerm

-- Binary lambda calculus: terms are in bijection with the valid BLC bit strings.
Lambda.bitsEquiv : Lambda ≃ { bs // Lambda.isBLC bs = true }

-- The de Bruijn terms of this library and the locally nameless terms of `cslib`
-- are the same calculus: the closed terms correspond, and beta-reduction is
-- carried across in both directions, so each library's confluence theorem
-- implies the other's.
Lambda.closedEquiv : { t : Lambda // Lambda.freeMax t = 0 } ≃ { M : Lambda.LNTerm // M.LC ∧ M.fv = ∅ }
Lambda.confluence_of_cslib : Lambda.Confluence
Lambda.cslib_confluence_of_lambda :
    ∀ (D : ℕ) (M M₁ M₂ : Lambda.LNTerm), Term.LcAt 0 M = true → (∀ a ∈ M.fv, a < D) →
      (M ↠βᶠ M₁) → (M ↠βᶠ M₂) → ∃ M₃, (M₁ ↠βᶠ M₃) ∧ (M₂ ↠βᶠ M₃)
```

### Types, proof theory and complexity

```lean
-- Tait strong normalization for the simply typed lambda calculus.
Lambda.sn_of_typing :
    ∀ {Γ : List Lambda.Ty} {t : Lambda} {A : Lambda.Ty}, Lambda.Typing Γ t A → t.SN

-- Canonicity for Gödel's System T: every closed term of type nat reduces to a numeral.
GodelT.exists_reduces_num :
    ∀ {t : GodelT.Tm}, GodelT.Typing [] t GodelT.Ty.nat → ∃ n, GodelT.reduces t (GodelT.num n)

-- Blum-style complexity: no computable time bound captures every computable function.
Complexity.exists_computable_steps_gt :
    ∀ {t : ℕ → ℕ}, Computable t →
      ∃ f, Computable f ∧ ∀ c : Nat.Partrec.Code,
        (∀ x : ℕ, c.eval x = Part.some (f x)) → ∃ x, ¬ Complexity.StepsLe c x (t x)

-- P, NP, polynomial-time many-one reductions and NP-completeness over binary
-- words, with polynomial time for functions defined by Cobham's axioms.
Complexity.inNP_of_inP : ∀ {L : Complexity.Language}, Complexity.InP L → Complexity.InNP L
Complexity.InNP.of_reduction :
    ∀ {L₁ L₂ : Complexity.Language},
      Complexity.PolyManyOne L₁ L₂ → Complexity.InNP L₂ → Complexity.InNP L₁
Complexity.peqNP_of_npComplete_of_inP :
    ∀ {L : Complexity.Language}, Complexity.NPComplete L → Complexity.InP L → Complexity.PeqNP
```

## Related work, and what is specific to this project

Public Lean 4 developments in this area, and how they relate (repository file listings checked
2026-08; none of the statements below is a claim about unpublished or private work):

| Project | What it covers | Relation to this library |
| --- | --- | --- |
| [`leanprover/cslib`](https://github.com/leanprover/cslib) | Lambda calculus in **locally nameless** style (β/η confluence, standardization, strong normalization), STLC, Fsub, automata, CCS, linear logic | Same metatheory, different representation: here everything is **de Bruijn**, and the development continues into computability and AIT, which `Cslib/Languages/LambdaCalculus/` does not cover (no Böhm trees, no Kolmogorov complexity, no `Ω`). `cslib` is a dependency of this repo, and `Start/Representation.lean` proves the two representations equivalent, transporting confluence in both directions (see [`docs/representations.md`](docs/representations.md)) |
| [`cameronfreer/algorithmic-randomness`](https://github.com/cameronfreer/algorithmic-randomness) | Algorithmic randomness over **program codes**: prefix machines, Kraft–Chaitin, Levin–Schnorr, Schnorr/Kurtz randomness, martingales | Complementary: the AIT here is defined through **lambda terms** (`Lambda.kolm`, `Lambda.kolmP`, `Lambda.chaitinOmega`), so the two developments meet at the level of statements rather than definitions; here the lambda complexity is compared with a machine-based one only in this repo's own terms (`KC.exists_const_KU_le_kolmP`), and no bridge to that repo's definitions is formalized on either side |
| [`a9lim/blam`](https://github.com/a9lim/blam) | Computational experiments in binary lambda calculus (censuses, BBλ, Ω/K measurements) | Numerical/experimental rather than a formalization; `Start/BLC.lean` proves the BLC decoder correct and gives the bijection `Lambda ≃ {bs // isBLC bs}` |
| `Mathlib.Computability` | Partial recursive functions, `Nat.Partrec.Code`, TM0/TM1/TM2, `Turing.PartrecToTM2` | Used as the base: the equivalences above are stated against mathlib's `Partrec`, `Computable`, `REPred` and `Turing.FinTM2`, not against a private notion of computability |

## Map of the library

`Start/` is self-contained; `Start.lean` imports everything.

- **Syntax, reduction, confluence, standardization** — `Start/Syntax.lean`,
  `Start/Reduction.lean`, `Start/GrossKnuth.lean`, `Start/Standardization.lean`,
  `Start/WeakHead.lean`, `Start/Leftmost.lean`.
- **Church–Turing equivalence** — the lambda calculus computes exactly the partial
  recursive functions (`Start/PartialCapstone.lean`, `Start/PartrecLambda.lean`), which are
  exactly the Turing machine computable ones (`Start/TM2Forward.lean`, `Start/TM2Partrec.lean`,
  `Start/TM2Capstone.lean`), with multi-argument and arbitrary-`Primcodable` versions in
  `Start/Encodings.lean`.
- **Recursion theory** — fixed points (`Start/FixedPoint.lean`), the s-m-n theorem
  (`Start/SMN.lean`), Kleene's second recursion theorem with parameters
  (`Start/SecondRecursion.lean`, `Start/RecursionParams.lean`), a self-interpreter
  (`Start/SelfInterpreter.lean`), Rice's theorem (`Start/Scott.lean`), undecidability of
  convergence, of normalization and of solvability (`Start/Undecidable.lean`,
  `Start/NormalizationUndecidable.lean`, `Start/Solvability.lean`).
- **Algorithmic information theory** — Kolmogorov complexity and Berry's paradox
  (`Start/Kolmogorov.lean`, `Start/KolmogorovBinary.lean`), Kraft's inequality
  (`Start/Kraft.lean`) together with its converse for non-decreasing lengths
  (`Start/KraftConverse.lean`), prefix complexity and Chaitin's `Ω` (`Start/ChaitinOmega.lean`,
  `Start/PlainVsPrefix.lean`), the busy beaver (`Start/BusyBeaver.lean`), the halting/`K`
  bridge (`Start/KolmogorovHalting.lean`), `Ω` as an uncomputable, irrational halting
  oracle (`Start/OmegaUncomputable.lean`, `Start/OmegaOracle.lean`), Chaitin's
  incompressibility theorem `n ≤ kolmP (omegaPrefix n) + c` (`Start/OmegaIncompressible.lean`),
  and the randomness of `Ω` itself (`Start/OmegaURandom.lean`, `Start/KCComputable.lean`).
- **Algorithmic randomness** — the uniform measure on Cantor space, Martin-Löf tests and
  Martin-Löf randomness (`Start/MartinLof.lean`): no computable sequence is random, and every
  random sequence has incompressible prefixes (the easy half of the Levin–Schnorr theorem).
  For the universal prefix machine `KC.KU` both halves are proved, giving the Levin–Schnorr
  theorem `KC.mlRandom_iff_exists_const_le_KU` (`Start/LevinSchnorr.lean`), of which the
  randomness of `Ω` is a corollary.  `Start/KUOptimal.lean` compares the two complexities:
  `KU s ≤ Lambda.kolmP s + c`, by running the lambda programs as a Kraft–Chaitin request stream.
- **Degrees of unsolvability** — the lambda halting set is Σ₁-complete, indeed one-one complete
  (`Start/HaltingComplete.lean`, on top of mathlib's `REPred`); Kleene's diagonal halting set is
  one-one complete as well, so the two halting problems are one-one equivalent
  (`Start/KleeneK.lean`).
- **Binary lambda calculus** — a decoder for the BLC bit-string code and the resulting
  bijection between terms and valid bit strings (`Start/BLC.lean`).
- **Representation bridges** — de Bruijn ⟺ locally nameless (`cslib`) ⟺ BLC: mutually inverse
  translations, substitution/reduction preservation in both directions, and confluence
  transported each way (`Start/Representation.lean`, note in
  [`docs/representations.md`](docs/representations.md)).
- **Complexity** — a Blum complexity measure (fuel counting) on the partial recursive codes,
  with both Blum axioms, and the diagonal result that no computable bound captures every
  computable function (`Start/StepComplexity.lean`); polynomial-time bounded machines in
  `Start/TM2PolyTime.lean`; and the classes `P` and `NP` over binary words with polynomial-time
  many-one reductions and NP-completeness (`Start/ComplexityClasses.lean`) — Cook–Levin is *not*
  formalized, so no language is proved NP-complete there.
- **Typed calculi and proof theory** — the simply typed lambda calculus over the same de Bruijn
  syntax, with Tait strong normalization and the untypability of `omega`
  (`Start/SimpleTypes.lean`); and Gödel's System T with strong normalization, subject reduction
  and canonicity (`Start/SystemTSyntax.lean`, `Start/SystemT.lean`, `Start/SystemTCanon.lean`).
- **Böhm's separation theorem** — finite Böhm trees of normal forms (`Start/Bohm.lean`), the
  Böhm-out transformation (`Start/BohmOut.lean`), and the separation theorem for trees that are
  not η-equal (`Start/BohmEta.lean`).
- **Denotational semantics** — two models of the untyped calculus.  Scott's *graph model*
  `D = Set Tok` is a reflexive object (the Scott-continuous function space is a retract of `D`,
  `Start/GraphModel.lean`); interpreting terms in it validates β and gives a semantic proof that
  `Ω` is not convertible to `I`, hence that the β-calculus is consistent, without using
  confluence (`Start/GraphModelSemantics.lean`).  Scott's **`D∞`** is built as the inverse limit
  of the tower `D₀ = Bool`, `Dₙ₊₁ = [Dₙ →𝒄 Dₙ]` with its embedding-projection pairs
  (`Start/ScottTower.lean`, `Start/ScottDinf.lean`, `Start/ScottPsi.lean`), and the isomorphism
  `D∞ ≅ [D∞ →𝒄 D∞]` is proved in `Start/ScottDinfIso.lean`; because it is an isomorphism and
  not just a retraction, the induced interpretation is extensional and validates η as well as β
  (`Start/ScottDinfModel.lean`).  In `D∞` the diverging term `Ω` denotes the least element, so
  `Ω` and `I` are not βη-convertible: the **λη calculus is consistent**, again by a purely
  semantic argument (`Start/ScottDinfOmega.lean`).

`Start/Demo.lean` is a guided tour with `#check`s of the headline statements.

## Building

The project pins Lean `v4.33.0` (`lean-toolchain`) and Mathlib `v4.33.0` (`lakefile.toml` and
`lake-manifest.json`).  These three must agree: if they do not, `lake` re-resolves the
dependencies on every invocation and starts compiling all of Mathlib from source, which never
finishes in reasonable time.

From a fresh clone:

```bash
lake exe cache get   # download prebuilt Mathlib artifacts (do this first!)
lake build           # builds the `Start` library
```

`lake exe cache get` is what keeps `lake build` from recompiling Mathlib itself.

The Lake package is called `lambda_computability` (matching the repository name; Lake package
names must be Lean identifiers, hence the underscore).  The Lean library target is `Start`, so
`import Start.…` is unaffected.

## Releases

Library versions (`version` in `lakefile.toml`, currently `0.1.0`) are independent of the Lean
toolchain version, and releases are cut by hand.  See [`docs/RELEASING.md`](docs/RELEASING.md)
for the policy and [`docs/release-notes/`](docs/release-notes) for the notes of each release.

## Task board and evidence

`docs/goal/task-board.yaml` (rendered to `docs/current-goal-state.md`) tracks every result with an
evidence note in `docs/goal/evidence/`, including the honest boundary of each claim.  All 51 tasks
are `DONE_STRONG`.  Validate and re-render with:

```bash
python3 scripts/goal_state.py validate
python3 scripts/goal_state.py render
```

## Roadmap

Directions that are **not** formalized here yet, roughly in order of how close the existing
material gets to them:

| Direction | Why it is interesting | Starting point in this repo |
| --- | --- | --- |
| Levin–Schnorr for the lambda-calculus complexity `Lambda.kolmP` | Both halves are proved for the universal prefix machine `KC.KU` (`Start/LevinSchnorr.lean`), and `KU s ≤ kolmP s + c` is proved (`Start/KUOptimal.lean`); the opposite comparison, which is what would transfer the equivalence to `kolmP`, is not formalized and is not expected in that form | `Start/KUOptimal.lean`, `Start/LevinSchnorr.lean` |
| Schnorr randomness, Solovay tests | Deeper randomness notions, not covered by the Martin-Löf framework here | `Start/MartinLof.lean` |
| Cook–Levin: SAT is NP-complete | The definitions of `P`, `NP`, `≤ₘᵖ` and NP-completeness are in place (`Start/ComplexityClasses.lean`), but no language is proved NP-complete; that needs an encoding of formulas and a tableau construction | `Start/ComplexityClasses.lean`, `Start/TM2PolyTime.lean` |
| Cobham's theorem, and a link to machine-level polynomial time | Would connect `Start/ComplexityClasses.lean` (Cobham axioms) to `Start/TM2PolyTime.lean` (bounded TM2 machines) and to mathlib's `Computable` | `Start/ComplexityClasses.lean`, `Start/TM2PolyTime.lean` |
| Adequacy and full abstraction for the models | The two models are built and proved sound (`Start/GraphModelSemantics.lean`, `Start/ScottDinfModel.lean`), but nothing says that equal denotations imply convertibility, and the local structure of `D∞` is not identified | `Start/ScottDinfModel.lean`, `Start/Bohm.lean` |
| Gentzen consistency, ordinal analysis up to `ε₀` | Proof theory beyond strong normalization | `Start/SystemT.lean`, `Start/SystemTCanon.lean` |
| Reverse mathematics (Big Five calibration) | Would connect this development to the reverse-mathematics libraries | `Start/HaltingComplete.lean`, `Start/MartinLof.lean` |
| Bridge to `algorithmic-randomness`: lambda-term randomness ⟺ program-code randomness | Makes the AIT results above reusable outside this repo (the `cslib` representation bridge is now done — `Start/Representation.lean`) | `Start/Kolmogorov.lean` |

## License

Apache License 2.0 — see [`LICENSE`](LICENSE).

## Scratch files

These files are experiments kept from earlier exploration.  They are **not** part of the `Start`
library target, are not built by `lake build`, and still contain `sorry`s and dead ends.  Nothing
in `Start/` depends on them: `temp.lean`, `temp2.lean` (earlier monolithic drafts), `Check.lean`,
`check_subst.lean` (standalone `Primrec`/substitution checks), `MLTestRequests.lean` (a first
draft superseded by `Start/OmegaURandom.lean`) and `Scratch.lean`.

## Provenance and status

The library compiles with `lake build` on the pinned toolchain, contains no `sorry` and no
`axiom` in `Start/`, and its headline results depend only on `propext`, `Classical.choice` and
`Quot.sound`.

This project was edited by [Aristotle](https://aristotle.harmonic.fun).  To cite Aristotle, tag
`@Aristotle-Harmonic` on GitHub PRs/issues, or add it as a commit co-author:

```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
