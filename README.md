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
![tasks](https://img.shields.io/badge/task%20board-91%2F92%20DONE__STRONG-brightgreen)

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

-- Post's simple set: r.e., with an infinite complement that meets no infinite r.e. set.
Lambda.Post.rePred_simpleSet        : REPred Lambda.Post.simpleSet
Lambda.Post.simpleSet_compl_infinite : {x : ℕ | ¬ Lambda.Post.simpleSet x}.Infinite
Lambda.Post.simpleSet_meets_rePred :
    ∀ {p : ℕ → Prop}, REPred p → {x : ℕ | p x}.Infinite → ∃ x, p x ∧ Lambda.Post.simpleSet x

-- Post's problem for many-one reducibility: an r.e. set that is neither
-- computable nor many-one complete.
Lambda.Post.exists_rePred_not_computable_not_manyOneComplete :
    ∃ p : ℕ → Prop, REPred p ∧ ¬ ComputablePred p ∧ ¬ ∀ q : ℕ → Prop, REPred q → q ≤₀ p

-- Myhill's theorem, the other extreme: a creative set (r.e. with productive
-- complement) is many-one complete, hence many-one equivalent to the halting
-- set and never simple.
Lambda.Post.manyOneReducible_of_productive_compl :
    ∀ {C A : ℕ → Prop}, Lambda.Post.Productive (fun x => ¬ C x) → REPred A → A ≤₀ C
Lambda.Post.Creative.manyOneEquiv_haltK :
    ∀ {C : ℕ → Prop}, Lambda.Post.Creative C → ManyOneEquiv C Lambda.HaltK
Lambda.Post.creative_iff_manyOneComplete :
    ∀ {C : ℕ → Prop}, Lambda.Post.Creative C ↔ REPred C ∧ ∀ q : ℕ → Prop, REPred q → q ≤₀ C
Lambda.Post.not_creative_simpleSet : ¬ Lambda.Post.Creative Lambda.Post.simpleSet

-- Myhill's isomorphism theorem: one-one equivalence is recursive isomorphism,
-- where `RecIso A B` means `∃ h, Computable h ∧ Function.Bijective h ∧ ∀ x, A x ↔ B (h x)`.
Lambda.Myhill.recIso_iff_oneOneEquiv :
    ∀ {A B : ℕ → Prop}, Lambda.Myhill.RecIso A B ↔ OneOneEquiv A B

-- Hence the classification of the creative sets: a productive set has an
-- injective production function, so a creative set is one-one complete and
-- recursively isomorphic to `K`.
Lambda.Post.exists_injective_productive :
    ∀ {P : ℕ → Prop}, Lambda.Post.Productive P → ∃ q : ℕ → ℕ, Computable q ∧
      Function.Injective q ∧ ∀ e, (∀ x, Lambda.Post.Wset e x → P x) →
        P (q e) ∧ ¬ Lambda.Post.Wset e (q e)
Lambda.Post.Creative.recIso_haltK :
    ∀ {C : ℕ → Prop}, Lambda.Post.Creative C → Lambda.Myhill.RecIso C Lambda.HaltK
Lambda.Post.Creative.recIso :
    ∀ {C D : ℕ → Prop}, Lambda.Post.Creative C → Lambda.Post.Creative D →
      Lambda.Myhill.RecIso C D
Lambda.Post.creative_iff_recIso_haltK :
    ∀ {C : ℕ → Prop}, Lambda.Post.Creative C ↔ Lambda.Myhill.RecIso C Lambda.HaltK

-- Rice–Shapiro: an r.e. extensional class of r.e. sets is generated by its
-- finite members.  Hence the indices of the empty set, and the indices of the
-- total functions, are not r.e.
Lambda.Post.rice_shapiro :
    ∀ {A : ℕ → Prop}, REPred A → Lambda.Post.Extensional A → ∀ e : ℕ,
      (A e ↔ ∃ d : ℕ, {x : ℕ | Lambda.Post.Wset d x}.Finite ∧
        (∀ x, Lambda.Post.Wset d x → Lambda.Post.Wset e x) ∧ A d)
Lambda.Post.not_rePred_emptyIndex : ¬ REPred fun d => ∀ x, ¬ Lambda.Post.Wset d x
Lambda.Post.not_rePred_totalIndex : ¬ REPred fun d => ∀ x, Lambda.Post.Wset d x
```

### Relative computability, the jump, and the arithmetical hierarchy

```lean
-- There are uncountably many Turing degrees (each oracle computes only
-- countably many partial functions).
Lambda.Oracle.not_countable_turingDegree :
    ¬ Countable (Antisymmetrization (ℕ →. ℕ) TuringReducible)

-- The jump is Σ₁-hard, uniformly in the oracle: one computable reduction works
-- for every oracle at once.
Lambda.Oracle.exists_index_repred :
    ∀ {P : ℕ → Prop}, REPred P →
      ∃ k, Computable k ∧ ∀ (A : ℕ → Bool) (x : ℕ), P x ↔ Lambda.Oracle.Jump A (k x)

-- Shoenfield's limit lemma: limit computable = computable from ∅′.
Lambda.Oracle.limitComputable_iff_turingReducible_haltingOracle :
    ∀ A : ℕ → Bool, Lambda.Oracle.LimitComputable A ↔
      TuringReducible (Lambda.Oracle.oracleFun A)
        (Lambda.Oracle.oracleFun Lambda.Oracle.haltingOracle)
Lambda.Oracle.not_limitComputable_jumpChar_haltingOracle :
    ¬ Lambda.Oracle.LimitComputable (Lambda.Oracle.jumpChar Lambda.Oracle.haltingOracle)

-- The arithmetical hierarchy: Σ⁰ₙ, Π⁰ₙ, Δ⁰ₙ as alternating quantifier prefixes
-- over a computable matrix.  Its bottom levels are the familiar classes.
Lambda.Arith.deltaAt_one_iff : ∀ {P : ℕ → Prop}, Lambda.Arith.DeltaAt 1 P ↔ ComputablePred P
Lambda.Arith.sigmaAt_one_iff : ∀ {P : ℕ → Prop}, Lambda.Arith.SigmaAt 1 P ↔ REPred P
Lambda.Arith.piAt_one_iff :
    ∀ {P : ℕ → Prop}, Lambda.Arith.PiAt 1 P ↔ REPred fun x => ¬ P x
Lambda.Arith.SigmaAt.exists :
    ∀ {n : ℕ} {Q : ℕ → Prop}, Lambda.Arith.SigmaAt (n + 1) Q →
      Lambda.Arith.SigmaAt (n + 1) fun x => ∃ y, Q (Nat.pair x y)

-- Post's theorem at level two: Δ⁰₂ = limit computable = decidable from ∅′.
Lambda.Arith.deltaAt_two_iff_limitComputablePred :
    ∀ {P : ℕ → Prop}, Lambda.Arith.DeltaAt 2 P ↔ Lambda.Arith.LimitComputablePred P
Lambda.Arith.deltaAt_two_iff_turingReducible_haltingOracle :
    ∀ {P : ℕ → Prop}, Lambda.Arith.DeltaAt 2 P ↔
      ∃ A, (∀ x, P x ↔ A x = Bool.true) ∧
        TuringReducible (Lambda.Oracle.oracleFun A)
          (Lambda.Oracle.oracleFun Lambda.Oracle.haltingOracle)
```

### Algorithmic information theory

```lean
-- Berry's paradox: Kolmogorov complexity is not computable, and is unbounded.
Lambda.not_computable_kolm  : ¬ Computable Lambda.kolm
Lambda.exists_incompressible : ∀ n : ℕ, ∃ s, n ≤ Lambda.kolm s

-- Chaitin's incompleteness theorem: a sound, recursively enumerable system of assertions
-- "K x > n" proves only boundedly many of them, so from some threshold on none at all.
Lambda.chaitin_incompleteness :
    ∀ {S : ℕ → ℕ → Prop}, REPred (fun q : ℕ × ℕ => S q.1 q.2) →
      (∀ x n, S x n → n < Lambda.kolm x) → ∃ c, ∀ x n, S x n → n < c

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

-- η-reduction terminates and commutes with β, so βη is confluent as well.
Lambda.reduces_etaReduces_commute :
    Lambda.reduces t u → Lambda.etaReduces t v →
      ∃ w, Lambda.etaReduces u w ∧ Lambda.reduces v w
Lambda.betaEta_church_rosser :
    Lambda.betaEtaReduces t u → Lambda.betaEtaReduces t v →
      ∃ w, Lambda.betaEtaReduces u w ∧ Lambda.betaEtaReduces v w

-- η-postponement: βη-reduction is β-reduction followed by η-reduction.
Lambda.betaEtaReduces_iff :
    Lambda.betaEtaReduces t u ↔ ∃ m, Lambda.reduces t m ∧ Lambda.etaReduces m u

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

-- Strong normalization for System F, by Girard's reducibility candidates.
SystemF.sn_of_typing :
    ∀ {Γ : List SystemF.FTy} {t : Lambda} {A : SystemF.FTy}, SystemF.Typing Γ t A → t.SN

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

-- Cook–Levin: SAT is NP-hard, hence NP-complete; so P = NP iff SAT is in P.
Complexity.npHard_SAT : Complexity.NPHard Complexity.Sat.SAT
Complexity.npComplete_SAT : Complexity.NPComplete Complexity.Sat.SAT
Complexity.peqNP_iff_inP_SAT : Complexity.PeqNP ↔ Complexity.InP Complexity.Sat.SAT
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
  (`Start/SelfInterpreter.lean`), Rice's theorem (`Start/Scott.lean`), the Scott–Curry theorem
  on recursively inseparable code sets (`Start/ScottCurry.lean`), the effective form of Rice's
  theorem exhibiting creative code sets (`Start/RiceCreative.lean`, `Start/CreativeCodeSets.lean`),
  undecidability of
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
  Chaitin's incompleteness theorem for complexity lower bounds
  (`Start/ChaitinIncompleteness.lean`), the upper semicomputability of `K` — `K s ≤ n` is
  recursively enumerable, `n < K s` is not, and `K` is the infimum of a primitive recursive
  decreasing approximation (`Start/KolmogorovApprox.lean`),
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
  (`Start/KleeneK.lean`).  **Myhill's isomorphism theorem** upgrades one-one equivalence to
  recursive isomorphism: `Lambda.Myhill.recIso_iff_oneOneEquiv` (`Start/MyhillIso.lean`).  Every
  productive set has an injective production function, so the creative sets are exactly the sets
  recursively isomorphic to `K`, and any two of them are recursively isomorphic to each other
  (`Start/CreativeIso.lean`).
- **Relative computability and the jump** — oracle machines and relative recursiveness
  (`Start/OracleSound.lean`, `Start/OracleUniversal.lean`), the join of two oracles as the least
  upper bound of two degrees (`Start/OracleJoin.lean`), the Kleene–Post construction
  (`Start/KleenePost.lean`), and the counting argument giving uncountably many Turing degrees
  (`Start/OracleCone.lean`).  The Turing jump is Σ₁-hard uniformly in the oracle
  (`Start/JumpSigmaOne.lean`), and, with a primitive recursive stagewise approximation of `∅′`
  (`Start/JumpApprox.lean`), **Shoenfield's limit lemma** identifies the limit computable sets
  with the sets computable from `∅′` (`Start/LimitLemma.lean`).
- **The arithmetical hierarchy** — `Σ⁰ₙ`, `Π⁰ₙ` and `Δ⁰ₙ` as alternating quantifier prefixes over
  a computable matrix, with duality, substitution, the inclusions `Σ⁰ₙ ∪ Π⁰ₙ ⊆ Δ⁰ₙ₊₁` and the
  closure properties, bottoming out at the computable, r.e. and co-r.e. predicates
  (`Start/ArithHierarchy.lean`); and **Post's theorem at level two**: `Δ⁰₂` is exactly the class
  of limit computable predicates, hence exactly the predicates decidable from `∅′`
  (`Start/PostTheoremTwo.lean`).
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
  many-one reductions and NP-completeness (`Start/ComplexityClasses.lean`).  **SAT is in NP**:
  CNFs are encoded as binary words and an explicit Cobham verifier evaluates them
  (`Start/Sat.lean`), and the **Tseitin translation** from Boolean circuits to CNF is proved to
  preserve satisfiability and to have linear size (`Start/Tseitin.lean`).  Every Cobham term is
  compiled into a Boolean circuit of polynomial size, which gives `P ⊆ P/poly` and, for every
  language in NP, a polynomial-size circuit family satisfiable exactly on the language
  (`Start/CobhamCircuit.lean`, `Start/CobhamBRec.lean`, `Start/PolyCircuit.lean`).  **SAT is
  NP-hard, and NP-complete** — `Complexity.npHard_SAT`, `Complexity.npComplete_SAT` and hence
  `Complexity.peqNP_iff_inP_SAT` (`P = NP` iff SAT is in `P`) — unconditionally
  (`Start/CookLevinNPHard.lean`); the missing uniformity of the acceptance families is supplied
  there by `Complexity.stdUniformAcceptFamilies`, built from the segment decoder of
  `Start/UniformSegDec.lean` and the verifier compiler of `Start/UniformSigAll.lean`.  The route
  to it was incremental, and the intermediate implications are kept: the dependence on the
  instance was removed first — the acceptance circuits read the instance off their own input
  (`Start/PinnedCircuit.lean`), the instance is written into the formula by unit clauses
  (`Start/PinnedCnf.lean`) and those are emitted by an explicit Cobham term
  (`Start/CobhamPin.lean`), which reduced the problem to the usual P-uniformity of a
  *length-indexed* circuit family (`Start/CookLevinUniform.lean`, `Start/CookLevinBound.lean`).
  On the other side,
  the reduction to SAT is unconditional for every language decided by a P-uniform circuit family
  (`Start/UniformDecide.lean`), a class that contains every regular language
  (`Start/UniformAuto.lean`) and every symmetric language whose count predicate is decided in
  unary by a Cobham term — majority, exactly half, count divisible by `k`
  (`Start/UniformMaj.lean`, `Start/UniformSym.lean`).  Both are subsumed by the language of any
  automaton with *polynomially many* states whose number of states, transition function and
  acceptance predicate are computed in unary by Cobham terms (`Start/UniformState.lean`,
  `Start/UniformStateCode.lean`), and both earlier families are derived from it
  (`Start/UniformStateSubsume.lean`); a further instance decides whether the binary value of a word is
  divisible by its length plus one, a language that is neither regular nor symmetric
  (`Start/UniformStateInst.lean`).  The Cook–Levin tableau itself is formalized: the space–time
  diagram of a cellular automaton run on a Cobham-computable width and time is a P-uniform circuit
  family (`Start/UniformCA.lean`, `Start/UniformCACode.lean`), and so is the language of a one-tape
  deterministic Turing machine with finitely many states under the same bounds
  (`Start/UniformTM.lean`).  A further loop rule stacks polynomially many copies of a P-uniform
  *stage* circuit over a P-uniform base, each copy rewired to the outputs of the copy below — the
  shape the unrolling of a bounded recursion has — and proves the stack P-uniform
  (`Start/UniformIterate.lean`), the gates of a copy being read off the description of the stage by
  a Cobham term (`Start/UniformSelect.lean`).  The compiler itself is in place for the whole
  non-recursive fragment of the Cobham algebra: every term built from projections, the empty
  word, appending a bit, concatenation and composition is turned into a P-uniform circuit family
  computing it, together with a polynomial length bound
  (`Start/UniformSigCompile.lean`, `Start/UniformSigFlat.lean`), leaving bounded recursion
  (`Cob.bRec`) as the only shape for which the device must still be produced by hand.
- **Typed calculi and proof theory** — the simply typed lambda calculus over the same de Bruijn
  syntax, with Tait strong normalization and the untypability of `omega`
  (`Start/SimpleTypes.lean`); **System F**, the polymorphic lambda calculus in Curry style over
  the same terms, with Girard's reducibility candidates and strong normalization
  (`Start/SystemF.lean`), the substitution lemmas and subject reduction with its generation lemma
  (`Start/SystemFSubst.lean`, `Start/SystemFSR.lean`), and the polymorphic Church numerals,
  self-application — typable in System F but not in the simply typed calculus — and unique normal
  forms (`Start/SystemFChurch.lean`), with the Church-style presentation and its strong
  normalization by erasure, together with its subject reduction (`Start/SystemFC.lean`,
  `Start/SystemFCSR.lean`) and the confluence of its annotated reduction, both β and type-β, by
  parallel reduction (`Start/SystemFCSubst.lean`, `Start/SystemFCConfluence.lean`); and Gödel's
  System T with strong
  normalization, subject reduction and canonicity (`Start/SystemTSyntax.lean`, `Start/SystemT.lean`,
  `Start/SystemTCanon.lean`).
  Reduction in System T is confluent (`Start/SystemTConfluence.lean`), and the set-theoretic
  denotational semantics of System T is **adequate**: a closed term of type `nat` reduces to the
  numeral of its denotation, so at base type equality of denotations, convertibility and
  observational equivalence all coincide (`Start/SystemTDenot.lean`).
- **Curry–Howard–Lambek** — an intrinsically typed simply typed lambda calculus with a unit type,
  binary products and function types, with its substitution calculus and βη-conversion
  (`Start/Stlc.lean`).  Its *syntactic category* — types as objects, terms with one free variable
  modulo conversion as morphisms, substitution as composition — has finite products and an
  exponential, i.e. it is **cartesian closed** (`Start/StlcCcc.lean`).  Conversely, every
  cartesian closed category interprets the calculus, conversion is sound for that interpretation,
  and the interpretation assembles into a functor out of the syntactic category
  (`Start/CccModel.lean`).
- **Dependent types: `λΠ` and locally cartesian closed categories** — the layer above
  Curry–Howard–Lambek, where a type may depend on a term.  The calculus `λΠ` is formalized as a
  pure type system: raw syntax with a full parallel-substitution calculus and **Church–Rosser**
  for β (`Start/LambdaPi.lean`), and the typing judgement with weakening, the substitution lemma,
  the five inversion lemmas, validity, context conversion and **subject reduction**
  (`Start/LambdaPiTyping.lean`, `Start/LambdaPiBound.lean`).  The calculus is then normalized:
  types are unique up to conversion and the terms split into kinds, families and objects
  (`Start/LambdaPiUnique.lean`); forgetting the dependency sends a type to its **skeleton**, a
  simple type, which depends only on the type variables and is therefore invariant under
  conversion (`Start/LambdaPiSkeleton.lean`); a dependent derivation erases to a simply typed one
  over the skeletons (`Start/LambdaPiSimple.lean`); and Tait's reducibility method, in the Kripke
  form that the type annotations force, gives **strong normalization** for `λΠ`
  (`LambdaPi.Typing.sn`, `Start/LambdaPiSN.lean`).  Reading the calculus as a logic, this yields
  **consistency**: in the context declaring a type variable `α : ∗` no term has type `α`
  (`LambdaPi.not_typing_var_zero`, `Start/LambdaPiConsistent.lean`).  The other rule for
  functions, η, is settled in `Start/LambdaPiEta.lean`: on raw terms η-reduction terminates and is
  **confluent** (`LambdaPi.EtaRed.church_rosser`), but βη-reduction is **not**
  (`LambdaPi.not_church_rosser_betaEta`) — βη-conversion identifies two abstractions that differ
  only in their domain annotation (`LambdaPi.betaEtaConv_lam_annot`), and Nederpelt's term
  `λ(x : ∗). ((λ(y : □). y) x)` has the two distinct βη-normal reducts `λ(x : ∗). x` and
  `λ(y : □). y`.  So η can enter a Church-style calculus only through *typed* conversion; for the
  *untyped* calculus, whose abstractions carry no annotation, η instead terminates and **commutes
  with β** (`Lambda.reduces_etaReduces_commute`), so βη is confluent there
  (`Lambda.betaEta_church_rosser`, `Start/LambdaEta.lean`, `Start/LambdaBetaEta.lean`), and η can
  even be **postponed**: βη-reduction is β-reduction followed by η-reduction
  (`Lambda.betaEtaReduces_iff`, `Start/LambdaEtaPostpone.lean`).  Termination and confluence
  together make the calculus effective: a verified reduction strategy computes the normal form of
  a strongly normalizing term, so conversion of typable terms is **decidable**
  (`Start/LambdaPiNormalize.lean`), and the type-inference algorithm — written as a function that
  returns a type *together with a derivation*, hence sound by construction, and proved complete —
  decides typability and type checking (`LambdaPi.infer`, `LambdaPi.decidableTyping`,
  `Start/LambdaPiInfer.lean`).  Its **syntactic category** —
  objects
  the well-formed contexts, morphisms the well-typed substitutions modulo conversion — has a
  terminal object, and its context-extension squares are **pullbacks**
  (`Start/LambdaPiCat.lean`), which is the universal property that "a substitution into `A :: Γ`
  is a substitution into `Γ` plus a term of `A`".  On the semantic side, `Start/Cwa.lean` defines
  categories with attributes and their Π-structures, `Start/CwaType.lean` builds the standard
  model of families of types, `Start/Lccc.lean` packages Mathlib's chosen pullbacks and
  exponentiable morphisms into an explicit `LocallyCartesianClosed` class with the adjoint chain
  `Σ_f ⊣ f* ⊣ Π_f`, and `Start/LcccType.lean` proves that `Type u` is locally cartesian closed
  with an explicit dependent product and **identifies that categorical Π with the type-theoretic
  one** of the standard model.  The syntax of `λΠ` itself is a category with attributes with a
  weak Π-structure, and the η-law is proved to fail there (`Start/LambdaPiCwa.lean`).  On the
  semantic side the coherence problem is solved: types are presented by **local universes**, which
  makes substitution strictly functorial, so every category with pullbacks is a category with
  attributes and no slice object is lost (`Start/CwaLocalUniverse.lean`).  That strictified model
  also carries **both quantifiers**: for a locally cartesian closed category, the dependent product
  is built generically — its base is the pushforward classifying the pair `(A, B)`, its total space
  the pushforward of the display map of the generic `B` — so it is *strictly* stable under
  substitution, and abstraction and application are the two legs of one bijection, hence satisfy
  **β and η** (`Cwa.piStructOfLccc`); the dependent sum comes with it (`Cwa.sigmaStructOfLccc`), and
  `Type u` is an instance (`Start/CwaPi.lean`, `Start/CwaPiType.lean`).  Abstraction and
  application of that dependent product are natural in the context, so the model also validates
  the substitution law `(λ b)[σ] = λ (b[σ⁺])` (`LuTy.lam_sub`, `Start/CwaPiSub.lean`).  Since the
  types of `λΠ` are the *terms of the sort `∗`* rather than all the types of a model,
  `Start/CwaSmall.lean` extracts from a model with a universe its **small fragment**
  (`Cwa.Universe.smallCwa`): the category with attributes whose types are the codes, with its
  inclusion into the ambient model, the restriction of universe-preserving comparisons to it, and
  — when the universe is closed under products naturally — its own dependent product
  (`Cwa.Universe.smallWeakPi`).  Both sides supply an instance: the model presented by a universe
  object, whose types in a context are the maps into it (`CwaUniv.smallTyEquivHom`), and the small
  fragment of the syntactic model of `λΠ` (`LambdaPiUniv.smallSyntacticPi`), for which the code of
  a product is proved stable under substitution (`LambdaPiUniv.codeQ_sub`).  That small fragment
  is then compared with the model whose types are the small types of the calculus, and the two are
  found to be **the same model**: the identity on contexts is a morphism of categories with
  attributes in each direction (`LambdaPiUniv.smallToCwa` and `LambdaPiUniv.cwaToSmall`), acting on
  types by the bijection between the terms of `∗` and the small types, and the two composites are
  the identity, so the two syntactic models are isomorphic in the category of models
  (`LambdaPiUniv.smallModelIso`, `Start/LambdaPiSmallCompare.lean`).  Finally the syntax is
  interpreted in an **arbitrary** model: `LambdaPi.Model` is the structure a category of contexts
  must carry, the interpretation of raw expressions is given by the relations `LambdaPi.TyI` and
  `LambdaPi.TmI` (`Start/LambdaPiInterp.lean`), it is single-valued in a model whose product former
  is injective (`LambdaPi.functional_of_piInj`), commutes with renaming and substitution
  (`Start/LambdaPiInterpSub.lean`) and is invariant under β-conversion
  (`Start/LambdaPiInterpConv.lean`), and it is total on derivations
  (`LambdaPi.Typing.interp_total`).  Hence **initiality**: a derivable term denotes exactly one term
  of exactly one type (`LambdaPi.interp_exists_unique`), a well-typed substitution is carried by
  exactly one morphism (`LambdaPi.subI_exists_unique`), the interpretation is a functor on the
  syntactic category (`LambdaPiInitial.functor`), and it assembles into a morphism of categories
  with attributes out of the syntactic model (`LambdaPiInitial.mor`, `Start/LambdaPiInitial.lean`).
  That comparison morphism respects the whole structure of a model of `λΠ` and not merely the
  category with attributes: it carries the sort `∗` to the universe of the model and commutes with
  decoding (`LambdaPiInitial.mor_preservesUniverse`), preserves the dependent products over the
  small types (`mor_preservesSmallPi`) and the codes for those products (`mor_preservesPiClosed`,
  `Start/LambdaPiInitialUniv.lean`).
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
- **Adequacy of the graph model** — the interpretation in the graph model is not merely sound: a
  term whose denotation contains a token, in any environment, has a **head normal form**
  (`Start/GraphAdequacy.lean`, by a computability argument on the tokens), and conversely a head
  normal form has a nonempty denotation, so for a closed term `⟦t⟧ρ = ∅` exactly when `t` has no
  head normal form.  For closed terms this coincides with unsolvability
  (`Start/HnfSolvable.lean`: a closed head normal form is solvable, by the substitution calculus
  of `Start/Bohm.lean`), so the least element of the model is precisely the unsolvable terms; and
  denotational equality implies **observational equivalence** at head normalization
  (`Start/GraphObs.lean`); the converse fails, see below.
- **Adequacy of `D∞`** — the same holds for the inverse limit.  Every head normalizable term has a
  denotation different from the least element in a suitable environment (`Start/DinfHnf.lean`),
  and conversely a term whose denotation is not the least element, in any environment, has a head
  normal form (`ScottDinf.hasHnf_of_ddenot_ne_botDinf`, `Start/DinfAdequacy.lean`).  The proof is
  the classical computability argument, carried out along the *tower* — `ScottDinf.RelD n z t`
  relates a stage-`n` value to a term, is compatible with the embedding–projection pairs and
  closed under suprema of chains, and the fundamental lemma `ScottDinf.realD_substEnv` shows the
  interpretation preserves it.  Hence `⟦t⟧ρ = ⊥` in every environment exactly when `t` has no head
  normal form, for a closed term exactly when it is unsolvable, and denotational equality implies
  observational equivalence at head normalization (`ScottDinf.obsEqHnf_of_ddenot_eq`).
- **Full abstraction fails for the graph model** (`Start/GraphNotFullyAbstract.lean`) — the
  identity `λx. x` and its eta-expansion `λx. λy. x y` have different graph denotations, the graph
  model not being extensional, but no context distinguishes them, because `D∞` validates eta and
  is adequate.  So the inclusion of denotational into observational equality is strict there
  (`GraphNotFullyAbstract.graph_not_fully_abstract`), and `D∞` identifies strictly more terms than
  the graph model.
- **The approximation theorem for the graph model** (`Start/GraphApprox.lean`,
  `Start/GraphApproxTheorem.lean`) — the direct approximant `ω(M)` keeps the abstraction prefix
  and the variable head of `M` and erases everything under a head redex to `Ω`.  The denotation
  of a term is exactly the union of the denotations of the direct approximants of its reducts,
  `⟦M⟧ρ = ⋃ {⟦ω(M')⟧ρ : M ↠ M'}` (`GraphModel.denot_eq_iUnion_denot_direct`): no information of
  a term is invisible to all of its finite approximants.  The easy inclusion is monotonicity of
  the denotation for the approximation order; the hard one is a Kripke-style computability
  argument on the tokens, whose fundamental lemma `GraphModel.arealAux_substEnv` carries two
  environments, one for the free variables of the term and one for the target context of the
  substitution.
- **The approximation theorem for `D∞`** (`Start/DinfApprox.lean`) — the same statement in the
  order-theoretic form the continuous model calls for: `⟦M⟧ρ` is the least upper bound of
  `{⟦ω(M')⟧ρ : M ↠ M'}` (`ScottDinf.isLUB_ddenot_direct`).  The computability relation is indexed
  by the finite levels of the inverse limit; each level is finite, so a supremum along a chain is
  attained there, and confluence merges the finitely many reducts the different levels produce.
- **Full abstraction of `D∞` on closed normal forms** (`Start/DinfApply.lean`,
  `Start/DinfBohmEta.lean`, `Start/DinfNormalFullAbstraction.lean`) — the finite case of
  Wadsworth's theorem.  `D∞` is extensional (`ScottDinf.dinf_ext_dappN`), which lets two
  denotations be compared by feeding them a common stack of arguments; a size induction mirroring
  the η-general Böhm-out descent then shows that η-equal Böhm trees have the same denotation
  (`ScottDinf.ddenot_toTerm_eq_of_tagEq`).  Conversely separable terms are distinguished by the
  context `X a₁ … aₖ Ω I` (`ScottDinf.not_obsEqHnf_of_separable`).  With Böhm's theorem in its
  η-general form this gives `ScottDinf.obsEqHnf_iff_ddenot_eq_normal`: for closed β-normal forms,
  observational equivalence and equality of `D∞` denotations coincide, and hence
  `ScottDinf.obsEqHnf_iff_ddenot_eq_of_normalizes` for every closed term that has a normal form.
  The general case needs a separation argument for the finite approximants `ω(M')`, which contain
  `Ω`; `Start/DinfWadsworth.lean` makes that gap precise, proving that contexts are monotone in
  their hole (`ScottDinf.ddenot_fill_mono`) and reducing full abstraction to a separation
  principle `ScottDinf.SeparatesApprox`, which the next item discharges.
- **Wadsworth's theorem** (`Start/HeadSpine.lean`, `Start/TagFail.lean`, `Start/ApproxShape.lean`,
  `Start/DinfSpine.lean`, `Start/DinfTagBelow.lean`, `Start/DinfTagBelowSound.lean`) — two closed
  terms are observationally equivalent, by head normalisation, exactly when they have the same
  denotation in `D∞` (`ScottDinf.obsEqHnf_iff_ddenot_eq`).  `Lambda.TagFail` is a *finite failure
  witness* for the comparison of two arbitrary terms, and `Lambda.sepDiv_of_tagFail` is the
  Böhm-out that turns such a witness into closed arguments on which the first term head-converges
  and the second head-diverges; the converse, `ScottDinf.tagBelowSound`, says that absence of a
  witness implies the `D∞` inequality, so the order between closed terms *is* the absence of a
  failure witness (`ScottDinf.ddenot_le_iff_not_tagFail_unconditional`).  Its proof splits at the
  approximation theorem: a finite approximant is put below a term by a size induction on the shape
  of the approximant (`Lambda.approx_direct_shape`,
  `ScottDinf.le_ddenot_of_not_tagFail_approx`), whose only non-structural case — a variable
  against a possibly *infinite* η-expansion of it — is settled level by level in the inverse limit
  (`ScottDinf.le_ddenot_of_not_tagFail_var`).
- **The infinite η-expansion of the identity** (`Start/DinfEtaLimit.lean`) — the reason no relation
  generated by *finite* witnesses can decide the `D∞` order.  Let `J = Θ (λ j x y. x (j y))`, so
  that `J ↠ λx y. x (J y)` (`ScottDinf.Jterm_reduces`): unfolding, `J` is the identity η-expanded
  infinitely often.  `ScottDinf.eq_dId_of_eta_fixpoint` characterises the identity of `D∞` by the
  two η-limit equations `x · y · z = y · (x · z)` and `x · ⊥ = ⊥`, by two simultaneous inductions
  over the levels of the inverse limit; applied to `J` it gives `⟦J⟧ = ⟦I⟧`
  (`ScottDinf.ddenot_Jterm_eq_ddenot_id`), hence `ScottDinf.obsEqHnf_Jterm_id` and
  `ScottDinf.obsEqHnf_app_Jterm` (`J M` is indistinguishable from `M`).  The identification is not
  a β-conversion: the graph model, sound for β and not extensional, separates the two
  (`ScottDinf.not_conv_Jterm_I`).
- **Head reduction** — the head strategy (weak head steps, allowed under a leading abstraction)
  is defined in `Start/HeadReduction.lean` and proved deterministic and *normalizing*: a term has
  a head normal form exactly when the strategy terminates on it
  (`Lambda.hasHnf_iff_hasHeadEval`), by standardization for weak head reduction and confluence.
  This yields the structural laws that arbitrary reductions do not give: head divergence is
  preserved by substitution (`Lambda.hasHnf_of_hasHnf_subst`) and head normalizability of an
  application is inherited by its function part (`Lambda.HasHnf.app_left`).  Hence a purely
  syntactic proof that every solvable term has a head normal form (`Start/HeadSolvable.lean`),
  which makes Wadsworth's characterization of closed solvable terms independent of the graph
  model.
- **Intersection types and the filter model** (`Start/IntersectionTypes.lean`,
  `Start/FilterModel.lean`, `Start/IntersectionNormalization.lean`) — the third model, and the one
  that explains the other two.  The strict types of the Coppo–Dezani system `λ∩` are *literally*
  the tokens of the graph model, and `Inter.deriv_iff_mem_denot` proves the coincidence exact:
  `Γ ⊢ M : σ` holds precisely when the token `σ` lies in the denotation of `M` in the environment
  read off from `Γ`.  The set of types of a term therefore **is** its denotation, so the graph
  model is the filter model of `λ∩`.  Subject reduction and subject expansion are then immediate
  (`Inter.deriv_reduces`, `Inter.deriv_expansion`), and typability coincides with head
  normalisability and with solvability (`Inter.typable_iff_hasHnf`, `Inter.typable_iff_solvable`):
  "syntactically typable" and "semantically different from the empty denotation" are the same
  statement.  Restricting to `ω`-free types gives the **Coppo–Dezani normalisation theorem**
  (`Inter.properTypable_iff_hasNormalForm`): a term is typable without `ω` exactly when it has a
  β-normal form — proved through the approximation theorem rather than by reducibility — and the
  inclusion is strict (`Inter.exists_typable_not_properTypable`, witnessed by `x Ω`).

`Start/Demo.lean` is a guided tour with `#check`s of the headline statements.

## Building

> **Note on the pinned toolchain.**  The library is built against Lean `v4.33.0` and a matching
> Mathlib checkout supplied at `.lake/packages/mathlib`; it is verified against Mathlib commit
> `db584cd6`, the `v4.33.0` tag.  `cslib` is supplied the same way, at
> `.lake/packages/cslib`, the revision built for Lean `v4.33.0`.  All of `Start/`
> compiles on that toolchain, including the two modules that depend on `cslib`
> (`Start/Representation.lean` and `Start/KolmogorovRepresentation.lean`).

The project pins Lean `v4.33.0` (`lean-toolchain`); `lakefile.toml` requires Mathlib and `cslib`
as local checkouts under `.lake/packages/`, and `lake-manifest.json` records them as such.  These
sources must agree: if they do not, `lake` re-resolves the dependencies on every invocation and
starts compiling all of Mathlib from source, which never finishes in reasonable time.

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
evidence note in `docs/goal/evidence/`, including the honest boundary of each claim.  Of the 92
tasks, 91 are `DONE_STRONG`; the one `BACKEND_PARTIAL` task (`M9-LAMBDAPI-LCCC`) carries an
explicit open boundary.  Validate and re-render with:

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
| Cobham's theorem, and a link to machine-level polynomial time | Would connect `Start/ComplexityClasses.lean` (Cobham axioms) to `Start/TM2PolyTime.lean` (bounded TM2 machines) and to mathlib's `Computable` | `Start/ComplexityClasses.lean`, `Start/TM2PolyTime.lean` |
| Full abstraction for the untyped models | Adequacy is proved for the typed setting of System T (`Start/SystemTDenot.lean`) and, for the untyped calculus, for both the graph model (`Start/GraphAdequacy.lean`, `Start/HnfSolvable.lean`, `Start/GraphObs.lean`) and `D∞` (`Start/DinfAdequacy.lean`); for the graph model full abstraction is now *disproved* (`Start/GraphNotFullyAbstract.lean`: the identity and its eta-expansion are observationally equivalent but have different graph denotations); the approximation theorem for the graph model is proved (`Start/GraphApproxTheorem.lean`: a denotation is the union of the denotations of the direct approximants of the reducts); the approximation theorem for `D∞` is proved as well (`Start/DinfApprox.lean`: a denotation is the least upper bound of the denotations of the direct approximants of the reducts), and full abstraction of `D∞` is proved for arbitrary closed terms — Wadsworth's theorem, `ScottDinf.obsEqHnf_iff_ddenot_eq` in `Start/DinfTagBelowSound.lean`, the normal-form case being `Start/DinfNormalFullAbstraction.lean` | `Start/GraphNotFullyAbstract.lean`, `Start/GraphApprox.lean`, `Start/GraphApproxTheorem.lean`, `Start/DinfApprox.lean`, `Start/DinfBohmEta.lean`, `Start/DinfNormalFullAbstraction.lean`, `Start/TagFail.lean`, `Start/ApproxShape.lean`, `Start/DinfTagBelow.lean`, `Start/DinfTagBelowSound.lean`, `Start/DinfAdequacy.lean`, `Start/GraphObs.lean` |
| Gentzen consistency, ordinal analysis up to `ε₀` | Proof theory beyond strong normalization | `Start/SystemT.lean`, `Start/SystemTCanon.lean` |
| Post's problem for **Turing** reducibility (Friedberg–Muchnik) | The many-one case is settled here (`Start/PostSimple.lean`, `Start/PostIncomplete.lean`: a simple set is neither computable nor many-one complete, and `Start/PostCreative.lean`: creative sets are many-one complete); relative computability, the jump and the Kleene–Post construction are formalized (`Start/OracleUniversal.lean`, `Start/KleenePost.lean`, `Start/JumpSigmaOne.lean`), but the Turing case of Post's problem needs a priority construction with injury, which is not formalized | `Start/PostSimple.lean`, `Start/PostIncomplete.lean`, `Start/KleenePost.lean`, `Start/JumpSigmaOne.lean` |
| Post's theorem at every level (`Σ⁰ₙ₊₁` is exactly "r.e. in `∅⁽ⁿ⁾`") | Level one and level two are proved (`Start/ArithHierarchy.lean`, `Start/PostTheoremTwo.lean`); the general case needs the hierarchy relativized to an oracle | `Start/ArithHierarchy.lean`, `Start/PostTheoremTwo.lean`, `Start/JumpSigmaOne.lean` |
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
