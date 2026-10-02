# Related work: where this library stands

This note places the library in `Start/` among existing formalizations of computability
and complexity in Lean, Coq/Rocq, Isabelle, Agda and HOL4. It is written for readers who
want to check it, so every statement is labelled with how it was checked.

## How this note was checked

**Claims about this library.** Each one names the module and declaration that carry it. I
checked each name against the source of this repository (commit `bbaa6ec`, 2026-10-02):
the declaration exists with that fully qualified name in that file, and I read its
statement. I also ran a text search of `Start/` for `sorry`, `admit` and `axiom`. None of
them occurs outside comments and prose. I did **not** rebuild the library for this note,
so the check is against the source text and not a fresh compilation.

**Claims about other projects.** Each one carries one of three labels:

- **[V] verified against a source I can name.** I retrieved that source on 2026-10-02 and
  read the relevant part. The source is given: a repository README, a file or directory
  listing, a file header, or an Archive of Formal Proofs (AFP) entry page. A [V] label
  verifies only what that source says. Where the source is a README or an abstract, I did
  not open the proof files behind it.
- **[M] believed from memory, unverified.** I believe this but did not check it against a
  source during this review.
- **[N] no information.** I know of no formalization, and I did not find one with the
  searches described. This is evidence of absence only to the extent of those searches.

The phrase "none known to me" always comes with one of these labels and a sentence on what
was searched. This note never claims that something is formalized for the first time.

**Versions compared against.**

- Mathlib at the tag the library pins, `v4.33.0`. I downloaded its source tree and searched
  it.
- cslib at the pinned revision `3951377e5a3f5772737f11cd62bc5bb6a72f95d1`. I searched a
  checkout of that revision.
- The other projects at the default branch of their public repositories on 2026-10-02.

## 0. The four former to-do items

The to-do list once kept in `Start/Basic.lean` had four technical items. All four are
settled.

| Item | Outcome | Where |
| --- | --- | --- |
| `M3-LAMBDA-PREC-COMPILER` | done (`DONE_STRONG` on the task board). Every primitive recursive function has a closed λ-realizer on Church numerals. | `Start/Realizer.lean`: `Lambda.exists_realizer_of_primrec` |
| `M3-LAMBDA-MU-CORRECTNESS` | done (`DONE_STRONG`). The specification `Lambda.MuCorrectness` of the minimisation combinator is proved. | `Start/Recursion.lean`: `Lambda.MuCorrectness`; `Start/Minimization.lean`: `Lambda.muCorrectness` |
| `M3-PARTREC-IMP-LAMBDACOMPUTABLE` | done (`DONE_STRONG`). The total case is proved, and later the partial case too. | `Start/PartrecLambda.lean`: `Lambda.exists_realizer_of_computable`, `lambdaComputable_of_computable`; `Start/PartialCapstone.lean`: `lambdaComputable_of_partrec` |
| The assumption `Lambda.EvalCorrectness` | **refuted**, and replaced by an assumption-free route | see below |

`Lambda.EvalCorrectness` (`Start/Arithmetic.lean`) said that the code-level evaluator
`Lambda.eval` is correct. It is false. `Lambda.not_evalCorrectness` (`Start/EvalCorrect.lean`)
proves its negation with an explicit term. The evaluator's substitution `Lambda.subst_code`
substitutes into bound variables.

The theorem that used the assumption, `LambdaComputable_imp_Partrec` (`Start/Arithmetic.lean`),
is therefore vacuous. It is superseded by `LambdaComputable_imp_Partrec_unconditional`
(`Start/EvalGK.lean`), which has no hypothesis. That theorem uses the Gross–Knuth evaluator,
whose correctness is the theorem `Lambda.evalCorrectnessGK` (`Start/EvalGK.lean`). The
Church–Turing capstone `lambdaComputable_iff_partrec` (`Start/PartialCapstone.lean`) is
built from this route and `lambdaComputable_of_partrec`.

So the fourth item is a result, not a gap: a stated assumption turned out to be false, the
library proves that it is false, and the theorem it was meant to support holds without it.

## 1. Main results and their closest existing formalizations

"Closest" means the nearest formalization I know of the same theorem, in any system. It
does not mean the same formulation. Many of the neighbours use a different model of
computation, such as weak call-by-value λ-calculus, Turing machines or synthetic
computability.

| # | Result in this library | Module : declaration | Closest existing formalization known to me | Label |
| --- | --- | --- | --- | --- |
| 1 | λ-definable = partial recursive (`ℕ →. ℕ`) | `Start/PartialCapstone.lean` : `lambdaComputable_iff_partrec` | HOL4 `examples/computability/lambda` (Norrish), which does computability with λ-terms as the model. Coq Library of Undecidability Proofs, `Synthetic/Models_Equivalent.v`, equivalence of models including weak call-by-value λ (L). | [V] directory listing of HOL4; [V] Coq README. Exact HOL4 theorem not inspected |
| 2 | Bundled TM2 machines compute exactly the partial recursive functions; λ ⇔ TM2 | `Start/TM2Capstone.lean` : `TM2Partrec.tm2Computable_iff_partrec`, `lambdaComputable_iff_tm2Computable` | Mathlib `v4.33.0` has only Partrec ⇒ TM2 (`Turing.PartrecToTM2.tr_eval`); the converse arithmetization is this library's (`Start/TM2Partrec.lean`). Isabelle AFP *Universal Turing Machine* (Xu, Zhang, Urban, Joosten, Regensburger). Coq `Models_Equivalent.v` | [V] Mathlib source; [V] AFP page; [V] Coq README |
| 3 | Confluence of β (and of βη) on de Bruijn terms | `Start/Reduction.lean` : `Lambda.confluence_theorem`; `Start/LambdaBetaEta.lean` : `Lambda.betaEta_church_rosser` | cslib `LocallyNameless/Untyped/FullBetaConfluence.lean`, `FullBetaEtaConfluence.lean`; HOL4 `examples/lambda/barendregt` | [V] cslib checkout; [V] HOL4 README |
| 4 | Rice/Scott for λ-terms, s-m-n, a self-interpreter, Kleene's second recursion theorem with parameters | `Start/Scott.lean` : `Lambda.scott_theorem`; `Start/SMN.lean` : `Lambda.exists_smn`; `Start/SelfInterpreter.lean` : `Lambda.exists_self_interpreter`; `Start/RecursionParams.lean` : `Lambda.exists_recursion_with_parameters` | Mathlib (codes, not λ-terms): `ComputablePred.rice`, `Nat.Partrec.Code.smn`, `Nat.Partrec.Code.fixed_point₂`. HOL4 `recsetsScript.sml` : `Rices_Theorem`, `recfunsScript.sml` : `recursion_thm` | [V] Mathlib source; [V] HOL4 file |
| 5 | Halting set one-one complete; Post's simple set; Post's problem for many-one reducibility | `Start/HaltingComplete.lean` : `Lambda.codeHasNormalForm_one_complete`; `Start/PostSimple.lean` : `Lambda.Post.rePred_simpleSet`; `Start/PostIncomplete.lean` : `Lambda.Post.exists_rePred_not_computable_not_manyOneComplete` | Coq *Synthetic Computability* (Forster et al.): simple and hypersimple predicates, and Post's problem for many-one and truth-table reducibility (CSL 2023) | [V] README of `uds-psl/coq-synthetic-computability` |
| 6 | Myhill's isomorphism theorem; creative sets are recursively isomorphic to `K` | `Start/MyhillIso.lean` : `Lambda.Myhill.recIso_iff_oneOneEquiv`; `Start/CreativeIso.lean` : `Lambda.Post.Creative.recIso_haltK` | Coq *Synthetic Computability*: `Basic/Myhill.v` (CPP 2023 proof pearl). For the classification of creative sets: none known to me | [V] README; creative sets [N] |
| 7 | Rice–Shapiro; Myhill–Shepherdson (effective operations are continuous) | `Start/RiceShapiro.lean` : `Lambda.Post.rice_shapiro`; `Start/EffectiveOperation.lean` : `Lambda.Post.effop_continuous` | none known to me | [N] |
| 8 | Uncountably many Turing degrees; Kleene–Post incomparable degrees; join as least upper bound | `Start/OracleCone.lean` : `Lambda.Oracle.not_countable_turingDegree`; `Start/KleenePost.lean` : `Lambda.Oracle.turingDegree_incomparable`; `Start/OracleJoin.lean` : `Lambda.Oracle.turingDegree_isLUB_join` | Mathlib defines `TuringReducible` / `TuringDegree` (Duve, Roth) but has no countability or Kleene–Post theorem. Coq *Synthetic Computability*: oracle computability and `PostsTheorem/KleenePostTheorem.v` | [V] Mathlib source (searched `TuringDegree.lean`, `RecursiveIn.lean`); [V] Coq README |
| 9 | Shoenfield's limit lemma | `Start/LimitLemma.lean` : `Lambda.Oracle.limitComputable_iff_turingReducible_haltingOracle` | none known to me | [N] |
| 10 | Arithmetical hierarchy: Post's theorem at level 2, properness at every level, no universal arithmetical predicate | `Start/PostTheoremTwo.lean` : `Lambda.Arith.deltaAt_two_iff_turingReducible_haltingOracle`; `Start/ArithHierarchyProper.lean` : `Lambda.Arith.sigmaAt_proper`, `Lambda.Arith.not_exists_univ_arithmetical` | Coq: Post's theorem for the arithmetical hierarchy (`coq-synthetic-computability`, `PostsTheorem/PostsTheorem.v`; Mück's `coq-posts-theorem`). HOL4 `recdegreesScript.sml` defines `rec_sigma`/`rec_pi`/`rec_delta` with their lowest levels | [V] READMEs; [V] HOL4 file. Whether the Coq development states properness at every level: [N] |
| 11 | Kolmogorov complexity of λ-terms is uncomputable; Chaitin's incompleteness for an abstract sound r.e. system | `Start/Kolmogorov.lean` : `Lambda.not_computable_kolm`; `Start/ChaitinIncompleteness.lean` : `Lambda.chaitin_incompleteness` | HOL4 `examples/computability/kolmog` (`kolmog_incomputableScript.sml` : `UKC_incomp`, invariance theorem, plain and prefix-free complexity, Kraft inequality). Coq *Synthetic Computability*: nonrandom numbers form a simple predicate. Lean repositories found by search: `AlexeyMilovanov/kolmogorov-complexity-lean`, `krstopro/lean-kolmogorov-complexity` | [V] HOL4 listing and theorem names; [V] Coq README; Lean repositories: description only. Chaitin's incompleteness elsewhere: [N] |
| 12 | Chaitin's Ω for the λ prefix machine: in `(0,1)`, irrational, Martin-Löf random | `Start/ChaitinOmega.lean` : `Lambda.chaitinOmega_mem_Ioo`; `Start/OmegaOracle.lean` : `Lambda.irrational_chaitinOmega`; `Start/OmegaURandom.lean` : `KC.mlRandom_omegaSeq` | none known to me | [N]. The README of `cameronfreer/algorithmic-randomness` mentions Kraft–Chaitin allocation but not Ω (checked by text search) |
| 13 | Levin–Schnorr: ML-random ⇔ prefix-incompressible | `Start/LevinSchnorr.lean` : `KC.mlRandom_iff_exists_const_le_KU` | Lean `cameronfreer/algorithmic-randomness`: `IsMartinLofRandom x ↔ ∃ c, ∀ n, n ≤ prefixComplexity (initSeg x n) + c` | [V] README |
| 14 | Kraft's inequality for prefix-free codes | `Start/Kraft.lean` : `Kraft.tsum_wt_le_one` | Mathlib `InformationTheory/Coding/KraftMcMillan.lean` (Kraft–McMillan for uniquely decodable codes, so more general); HOL4 `kraft_ineqScript.sml` | [V] Mathlib source; [V] HOL4 listing |
| 15 | Eight complexity measures as instances of one description system | `Start/DescriptionSystem.lean` : `Complexity.DescSystem`; see §3 | none known to me for the common interface | [N] |
| 16 | Busy beaver for λ is uncomputable | `Start/BusyBeaver.lean` : `Lambda.not_computable_bbTime` | Isabelle AFP *The Busy Beaver Function* (2026); HOL4 `kolmog/busyBeaverScript.sml` | [V] AFP topic listing (title only); [V] HOL4 listing (file name only) |
| 17 | Blum: no computable time bound covers every computable function; Borodin-style gap theorem; Levin's universal search is optimal | `Start/StepComplexity.lean` : `Complexity.exists_computable_steps_gt`; `Start/GapTheorem.lean` : `Complexity.exists_gap`; `Start/LevinSearch.lean` : `Complexity.levin_optimal` | none known to me | [N] |
| 18 | Cook–Levin: SAT, CIRCUIT-SAT and k-SAT (k ≥ 3) are NP-complete | `Start/CookLevinNPHard.lean` : `Complexity.npComplete_SAT`; `Start/SatToCircuitCob.lean` : `Complexity.npComplete_CSAT`; `Start/ThreeSat.lean` : `Complexity.npComplete_KSAT` | Coq: Gäher–Kunze, ITP 2021 (`coq-library-complexity`, `NP/SAT`). Isabelle AFP *The Cook-Levin theorem* (Balbach, 2023). Lean repositories found by search (`EdouardBonnet/cook-levin`, `PierreSenellart/descriptive-complexity`, others) | [V] Coq README; [V] AFP page; Lean repositories: description only |
| 19 | Savitch's theorem, in the memory model of a stack machine | `Start/SavitchSpace.lean` : `Complexity.Space.savitch_accepts_iff`, `Complexity.Space.savitch_poly_memory` | Lean `EdouardBonnet/savitch`, whose description reads "Lean statements, finite reachability proofs, and explicit machine obligations" | description only; otherwise [N] |
| 20 | P ⊆ PSPACE on an offline Turing machine | `Start/CobhamPspace.lean` : `Complexity.Space.pspace_of_inP` | none known to me | [N] |
| 21 | TQBF is PSPACE-hard (completeness open; see §4) | `Start/QbfCobReduction.lean` : `Complexity.Qbf.QBF.pspaceHard_tqbfLang` | none known to me | [N] |
| 22 | Baker–Gill–Solovay, separating half: some oracle `B` with `P^B ≠ NP^B` | `Start/BakerGillSolovay.lean` : `Complexity.bgs_different`; `Start/Relativization.lean` : `Complexity.peqnp_does_not_relativize` | none known to me | [N] |
| 23 | Shamir arithmetization of QBF; one-round sum-check soundness | `Start/QbfArith.lean` : `Complexity.Qbf.QBF.tqbf_iff_arith`, `Polynomial.card_eval_eq_le` | Lean `Verified-zkEVM/ArkLib` has a `ProofSystem/Sumcheck` directory | [V] directory listing only; contents not inspected |
| 24 | Krivine machine: β-steps are a polynomial time cost for weak head evaluation; one transition is a Cobham term | `Start/KrivineBound.lean` : `Krivine.eval_cost`; `Start/KrivineHeapCost.lean` : `Krivine.Impl.eval_impl_cost`; `Start/KrivineCobStep.lean` : `Krivine.Impl.eval_impl_cob_cost` | Coq: Forster–Kunze–Smolka–Wuttke, *time invariance thesis for weak call-by-value λ*, ITP 2021; Forster–Kunze–Roth, *the weak call-by-value λ-calculus is reasonable for both time and space*, POPL 2020. A HOL4 translation of the POPL 2020 development (`examples/lambda/wcbv-reasonable`) | [V] Coq READMEs; [V] HOL4 README |
| 25 | Krivine machine: space measured by live cells, garbage collection, `O(s log s)` bits on a work tape | `Start/KrivineSpaceRun.lean` : `Krivine.Impl.eval_impl_space`; `Start/KrivineSpaceConfig.lean` : `Krivine.Impl.spaceConfig_space_le_of_run_budget` | the same Coq and HOL4 developments (row 24); HOL4 `examples/lambda/cbpv-reasonable` (heap-machine space simulation) | [V] READMEs |
| 26 | Böhm's separation theorem for normal forms whose Böhm trees are not η-equal | `Start/BohmEta.lean` : `Lambda.separable_toTerm_of_not_tagEq` | HOL4 `examples/lambda/barendregt`: `separabilityScript.sml` ("Böhm's separation theorem (full version)", Chun Tian, 2026), and the effective Böhm trees and λη-completeness of Tian–Norrish, ITP 2025 | [V] HOL4 README and theorem names (`beta_separability_strong`) |
| 27 | Strong normalization: simply typed λ, System F (Girard candidates), Gödel's T, λΠ | `Start/SimpleTypes.lean` : `Lambda.sn_of_typing`; `Start/SystemF.lean` : `SystemF.sn_of_typing`; `Start/SystemTCanon.lean` : `GodelT.exists_reduces_num`; `Start/LambdaPiSN.lean` : `LambdaPi.Typing.sn` | Simply typed: cslib `Stlc/StrongNorm.lean` [V]. System F, System T and LF/λΠ have many formalizations in Coq, Agda and Isabelle [M]; I did not check any specific one | mixed, as stated |
| 28 | λΠ: decidable typing; βη is not Church–Rosser on annotated raw terms; initiality of the syntax | `Start/LambdaPiInfer.lean` : `LambdaPi.decidableTyping`; `Start/LambdaPiEta.lean` : `LambdaPi.not_church_rosser_betaEta`; `Start/LambdaPiInterpTotal.lean` : `LambdaPi.interp_exists_unique`; `Start/LambdaPiInitialModelHom.lean` : `LambdaPiInitial.biInitial_syntacticModel` | Lean4Lean (Carneiro): a Lean kernel in Lean, with metatheory of Lean's typing relation. Lean `sinhp/HoTTLean`: MLTT with Π, Σ, Id, natural-model semantics and its soundness. Agda initiality for a Martin-Löf type theory (Brunerie, de Boer, Lumsdaine, Mörtberg) [M]. Decidability of conversion for MLTT in Agda (Abel, Öhman, Vezzosi) [M] | [V] READMEs of Lean4Lean and HoTTLean; others [M] |
| 29 | Biequivalence between LCCCs and their strictified models (categories with attributes) | `Start/LcccBiequivalence.lean` : `Cwa.lcccModelCat_biequivalent` | UniMath (Rocq): `Bicategories/ComprehensionCat/Biequivalence/` (finite-limit categories ⇔ DFL comprehension categories, extended to Π and LCCCs, after Clairambault–Dybjer) | [V] UniMath file headers |
| 30 | Realizability: PCAs, `K₁`, assemblies (regular), PER ≃ modest sets, an ex/reg-style completion | `Start/PCA.lean` : `Realizability.PCA`; `Start/AssemblyRegular.lean` : `Realizability.Assembly.strongEpi_of_isPullback`; `Start/ModestEquiv.lean` : `Realizability.perEquivModest`; `Start/AsmExRegRegular.lean` : `Realizability.ExReg.instRegular` | Cubical Agda `rahulc29/realizability`: assemblies (finite limits, cartesian closed), modest sets, the realizability tripos, and "the construction of the realizability topos" | [V] README |
| 31 | `K₂ → K₁`: no applicative morphism separates bits | `Start/KleeneNoRetraction.lean` : `Realizability.KleeneTwo.no_separatesBits_morphism` | none known to me | [N] |
| 32 | Scott's `D∞ ≅ [D∞ → D∞]`, consistency of λη by semantics, adequacy; the graph model is not fully abstract | `Start/ScottDinfIso.lean` : `ScottDinf.dinfOrderIso`; `Start/ScottDinfOmega.lean` : `ScottDinf.convBE_consistent`; `Start/DinfAdequacy.lean` : `ScottDinf.hasHnf_of_ddenot_ne_botDinf`; `Start/GraphNotFullyAbstract.lean` : `GraphNotFullyAbstract.graph_not_fully_abstract` | Inverse-limit solutions of domain equations exist in Isabelle/HOLCF and in Coq (Benton–Kennedy–Varming) [M]. A `D∞` λ-model with adequacy, and graph-model full abstraction: none known to me | [M] / [N] |
| 33 | Binary λ-calculus: `Lambda ≃ {bs // isBLC bs}` | `Start/BLC.lean` : `Lambda.bitsEquiv` | `a9lim/blam`: experiments in binary λ-calculus, with "Lean-checked divergence certificates" in its description | description only |
| 34 | de Bruijn ⇔ cslib locally nameless, with confluence transported both ways | `Start/Representation.lean` : `Lambda.closedEquiv`, `Lambda.confluence_of_cslib`, `Lambda.cslib_confluence_of_lambda` | HOL4 `examples/lambda/other-models` has de Bruijn, locally nameless and transfer theories (`dBScript.sml`, `lnamelessScript.sml`, `pdbTransferScript.sml`) | [V] directory listing; contents not inspected |

### How each "none known to me" was checked, and how confident I am

Every [N] entry above was checked in the same way:

1. A text search of Mathlib `v4.33.0` and of the pinned cslib for the theorem's name and
   its key terms. Neither covers any of the [N] rows. This part is **verified**: high
   confidence for Mathlib and cslib themselves.
2. Reading the READMEs and file listings named in this note: the Coq Library of
   Undecidability Proofs, *Synthetic Computability*, the Coq Library of Complexity Theory,
   the HOL4 `examples/computability` and `examples/lambda` trees, the AFP topic page
   *Logic/Computability*, and the READMEs of the Lean projects named here.
3. GitHub repository-name searches for a few topics, restricted to Lean where the search
   allowed it: Cook–Levin, Savitch, Kolmogorov complexity, realizability. The search API's
   rate limit ended this before every row had been searched.

So an [N] means the theorem is absent from Mathlib and cslib (verified), and that I found
it in none of the other sources above. It does not rule out a formalization in a paper
artifact, a thesis, or a repository whose README does not mention the theorem.

My confidence that the following rows have **no** formalization anywhere is only
**low to moderate**:

- **Low:** row 7 (Rice–Shapiro, Myhill–Shepherdson) and row 9 (limit lemma). The
  synthetic-computability group has worked near these results, and I did not open their
  proof files.
- **Moderate:** row 17 (Blum, gap theorem, Levin search), row 20 (P ⊆ PSPACE on a
  concrete machine), row 21 (TQBF hardness), row 22 (Baker–Gill–Solovay), row 31
  (`K₂ → K₁`), and the graph-model part of row 32. I know of none and found none, but my
  searches of Coq, Isabelle and Agda archives were not exhaustive.
- Row 12 (Ω) and row 15 (description systems): **low**. Several Lean repositories on
  Kolmogorov complexity exist, and I read only their one-line descriptions.

## 2. Comparison with the neighbours

### Mathlib's `Computability` (Lean)

**Source.** Mathlib `v4.33.0` source tree [V]. Author lines: Mario Carneiro for `Partrec`,
`PartrecCode`, `Halting`, `RE`, `TuringMachine/ToPartrec`; Duve and Roth for `RecursiveIn` and
`TuringDegree`; Spelier and van Gent for `TuringMachine/Computable`.

**Covered by Mathlib and not by this library.**
- Primitive recursion and `Primrec` closure in general.
- The Ackermann function is not primitive recursive (`not_primrec_ack_self`).
- TM0/TM1/TM2 and Post–Turing machine models, with simulations between them.
- Automata: DFA, NFA, ε-NFA, regular expressions, context-free grammars, Myhill–Nerode.
- Kraft–McMillan for uniquely decodable codes.
- Akra–Bazzi.
- The category theory of locally cartesian closed categories that `Start/Lccc.lean` builds
  on.

**Covered by this library and not by Mathlib.**
- The untyped λ-calculus and all of its theory.
- Turing-machine computable ⇒ partial recursive (`Start/TM2Partrec.lean`,
  `Start/TM2Capstone.lean`). Mathlib proves only the other direction (`tr_eval`).
- Everything from recursion theory onwards in the table, except what Mathlib has for codes:
  Rice, s-m-n, the fixed-point theorem, undecidability of halting, and the basic theory of
  many-one and one-one reducibility.
- P, NP, PSPACE, AIT and realizability.

**Relation.** The library is built on Mathlib. Its equivalences are stated against
Mathlib's `Partrec`, `Computable`, `REPred`, `ComputablePred`, `TuringReducible` and
`Turing.FinTM2`. Examples: `lambdaComputable_iff_partrec` (`Start/PartialCapstone.lean`)
and `Lambda.Oracle.not_countable_turingDegree` (`Start/OracleCone.lean`).

### Lean4Lean (Carneiro)

**Source.** README of `digama0/lean4lean` [V]: "an implementation of the Lean 4 kernel
written in (mostly) pure Lean 4", plus "some metatheory regarding the Lean system". It has
a typing relation (`Theory/Typing/Basic.lean`), lemmas about it, conjectures about unique
typing (`UniqueTyping.lean`), and a proof that the implementation meets the abstract
specification (`Verify`).

**Covered by Lean4Lean and not by this library.** A real kernel: inductive types,
quotients, universe levels, and a verified relationship between implementation and
specification for a production type theory.

**Covered by this library and not by Lean4Lean.** None of the computability or complexity
content. For a much smaller dependent type theory (λΠ), this library proves:
- uniqueness of types up to conversion (`LambdaPi.Typing.unique`,
  `Start/LambdaPiUnique.lean`). The Lean4Lean README lists unique typing among its
  conjectures for Lean's theory;
- strong normalization (`LambdaPi.Typing.sn`, `Start/LambdaPiSN.lean`);
- decidable type checking (`LambdaPi.decidableTyping`, `Start/LambdaPiInfer.lean`).

The comparison is lopsided: λΠ has no universes beyond `∗ : □` and no inductive types.

**Overlap.** Small. Lean4Lean is the nearest Lean project for the type-theory half of
this library (rows 27–29), not for computability.

### Forster's Coq Library of Undecidability Proofs and synthetic computability (Coq)

**Sources** [V]:
- README of `uds-psl/coq-library-undecidability`;
- README of `uds-psl/coq-synthetic-computability`;
- README of `uds-psl/coq-library-complexity`;
- READMEs of `coq-kolmogorov-complexity` and `coq-posts-theorem`.

**Covered by them and not by this library.**
- A large web of many-one reductions: PCP, Hilbert's tenth problem, Minsky and counter
  machines, FRACTRAN, semi-unification, first-order logic (the Entscheidungsproblem,
  Trakhtenbrot's theorem), linear logic, System F typability and inhabitation.
- Multi-tape Turing machines with a verified programming framework.
- The weak call-by-value λ-calculus L with time **and** space invariance against Turing
  machines (POPL 2020, ITP 2021).
- The Time Hierarchy Theorem (complexity library).
- Synthetic computability based on axioms of Church's thesis.
- Truth-table reducibility and hypersimple sets.
- A solution of Post's problem.
- Post's theorem for the whole arithmetical hierarchy.
- Essential incompleteness of Robinson arithmetic (`coq-synthetic-incompleteness`).

This library has none of these:
- no reduction web;
- no hierarchy theorems (task `M15-TIME-HIERARCHY-REL` is open);
- no Friedberg–Muchnik: `Start/Priority.lean` proves only the finite injury lemma for an
  abstract construction, `Lambda.Priority.Injury.acts_finite`;
- Post's theorem only at level 2 (`Start/PostTheoremTwo.lean`).

**Covered by this library and not by them**, to the extent their READMEs show [V]; I did
not search their proof files:
- the full untyped β-calculus with confluence, standardization, Böhm separation and
  denotational models;
- AIT up to Ω and Levin–Schnorr;
- Kraft's inequality;
- P ⊆ PSPACE, TQBF hardness, Savitch in a memory model, and the Baker–Gill–Solovay
  separation;
- typed calculi with strong normalization;
- categorical semantics: CwAs, the LCCC biequivalence, realizability categories.

**Different foundations.** Their computability is *synthetic* (in constructive type
theory, with Church's thesis as an axiom or as a model property). This library's is
*analytic*: classical Lean, with explicit codes and Mathlib's `Partrec`. Their primary
concrete model is weak call-by-value λ (L). This library's is the full untyped
β-calculus on de Bruijn terms.

### Paulson's Gödel incompleteness (Isabelle)

**Source.** AFP entry *Gödel's Incompleteness Theorems* [V]. Both incompleteness theorems
are formalized in the theory of hereditarily finite sets, following Świerczkowski, with
Löb's theorem added by Bailitis (2024). Sessions include `Coding`, `Sigma`, `Goedel_I`,
`Goedel_II`, `Loebs_Theorem`.

**Covered there and not here.** A formal first-order theory, its proof calculus, coding of
syntax inside it, the derivability conditions, Gödel I and II, and Löb's theorem. This
library has none of these (§5). Its only incompleteness result is Chaitin's, for an
abstract sound r.e. set of assertions:
- `Lambda.chaitin_incompleteness` (`Start/ChaitinIncompleteness.lean`);
- `Lambda.exists_true_unprovable_kolm_lower_bound` (`Start/ChaitinIncompleteness.lean`).

**Covered here and not there.** The session list contains no machine model,
partial recursive functions or complexity, so essentially all of this library. That
inference rests on session names only. [V] for the session list, [M] for the inference.

### Norrish's HOL4 computability and λ-calculus (HOL4)

**Sources** [V]:
- directory listings of `HOL-Theorem-Prover/HOL`, `examples/computability/*` and
  `examples/lambda/*`;
- the README of `examples/lambda/barendregt`;
- theorem names in `recsets`, `recfuns`, `HaltingProblems`, `recdegrees` and the `kolmog`
  scripts.

Norrish's paper *Mechanised computability theory* (ITP 2011) is what I remember as the
reference for the λ-based part [M].

**Covered there and not here.**
- The full Böhm separation theorem (Tian, 2026, unpublished, per the README).
- Böhm trees, and Hilbert–Post completeness of λη (Tian–Norrish, ITP 2025).
- Finite developments, after Barendregt's chapter 11.
- Register machines.
- A HOL4 translation of the Forster–Kunze–Roth time-and-space result.
- A verified cost model for call-by-push-value (`cbpv-reasonable`).

**Covered here and not there**, judged from file names only [V for the listing]:
- complexity classes (P, NP, PSPACE), Cook–Levin, Savitch, relativization;
- Martin-Löf randomness, Levin–Schnorr, Ω;
- Myhill's theorem, the limit lemma, properness of the arithmetical hierarchy;
- typed calculi beyond the simply typed (`examples/lambda/typing` has `stt` and type
  schemas);
- categorical semantics and realizability.

**Overlap.** This is the neighbour closest in spirit to this library: computability done
with λ-terms as the model, Kolmogorov complexity (plain and prefix-free, Kraft, invariance,
incomputability), the busy beaver, Rice's theorem, and the start of the arithmetical
hierarchy (`rec_sigma`, `rec_pi`, `rec_delta`).

### Xu–Zhang–Urban's Turing machines (Isabelle)

**Source.** AFP entry *Universal Turing Machine* [V]. Authors: Xu, Zhang, Urban, Joosten,
Regensburger. It covers recursive functions, undecidability of the halting problem and the
existence of a universal Turing machine, following Boolos–Burgess–Jeffrey, and corresponds
to the ITP 2013 paper. Regensburger's 2022 additions define Turing decidability,
computability and reducibility.

**Covered there and not here.** An explicit universal Turing machine, abacus machines, and
the compilation chain from recursive functions through abacus machines to Turing machines,
all built inside the development. This library has no universal machine of its own and no
register or abacus machines. It obtains Partrec ⇒ TM2 by bundling Mathlib's compiler
(`TM2Partrec.trFinTM2`, `Start/TM2Forward.lean`). That the AFP entry also proves
TM ⇒ recursive functions is my recollection of the paper [M].

**Covered here and not there.** The λ-calculus, and everything beyond the halting problem.

### cslib (Lean), a dependency of this library

**Source.** A checkout of the pinned revision `3951377…` [V].

**Covered by cslib and not by this library.**
- Automata and ω-automata (Büchi; NA/DA constructions), ω-regular languages,
  Myhill–Nerode.
- The FLP impossibility theorem.
- CCS, labelled transition systems and bisimulation.
- Linear logic with cut elimination; modal logic and HML.
- URM computability (`Computability/URM`).
- SKI combinatory logic with general recursion (`Languages/CombinatoryLogic/Recursion.lean`).
- Single- and multi-tape Turing machines with time *and* space measures
  (`Machines/Turing/MultiTape/Deterministic.lean`, `DecidableInTimeAndSpace`).
- System F<: and STLC safety.
- Locally nameless λ-calculus with standardization and η.
- A time-cost monad (`Algorithms/Lean/TimeM.lean`); cryptography and PAC learning.

**Covered by this library and not by cslib.** Equivalence with partial recursive
functions (cslib's SKI recursion builds the combinators but, by text search, states no
`Partrec` theorem), and everything from recursion theory upwards.

**Relation.** This library uses cslib only through `Start/Representation.lean` and
`Start/KolmogorovRepresentation.lean`:
- the closed de Bruijn terms correspond to the closed locally nameless terms
  (`Lambda.closedEquiv`);
- β-reduction is carried both ways, so each library's confluence theorem implies the
  other's (`Lambda.confluence_of_cslib`, `Lambda.cslib_confluence_of_lambda`);
- Kolmogorov complexity does not change with the representation: `Lambda.kolmLN_eq_kolm`
  (`Start/KolmogorovRepresentation.lean`) proves `kolmLN s = kolm s`.

**Note for future work.** cslib's multi-tape machine with space measured by cells visited
is a natural target for the space results of §4, which currently use this library's own
offline machine (`Start/SpaceMachine.lean`).

### Other neighbours that the checking turned up

- **`cameronfreer/algorithmic-randomness` (Lean)** [V README]: ML, computable, Schnorr and
  Kurtz randomness and the implications between them, Levin–Schnorr, prefix-free machines
  as codes, Kraft–Chaitin. It goes beyond this library on randomness notions. This library
  defines its complexities through λ-terms and has Ω. Neither side formalizes a bridge to
  the other's definitions.
- **`sinhp/HoTTLean` (Lean)** [V README]: MLTT syntax with Π, Σ and Id, natural-model
  semantics with a soundness proof, and a `sorry`-free groupoid model. That is exactly
  what tasks `M23-ID-TYPES` and `M23-GROUPOID-MODEL` would add here.
- **UniMath (Rocq)** [V file headers]: the Clairambault–Dybjer biequivalence for
  comprehension categories, extended to Π, LCCCs and further local properties.
- **`rahulc29/realizability` (Cubical Agda)** [V README]: realizability up to the
  realizability topos.
- **Isabelle AFP *Logic/Computability* topic** [V listing]: also lists Cook–Levin
  (Balbach), a verified translation from multitape to single-tape TMs (Dalvit–Thiemann),
  DPRM, Minsky machines, *Recursion Theory I* (Nedzelsky), inductive inference (Balbach),
  and the Busy Beaver function.

## 3. What is unusual here, after checking

The brief proposed five candidates. Each was checked against the library source and the
neighbours above.

**Dropped: "the λ-calculus is the primary model, with Turing machines derived rather than
the reverse."**
- The first half holds for this library. Kolmogorov complexity, Ω, the busy beaver and
  the recursion theorems are defined on λ-terms. Examples: `Lambda.kolmSystem`
  (`Start/KolmogorovMachines.lean`), `Lambda.chaitinOmega_mem_Ioo`
  (`Start/ChaitinOmega.lean`).
- It is not unusual. Norrish's HOL4 computability takes λ-terms as the model [V
  listing], and Forster's Coq libraries take weak call-by-value λ as theirs [V READMEs].
- The second half is false. The Turing machines are not derived from λ: the λ ⇔ TM2
  equivalence goes through Mathlib's `Partrec`, using Mathlib's own compiler for
  Partrec ⇒ TM2 (`TM2Partrec.trFinTM2`, `Start/TM2Forward.lean`) and this library's
  arithmetization for TM2 ⇒ Partrec (`TM2Partrec.tm2Computable_iff_partrec`,
  `Start/TM2Capstone.lean`).

**Dropped: "time *and* space invariance for the Krivine machine end to end."**
- Time is one direction only: λ evaluation is simulated with polynomial overhead
  (`Krivine.eval_cost`, `Krivine.Impl.eval_impl_cost`, `Krivine.Impl.eval_impl_cob_cost`).
  The cost is counted in passes over an encoded state, with one transition shown to be a
  Cobham term (`Krivine.Impl.stepT`, `Start/KrivineCobStep.lean`), not against a Turing
  machine.
- I found no converse simulation of machines by λ-terms with polynomial overhead
  (searched `Start/` and the task board).
- Space stops at a memory measure. `Krivine.Impl.spaceConfig_space_le_of_run_budget`
  (`Start/KrivineSpaceConfig.lean`) bounds the bits of a work tape. A `DSPACE` membership
  is the open task `M14-KRIVINE-SPACE-CLASS`, and the converse direction is
  `M14-SPACE-REASONABLE` (status `TODO_NEEDS_DESIGN`).
- By contrast, Forster–Kunze–Roth (POPL 2020) and Forster–Kunze–Smolka–Wuttke (ITP 2021)
  mechanise both directions for time, and time and space, for weak call-by-value λ against
  Turing machines [V READMEs]. A HOL4 translation exists [V].

**Dropped: "the realizability stack from PCA to the exact completion."**
- The library does build PCAs (`Realizability.PCA`), Kleene's `K₁`
  (`Realizability.Kleene.instPCANat`, `Start/PCAKleene.lean`), regular assemblies, PER ≃
  modest sets (`Realizability.perEquivModest`) and a completion `ExReg(A)` that is regular
  (`Realizability.ExReg.instRegular`).
- That completion is **proved not exact**
  (`Realizability.ExReg.NotExact.kleene_exReg_not_exact`, `Start/AsmExRegNotExact.lean`).
  Exactness is shown only on partitioned bases
  (`Realizability.ExReg.ExRegP.exists_effective_quotient`, `Start/AsmExRegEffective.lean`).
  The effective topos is not reached.
- Cubical Agda already constructs the realizability topos [V README].

**Dropped: "the 2-categorical treatment of λΠ models."**
- `Cwa.lcccModelCat_biequivalent` (`Start/LcccBiequivalence.lean`) is a biequivalence
  between LCCCs and a 2-category `Cwa.LcccModelCat` that is *defined* as the full
  sub-2-category spanned by strictifications. Its essential surjectivity therefore holds
  by construction, and the content is the local equivalence.
- UniMath has the Clairambault–Dybjer biequivalence for comprehension categories, with Π
  and LCCCs [V].
- Within Lean I know of no such biequivalence [N; Mathlib `v4.33.0` searched, other Lean
  projects not searched]. That is too narrow to call unusual.

**Kept, with a qualification: many complexity measures as instances of one description
system.** `Complexity.DescSystem` (`Start/DescriptionSystem.lean`) is a size on programs
plus an output relation, with complexity `Complexity.DescSystem.K` and a generic
invariance estimate `Complexity.DescSystem.K_le_add_cost`. The brief said six measures.
The source has **eight** systems:

| Measure | System |
| --- | --- |
| plain | `Lambda.kolmSystem` |
| conditional | `Lambda.kolmCondSystem` |
| interpreter-relative | `Lambda.kolmWithSystem` |
| prefix | `Lambda.kolmPSystem` |
| Kraft–Chaitin universal machine | `KC.kuSystem` |
| locally nameless | `Lambda.kolmLNSystem` |
| Levin `Kt` | `Lambda.ktSystem` |
| time-bounded `K^T` | `Lambda.ktimeSystem` |

There are also the interpreter-relative variants `ktWithSystem` and `ktimeWithSystem`. For
seven of the eight, the measure is the system's `K` by definition (`Lambda.kolm_eq_kolmSystem_K`
and others proved by `rfl`, or a `def … := ….K`). `KC.KU` is proved equal to it
(`KC.KU_eq_kuSystem_K`). The abstraction itself is small, an infimum over descriptions. What
may be unusual is the range it is instantiated on: plain, prefix, conditional, time-bounded,
Levin and representation-changed complexity, all for one language of programs (λ-terms)
and compared through translations. I know of no other development that does this, but my
confidence is low (§1).

**Kept: a library that is wide rather than deep, on one core.** One de Bruijn λ-calculus,
connected to Mathlib's `Partrec`, carries all of the following in a single development:
- recursion theory up to Myhill's theorem, the limit lemma and properness of the
  arithmetical hierarchy;
- AIT up to Ω and Levin–Schnorr;
- complexity up to Cook–Levin, P ⊆ PSPACE, TQBF hardness and a relativization barrier;
- typed calculi up to λΠ with initiality;
- denotational models (graph model, `D∞`);
- realizability categories.

Many rows of §1 have a comparable or deeper formalization somewhere; the rows marked [N]
have none that I found. What I did not find is one development that covers all of these
together. This is a statement about breadth, checked only against the neighbours listed
here, not a claim of priority.

**Kept: refuted statements are recorded as theorems.** Where a natural statement turned out
false, the library proves its negation and keeps the corrected statement next to it:
- `Lambda.not_evalCorrectness` (§0);
- `LambdaPi.not_church_rosser_betaEta`, with confluence restored modulo annotations by
  `LambdaPi.erased_betaEta_church_rosser`;
- `Realizability.ExReg.NotExact.kleene_exReg_not_exact`;
- `CwaType.not_equivalent_ofPullbacks` (`Start/CwaFamiliesNoStrictify.lean`);
- `GraphNotFullyAbstract.graph_not_fully_abstract`;
- for `K₂ → K₁`, the counterexample `Realizability.AppMorphism.trivialMor`
  (`Start/KleeneNoRetraction.lean`) shows that the unqualified "no morphism `K₂ → K₁`" is
  false, so the theorem `Realizability.KleeneTwo.no_separatesBits_morphism` carries the
  hypothesis that makes it true.

This is a property of how the library is written. I make no claim about how common it is.

## 4. Caveats on the complexity results

Readers comparing rows 18–22 with machine-based developments should know these points:

- **P and NP are defined through Cobham's function algebra, not through machines.**
  `Complexity.InP` and `Complexity.InNP` in `Start/ComplexityClasses.lean` quantify over
  Cobham terms (`Cob`). I found no theorem in `Start/` identifying Cobham's class with
  polynomial-time Turing machines.
- **Space is defined on an offline Turing machine** (`Start/SpaceMachine.lean`:
  `Complexity.Space.DSPACE`, `Complexity.Space.PSPACE`). The bridge between the two models
  is the compiler of `Start/CobhamSpace.lean`, which gives `Complexity.Space.pspace_of_inP`.
- **Savitch's theorem is proved for the memory of a stack machine, not as `NPSPACE ⊆
  PSPACE` on the offline machine.** `Complexity.Space.savitch_poly_memory` bounds
  `memBits` of a `Trace`. The library proves only `PSPACE ⊆ NPSPACE`
  (`Complexity.Space.npspace_of_pspace`).
- **TQBF is PSPACE-hard but not proved PSPACE-complete.** Membership is the open task
  `M14-TQBF-IN-PSPACE`. Only a memory bound for the evaluator is proved
  (`Complexity.Qbf.tqbf_memBits_le_length_enc`, `Start/QbfCodeSpace.lean`).
- **Baker–Gill–Solovay: only the separating oracle.** The collapsing oracle is the open
  task `M15-BGS-EQUAL`.

## 5. What the library is not

These are absences, each checked by a text search of `Start/` and against the open rows of
`docs/goal/task-board.yaml`:

- **No formal theory of arithmetic.** There is no first-order language, proof calculus,
  Robinson's Q or PA, and no Gödel I/II or Löb. The only incompleteness theorem is
  Chaitin's, for an abstract sound r.e. system (`Lambda.chaitin_incompleteness`). Supplied
  by `M24-ARITH-THEORY`, then `M24-ABSTRACT-LOB` and `M24-GODEL2-ARITH` (and `M24-GL`).
- **No ordinals.** A search of `Start/` for "ordinal" finds nothing. Anything beyond the
  arithmetical hierarchy (Kleene's O, hyperarithmetical sets) is `M24-HYPERARITH`, status
  `TODO_NEEDS_DESIGN`. Reverse mathematics is planned on ω-models precisely to avoid
  ordinals (`M24-OMEGA-MODELS`).
- **No identity types.** λΠ has Π only. The matches for "identity type" in `Start/` refer
  to System F's polymorphic identity `∀α. α → α`. Supplied by `M23-ID-TYPES`, then
  `M23-GROUPOID-MODEL` and `M23-UIP-INDEPENDENT`.
- **No probability beyond one measure.** The only measure is the fair-coin measure on
  Cantor space (`Lambda.cantorMeasure`, `Start/MartinLof.lean`), used for Martin-Löf tests
  and Ω. There are no randomized machines, no BPP and no interactive proofs. `M21-IP-DEF`
  plans acceptance probability "by counting … (a finite average; no measure theory)",
  followed by the other `M21-*` rows up to `M21-IP-EQ-PSPACE`.
- **No nondeterministic tape programs.** The structured tape programs
  `Complexity.Space.Prog` (`Start/SpaceProg.lean`) are deterministic. Nondeterministic
  space exists only as the class `Complexity.Space.NPSPACE` on raw machines. Supplied by
  `M22-NONDET-PROG`, a prerequisite of `M22-IMMERMAN-SZELEPCSENYI`.

Other absences a reader may look for: hierarchy theorems (`M15-TIME-HIERARCHY-REL`), coNP
and the polynomial hierarchy (`M22-CONP-PH`), an explicit universal Turing machine (no
task), and the reduction web of the Coq library (no task).

## 6. Claims in this note that I could not verify

- Norrish's ITP 2011 paper *Mechanised computability theory* as the reference for the HOL4
  λ-based computability development; only the directory and file contents were checked.
- That Paulson's AFP entry contains no general computability theory (inferred from its
  session names).
- That the Xu–Zhang–Urban entry proves TM ⇒ recursive functions as well as the converse.
- Formalizations of strong normalization for System F, System T and LF/λΠ in Coq, Agda
  and Isabelle (row 27); none was checked.
- The Agda initiality formalization (Brunerie, de Boer, Lumsdaine, Mörtberg) and the Agda
  decidability of conversion (Abel, Öhman, Vezzosi) (row 28).
- Inverse-limit domain constructions in Isabelle/HOLCF and in Coq (Benton–Kennedy–Varming)
  (row 32).
- The contents behind every README, abstract or directory listing marked [V]. Only the
  quoted text or listing was checked, not the proof files. In particular: the Lean
  repositories found by search (Cook–Levin, Savitch, Kolmogorov, `Kt`, descriptive
  complexity, `blam`) are cited by their one-line descriptions only; ArkLib's sum-check
  directory was not opened; HOL4 `other-models` and `busyBeaverScript.sml` were not
  opened.
- Every [N] entry in §1. Absence was checked only within the sources and searches listed
  there; the GitHub search was cut short by the API rate limit.
- That the library compiles at commit `bbaa6ec`. I checked declarations against the source
  text and searched for `sorry`/`admit`/`axiom`, but did not rebuild the library for this
  note.
