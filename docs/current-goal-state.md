# Current goal state

- Active milestone: `M9`

| Rank | ID | Priority | Status | Depends on | Evidence | Open Boundary |
|---:|---|---|---|---|---|---|
| 10 | `M1-BOUNDARY-SORRY-CLOSURE` | `P0` | `DONE_STRONG` | - | docs/goal/evidence/M1-BOUNDARY-SORRY-CLOSURE.md |  |
| 20 | `M1-ENCODING-EXTRACTION-CLOSURE` | `P0` | `DONE_STRONG` | - | docs/goal/evidence/M1-ENCODING-EXTRACTION-CLOSURE.md |  |
| 30 | `M1-COMPUTABILITY-CLOSURE` | `P0` | `DONE_STRONG` | M1-ENCODING-EXTRACTION-CLOSURE | docs/goal/evidence/M1-COMPUTABILITY-CLOSURE.md |  |
| 40 | `M1-MODULAR-ENTRYPOINT-SWITCH` | `P1` | `DONE_STRONG` | M1-BOUNDARY-SORRY-CLOSURE, M1-COMPUTABILITY-CLOSURE | docs/goal/evidence/M1-MODULAR-ENTRYPOINT-SWITCH.md |  |
| 50 | `M1-BASIC-COMPAT-SHIM` | `P1` | `DONE_STRONG` | M1-MODULAR-ENTRYPOINT-SWITCH | docs/goal/evidence/M1-BASIC-COMPAT-SHIM.md |  |
| 60 | `M1-LINTER-HARDENING` | `P2` | `DONE_STRONG` | M1-MODULAR-ENTRYPOINT-SWITCH | docs/goal/evidence/M1-LINTER-HARDENING.md |  |
| 10 | `M2-EVAL-CORRECTNESS-DISCHARGE` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M2-EVAL-CORRECTNESS-DISCHARGE.md |  |
| 20 | `M2-STYLE-RESIDUE` | `P2` | `DONE_STRONG` | - | docs/goal/evidence/M2-STYLE-RESIDUE.md |  |
| 30 | `M2-AESOP-NONTERMINAL` | `P2` | `DONE_STRONG` | - | docs/goal/evidence/M2-AESOP-NONTERMINAL.md |  |
| 40 | `M2-EVAL-NORMALIZATION-HOLDS` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M2-EVAL-NORMALIZATION-HOLDS.md |  |
| 10 | `M3-STANDARDIZATION` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M3-STANDARDIZATION.md |  |
| 20 | `M3-LAMBDA-PREC-COMPILER` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M3-LAMBDA-PREC-COMPILER.md |  |
| 21 | `M3-LAMBDA-MU-CORRECTNESS` | `P1` | `DONE_STRONG` | M3-LAMBDA-PREC-COMPILER | docs/goal/evidence/M3-LAMBDA-MU-CORRECTNESS.md |  |
| 22 | `M3-PARTREC-IMP-LAMBDACOMPUTABLE` | `P1` | `DONE_STRONG` | M3-LAMBDA-PREC-COMPILER, M3-LAMBDA-MU-CORRECTNESS | docs/goal/evidence/M3-PARTREC-IMP-LAMBDACOMPUTABLE.md |  |
| 30 | `M4-CHURCH-TURING-LAMBDA` | `P2` | `DONE_STRONG` | M2-EVAL-NORMALIZATION-HOLDS, M3-PARTREC-IMP-LAMBDACOMPUTABLE | docs/goal/evidence/M4-CHURCH-TURING-LAMBDA.md |  |
| 40 | `M4-TM2-IMP-PARTREC` | `P3` | `DONE_STRONG` | - | docs/goal/evidence/M4-TM2-IMP-PARTREC.md |  |
| 50 | `M4-SCOTT-RICE` | `P3` | `DONE_STRONG` | M4-CHURCH-TURING-LAMBDA | docs/goal/evidence/M4-SCOTT-RICE.md |  |
| 60 | `M4-SMN-UNIFORM` | `P3` | `DONE_STRONG` | - | docs/goal/evidence/M4-SMN-UNIFORM.md |  |
| 70 | `M4-SELF-INTERPRETER` | `P3` | `DONE_STRONG` | M4-CHURCH-TURING-LAMBDA | docs/goal/evidence/M4-SELF-INTERPRETER.md |  |
| 10 | `M5-RECURSION-PARAMS` | `P3` | `DONE_STRONG` | M4-SMN-UNIFORM | docs/goal/evidence/M5-RECURSION-PARAMS.md |  |
| 20 | `M5-ENCODINGS-MULTIARG` | `P3` | `DONE_STRONG` | M4-CHURCH-TURING-LAMBDA | docs/goal/evidence/M5-ENCODINGS-MULTIARG.md |  |
| 30 | `M5-SOLVABILITY` | `P3` | `DONE_STRONG` | M4-SCOTT-RICE | docs/goal/evidence/M5-SOLVABILITY.md |  |
| 40 | `M5-ALGORITHM-REPRESENTATION` | `P3` | `DONE_STRONG` | M4-CHURCH-TURING-LAMBDA | docs/goal/evidence/M5-ALGORITHM-REPRESENTATION.md |  |
| 50 | `M5-POLYTIME` | `P3` | `DONE_STRONG` | M4-TM2-IMP-PARTREC | docs/goal/evidence/M5-POLYTIME.md |  |
| 10 | `M6-KOLMOGOROV-CORE` | `P3` | `DONE_STRONG` | M4-CHURCH-TURING-LAMBDA | docs/goal/evidence/M6-KOLMOGOROV-CORE.md |  |
| 20 | `M6-KOLMOGOROV-BERRY` | `P3` | `DONE_STRONG` | M6-KOLMOGOROV-CORE | docs/goal/evidence/M6-KOLMOGOROV-BERRY.md |  |
| 30 | `M6-KOLMOGOROV-INVARIANCE` | `P3` | `DONE_STRONG` | M6-KOLMOGOROV-CORE, M4-TM2-IMP-PARTREC | docs/goal/evidence/M6-KOLMOGOROV-INVARIANCE.md |  |
| 40 | `M6-KOLMOGOROV-OMEGA` | `P3` | `DONE_STRONG` | M6-KOLMOGOROV-INVARIANCE | docs/goal/evidence/M6-KOLMOGOROV-OMEGA.md |  |
| 5 | `M7-VERIFICATION-DEBT` | `P0` | `DONE_STRONG` | - | docs/goal/evidence/M7-VERIFICATION-DEBT.md |  |
| 7 | `M7-LICENSE` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M7-LICENSE.md |  |
| 8 | `M7-LEGACY-MODULE-BACKFILL` | `P2` | `DONE_STRONG` | - | docs/goal/evidence/M7-LEGACY-MODULE-BACKFILL.md |  |
| 10 | `M7-CODE-FOLD-ARITH` | `P2` | `DONE_STRONG` | M6-KOLMOGOROV-CORE | docs/goal/evidence/M7-CODE-FOLD-ARITH.md |  |
| 20 | `M7-LEFTMOST-CLOCK` | `P2` | `DONE_STRONG` | M7-CODE-FOLD-ARITH | docs/goal/evidence/M7-LEFTMOST-CLOCK.md |  |
| 30 | `M7-BUSY-BEAVER` | `P2` | `DONE_STRONG` | M7-LEFTMOST-CLOCK | docs/goal/evidence/M7-BUSY-BEAVER.md |  |
| 40 | `M7-KOLM-HALTING-BRIDGE` | `P2` | `DONE_STRONG` | M7-LEFTMOST-CLOCK, M6-KOLMOGOROV-BERRY | docs/goal/evidence/M7-KOLM-HALTING-BRIDGE.md |  |
| 50 | `M7-PLAIN-VS-PREFIX` | `P2` | `DONE_STRONG` | M6-KOLMOGOROV-OMEGA | docs/goal/evidence/M7-PLAIN-VS-PREFIX.md |  |
| 60 | `M7-OMEGA-UNCOMPUTABLE` | `P1` | `DONE_STRONG` | M6-KOLMOGOROV-OMEGA, M7-LEFTMOST-CLOCK | docs/goal/evidence/M7-OMEGA-UNCOMPUTABLE.md |  |
| 70 | `M7-OMEGA-ORACLE` | `P1` | `DONE_STRONG` | M7-OMEGA-UNCOMPUTABLE | docs/goal/evidence/M7-OMEGA-ORACLE.md |  |
| 75 | `M7-OMEGA-INCOMPRESSIBLE` | `P1` | `DONE_STRONG` | M7-OMEGA-ORACLE, M7-PLAIN-VS-PREFIX | docs/goal/evidence/M7-OMEGA-INCOMPRESSIBLE.md |  |
| 78 | `M7-ML-RANDOMNESS-FRAMEWORK` | `P1` | `DONE_STRONG` | M7-OMEGA-INCOMPRESSIBLE | docs/goal/evidence/M7-ML-RANDOMNESS-FRAMEWORK.md |  |
| 80 | `M7-OMEGA-ML-RANDOM` | `P1` | `DONE_STRONG` | M7-ML-RANDOMNESS-FRAMEWORK | docs/goal/evidence/M7-OMEGA-ML-RANDOM.md |  |
| 90 | `M7-BOHM-SEPARATION` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M7-BOHM-SEPARATION.md |  |
| 82 | `M7-HALTING-SIGMA1-COMPLETE` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M7-HALTING-SIGMA1-COMPLETE.md |  |
| 84 | `M7-BLC-BRIDGE` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M7-BLC-BRIDGE.md |  |
| 86 | `M7-STLC-SN` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M7-STLC-SN.md |  |
| 88 | `M7-SYSTEM-T` | `P1` | `DONE_STRONG` | M7-STLC-SN | docs/goal/evidence/M7-SYSTEM-T.md |  |
| 83 | `M7-KLEENE-K-BRIDGE` | `P1` | `DONE_STRONG` | M7-HALTING-SIGMA1-COMPLETE | docs/goal/evidence/M7-KLEENE-K-BRIDGE.md |  |
| 79 | `M7-KRAFT-CONVERSE` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M7-KRAFT-CONVERSE.md |  |
| 92 | `M7-STEP-COMPLEXITY` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M7-STEP-COMPLEXITY.md |  |
| 95 | `M7-LEVIN-SCHNORR` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M7-LEVIN-SCHNORR.md |  |
| 96 | `M8-KU-OPTIMAL` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M8-KU-OPTIMAL.md |  |
| 100 | `M9-REPRESENTATION-BRIDGE` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M9-REPRESENTATION-BRIDGE.md |  |
| 110 | `M9-COMPLEXITY-CLASSES` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M9-COMPLEXITY-CLASSES.md |  |
| 115 | `M9-KOLMOGOROV-REPRESENTATION` | `P1` | `DONE_STRONG` | M9-REPRESENTATION-BRIDGE | docs/goal/evidence/M9-KOLMOGOROV-REPRESENTATION.md |  |
| 120 | `M9-COOK-LEVIN` | `P2` | `DONE_STRONG` | M9-COMPLEXITY-CLASSES | docs/goal/evidence/M9-COOK-LEVIN.md |  |
| 130 | `M9-GRAPH-MODEL` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M9-GRAPH-MODEL.md |  |
| 140 | `M9-SCOTT-DINF` | `P1` | `DONE_STRONG` | M9-GRAPH-MODEL | docs/goal/evidence/M9-SCOTT-DINF.md |  |
| 150 | `M9-SYSTEMT-ADEQUACY` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M9-SYSTEMT-ADEQUACY.md |  |
| 160 | `M9-STLC-CCC` | `P1` | `DONE_STRONG` | M9-SCOTT-DINF | docs/goal/evidence/M9-STLC-CCC.md |  |
| 170 | `M9-LAMBDAPI-LCCC` | `P1` | `BACKEND_PARTIAL` | M9-STLC-CCC | docs/goal/evidence/M9-LAMBDAPI-LCCC.md | Both sides are built, but the biequivalence is not claimed. Syntax: LambdaPiCwa.syntactic is a category with attributes whose types are the small types, LambdaPiCwa.weakPi its dependent product, and LambdaPiCwa.not_piStruct_weakPi shows eta genuinely fails. Semantics: the strictified model (Cwa.ofPullbacks) presents types by local universes, so substitution is strictly functorial, and a locally cartesian closed category carries there a dependent product with beta and eta (Cwa.piStructOfLccc) and a dependent sum. Universes: Cwa.Universe, SmallPi, PiClosed and the weaker CodePi and CodeSigma are what an interpretation needs; LambdaPiUniv.univ makes star a universe in the syntactic model, and CwaUniv.universeOfHom makes every morphism a universe in the strictified model. Cwa.Universe.smallCwa extracts the model whose types are the codes (inclusion smallMor, products smallWeakPiOfCodePi, sums smallSigmaOfCodeSigma); the two syntactic models are isomorphic (LambdaPiUniv.smallModelIso). Substitution of terms is functorial in both (Cwa.ExtCoherent) and models form a category (Cwa.Model.instCategory). A set-theoretic model is built (CwaTypeModel.model, modelPiNatural): over Type (u+1) the universe object is Type u, types are the small families (modelTyEquiv), terms the dependent functions (modelTmEquiv), and the universe is closed under products (codePi, the dependent function type, with beta, eta and piLam_sub) and sums (modelSigma). Not claimed: interpretation of the syntax into an arbitrary model with a universe (initiality), any comparison between syntax and an arbitrary model, and closure of the universe of a general strictified model under the pushforward product on the nose (Cwa.Universe.PiClosed). That closure is genuine extra structure: CwaTypeNotClosed.twoUniverse is a two-code universe of the standard model with products over its small types, and not_piClosed and not_codePi rule out both Cwa.Universe.PiClosed and the weaker Cwa.Universe.CodePi for it. |
| 172 | `M9-LAMBDAPI-SN` | `P1` | `DONE_STRONG` | M9-LAMBDAPI-LCCC | docs/goal/evidence/M9-LAMBDAPI-SN.md |  |
| 175 | `M9-SYSTEM-F` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M9-SYSTEM-F.md |  |
| 180 | `M9-DINF-ADEQUACY` | `P2` | `DONE_STRONG` | M9-SCOTT-DINF | docs/goal/evidence/M9-DINF-ADEQUACY.md |  |
| 182 | `M9-UNTYPED-FULL-ABSTRACTION` | `P3` | `BACKEND_PARTIAL` | M9-DINF-ADEQUACY, M9-GRAPH-ADEQUACY | docs/goal/evidence/M9-UNTYPED-FULL-ABSTRACTION.md | Both exit criteria are now met, but the headline question is only settled for one of the two models. Adequacy is proved for both untyped models (M9-GRAPH-ADEQUACY, M9-DINF-ADEQUACY), so denotational equality implies observational equivalence at head normalization. For the graph model the converse provably fails: GraphNotFullyAbstract.graph_not_fully_abstract exhibits closed terms, the identity and its eta-expansion, that no context distinguishes (D-infinity validates eta and is adequate) but whose graph-model denotations differ in every environment, the graph model not being extensional. The approximation theory is now complete for the graph model: Start/GraphApprox.lean defines the approximation order Lambda.Approx and the direct approximant Lambda.direct and proves the soundness inclusion, and Start/GraphApproxTheorem.lean proves the approximation theorem itself, GraphModel.denot_eq_iUnion_denot_direct: the denotation of a term is exactly the union of the denotations of the direct approximants of its reducts. What remains open is full abstraction for D-infinity (Wadsworth theorem), for which the corresponding approximation theorem in D-infinity, not proved here, is the missing step. |
| 185 | `M9-GRAPH-ADEQUACY` | `P2` | `DONE_STRONG` | M9-GRAPH-MODEL, M5-SOLVABILITY | docs/goal/evidence/M9-GRAPH-ADEQUACY.md |  |
| 190 | `M9-HEAD-REDUCTION` | `P2` | `DONE_STRONG` | M9-GRAPH-ADEQUACY | docs/goal/evidence/M9-HEAD-REDUCTION.md |  |
| 195 | `M9-DINF-HNF` | `P2` | `DONE_STRONG` | M9-SCOTT-DINF, M9-GRAPH-ADEQUACY | docs/goal/evidence/M9-DINF-HNF.md |  |

Next: `M9-LAMBDAPI-LCCC`

- Title: Dependent types: the calculus lambda-Pi, categories with attributes, and locally cartesian closed categories
- Status: `BACKEND_PARTIAL`
- Open boundary: Both sides are built, but the biequivalence is not claimed. Syntax: LambdaPiCwa.syntactic is a category with attributes whose types are the small types, LambdaPiCwa.weakPi its dependent product, and LambdaPiCwa.not_piStruct_weakPi shows eta genuinely fails. Semantics: the strictified model (Cwa.ofPullbacks) presents types by local universes, so substitution is strictly functorial, and a locally cartesian closed category carries there a dependent product with beta and eta (Cwa.piStructOfLccc) and a dependent sum. Universes: Cwa.Universe, SmallPi, PiClosed and the weaker CodePi and CodeSigma are what an interpretation needs; LambdaPiUniv.univ makes star a universe in the syntactic model, and CwaUniv.universeOfHom makes every morphism a universe in the strictified model. Cwa.Universe.smallCwa extracts the model whose types are the codes (inclusion smallMor, products smallWeakPiOfCodePi, sums smallSigmaOfCodeSigma); the two syntactic models are isomorphic (LambdaPiUniv.smallModelIso). Substitution of terms is functorial in both (Cwa.ExtCoherent) and models form a category (Cwa.Model.instCategory). A set-theoretic model is built (CwaTypeModel.model, modelPiNatural): over Type (u+1) the universe object is Type u, types are the small families (modelTyEquiv), terms the dependent functions (modelTmEquiv), and the universe is closed under products (codePi, the dependent function type, with beta, eta and piLam_sub) and sums (modelSigma). Not claimed: interpretation of the syntax into an arbitrary model with a universe (initiality), any comparison between syntax and an arbitrary model, and closure of the universe of a general strictified model under the pushforward product on the nose (Cwa.Universe.PiClosed). That closure is genuine extra structure: CwaTypeNotClosed.twoUniverse is a two-code universe of the standard model with products over its small types, and not_piClosed and not_codePi rule out both Cwa.Universe.PiClosed and the weaker Cwa.Universe.CodePi for it.
