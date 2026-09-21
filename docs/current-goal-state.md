# Current goal state

- Active milestone: `M14`

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
| 170 | `M9-LAMBDAPI-LCCC` | `P1` | `DONE_STRONG` | M9-STLC-CCC | docs/goal/evidence/M9-LAMBDAPI-LCCC.md |  |
| 172 | `M9-LAMBDAPI-SN` | `P1` | `DONE_STRONG` | M9-LAMBDAPI-LCCC | docs/goal/evidence/M9-LAMBDAPI-SN.md |  |
| 175 | `M9-SYSTEM-F` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M9-SYSTEM-F.md |  |
| 180 | `M9-DINF-ADEQUACY` | `P2` | `DONE_STRONG` | M9-SCOTT-DINF | docs/goal/evidence/M9-DINF-ADEQUACY.md |  |
| 182 | `M9-UNTYPED-FULL-ABSTRACTION` | `P3` | `DONE_STRONG` | M9-DINF-ADEQUACY, M9-GRAPH-ADEQUACY | docs/goal/evidence/M9-UNTYPED-FULL-ABSTRACTION.md |  |
| 185 | `M9-GRAPH-ADEQUACY` | `P2` | `DONE_STRONG` | M9-GRAPH-MODEL, M5-SOLVABILITY | docs/goal/evidence/M9-GRAPH-ADEQUACY.md |  |
| 190 | `M9-HEAD-REDUCTION` | `P2` | `DONE_STRONG` | M9-GRAPH-ADEQUACY | docs/goal/evidence/M9-HEAD-REDUCTION.md |  |
| 195 | `M9-DINF-HNF` | `P2` | `DONE_STRONG` | M9-SCOTT-DINF, M9-GRAPH-ADEQUACY | docs/goal/evidence/M9-DINF-HNF.md |  |
| 200 | `M10-COMPLEXITY-DESCSYSTEM` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M10-COMPLEXITY-DESCSYSTEM.md |  |
| 210 | `M10-LEVIN-KT` | `P1` | `DONE_STRONG` | M10-COMPLEXITY-DESCSYSTEM | docs/goal/evidence/M10-LEVIN-KT.md |  |
| 220 | `M10-CAPSTONE-REGISTRY` | `P0` | `DONE_STRONG` | M10-LEVIN-KT | docs/goal/evidence/M10-CAPSTONE-REGISTRY.md |  |
| 230 | `M10-INTERSECTION-FILTER` | `P1` | `DONE_STRONG` | M10-CAPSTONE-REGISTRY | docs/goal/evidence/M10-INTERSECTION-FILTER.md |  |
| 240 | `M10-LAMBDA-THEORY-LATTICE` | `P1` | `DONE_STRONG` | M10-INTERSECTION-FILTER | docs/goal/evidence/M10-LAMBDA-THEORY-LATTICE.md |  |
| 250 | `M10-POST-SIMPLE-INCOMPLETE` | `P1` | `DONE_STRONG` | M10-CAPSTONE-REGISTRY | docs/goal/evidence/M10-POST-SIMPLE-INCOMPLETE.md |  |
| 251 | `M10-MYHILL-CREATIVE` | `P1` | `DONE_STRONG` | M10-POST-SIMPLE-INCOMPLETE | docs/goal/evidence/M10-MYHILL-CREATIVE.md |  |
| 252 | `M10-RICE-SHAPIRO` | `P1` | `DONE_STRONG` | M10-MYHILL-CREATIVE | docs/goal/evidence/M10-RICE-SHAPIRO.md |  |
| 253 | `M10-CHAITIN-INCOMPLETENESS` | `P1` | `DONE_STRONG` | M10-RICE-SHAPIRO | docs/goal/evidence/M10-CHAITIN-INCOMPLETENESS.md |  |
| 254 | `M10-KOLM-UPPER-SEMICOMPUTABLE` | `P1` | `DONE_STRONG` | M10-CHAITIN-INCOMPLETENESS | docs/goal/evidence/M10-KOLM-UPPER-SEMICOMPUTABLE.md |  |
| 255 | `M10-TOOLCHAIN-V433-RESTORE` | `P0` | `DONE_STRONG` | M10-KOLM-UPPER-SEMICOMPUTABLE | docs/goal/evidence/M10-TOOLCHAIN-V433-RESTORE.md |  |
| 256 | `M10-LAMBDAPI-ETA` | `P1` | `DONE_STRONG` | M9-LAMBDAPI-LCCC | docs/goal/evidence/M10-LAMBDAPI-ETA.md |  |
| 257 | `M10-LAMBDA-BETAETA` | `P1` | `DONE_STRONG` | M10-LAMBDAPI-ETA | docs/goal/evidence/M10-LAMBDA-BETAETA.md |  |
| 258 | `M10-LAMBDA-ETAPOSTPONE` | `P1` | `DONE_STRONG` | M10-LAMBDA-BETAETA | docs/goal/evidence/M10-LAMBDA-ETAPOSTPONE.md |  |
| 260 | `M10-SCOTT-CURRY` | `P1` | `DONE_STRONG` | M9-KOLMOGOROV-REPRESENTATION | docs/goal/evidence/M10-SCOTT-CURRY.md |  |
| 262 | `M10-RICE-CREATIVE` | `P1` | `DONE_STRONG` | M10-SCOTT-CURRY | docs/goal/evidence/M10-RICE-CREATIVE.md |  |
| 264 | `M10-CREATIVE-CODESETS` | `P1` | `DONE_STRONG` | M10-RICE-CREATIVE | docs/goal/evidence/M10-CREATIVE-CODESETS.md |  |
| 270 | `M10-TOOLCHAIN-V428-REPIN` | `P0` | `DONE_STRONG` | M10-TOOLCHAIN-V433-RESTORE | docs/goal/evidence/M10-TOOLCHAIN-V428-REPIN.md |  |
| 272 | `M10-MYHILL-ISO` | `P1` | `DONE_STRONG` | M10-CREATIVE-CODESETS | docs/goal/evidence/M10-MYHILL-ISO.md |  |
| 280 | `M10-CREATIVE-ISO` | `P1` | `DONE_STRONG` | M10-MYHILL-ISO | docs/goal/evidence/M10-CREATIVE-ISO.md |  |
| 290 | `M10-TOOLCHAIN-V433-RETURN` | `P0` | `DONE_STRONG` | M10-TOOLCHAIN-V428-REPIN | docs/goal/evidence/M10-TOOLCHAIN-V433-RETURN.md |  |
| 300 | `M10-JUMP-SIGMA-ONE` | `P1` | `DONE_STRONG` | M10-TOOLCHAIN-V433-RETURN | docs/goal/evidence/M10-JUMP-SIGMA-ONE.md |  |
| 310 | `M10-LIMIT-LEMMA` | `P1` | `DONE_STRONG` | M10-JUMP-SIGMA-ONE | docs/goal/evidence/M10-LIMIT-LEMMA.md |  |
| 320 | `M10-ARITH-HIERARCHY` | `P1` | `DONE_STRONG` | M10-POST-SIMPLE-INCOMPLETE | docs/goal/evidence/M10-ARITH-HIERARCHY.md |  |
| 330 | `M10-POST-THEOREM-TWO` | `P1` | `DONE_STRONG` | M10-ARITH-HIERARCHY, M10-LIMIT-LEMMA | docs/goal/evidence/M10-POST-THEOREM-TWO.md |  |
| 335 | `M10-ARITH-HIERARCHY-PROPER` | `P1` | `DONE_STRONG` | M10-ARITH-HIERARCHY | docs/goal/evidence/M10-ARITH-HIERARCHY-PROPER.md |  |
| 336 | `M10-ARITH-BOUNDED` | `P1` | `DONE_STRONG` | M10-ARITH-HIERARCHY | docs/goal/evidence/M10-ARITH-BOUNDED.md |  |
| 337 | `M10-ARITH-COMPLETE` | `P1` | `DONE_STRONG` | M10-ARITH-HIERARCHY-PROPER | docs/goal/evidence/M10-ARITH-COMPLETE.md |  |
| 338 | `M10-ARITH-INDEX-SETS` | `P1` | `DONE_STRONG` | M10-ARITH-COMPLETE | docs/goal/evidence/M10-ARITH-INDEX-SETS.md |  |
| 340 | `M10-LAMBDA-MODEL-REFLEXIVE` | `P1` | `DONE_STRONG` | M10-LAMBDA-THEORY-LATTICE | docs/goal/evidence/M10-LAMBDA-MODEL-REFLEXIVE.md |  |
| 350 | `M10-CWA-BICATEGORY` | `P1` | `DONE_STRONG` | M10-LAMBDA-MODEL-REFLEXIVE | docs/goal/evidence/M10-CWA-BICATEGORY.md |  |
| 351 | `M10-CWA-DEMOCRATIC` | `P2` | `DONE_STRONG` | M10-CWA-BICATEGORY | docs/goal/evidence/M10-CWA-DEMOCRATIC.md |  |
| 355 | `M10-LAMBDAPI-SELF-INITIAL` | `P1` | `DONE_STRONG` | M10-CWA-BICATEGORY | docs/goal/evidence/M10-LAMBDAPI-SELF-INITIAL.md |  |
| 357 | `M10-LAMBDAPI-MODELHOM` | `P1` | `DONE_STRONG` | M10-LAMBDAPI-SELF-INITIAL | docs/goal/evidence/M10-LAMBDAPI-MODELHOM.md |  |
| 356 | `M10-CWA-STRICT-FUNCTOR` | `P1` | `DONE_STRONG` | M10-CWA-BICATEGORY | docs/goal/evidence/M10-CWA-STRICT-FUNCTOR.md |  |
| 360 | `M10-PCA-KLEENE` | `P1` | `DONE_STRONG` | M10-LAMBDA-MODEL-REFLEXIVE | docs/goal/evidence/M10-PCA-KLEENE.md |  |
| 370 | `M10-ASSEMBLY-CCC` | `P1` | `DONE_STRONG` | M10-PCA-KLEENE | docs/goal/evidence/M10-ASSEMBLY-CCC.md |  |
| 380 | `M10-PER-SYSTEMF` | `P1` | `DONE_STRONG` | M10-ASSEMBLY-CCC | docs/goal/evidence/M10-PER-SYSTEMF.md |  |
| 390 | `M10-LAMBDAPI-INTERP-NATURAL` | `P1` | `DONE_STRONG` | M10-CWA-BICATEGORY | docs/goal/evidence/M10-LAMBDAPI-INTERP-NATURAL.md |  |
| 400 | `M10-ASSEMBLY-NNO` | `P1` | `DONE_STRONG` | M10-ASSEMBLY-CCC | docs/goal/evidence/M10-ASSEMBLY-NNO.md |  |
| 410 | `M10-ASSEMBLY-SUBOBJECT` | `P1` | `DONE_STRONG` | M10-ASSEMBLY-NNO | docs/goal/evidence/M10-ASSEMBLY-SUBOBJECT.md |  |
| 420 | `M10-ASSEMBLY-GLOBAL-SECTIONS` | `P1` | `DONE_STRONG` | M10-ASSEMBLY-SUBOBJECT | docs/goal/evidence/M10-ASSEMBLY-GLOBAL-SECTIONS.md |  |
| 430 | `M10-MODEST-PER-EQUIV` | `P1` | `DONE_STRONG` | M10-ASSEMBLY-GLOBAL-SECTIONS | docs/goal/evidence/M10-MODEST-PER-EQUIV.md |  |
| 440 | `M10-MODEST-CCC` | `P1` | `DONE_STRONG` | M10-MODEST-PER-EQUIV | docs/goal/evidence/M10-MODEST-CCC.md |  |
| 450 | `M10-MANIFEST-CLOSURE-REPAIR` | `P0` | `DONE_STRONG` | M10-TOOLCHAIN-V433-RETURN | docs/goal/evidence/M10-MANIFEST-CLOSURE-REPAIR.md |  |
| 460 | `M10-CWA-TWOCELL-UNIV` | `P1` | `DONE_STRONG` | M10-CWA-BICATEGORY | docs/goal/evidence/M10-CWA-TWOCELL-UNIV.md |  |
| 470 | `M10-LAMBDAPI-TYPE-UNIQUE` | `P1` | `DONE_STRONG` | M9-LAMBDAPI-LCCC | docs/goal/evidence/M10-LAMBDAPI-TYPE-UNIQUE.md |  |
| 480 | `M10-TOOLCHAIN-V433-FINAL` | `P0` | `DONE_STRONG` | M10-TOOLCHAIN-V428-REPIN | docs/goal/evidence/M10-TOOLCHAIN-V433-FINAL.md |  |
| 490 | `M10-CWA-STRICT-SECTION` | `P1` | `DONE_STRONG` | M10-CWA-STRICT-FUNCTOR | docs/goal/evidence/M10-CWA-STRICT-SECTION.md |  |
| 500 | `M10-CWA-STRICT-RIGID` | `P1` | `DONE_STRONG` | M10-CWA-STRICT-SECTION, M10-CWA-BICATEGORY | docs/goal/evidence/M10-CWA-STRICT-RIGID.md |  |
| 505 | `M10-CWA-LAX-TWOCELL` | `P1` | `DONE_STRONG` | M10-CWA-STRICT-RIGID | docs/goal/evidence/M10-CWA-LAX-TWOCELL.md |  |
| 507 | `M10-CWA-LAX-CATEGORY` | `P1` | `DONE_STRONG` | M10-CWA-LAX-TWOCELL | docs/goal/evidence/M10-CWA-LAX-CATEGORY.md |  |
| 509 | `M10-CWA-LAX-WHISKER` | `P1` | `DONE_STRONG` | M10-CWA-LAX-CATEGORY | docs/goal/evidence/M10-CWA-LAX-WHISKER.md |  |
| 511 | `M10-CWA-LAX-RIGID` | `P1` | `DONE_STRONG` | M10-CWA-LAX-CATEGORY | docs/goal/evidence/M10-CWA-LAX-RIGID.md |  |
| 512 | `M10-CWA-LAX-INTERCHANGE` | `P1` | `DONE_STRONG` | M10-CWA-LAX-RIGID, M10-CWA-LAX-WHISKER | docs/goal/evidence/M10-CWA-LAX-INTERCHANGE.md |  |
| 513 | `M10-CWA-LAX-BICAT` | `P1` | `DONE_STRONG` | M10-CWA-LAX-INTERCHANGE | docs/goal/evidence/M10-CWA-LAX-BICAT.md |  |
| 514 | `M10-CWA-LAX-BIINITIAL` | `P1` | `DONE_STRONG` | M10-CWA-LAX-BICAT, M10-CWA-BICATEGORY | docs/goal/evidence/M10-CWA-LAX-BIINITIAL.md |  |
| 510 | `M10-ASSEMBLY-COLIMITS` | `P1` | `DONE_STRONG` | M10-ASSEMBLY-CCC | docs/goal/evidence/M10-ASSEMBLY-COLIMITS.md |  |
| 520 | `M10-MODEST-COLIMITS` | `P1` | `DONE_STRONG` | M10-MODEST-CCC, M10-ASSEMBLY-COLIMITS | docs/goal/evidence/M10-MODEST-COLIMITS.md |  |
| 530 | `M10-MODEST-REFLECTIVE` | `P1` | `DONE_STRONG` | M10-MODEST-COLIMITS | docs/goal/evidence/M10-MODEST-REFLECTIVE.md |  |
| 540 | `M10-MODEST-NNO` | `P1` | `DONE_STRONG` | M10-MODEST-COLIMITS, M10-ASSEMBLY-NNO | docs/goal/evidence/M10-MODEST-NNO.md |  |
| 550 | `M10-PER-NNO` | `P1` | `DONE_STRONG` | M10-MODEST-NNO | docs/goal/evidence/M10-PER-NNO.md |  |
| 560 | `M10-ASSEMBLY-IMAGE` | `P1` | `DONE_STRONG` | M10-ASSEMBLY-COLIMITS | docs/goal/evidence/M10-ASSEMBLY-IMAGE.md |  |
| 570 | `M10-ASSEMBLY-REGULAR` | `P1` | `DONE_STRONG` | M10-ASSEMBLY-IMAGE | docs/goal/evidence/M10-ASSEMBLY-REGULAR.md |  |
| 580 | `M10-MODEST-IMAGE` | `P1` | `DONE_STRONG` | M10-ASSEMBLY-REGULAR, M10-MODEST-COLIMITS | docs/goal/evidence/M10-MODEST-IMAGE.md |  |
| 585 | `M10-MANIFEST-RESTORE-V433` | `P0` | `DONE_STRONG` | M10-MANIFEST-CLOSURE-REPAIR | docs/goal/evidence/M10-MANIFEST-RESTORE-V433.md |  |
| 590 | `M10-ASM-KLEENE-NNO` | `P1` | `DONE_STRONG` | M10-ASSEMBLY-NNO, M10-PCA-KLEENE | docs/goal/evidence/M10-ASM-KLEENE-NNO.md |  |
| 595 | `M10-ASM-KLEENE-BOOL` | `P1` | `DONE_STRONG` | M10-ASM-KLEENE-NNO | docs/goal/evidence/M10-ASM-KLEENE-BOOL.md |  |
| 597 | `M10-ASM-PROJECTIVE` | `P1` | `DONE_STRONG` | M10-ASSEMBLY-REGULAR, M10-ASM-KLEENE-BOOL | docs/goal/evidence/M10-ASM-PROJECTIVE.md |  |
| 600 | `M10-CWA-STRICT-FULL` | `P1` | `DONE_STRONG` | M10-CWA-STRICT-SECTION, M10-CWA-STRICT-RIGID | docs/goal/evidence/M10-CWA-STRICT-FULL.md |  |
| 605 | `M10-LAMBDAPI-ETA-POSTPONE` | `P1` | `DONE_STRONG` | M10-LAMBDAPI-ETA, M9-LAMBDAPI-SN | docs/goal/evidence/M10-LAMBDAPI-ETA-POSTPONE.md |  |
| 610 | `M10-LAMBDAPI-ETA-CONFLUENT` | `P1` | `DONE_STRONG` | M10-LAMBDAPI-ETA-POSTPONE | docs/goal/evidence/M10-LAMBDAPI-ETA-CONFLUENT.md |  |
| 700 | `M11-REWRITING-INTERFACE` | `P2` | `DONE_STRONG` | - | docs/goal/evidence/M11-REWRITING-INTERFACE.md |  |
| 710 | `M11-REWRITING-MIGRATE` | `P2` | `DONE_STRONG` | M11-REWRITING-INTERFACE | docs/goal/evidence/M11-REWRITING-MIGRATE.md |  |
| 720 | `M11-REDUCTION-SPLIT` | `P2` | `DONE_STRONG` | M11-REWRITING-MIGRATE | docs/goal/evidence/M11-REDUCTION-SPLIT.md |  |
| 730 | `M11-REDUCESIN-GENERALIZE` | `P2` | `DONE_STRONG` | M11-REWRITING-INTERFACE | docs/goal/evidence/M11-REDUCESIN-GENERALIZE.md |  |
| 740 | `M11-CIRCUIT-SAT-NPC` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M11-CIRCUIT-SAT-NPC.md |  |
| 750 | `M11-THREE-SAT-NPC` | `P1` | `DONE_STRONG` | M11-CIRCUIT-SAT-NPC | docs/goal/evidence/M11-THREE-SAT-NPC.md |  |
| 760 | `M11-NP-INTERSECTION` | `P2` | `DONE_STRONG` | - | docs/goal/evidence/M11-NP-INTERSECTION.md |  |
| 770 | `M11-KLEENE-TWO-PCA` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M11-KLEENE-TWO-PCA.md |  |
| 780 | `M11-APPLICATIVE-MORPHISM` | `P2` | `DONE_STRONG` | M11-KLEENE-TWO-PCA | docs/goal/evidence/M11-APPLICATIVE-MORPHISM.md |  |
| 790 | `M11-SPECKER` | `P2` | `DONE_STRONG` | M11-APPLICATIVE-MORPHISM | docs/goal/evidence/M11-SPECKER.md |  |
| 795 | `M11-SPECKER-REAL` | `P2` | `DONE_STRONG` | M11-SPECKER | docs/goal/evidence/M11-SPECKER-REAL.md |  |
| 800 | `M11-MYHILL-SHEPHERDSON` | `P2` | `DONE_STRONG` | M11-SPECKER-REAL | docs/goal/evidence/M11-MYHILL-SHEPHERDSON.md |  |
| 810 | `M11-COMPUTABLE-REAL-CONTINUITY` | `P2` | `DONE_STRONG` | M11-SPECKER-REAL | docs/goal/evidence/M11-COMPUTABLE-REAL-CONTINUITY.md |  |
| 820 | `M11-MULTI-TYPES` | `P2` | `DONE_STRONG` | M10-INTERSECTION-FILTER | docs/goal/evidence/M11-MULTI-TYPES.md |  |
| 830 | `M11-KRIVINE-MACHINE` | `P2` | `DONE_STRONG` | M11-MULTI-TYPES | docs/goal/evidence/M11-KRIVINE-MACHINE.md |  |
| 840 | `M11-KRIVINE-SIMULATION` | `P2` | `DONE_STRONG` | M11-KRIVINE-MACHINE | docs/goal/evidence/M11-KRIVINE-SIMULATION.md |  |
| 850 | `M11-KRIVINE-INVARIANCE` | `P2` | `DONE_STRONG` | M11-KRIVINE-SIMULATION | docs/goal/evidence/M11-KRIVINE-INVARIANCE.md |  |
| 860 | `M11-KLEENE-NO-RETRACTION` | `P2` | `DONE_STRONG` | M11-COMPUTABLE-REAL-CONTINUITY | docs/goal/evidence/M11-KLEENE-NO-RETRACTION.md |  |
| 855 | `M11-KRIVINE-UNIT-COST` | `P2` | `DONE_STRONG` | M11-KRIVINE-INVARIANCE | docs/goal/evidence/M11-KRIVINE-UNIT-COST.md |  |
| 857 | `M11-KRIVINE-PASS-MACHINE` | `P2` | `DONE_STRONG` | M11-KRIVINE-UNIT-COST | docs/goal/evidence/M11-KRIVINE-PASS-MACHINE.md |  |
| 900 | `M12-KRIVINE-SPACE-LIVE` | `P1` | `DONE_STRONG` | M11-KRIVINE-UNIT-COST | docs/goal/evidence/M12-KRIVINE-SPACE-LIVE.md |  |
| 905 | `M12-KRIVINE-SPACE-LOG` | `P1` | `DONE_STRONG` | M12-KRIVINE-SPACE-LIVE | docs/goal/evidence/M12-KRIVINE-SPACE-LOG.md |  |
| 910 | `M12-KRIVINE-SPACE-INVARIANCE` | `P1` | `DONE_STRONG` | M12-KRIVINE-SPACE-LOG | docs/goal/evidence/M12-KRIVINE-SPACE-INVARIANCE.md |  |
| 925 | `M12-EXREG-REGULAR` | `P2` | `DONE_STRONG` | M12-EFF-EXREG | docs/goal/evidence/M12-EXREG-REGULAR.md |  |
| 930 | `M12-KRIVINE-SPACE-CALCULUS` | `P2` | `DONE_STRONG` | M12-KRIVINE-SPACE-INVARIANCE | docs/goal/evidence/M12-KRIVINE-SPACE-CALCULUS.md |  |
| 920 | `M12-EFF-EXREG` | `P2` | `DONE_STRONG` | - | docs/goal/evidence/M12-EFF-EXREG.md |  |
| 926 | `M12-EXREG-PROJ-EXACT` | `P2` | `DONE_STRONG` | M12-EFF-EXREG, M12-EXREG-REGULAR | docs/goal/evidence/M12-EXREG-PROJ-EXACT.md |  |
| 930 | `M13-SPACE-MODEL` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M13-SPACE-MODEL.md |  |
| 931 | `M13-SPACE-CONFIG-COUNT` | `P1` | `DONE_STRONG` | M13-SPACE-MODEL, M13-SAVITCH-REACH | docs/goal/evidence/M13-SPACE-CONFIG-COUNT.md |  |
| 932 | `M13-SAVITCH-REACH` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M13-SAVITCH-REACH.md |  |
| 933 | `M13-SAVITCH-VM` | `P1` | `DONE_STRONG` | M13-SAVITCH-REACH | docs/goal/evidence/M13-SAVITCH-VM.md |  |
| 934 | `M13-SAVITCH-SPACE` | `P1` | `DONE_STRONG` | M13-SPACE-CONFIG-COUNT, M13-SAVITCH-VM | docs/goal/evidence/M13-SAVITCH-SPACE.md |  |
| 935 | `M13-QBF-SPACE` | `P2` | `DONE_STRONG` | M13-SAVITCH-VM | docs/goal/evidence/M13-QBF-SPACE.md |  |
| 940 | `M14-TOOLCHAIN-V428-REPAIR` | `P0` | `DONE_STRONG` | - | docs/goal/evidence/M14-TOOLCHAIN-V428-REPAIR.md |  |
| 941 | `M14-KRIVINE-SPACE-CONFIG` | `P1` | `DONE_STRONG` | M12-KRIVINE-SPACE-INVARIANCE, M13-SPACE-MODEL | docs/goal/evidence/M14-KRIVINE-SPACE-CONFIG.md |  |
| 942 | `M14-QBF-REACH-FORMULA` | `P1` | `DONE_STRONG` | M13-SAVITCH-REACH, M13-QBF-SPACE | docs/goal/evidence/M14-QBF-REACH-FORMULA.md |  |
| 946 | `M14-QBF-STEP-FORMULA` | `P1` | `DONE_STRONG` | M14-QBF-REACH-FORMULA, M13-SPACE-MODEL | docs/goal/evidence/M14-QBF-STEP-FORMULA.md |  |
| 947 | `M14-QBF-PSPACE-FAMILY` | `P1` | `DONE_STRONG` | M14-QBF-STEP-FORMULA | docs/goal/evidence/M14-QBF-PSPACE-FAMILY.md |  |
| 943 | `M14-TQBF-PSPACE-HARD` | `P2` | `TODO_NEEDS_DESIGN` | M14-QBF-REACH-FORMULA, M14-QBF-STEP-FORMULA, M14-QBF-PSPACE-FAMILY, M14-QBF-WORD-LANG, M14-QBF-WORD-STREAM, M13-SAVITCH-SPACE | docs/goal/evidence/M14-QBF-PSPACE-FAMILY.md | The non-computational part is done, now down to the level of words: TQBF is a language of binary words (Complexity.Qbf.tqbfLang) and every language in PSPACE is mapped into it by one map of words whose output length is bounded by a single polynomial in the input length (M14-QBF-WORD-LANG); moreover the code of the formula of an input is a concatenation of blocks, one per level of the midpoint recursion, each a closed function of the level (M14-QBF-WORD-STREAM). What is missing is the computational half: a term of Complexity.Cob that writes those blocks, i.e. that the map of words is computed in polynomial time in the time model of Start/ComplexityClasses.lean - only then is TQBF PSPACE-hard. |
| 944 | `M14-KRIVINE-SPACE-CLASS` | `P1` | `TODO_NEEDS_DESIGN` | M14-KRIVINE-SPACE-CONFIG | docs/goal/evidence/M14-KRIVINE-SPACE-CONFIG.md | The memory half is done (M14-KRIVINE-SPACE-CONFIG): the word of a collected state is a work tape of Start/SpaceMachine.lean and its length is that model's memory measure, O(s log s) in the live data. What is missing is a machine of that model which performs the Krivine transitions on the word: a bit-level interpreter for Start/KrivineCobBin.lean's passes, with the invariant that its reachable configurations are the encodings of the states of the run, so that a language decided by a lambda-term within a space bound s lands in Complexity.Space.DSPACE (s * log s). |
| 945 | `M14-SPACE-REASONABLE` | `P2` | `TODO_NEEDS_DESIGN` | M14-KRIVINE-SPACE-CLASS | - | Nothing of this direction is formalised. It needs a compiler from a machine of Start/SpaceMachine.lean to a lambda-term, together with the analysis of the Krivine run of that term, showing its live-data peak polynomial (or linear) in the space of the machine; only with M14-KRIVINE-SPACE-CLASS does this give the two-directional statement that the lambda-calculus is a reasonable space cost model. |
| 948 | `M14-QBF-WORD-LANG` | `P1` | `DONE_STRONG` | M14-QBF-PSPACE-FAMILY | docs/goal/evidence/M14-QBF-WORD-LANG.md |  |
| 949 | `M14-QBF-WORD-STREAM` | `P1` | `DONE_STRONG` | M14-QBF-WORD-LANG | docs/goal/evidence/M14-QBF-WORD-STREAM.md |  |
| 950 | `M14-QBF-COB-PIECES` | `P1` | `DONE_STRONG` | M14-QBF-WORD-STREAM | docs/goal/evidence/M14-QBF-COB-PIECES.md |  |

Next: `M14-TQBF-PSPACE-HARD`

- Title: TQBF is PSPACE-hard, hence PSPACE-complete
- Status: `TODO_NEEDS_DESIGN`
- Open boundary: The non-computational part is done, now down to the level of words: TQBF is a language of binary words (Complexity.Qbf.tqbfLang) and every language in PSPACE is mapped into it by one map of words whose output length is bounded by a single polynomial in the input length (M14-QBF-WORD-LANG); moreover the code of the formula of an input is a concatenation of blocks, one per level of the midpoint recursion, each a closed function of the level (M14-QBF-WORD-STREAM). What is missing is the computational half: a term of Complexity.Cob that writes those blocks, i.e. that the map of words is computed in polynomial time in the time model of Start/ComplexityClasses.lean - only then is TQBF PSPACE-hard.
