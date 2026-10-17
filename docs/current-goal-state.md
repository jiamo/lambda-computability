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
| 943 | `M14-TQBF-PSPACE-HARD` | `P2` | `DONE_STRONG` | M14-QBF-REACH-FORMULA, M14-QBF-STEP-FORMULA, M14-QBF-PSPACE-FAMILY, M14-QBF-WORD-LANG, M14-QBF-WORD-STREAM, M13-SAVITCH-SPACE | docs/goal/evidence/M14-TQBF-IN-PSPACE.md |  |
| 1035 | `M14-KRIVINE-SPACE-CLASS` | `P1` | `TODO_READY` | M14-KRIVINE-SPACE-CONFIG, M14-SPACE-COMPILE | docs/goal/evidence/M14-KRIVINE-SPACE-CONFIG.md | The memory half is done (M14-KRIVINE-SPACE-CONFIG): the word of a collected state is a work tape of Start/SpaceMachine.lean and its length is that model's memory measure, O(s log s) in the live data. The run-level half of the simulation is now general (M14-SPACE-COMPILE): a realization in the sense of Complexity.Space.Realizes, or a loop program in the sense of Complexity.Space.Prog.realizes_loop, gives DSPACE membership with the bound on every reachable configuration. What is missing is the client's bridge lemma: a tape program performing one pass of Start/KrivineCobBin.lean on the word of a state, with its execution on the encoding of each state of the run, so that a language decided by a lambda-term within a space bound s lands in Complexity.Space.DSPACE (s * log s). |
| 1036 | `M14-SPACE-REASONABLE` | `P2` | `TODO_NEEDS_DESIGN` | M14-KRIVINE-SPACE-CLASS | - | Nothing of this direction is formalised. It is the converse bridge to M14-SPACE-COMPILE: a compiler from a machine of Start/SpaceMachine.lean to a lambda-term, together with the analysis of the Krivine run of that term, showing its live-data peak polynomial (or linear) in the space of the machine; only with M14-KRIVINE-SPACE-CLASS does this give the two-directional statement that the lambda-calculus is a reasonable space cost model. |
| 948 | `M14-QBF-WORD-LANG` | `P1` | `DONE_STRONG` | M14-QBF-PSPACE-FAMILY | docs/goal/evidence/M14-QBF-WORD-LANG.md |  |
| 949 | `M14-QBF-WORD-STREAM` | `P1` | `DONE_STRONG` | M14-QBF-WORD-LANG | docs/goal/evidence/M14-QBF-WORD-STREAM.md |  |
| 950 | `M14-QBF-COB-PIECES` | `P1` | `DONE_STRONG` | M14-QBF-WORD-STREAM | docs/goal/evidence/M14-QBF-COB-PIECES.md |  |
| 951 | `M14-QBF-COB-COND` | `P1` | `DONE_STRONG` | M14-QBF-COB-PIECES | docs/goal/evidence/M14-QBF-COB-PIECES.md |  |
| 952 | `M14-QBF-COB-CFGBLOCK` | `P1` | `DONE_STRONG` | M14-QBF-COB-COND | docs/goal/evidence/M14-QBF-COB-PIECES.md |  |
| 953 | `M14-QBF-COB-STEPCASE` | `P1` | `DONE_STRONG` | M14-QBF-COB-CFGBLOCK | docs/goal/evidence/M14-TQBF-PSPACE-HARD.md |  |
| 954 | `M14-QBF-COB-STEP` | `P1` | `DONE_STRONG` | M14-QBF-COB-STEPCASE | docs/goal/evidence/M14-TQBF-PSPACE-HARD.md |  |
| 955 | `M14-QBF-COB-INITACC` | `P1` | `DONE_STRONG` | M14-QBF-COB-CFGBLOCK | docs/goal/evidence/M14-TQBF-PSPACE-HARD.md |  |
| 956 | `M14-QBF-COB-LEVELS` | `P1` | `DONE_STRONG` | M14-QBF-COB-STEP | docs/goal/evidence/M14-TQBF-PSPACE-HARD.md |  |
| 957 | `M14-QBF-COB-MACHINE` | `P1` | `DONE_STRONG` | M14-QBF-COB-LEVELS, M14-QBF-COB-INITACC | docs/goal/evidence/M14-TQBF-PSPACE-HARD.md |  |
| 958 | `M14-QBF-COB-REDUCTION` | `P1` | `DONE_STRONG` | M14-QBF-COB-MACHINE | docs/goal/evidence/M14-TQBF-PSPACE-HARD.md |  |
| 960 | `M14-PSPACE-HARDNESS-USE` | `P2` | `DONE_STRONG` | M14-TQBF-PSPACE-HARD | docs/goal/evidence/M14-TQBF-PSPACE-HARD.md |  |
| 962 | `M14-QBF-CODE-SPACE` | `P1` | `DONE_STRONG` | M14-QBF-WORD-LANG | docs/goal/evidence/M14-QBF-CODE-SPACE.md |  |
| 935 | `M14-SPACE-COMPILE` | `P1` | `DONE_STRONG` | M13-SPACE-MODEL | docs/goal/evidence/M14-SPACE-COMPILE.md |  |
| 936 | `M14-QBF-STEP-PROG` | `P1` | `DONE_STRONG` | M14-SPACE-COMPILE, M14-QBF-CODE-SPACE | docs/goal/evidence/M14-TQBF-IN-PSPACE.md |  |
| 937 | `M14-TQBF-IN-PSPACE` | `P1` | `DONE_STRONG` | M14-QBF-WORD-LANG, M14-QBF-CODE-SPACE, M14-SPACE-COMPILE, M14-QBF-STEP-PROG | docs/goal/evidence/M14-TQBF-IN-PSPACE.md |  |
| 999 | `M15-ORACLE-PROG` | `P1` | `DONE_STRONG` | M14-SPACE-COMPILE | docs/goal/evidence/M15-ORACLE-PROG.md |  |
| 1000 | `M15-ORACLE-CLASSES` | `P1` | `DONE_STRONG` | M13-SPACE-MODEL, M15-ORACLE-PROG | docs/goal/evidence/M15-ORACLE-CLASSES.md |  |
| 1010 | `M15-BGS-EQUAL` | `P1` | `TODO_READY` | M15-ORACLE-CLASSES, M14-TQBF-PSPACE-HARD | docs/goal/evidence/M13-SAVITCH-SPACE.md | Both named ingredients are proved: NP^A in PSPACE^A for every oracle (Complexity.Space.inPSPACE_rel_of_inNP_rel) and TQBF in PSPACE (Complexity.Qbf.tqbf_pspace, M14-TQBF-IN-PSPACE). What is missing is PSPACE^TQBF in PSPACE: a space-bounded oracle machine whose queries are answered by a space-bounded subroutine deciding TQBF; the easy half PSPACE in P^TQBF follows from the hardness reduction (one query to the reduced word). |
| 1020 | `M15-BGS-DIFFERENT` | `P1` | `DONE_STRONG` | M15-ORACLE-CLASSES | docs/goal/evidence/M15-BGS-DIFFERENT.md |  |
| 1025 | `M15-BGS-COLLAPSE` | `P1` | `DONE_STRONG` | M15-ORACLE-CLASSES | docs/goal/evidence/M15-BGS-COLLAPSE.md |  |
| 1030 | `M15-NO-RELATIVIZING-PROOF` | `P1` | `DONE_STRONG` | M15-BGS-COLLAPSE, M15-BGS-DIFFERENT | docs/goal/evidence/M15-NO-RELATIVIZING-PROOF.md |  |
| 1040 | `M15-TIME-HIERARCHY-REL` | `P2` | `TODO_READY` | M15-ORACLE-CLASSES | docs/goal/evidence/M13-SPACE-MODEL.md |  |
| 1100 | `M16-REQUIREMENT-FRAMEWORK` | `P1` | `DONE_WEAK` | - | docs/goal/evidence/M16-REQUIREMENT-FRAMEWORK.md | The frame is generic and has not yet been instantiated by an actual construction; the first one to run in it is Friedberg-Muchnik, M16-FRIEDBERG-MUCHNIK, still open. |
| 1110 | `M16-FINITE-INJURY` | `P1` | `DONE_WEAK` | M16-REQUIREMENT-FRAMEWORK | docs/goal/evidence/M16-FINITE-INJURY.md | The lemma is proved for an arbitrary instance of the framework; no concrete construction has been fed to it yet, so the verification of the between-injuries hypothesis for a real strategy is still to come with M16-FRIEDBERG-MUCHNIK. |
| 1120 | `M16-FRIEDBERG-MUCHNIK` | `P1` | `TODO_NEEDS_DESIGN` | M16-FINITE-INJURY | docs/goal/evidence/M10-POST-SIMPLE-INCOMPLETE.md |  |
| 1130 | `M16-SACKS-SPLITTING` | `P2` | `TODO_NEEDS_DESIGN` | M16-FRIEDBERG-MUCHNIK | docs/goal/evidence/M10-POST-SIMPLE-INCOMPLETE.md |  |
| 1140 | `M16-MINIMAL-DEGREE` | `P2` | `TODO_NEEDS_DESIGN` | M16-REQUIREMENT-FRAMEWORK | docs/goal/evidence/M10-POST-SIMPLE-INCOMPLETE.md | This is not a priority construction but a forcing with perfect trees; it may be cheaper than M16-SACKS-SPLITTING and can be attempted independently, on top of Start/OracleForcing.lean. |
| 1200 | `M17-EXREG-PROJ-REGULAR` | `P1` | `TODO_READY` | - | docs/goal/evidence/M12-EXREG-PROJ-EXACT.md |  |
| 1210 | `M17-EXREG-UNIVERSAL` | `P1` | `TODO_READY` | M17-EXREG-PROJ-REGULAR | docs/goal/evidence/M12-EXREG-PROJ-EXACT.md |  |
| 1220 | `M17-EFF-TOPOS` | `P1` | `TODO_NEEDS_DESIGN` | M17-EXREG-UNIVERSAL | docs/goal/evidence/M12-EXREG-PROJ-EXACT.md |  |
| 1230 | `M17-EFF-IDENTIFY` | `P1` | `TODO_NEEDS_DESIGN` | M17-EFF-TOPOS | docs/goal/evidence/M12-EXREG-PROJ-EXACT.md |  |
| 1240 | `M17-INTERNAL-CT` | `P1` | `TODO_NEEDS_DESIGN` | M17-EFF-TOPOS | docs/goal/evidence/M12-EXREG-PROJ-EXACT.md | The internal language has to be set up first; this is the design question, and Start/Realizer.lean may already carry part of it. |
| 1250 | `M17-REALIZABILITY-HA` | `P2` | `TODO_NEEDS_DESIGN` | M17-INTERNAL-CT | docs/goal/evidence/M10-PCA-KLEENE.md |  |
| 1300 | `M18-KLS` | `P1` | `TODO_READY` | - | docs/goal/evidence/M11-MYHILL-SHEPHERDSON.md | Left TODO_READY in a later delivery under the queue rule (too large for the time left). First missing lemma (KLS continuity, with Nat.Partrec.Code as indices): theorem kls_continuous (F : Nat.Partrec.Code → Nat.Partrec.Code) (hF : Computable F) (hext : ∀ a b : Nat.Partrec.Code, (∀ n, (a.eval n).Dom) → (∀ n, (b.eval n).Dom) → a.eval = b.eval → (F a).eval = (F b).eval) (a : Nat.Partrec.Code) (ha : ∀ n, (a.eval n).Dom) (n : ℕ) : ∃ m, ∀ b : Nat.Partrec.Code, (∀ k, (b.eval k).Dom) → (∀ k < m, b.eval k = a.eval k) → (F b).eval n = (F a).eval n. |
| 1310 | `M18-WEIHRAUCH` | `P1` | `TODO_NEEDS_DESIGN` | - | docs/goal/evidence/M11-COMPUTABLE-REAL-CONTINUITY.md |  |
| 1320 | `M18-EXTENSIONAL-COLLAPSE` | `P2` | `TODO_NEEDS_DESIGN` | M18-KLS | docs/goal/evidence/M11-KLEENE-TWO-PCA.md | Longley's programme; the general theory of extensional collapses of PCAs is not fully settled in the literature, so the task should be scoped to K2 first. |
| 1330 | `M18-PCA-LATTICE` | `P2` | `DONE_WEAK` | - | docs/goal/evidence/M18-PCA-LATTICE.md | The order, its degeneracy, the refinement by decidable morphisms and the separation K1 < K2 are proved in Start/PCAOrder.lean. Two things are not: the strictness is proved for the refined order only - in the plain order all algebras are equivalent, which is itself a theorem here - and the third exit criterion, whether two algebras with equivalent realizability toposes are equivalent, is recorded as open rather than proved, since the library constructs the assemblies and their exact completion but not the realizability topos of an algebra. |
| 1400 | `M19-SYMMETRY-HARD-HALF` | `P1` | `TODO_NEEDS_DESIGN` | M19-DESCRIPTION-COST-AUDIT | docs/goal/evidence/M6-KOLMOGOROV-CORE.md | Start/KolmogorovCond.lean has the easy half, kolm_le_kolmCond_add. Start/KolmogorovCount.lean proves the base-4 counting bounds for the raw size measure (card_kolm_le, card_kolmCond_le) and the comparison with a prefix-free bit code (size <= \|bits\| <= 2 size). Still missing: an effective enumeration of {(s,y) : K(<s,y>) <= m} by dovetailing, and the conditional decoder recovering s from its index, y and m as a closed lambda term with explicit size; with base-4 counting the resulting inequality for kolm carries a factor 2 on the counting term. |
| 1410 | `M19-KT-DEFINITIONS` | `P1` | `DONE_WEAK` | - | docs/goal/evidence/M19-KT-DEFINITIONS.md | The measure, its basic theory and its invariance are proved in Start/KolmogorovTime.lean. The third exit criterion is not: that the language {(x, k) : K^T(x) <= k} is in NP. Lambda.ktime_le_iff gives its combinatorial half - the certificate is a program of size at most k - and what is missing is that checking such a certificate (running a guessed term for T steps) is polynomial time in the model of Start/ComplexityClasses.lean; the machinery for that is the Krivine machine in the Cobham model (Start/KrivineCobStep.lean) together with an encoding of terms as words. |
| 1420 | `M19-MCSP` | `P1` | `TODO_NEEDS_DESIGN` | M19-KT-DEFINITIONS | docs/goal/evidence/M9-COMPLEXITY-CLASSES.md | Whether MCSP is NP-complete is open; the task is to define it, place it in NP, and prove what is known unconditionally. |
| 1430 | `M19-OWF-KT` | `P2` | `TODO_NEEDS_DESIGN` | M19-KT-DEFINITIONS, M19-SYMMETRY-HARD-HALF | docs/goal/evidence/M10-LEVIN-KT.md | Recent research, 2020; the equivalence needs a probabilistic framework the library does not have, so the first half of the task is to decide how much probability to import from Mathlib. |
| 1500 | `M20-RANGE-PROPERTY` | `P2` | `TODO_NEEDS_DESIGN` | - | docs/goal/evidence/M10-LAMBDA-THEORY-LATTICE.md | Open. The range of a lambda-definable function on a lambda-theory is conjectured to be either a singleton or infinite; it is known for beta and for some theories, open in general. |
| 1510 | `M20-EASY-TERMS` | `P2` | `TODO_NEEDS_DESIGN` | - | docs/goal/evidence/M5-SOLVABILITY.md | Whether every unsolvable term is easy is open; Jacopini's theorem for Omega itself is not. |
| 1520 | `M20-THEORY-LATTICE-UNCOUNTABLE` | `P2` | `TODO_NEEDS_DESIGN` | - | docs/goal/evidence/M10-LAMBDA-THEORY-LATTICE.md |  |
| 1530 | `M20-GANDY` | `P1` | `TODO_NEEDS_DESIGN` | - | docs/goal/evidence/M4-CHURCH-TURING-LAMBDA.md | A faithful formalization of Gandy's mechanism principles and effective structural-state coding remains to be constructed. Computability of global evolution must follow from the principles rather than be assumed in the definition. The next research programme includes concrete mechanism instances and a simulation into the existing Church-Turing equivalence. |
| 1540 | `M20-RULE-110` | `P2` | `TODO_NEEDS_DESIGN` | - | docs/goal/evidence/M4-TM2-IMP-PARTREC.md | Cook's proof is long and combinatorial; the task is a serious engineering effort with a fully classical statement. |
| 1600 | `M21-QBF-ARITH` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M21-QBF-ARITH.md |  |
| 1605 | `M21-SUMCHECK-ROUND` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M21-QBF-ARITH.md |  |
| 1610 | `M21-QBF-SIMPLE-FORM` | `P1` | `TODO_READY` | M21-QBF-ARITH, M14-TQBF-PSPACE-HARD | docs/goal/proposed-M21-M24.md | Not on the route taken.  Shen's linearization was inserted directly into the formula tree (Complexity.Qbf.QBF.toOp, M21-LINEARIZE) and the sum-check game walks that tree (Complexity.Qbf.run, M21-SUMCHECK-GAME), so neither row needs a normal form and the dependency of M21-LINEARIZE on this row was dropped.  This row's own gap is unchanged: a Cobham translation of QBF codes to prenex form with distinct bound variables, with polynomial output size (or the statement that redTerm already produces such a form).  It would only become necessary if the verifier of M21-VERIFIER-POLY were written for prenex formulas rather than for the formula tree. |
| 1620 | `M21-LINEARIZE` | `P1` | `DONE_STRONG` | M21-QBF-ARITH | docs/goal/evidence/M21-LINEARIZE.md |  |
| 1630 | `M21-IP-DEF` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M21-IP-DEF.md |  |
| 1640 | `M21-SUMCHECK-GAME` | `P1` | `DONE_STRONG` | M21-SUMCHECK-ROUND, M21-LINEARIZE | docs/goal/evidence/M21-SUMCHECK-GAME.md |  |
| 1650 | `M21-FIELD-COBHAM` | `P1` | `DONE_STRONG` | M21-SUMCHECK-ROUND | docs/goal/evidence/M21-FIELD-COBHAM.md |  |
| 1652 | `M21-COB-TIME-ITERATE` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M21-COB-TIME-ITERATE.md |  |
| 1654 | `M21-SUMCHECK-REPLAY` | `P1` | `DONE_STRONG` | M21-SUMCHECK-GAME | docs/goal/evidence/M21-PSPACE-SUBSET-IP.md |  |
| 1656 | `M21-SUMCHECK-COINS` | `P1` | `DONE_STRONG` | M21-SUMCHECK-GAME | docs/goal/evidence/M21-PSPACE-SUBSET-IP.md |  |
| 1658 | `M21-VERIFIER-STEP-COB` | `P1` | `DONE_STRONG` | M21-SUMCHECK-REPLAY, M21-FIELD-COBHAM, M21-COB-TIME-ITERATE | docs/goal/evidence/M21-PSPACE-SUBSET-IP.md |  |
| 1660 | `M21-VERIFIER-POLY` | `P1` | `DONE_STRONG` | M21-IP-DEF, M21-SUMCHECK-GAME, M21-FIELD-COBHAM, M21-COB-TIME-ITERATE, M21-SUMCHECK-REPLAY, M21-SUMCHECK-COINS, M21-VERIFIER-STEP-COB | docs/goal/evidence/M21-PSPACE-SUBSET-IP.md |  |
| 1670 | `M21-TQBF-IN-IP` | `P1` | `DONE_STRONG` | M21-VERIFIER-POLY | docs/goal/evidence/M21-PSPACE-SUBSET-IP.md |  |
| 1680 | `M21-PSPACE-SUBSET-IP` | `P1` | `DONE_STRONG` | M21-TQBF-IN-IP, M14-TQBF-PSPACE-HARD | docs/goal/evidence/M21-PSPACE-SUBSET-IP.md |  |
| 1690 | `M21-COBHAM-TO-SPACE` | `P1` | `DONE_STRONG` | M14-SPACE-COMPILE | docs/goal/evidence/M21-COBHAM-TO-SPACE.md |  |
| 1700 | `M21-IP-SUBSET-PSPACE` | `P1` | `DONE_STRONG` | M21-IP-DEF, M21-COBHAM-TO-SPACE | docs/goal/evidence/M21-IP-EQ-PSPACE.md |  |
| 1710 | `M21-IP-EQ-PSPACE` | `P1` | `DONE_STRONG` | M21-PSPACE-SUBSET-IP, M21-IP-SUBSET-PSPACE | docs/goal/evidence/M21-IP-EQ-PSPACE.md |  |
| 1800 | `M22-NONDET-PROG` | `P1` | `DONE_STRONG` | M14-SPACE-COMPILE | docs/goal/evidence/M22-NONDET-PROG.md |  |
| 1810 | `M22-IMMERMAN-SZELEPCSENYI` | `P1` | `TODO_READY` | M22-NONDET-PROG | docs/goal/proposed-M21-M24.md |  |
| 1820 | `M22-SPACE-HIERARCHY` | `P2` | `TODO_READY` | M14-SPACE-COMPILE | docs/goal/proposed-M21-M24.md |  |
| 1830 | `M22-CONP-PH` | `P2` | `DONE_STRONG` | - | docs/goal/evidence/M22-CONP-PH.md |  |
| 1840 | `M22-COOK-RECKHOW` | `P1` | `DONE_STRONG` | M22-CONP-PH | docs/goal/evidence/M22-COOK-RECKHOW.md |  |
| 1850 | `M22-RESOLUTION` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M22-RESOLUTION.md |  |
| 1855 | `M22-RESOLUTION-PROOF-SYSTEM` | `P2` | `TODO_READY` | M22-RESOLUTION, M22-COOK-RECKHOW | docs/goal/evidence/M22-RESOLUTION.md | Left TODO_READY in a later delivery under the queue rule (too large for the time left); it needs a Cobham-term checker for resolution steps. First missing lemma: theorem Complexity.resolution_checker : ∃ f : Complexity.Cob, Complexity.IsProofSystem f ∧ ∀ (x : Complexity.Word) (d : Complexity.Sat.Refutation (Complexity.Sat.decode x)), ∃ π, f.eval [π] = x ∧ π.length ≤ 64 * (x.length + 1) ^ 2 * (d.size + 1). |
| 1860 | `M22-HAKEN-PHP` | `P1` | `DONE_STRONG` | M22-RESOLUTION, M22-HAKEN-PHP-DAG | docs/goal/evidence/M22-HAKEN-PHP.md |  |
| 1858 | `M22-HAKEN-PHP-DAG` | `P1` | `DONE_STRONG` | M22-RESOLUTION | docs/goal/evidence/M22-HAKEN-PHP.md |  |
| 1870 | `M22-AC0-DEF` | `P2` | `DONE_STRONG` | - | docs/goal/evidence/M22-AC0-DEF.md |  |
| 1880 | `M22-SWITCHING-LEMMA` | `P2` | `DONE_STRONG` | M22-AC0-DEF | docs/goal/evidence/M22-SWITCHING-LEMMA.md |  |
| 1890 | `M22-PARITY-NOT-AC0` | `P2` | `DONE_STRONG` | M22-SWITCHING-LEMMA | docs/goal/evidence/M22-PARITY-NOT-AC0.md |  |
| 1900 | `M22-FAGIN` | `P2` | `TODO_NEEDS_DESIGN` | - | docs/goal/proposed-M21-M24.md | Design question: which model of NP the logic side is compared with. The library's NP is certificate-checking by a Cobham term, not a Turing machine, so the tableau in the hard direction is a tableau of a Cobham evaluation. |
| 1995 | `M23-LAMBDAPI-EMBED` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M23-LAMBDAPI-EMBED.md |  |
| 2000 | `M23-PTS` | `P1` | `DONE_STRONG` | M23-LAMBDAPI-EMBED | docs/goal/evidence/M23-PTS.md |  |
| 2010 | `M23-FOMEGA` | `P2` | `DONE_STRONG` | M23-PTS | docs/goal/evidence/M23-FOMEGA.md |  |
| 2020 | `M23-COC-SN` | `P1` | `DONE_STRONG` | M23-PTS, M23-FOMEGA | docs/goal/evidence/M23-COC-SN.md |  |
| 2030 | `M23-HURKENS` | `P2` | `DONE_STRONG` | M23-PTS | docs/goal/evidence/M23-HURKENS.md |  |
| 2040 | `M23-ID-TYPES` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M23-ID-TYPES.md |  |
| 2050 | `M23-GROUPOID-MODEL` | `P1` | `TODO_READY` | M23-ID-TYPES | docs/goal/proposed-M21-M24.md |  |
| 2060 | `M23-UIP-INDEPENDENT` | `P1` | `TODO_READY` | M23-GROUPOID-MODEL | docs/goal/proposed-M21-M24.md |  |
| 2070 | `M23-LAMBDA-MU` | `P2` | `TODO_READY` | - | docs/goal/proposed-M21-M24.md |  |
| 2080 | `M23-LEVY-FAMILIES` | `P2` | `TODO_NEEDS_DESIGN` | - | docs/goal/proposed-M21-M24.md | Foundation for optimal reduction; the correctness of Lamping's algorithm is the separate row M23-LAMPING-ABSTRACT. |
| 2090 | `M23-LAMPING-ABSTRACT` | `P3` | `TODO_NEEDS_DESIGN` | M23-LEVY-FAMILIES | docs/goal/proposed-M21-M24.md | The full algorithm with bookkeeping, and the Lawall-Mairson and Asperti-Mairson complexity results, are not in scope of this row. |
| 2200 | `M24-ABSTRACT-LOB` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M24-ABSTRACT-LOB.md |  |
| 2210 | `M24-ARITH-THEORY` | `P1` | `TODO_READY` | - | docs/goal/proposed-M21-M24.md | The library has no first-order theory of arithmetic yet: Start/ChaitinIncompleteness.lean works with an abstract sound r.e. proof system. |
| 2220 | `M24-GODEL2-ARITH` | `P1` | `TODO_READY` | M24-ABSTRACT-LOB, M24-ARITH-THEORY | docs/goal/proposed-M21-M24.md |  |
| 2230 | `M24-GL` | `P2` | `TODO_READY` | M24-ABSTRACT-LOB | docs/goal/proposed-M21-M24.md |  |
| 2240 | `M24-OMEGA-MODELS` | `P1` | `TODO_READY` | - | docs/goal/proposed-M21-M24.md | Proof-theoretic reverse mathematics (the axiom systems as formal theories, the conservation results) is not in scope; the omega-model route needs no ordinals. |
| 2250 | `M24-VAN-LAMBALGEN` | `P2` | `TODO_READY` | - | docs/goal/proposed-M21-M24.md | Left TODO_READY in a later delivery under the queue rule (too large for the time left); relativized tests are not defined yet. First missing lemma (the unrelativized half): theorem Lambda.MLRandom.join_left (A B : ℕ → Bool) : Lambda.MLRandom (fun n => if n % 2 = 0 then A (n / 2) else B (n / 2)) → Lambda.MLRandom A. |
| 2260 | `M24-KUCERA-GACS` | `P2` | `TODO_READY` | - | docs/goal/proposed-M21-M24.md | Left TODO_READY in a later delivery under the queue rule (too large for the time left). First missing lemma (a universal Martin-Loef test): theorem Lambda.exists_universal_MLTest : ∃ U : Lambda.MLTest, ∀ X, Lambda.MLRandom X ↔ ∃ c, X ∉ U.level c. |
| 2270 | `M24-K-TRIVIAL` | `P2` | `TODO_READY` | - | docs/goal/proposed-M21-M24.md |  |
| 2280 | `M24-HYPERARITH` | `P3` | `TODO_NEEDS_DESIGN` | - | docs/goal/proposed-M21-M24.md | Needs ordinals and transfinite iterations of the jump; the library has no ordinals yet (Mathlib's do exist). |
| 2300 | `M25-UNIFICATION` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M25-UNIFICATION.md |  |
| 2310 | `M25-HM-TYPING` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M25-HM-TYPING.md |  |
| 2320 | `M25-HM-ALGORITHM-W` | `P1` | `DONE_STRONG` | M25-UNIFICATION, M25-HM-TYPING | docs/goal/evidence/M25-HM-ALGORITHM-W.md |  |
| 2330 | `M25-HM-PRINCIPAL` | `P1` | `DONE_STRONG` | M25-HM-ALGORITHM-W | docs/goal/evidence/M25-HM-PRINCIPAL.md |  |
| 2340 | `M25-CBV-MACHINE` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M25-CBV-MACHINE.md |  |
| 2345 | `M25-CBV-STEP-PROG` | `P1` | `TODO_READY` | M25-CBV-MACHINE | docs/goal/evidence/M25-CBV-COST.md |  |
| 2350 | `M25-CBV-COST` | `P1` | `DONE_WEAK` | M25-CBV-MACHINE, M25-CBV-STEP-PROG | docs/goal/evidence/M25-CBV-COST.md | The first criterion is proved, with a linear bound (Start/CbvCost.lean). The second and third are not: they need a tape program for one CEK transition on an encoding of states, which is the new row M25-CBV-STEP-PROG. |
| 2360 | `M25-CBNEED-MACHINE` | `P1` | `TODO_READY` | - | docs/goal/evidence/M12-KRIVINE-SPACE-LIVE.md |  |
| 2370 | `M25-CBNEED-COST` | `P2` | `TODO_READY` | M25-CBNEED-MACHINE | docs/goal/evidence/M11-KRIVINE-INVARIANCE.md |  |
| 2380 | `M25-CBPV` | `P2` | `TODO_READY` | M25-CBV-MACHINE | docs/goal/evidence/M9-SYSTEM-F.md |  |
| 2390 | `M25-FSUB-UNDECIDABLE` | `P1` | `TODO_NEEDS_DESIGN` | - | docs/goal/evidence/M4-TM2-IMP-PARTREC.md | The design question is which undecidable problem to reduce from and how to encode its configurations as subtyping judgements. cslib supplies the calculus and its soundness, so none of that has to be rebuilt. |
| 2400 | `M26-ARISTOTLE-ASK-TOOL` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M26-ARISTOTLE-ASK-TOOL.md |  |
| 2401 | `M26-ARISTOTLE-SOURCE-SUBMISSION` | `P1` | `DONE_STRONG` | M26-ARISTOTLE-ASK-TOOL | docs/goal/evidence/M26-ARISTOTLE-SOURCE-SUBMISSION.md |  |
| 2400 | `M26-OAI-DEGREE-QUESTION` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M26-OAI-ABSORPTION.md |  |
| 2410 | `M26-OAI-TYPESYSTEM` | `P1` | `DONE_STRONG` | M26-OAI-DEGREE-QUESTION | docs/goal/evidence/M26-OAI-ABSORPTION.md |  |
| 2415 | `M26-LOGSPACE-CONVERSE` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M26-OAI-ABSORPTION.md |  |
| 2420 | `M26-OAI-LOGSPACE` | `P1` | `DONE_STRONG` | M26-OAI-TYPESYSTEM, M26-LOGSPACE-CONVERSE | docs/goal/evidence/M26-OAI-ABSORPTION.md |  |
| 2430 | `M26-OAI-SOLENOIDAL` | `P1` | `DONE_STRONG` | M26-OAI-TYPESYSTEM | docs/goal/evidence/M26-OAI-ABSORPTION.md |  |
| 2440 | `M26-OAI-STARHEIGHT` | `P1` | `DONE_STRONG` | M26-OAI-SOLENOIDAL | docs/goal/evidence/M26-OAI-ABSORPTION.md |  |
| 2450 | `M26-OAI-WEISFEILERLEMAN` | `P1` | `DONE_STRONG` | M26-OAI-SOLENOIDAL | docs/goal/evidence/M26-OAI-ABSORPTION.md |  |
| 2460 | `M26-OAI-DEPTHTHREE` | `P1` | `DONE_STRONG` | M26-OAI-STARHEIGHT, M26-OAI-WEISFEILERLEMAN | docs/goal/evidence/M26-OAI-ABSORPTION.md |  |
| 2470 | `M26-OAI-DEGREE-RIGIDITY` | `P1` | `DONE_STRONG` | M26-OAI-DEPTHTHREE | docs/goal/evidence/M26-OAI-ABSORPTION.md |  |
| 2480 | `M26-DELIVERY-8-MERGE` | `P1` | `DONE_STRONG` | M26-ARISTOTLE-SOURCE-SUBMISSION | docs/goal/evidence/M26-DELIVERY-8-MERGE.md |  |
| 2490 | `M26-DELIVERY-12-MERGE` | `P1` | `DONE_STRONG` | M26-DELIVERY-8-MERGE | docs/goal/evidence/M26-DELIVERY-12-MERGE.md |  |
| 2500 | `M26-DELIVERY-15-MERGE` | `P1` | `DONE_STRONG` | M26-DELIVERY-12-MERGE | docs/goal/evidence/M26-DELIVERY-15-MERGE.md |  |
| 2510 | `M27-SPACE-MODEL-COMPILE` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M27-LOGSPACE-EQUIV.md |  |
| 2520 | `M27-SPACE-MODEL-TOTALIZE` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M27-LOGSPACE-TRANSFER.md |  |
| 2530 | `M27-LOGSPACE-TRANSFER` | `P1` | `DONE_STRONG` | M27-SPACE-MODEL-COMPILE, M27-SPACE-MODEL-TOTALIZE | docs/goal/evidence/M27-LOGSPACE-EQUIV.md |  |
| 2535 | `M27-HOST-RANDOMIZED-SPACE` | `P1` | `DONE_STRONG` | M27-LOGSPACE-TRANSFER | docs/goal/evidence/M27-HOST-RANDOMIZED-SPACE.md |  |
| 2538 | `M27-POLYTIME-TO-COBHAM` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M27-POLYTIME-TO-COBHAM.md |  |
| 2540 | `M27-POLYTIME-MODEL-EQUIV` | `P1` | `TODO_NEEDS_DESIGN` | M27-POLYTIME-TO-COBHAM | docs/goal/evidence/M26-OAI-ABSORPTION.md | The exact source tape-machine representation and effective compilation interface need to be selected; computability results alone do not prove polynomial-time equivalence. |
| 2550 | `M27-DEPTH3-HOST` | `P1` | `DONE_STRONG` | M27-POLYTIME-TO-COBHAM, M26-OAI-DEPTHTHREE | docs/goal/evidence/M27-DEPTH3-HOST.md |  |
| 2600 | `M28-STARHEIGHT-SINGLE-SPLIT` | `P1` | `DONE_STRONG` | M26-OAI-STARHEIGHT | docs/goal/evidence/M28-STARHEIGHT-SINGLE-SPLIT.md |  |
| 2610 | `M28-STARHEIGHT-TWO-CLASS` | `P1` | `DONE_WEAK` | M28-STARHEIGHT-SINGLE-SPLIT, M28-STARHEIGHT-TWO-GROUPS | docs/goal/evidence/M28-STARHEIGHT-TWO-CLASS.md | Proved for finite commutative monoids (C contains Z/2), which is inside known height-one results. Open: a class not covered by Pin-Straubing-Therien, e.g. one containing S3; first target: every language recognized by S3 has height at most two. |
| 2620 | `M28-STARHEIGHT-TWO` | `P1` | `TODO_READY` | M28-STARHEIGHT-SINGLE-SPLIT | docs/goal/evidence/M28-STARHEIGHT-TWO.md | Open problem; main gives three. First missing lemma: theorem singleSplit_of_finite {Alphabet : Type u} [Finite Alphabet] [Nonempty Alphabet] (M : Type) [Monoid M] [Fintype M] (T : FreeMonoid Alphabet →* M) : SingleSplit T (then main_two_of_singleSplit gives main_two). |
| 2605 | `M28-STARHEIGHT-TWO-GROUPS` | `P1` | `DONE_STRONG` | M28-STARHEIGHT-SINGLE-SPLIT | docs/goal/evidence/M28-STARHEIGHT-TWO-CLASS.md |  |
| 2606 | `M28-STARHEIGHT-ONE-A4` | `P1` | `DONE_STRONG` | M28-STARHEIGHT-TWO-GROUPS | docs/goal/evidence/M28-STARHEIGHT-ONE.md |  |
| 2607 | `M28-STARHEIGHT-ONE-PURE` | `P1` | `DONE_STRONG` | M28-STARHEIGHT-TWO-GROUPS | docs/goal/evidence/M28-STARHEIGHT-ONE.md |  |
| 2608 | `M28-STARHEIGHT-WREATH-STEP` | `P2` | `DONE_STRONG` | M28-STARHEIGHT-TWO-GROUPS | docs/goal/evidence/M28-STARHEIGHT-ONE.md |  |
| 2609 | `M28-STARHEIGHT-INDEX-THREE` | `P1` | `DONE_STRONG` | M28-STARHEIGHT-ONE-A4 | docs/goal/evidence/M28-STARHEIGHT-ONE.md |  |
| 2611 | `M28-STARHEIGHT-BOURNE-411` | `P1` | `DONE_STRONG` | M28-STARHEIGHT-INDEX-THREE | docs/goal/evidence/M28-STARHEIGHT-ONE.md |  |
| 2612 | `M28-STARHEIGHT-ORDER-LT-20` | `P1` | `DONE_STRONG` | M28-STARHEIGHT-INDEX-THREE | docs/goal/evidence/M28-STARHEIGHT-ONE.md |  |
| 2601 | `M28-STARHEIGHT-Z4-ROT2` | `P1` | `TODO_READY` | M28-STARHEIGHT-Z4-CORE-ONE-ROTATION | docs/goal/evidence/M28-STARHEIGHT-Z4.md | Open. No height-one expression known. Obstruction (proof by hand in the evidence file): a code Y whose blocks return to 0 and whose star contains every word in state 0 contains b c^(2i+1) b but not b c^(2i) b, so Y ∩ b c* b = b c (cc)* b and Y is not star-free; the A4/PM1 method (block classes of a state-tracking star-free code plus Z2 and letter counts) is unavailable. Computation (not Lean-verified): on the 2463 returning words of length ≤ 8, N is not in the rational span of letter counts, all letter-in-state counts of the 21 single-rotation ZMod 4 counters, and the first-return classes to the even states read from the prefixes '' and b; it already fails at length ≤ 6; adding factor counts (length ≤ 4) or factor-at-counter-state counts (length ≤ 3) does not help. Needed: a height-one quantity seeing the characters i^(B+2C) without a state-tracking code. |
| 2602 | `M28-STARHEIGHT-Z4-PM1` | `P1` | `TODO_READY` | M28-STARHEIGHT-Z4-CORE-ONE-ROTATION | docs/goal/evidence/M28-STARHEIGHT-Z4.md | Open in Lean; the mathematics is settled up to one common lemma. First missing lemma: the first-return code X to state 0 of the ±1 walk on ZMod 4 (and, for (a), its blocks not reading x at 0) is star-free: while the walk avoids 0 the automaton is a 3-state path, whose transition monoid is aperiodic, but the repository has no aperiodic-implies-star-free theorem and the A4 code relied on a reset automaton. With it, (a) is B0lang_eq/V0lang_eq verbatim. For (m) the identity 2·N0(u) = Z2(u) + #C+(u) - #C-(u) - #{blocks of bb·u equal to ad} on words u in state 0 (C+: blocks starting with a whose last two letters are not a then an up letter; C-: blocks starting with b or d whose last two letters are a then an up letter; Z2(u) = a at even positions) holds on all 298936 returning words of length ≤ 12 and on random words up to length 400, and C+, C-, C+*, C-* have aperiodic minimal automata (computation, not Lean-verified; docs/goal/evidence/M28-STARHEIGHT-Z4-search.py). Remaining: these star-freeness facts in Lean, the identity as an automaton invariant, the assembly as in coreK_eq. |
| 2613 | `M28-STARHEIGHT-Z4-CORE-ONE-ROTATION` | `P1` | `DONE_STRONG` | M28-STARHEIGHT-ONE-PURE | docs/goal/evidence/M28-STARHEIGHT-Z4.md |  |
| 2614 | `M28-STARHEIGHT-Z4-CORE` | `P1` | `DONE_WEAK` | M28-STARHEIGHT-Z4-ROT2, M28-STARHEIGHT-Z4-PM1, M28-STARHEIGHT-Z4-CORE-ONE-ROTATION | docs/goal/evidence/M28-STARHEIGHT-Z4.md | Z4CoreHeightOne is proved only from the two open cases Z4CoreRot2 (M28-STARHEIGHT-Z4-ROT2: a letter of rotation 2 with a letter of odd rotation) and Z4CorePM1 (M28-STARHEIGHT-Z4-PM1: rotations 1 and 3, no 2). Every other case is proved (M28-STARHEIGHT-Z4-CORE-ONE-ROTATION). |
| 2615 | `M28-STARHEIGHT-INDEX-FOUR` | `P1` | `DONE_WEAK` | M28-STARHEIGHT-Z4-CORE, M28-STARHEIGHT-BOURNE-411 | docs/goal/evidence/M28-STARHEIGHT-Z4.md | Conditional on Z4CoreHeightOne (M28-STARHEIGHT-Z4-CORE), which reduces to the open rows M28-STARHEIGHT-Z4-ROT2 and M28-STARHEIGHT-Z4-PM1. F20 needs both (x ↦ -x has rotation 2, x ↦ 2x rotation 1). |
| 2700 | `M29-EP-STATEMENT` | `P1` | `IN_PROGRESS` | M23-PTS | docs/goal/evidence/M29-EP.md | Exit criterion 1 is met. Exit criterion 2 is not. Stage A outcome (this delivery): no route closed. Route (a) (relaxed nf-abstraction) makes the substitution lemma and \|- in \|-nf immediate, but the abstraction case of the bridge \|-nf in \|-r is exactly ProductNormalizationR; route (b) (Stage B induction with B' = nf(B)) fails for lack of a measure once rules are dependent; no route (c). Proved: for weakly normalizing P, ExpansionPostponement P <-> ProductNormalizationR P. First missing lemma: theorem productNormalizationR_of_wn {S : Type u} {P : Specification S} (hw : SystemWeaklyNormalizing P) : ProductNormalizationR P. Verdict: the gap in Poll's Lemma 10 (abstraction case: the premise Pi A[s] nf(B[s']) : s is needed, only Pi A[s] B[s'] : s is available, and closing it is Theorem 11) is genuine as far as his argument goes, and was not repaired. |
| 2710 | `M29-EP-CLASS` | `P1` | `DONE_STRONG` | M29-EP-STATEMENT | docs/goal/evidence/M29-EP.md |  |
| 2715 | `M29-EP-BEYOND-POLL` | `P1` | `DONE_STRONG` | M29-EP-STATEMENT | docs/goal/evidence/M29-EP.md |  |
| 2720 | `M29-EP` | `P1` | `TODO_READY` | M29-EP-STATEMENT | docs/goal/evidence/M29-EP.md | Open problem since Pollack (1992); TLCA open problem 23. Equivalent form proved: expansionPostponement_iff_sortedSubjectReductionR. Closed for stratified specifications (expansionPostponement_of_stratification, M29-EP-CLASS), so an open case has dependent rules, unbounded levels or no stratification. Stage C (this delivery) stopped under the stop rule: no measure and no counterexample route found for Wdep := W + (o,t,t) (Wdep_not_stratified, Wdep_not_wn) or for lambda-star. First missing lemma: theorem Wdep_expansionPostponement : ExpansionPostponement BeyondPoll.Wdep; in general: theorem sortedSubjectReductionR_all {S : Type u} (P : Specification S) : SortedSubjectReductionR P. Later delivery: unbounded levels closed (M29-EP-LOCAL, expansionPostponement_of_levels); dependent cube corners reduced to ProductNormalizationR (M29-EP-CUBE, stopped under the stop rule); the Wdep lead was not reached. |
| 2730 | `M29-SD-COMPLETE` | `P1` | `DONE_STRONG` | M29-EP-CLASS | docs/goal/evidence/M29-SD-COMPLETE.md |  |
| 2740 | `M29-EP-LOCAL` | `P1` | `DONE_STRONG` | M29-SD-COMPLETE | docs/goal/evidence/M29-EP.md |  |
| 2745 | `M29-SD-FUNCTIONAL` | `P1` | `DONE_STRONG` | M29-SD-COMPLETE | docs/goal/evidence/M29-SD-COMPLETE.md |  |
| 2750 | `M29-EP-CUBE` | `P1` | `DONE_STRONG` | M29-EP-STATEMENT | docs/goal/evidence/M29-EP.md |  |
| 2755 | `M29-EP-CUBE-REST` | `P1` | `IN_PROGRESS` | M29-EP-CUBE | docs/goal/evidence/M29-EP.md | λPω̲ (stop rule fired this delivery after steps 1 and 2 of the plan). Proved before: cube_classification, eraseK_subst (Start/PTSExpansionLambdaPOmegaBar.lean), the kind skeleton Expr.skelK with skelK_subst, skelK_size_pi_obj and skelK_size_pi_kind (Start/PTSExpansionLambdaPOmegaBarSkel.lean). New: step 1, the canonical judgement HasTypeNW (β-normal subjects and types, application result type a normal form of the instantiated codomain, no base-erasure restriction on arguments) with toHasTypeR, normal, rename, lam_inv and HasTypeNR.toHasTypeNW (Start/PTSExpansionLambdaPOmegaBarCanon.lean); step 2, object-level hereditary substitution HasTypeNW.hsubst_obj for PWbar = cubeSpec lambdaPOmegaBar, by induction on the erasure of the variable's type, with not_vis_of_typed (object substitution never changes the erasure of a normal type) (Start/PTSExpansionLambdaPOmegaBarObj.lean). First missing lemma (step 3, constructor-level hereditary substitution by induction on skelK of the kind): theorem HasTypeNW.hsubst_con {Γ : List (Expr Srt)} {N K M B : Expr Srt} (hK : K.isKindB = true) (hN : HasTypeNW PWbar Γ N K) (hM : HasTypeNW PWbar (K :: Γ) M B) : ∃ M' B', Reduces (M.instantiate N) M' ∧ Reduces (B.instantiate N) B' ∧ HasTypeNW PWbar Γ M' B'. Then normalizeNR for λPω̲, theorem lambdaPOmegaBar_productNormalizationR : ProductNormalizationR (cubeSpec lambdaPOmegaBar), and cube_expansionPostponement_of_productNormalizationR. λP2 and λC are impredicative: substituting a type for a type variable changes erasures, so a normalization argument (Poll) is needed. |
| 1385 | `M19-TERM-COUNT-LOWER` | `P1` | `DONE_STRONG` | - | docs/goal/evidence/M19-TERM-COUNT-LOWER.md |  |
| 1386 | `M19-INDEX-CODE-RATE` | `P1` | `DONE_STRONG` | M19-TERM-COUNT-LOWER | docs/goal/evidence/M19-INDEX-CODE-RATE.md |  |
| 1390 | `M19-DESCRIPTION-COST-AUDIT` | `P1` | `DONE_WEAK` | M19-TERM-COUNT-LOWER, M19-INDEX-CODE-RATE | docs/goal/evidence/M19-DESCRIPTION-COST-AUDIT.md | The counting bounds and the comparison with bit length are proved in Start/KolmogorovCount.lean, and the matching lower bounds in Start/KolmogorovCountLower.lean (M19-TERM-COUNT-LOWER): between 3^m and 4^m terms of size <= m, at least 2^m <= (count)^110, i.e. base 2^(1/110), numbers of complexity <= m. What remains for the second exit criterion is the coding rate of indices: the binary realizers cost 55 log2 N + O(1) to write an index below N, so the constant on the counting term of the symmetry law is only justified up to that factor; deciding whether the constant 1 is attainable needs an index code of size log4 N + o(log N), which is not formalised. |

Next: `M14-KRIVINE-SPACE-CLASS`

- Title: The Krivine space bound, stated against DSPACE
- Status: `TODO_READY`
- Open boundary: The memory half is done (M14-KRIVINE-SPACE-CONFIG): the word of a collected state is a work tape of Start/SpaceMachine.lean and its length is that model's memory measure, O(s log s) in the live data. The run-level half of the simulation is now general (M14-SPACE-COMPILE): a realization in the sense of Complexity.Space.Realizes, or a loop program in the sense of Complexity.Space.Prog.realizes_loop, gives DSPACE membership with the bound on every reachable configuration. What is missing is the client's bridge lemma: a tape program performing one pass of Start/KrivineCobBin.lean on the word of a state, with its execution on the encoding of each state of the run, so that a language decided by a lambda-term within a space bound s lands in Complexity.Space.DSPACE (s * log s).
