# M31 — unification of the library

Requested 2026-10-28: "我希望整个项目被统一起来", then "把两阶段做完".

## Definition

The spine of the library is:
- the untyped λ core (`Start/Syntax.lean`, `Start/Reduction.lean`, …);
- computability, with `LambdaComputable f ↔ Partrec f` (`Start/PartialCapstone.lean`) and the
  equivalence of λ with TM2 (`Start/TM2Capstone.lean`);
- the host complexity classes (`Start/ComplexityClasses.lean`, `Start/SpaceMachine.lean`).

The library is unified in two stages.
1. **No islands.** Every part of the import graph is connected to the rest by a *bridge
   theorem*: a theorem whose statement relates notions of both parts. Imports added only to
   connect the graph do not count. `scripts/check_unification.py` measures the connectivity,
   with the aggregators `Capstones` and `Demo` left out.
2. **Foundations.** The basic objects of the large areas are related to the spine by
   equivalences or embeddings, so that intermediate results transfer as well, not only the end
   results. This covers:
   - rigidity and DepthThree (rows `M26-UNIFY-*`);
   - realizability;
   - categorical models;
   - MLTT.

## Baseline (2026-10-28)

`check_unification.py` reported 15 components over 2182 modules (largest 1985). The islands:

| size | modules | row |
|---|---|---|
| 118 | star height | M31-BRIDGE-STARHEIGHT |
| 43 | Weisfeiler–Leman (absorbed) | M31-BRIDGE-WL |
| 13 | Minsky machines, F<: | M31-BRIDGE-MINSKY |
| 5 | STLC, CCC, NbE | M31-BRIDGE-STLC |
| 5 | solenoidal recorders (absorbed) | M31-BRIDGE-SOLENOIDAL |
| 2 + 1 | step complexity, gap theorem; Levin search | M31-BRIDGE-BLUM |
| 2 + 1 | GL; abstract Löb | M31-BRIDGE-LOGIC |
| 2 | size-change termination | M31-BRIDGE-SIZECHANGE |
| 2 | System FC with data types | M31-BRIDGE-SYSTEMFC |
| 1 | CBPV | M31-BRIDGE-CBPV |
| 1 | recursive inseparability | M31-BRIDGE-INSEPARABLE |
| 1 | skeletons of CC^ω | M31-BRIDGE-SKELETON |

Even inside the largest component, few modules build on the λ core:

| area | modules on the λ core |
|---|---|
| rigidity | 0/976 |
| complexity | 80/496 |
| categorical models | 13/74 |
| realizability | 4/40 |
| MLTT | 0/29 |

## 2026-10-28 — first bridges (15 → 9 components)

Each module below was type-checked on its own, against the existing `.lake` oleans of the
modules it imports; the full build is CI's.

- **Recursion theory and Blum complexity** (`Start/BridgeComputability.lean`).
  - `LambdaDecidable p` means the characteristic function of `p` is λ-definable.
  - `lambdaDecidable_iff_computablePred` identifies it with Mathlib's `ComputablePred`, through
    `lambdaComputable_iff_computable`.
  - Restated over λ-definability:
    - inseparability: `Lambda.Inseparable.no_lambda_separation`;
    - the Blum hierarchy: `Complexity.exists_lambda_not_withinFuel`;
    - the gap theorem: `Complexity.exists_gap_lambda`.
  - Levin search is instantiated with `Code.evaln` (`Complexity.levin_optimal_codes`), which
    connects `LevinSearch` to the step measure.
- **Counter machines and F<:** (`Start/BridgeMinsky.lean`).
  - `ComputablePred.of_lambdaDecidable_encode` reduces a predicate on a `Primcodable` type to
    its coded version.
  - The halting problem of `M_u` is not λ-decidable
    (`Minsky.Universal.cm_halts_not_lambdaDecidable`), and neither is F<: subtyping
    (`FsubCode.sub_not_lambdaDecidable`).
- **STLC** (`Start/BridgeStlc.lean`).
  - `CccModel` instantiated at the cartesian closed category of assemblies (`AssemblyCcc`) gives
    the realizability interpretation of STLC over any PCA: `Stlc.asmTm`, its realizer
    `asmTm_tracked`, soundness for βη `asmTm_conv`, and agreement with NbE `asmTm_nf`.
  - The row first planned an erasure to the λ core. Under Church encodings that erasure fails
    the η rules of unit and products, so it was replaced.
- **CBPV** (`Start/BridgeLambdaEnv.lean`, `Start/BridgeCBPV.lean`).
  - The core's `lift 1 k` and `subst v 0` are written as parallel substitutions
    (`Lambda.lift_eq_substEnv`, `Lambda.subst_zero_eq_substEnv`).
  - The source calculus of CBPV is the λ core: `CBPV.STm.toLambda_beta`.
  - Call-by-name and call-by-value steps are core β-steps: `NStep.toLambda`, `VStep.toLambda`.

`check_unification.py` now reports 9 components (largest 2013). The remaining islands are star
height (118), WL (43), Solenoidal (5), GL (2), size-change (2), System FC with data (2), the
abstract Löb theorem (1), and the skeletons of CC^ω (1).

## 2026-10-28 — System FC with data, star height (9 → 7 components)

- **System FC** (`Start/BridgeSystemFC.lean`).
  - `FCBridge.embTy`, `embCo`, `embTm`, `embAx` embed System FC with coercions
    (`SystemFCoerce`) into System FC with data types (`SystemFCTyCon`) at the empty data
    signature. An axiom `A ~ B` becomes the scheme with no parameters.
  - The embedding commutes with renaming, substitution and instantiation of types, coercions
    and terms.
  - It preserves coercion typing (`coTyping_emb`) and typing (`typing_emb`) for closed axioms,
    and maps each step to a step (`step_emb`).
- **Star height** (`Start/BridgeStarHeight.lean`).
  - `Complexity.Space.DFASim.machine` compiles a DFA over `Bool` into a host offline machine
    (`Start/SpaceMachine.lean`). It scans the input once and halts in a copy of the automaton's
    state at the end marker.
  - `reach_iff` describes all of its runs; it is well formed, deterministic and uses one work
    cell.
  - `Complexity.Space.dspace_of_isRegular`: every regular language over `Bool` is in
    `DSPACE (fun _ => 1)`.
  - `GeneralizedStarHeight.regular_starHeight_dspace` states the star-height theorem for such
    languages together with this space bound.

`check_unification.py` reports 7 components (largest 2135).

## 2026-10-28 — Weisfeiler–Leman (7 → 6 components)

- **WL lower bound for host machines** (`Start/BridgeWL.lean`).
  - `WLBridge.tm` compiles a host `DepthThreeLowerBound.FiniteMultiTapeMachine` into a
    `WLTime.TM`:
    - one WL tape per host tape, with the input tape first;
    - symbols numbered with the blank at `0` and the input bits at `1` and `2`;
    - one WL state per host state, plus the halting states `1` and `2`.
  - `WLBridge.rel_run` is the step-for-step simulation.
  - `WLBridge.haltsIn_tm`: when a host run halts with output `b` within `T` steps, the WL run
    halts within `T + 1` steps and accepts iff `b`.
  - **`WLTime.multiTape_lower_bound`**: the WL main theorem for host machines. If a host machine
    decides `k`-WL equivalence within `T n` steps, then `n ^ (c k) ≤ T n + 1` for large `n`.
  - **`WLTime.multiTape_not_poly`**: once `2a < c k`, no host machine decides `k`-WL equivalence
    within time `C (|x| + 1) ^ a`. The host machines are the ones whose polynomial-time deciders
    are in Cobham's class (`Complexity.MultiTapeCobham.inP_of_multiTapeHaltsIn`).

## 2026-10-28 — the last islands (6 → 1 component); the gate

- **GL and the abstract Löb theorem** (`Start/BridgeGL.lean`).
  - `Lambda.Lob.ProvabilitySystem.gl_sound`: GL is sound for every classical provability system,
    under every interpretation of its variables. Löb's axiom is `lob_internal`, `K` is `D2`, and
    necessitation is `D1`. `trueBox_isClassical` shows the hypothesis is satisfiable.
  - `ModalGL.complete_fin`: completeness with a bound on the model size. A formula with `s`
    subformula occurrences that is forced on every transitive irreflexive frame on `Fin m`, for
    every `m ≤ 4 ^ s`, is a theorem. The proof bounds the canonical model by `4 ^ s` worlds
    (`card_canWorld_le`).
  - `ModalGL.Fml.ofNat` is a numbering of all formulas: `Fml.ofNat_toNat` shows every formula
    gets a number.
  - `ModalGL.decideGL` checks every model up to that size; relations and valuations are given
    as bit lists, and forcing is computed by strong recursion on the code. It is correct
    (`decideGL_iff`) and primitive recursive (`decideGL_primrec`, via `Primrec.nat_strong_rec`).
  - Hence `ModalGL.provable_lambdaDecidable`: theoremhood of GL is λ-decidable.
- **Skeletons of CC^ω** (`Start/BridgeSkT.lean`).
  - The erasure into the λ core commutes with renaming and substitution, and every skeleton
    β-step is a core β-step (`SkT.Step.erase`).
  - Erasures are simply typed (`SkT.erase_typing`).
  - So every skeleton term is strongly normalizing (`SkT.sn`, from `Lambda.sn_of_typing`). This
    is the normalization that the M29 module avoided by evaluating in a model.
- **Size-change termination** (`Start/BridgeSizeChange.lean`).
  - A two-counter machine is read as a call graph: one function per label, the two counters as
    parameters, and one call per transition into the program.
  - The size-change graphs are sound for the transitions (`FsubGhelli.CM.descent`).
  - `FsubGhelli.CM.halts_of_sct` and `halts_of_criterion`: size-change termination certifies
    halting on every input. Halting itself is not λ-decidable
    (`Minsky.Universal.cm_halts_not_lambdaDecidable`).
- **Solenoidal recorders** (`Start/BridgeSolenoidal.lean`).
  - A solenoidal machine, given two non-blank symbols for the bits, compiles step for step into
    a one-tape host `FiniteMultiTapeMachine`; `swapBlank` exchanges the blank with the host's
    default symbol.
  - `Solenoidal.Machine.halts_iff_host`: the machine halts on the encoding of a bit string iff
    the host machine halts on the string.
  - `Solenoidal.Recorder.terminal_iff_host`: the recorder reaches a terminal configuration iff
    the host machine halts.

`check_unification.py --strict` now passes: 1 component over 2194 modules.
`scripts/pack_gate.sh` runs it on the packed tree, and `docs/RELEASING.md` lists it among the
gates (M31-UNIFY-GATE).

## 2026-10-28 — phase 2: MLTT erasure and the λ term model

- **MLTT → λ core** (`Start/BridgeMLTTLambda.lean`).
  - `MLTT.Tm.erase` keeps variables, abstractions and applications. `emptyrec P e` erases to
    the erasure of `e`; the type formers erase to `λx. x`.
  - Erasure commutes with renaming, substitution and β-substitution for every term
    (`erase_rename`, `erase_subst`, `erase_inst`).
  - On the pure fragment (`Tm.Pure`: no `zero`, `succ` or `natrec`), a full-reduction step is
    simulated by core reduction (`FStep.erase`), and an MLTT normal form erases to a β-normal
    term (`NfB.erase_normal`).
  - With `MLTT.HasTy.wn`, the erasure of a typable pure term has a β-normal form
    (`HasTy.erase_hasNormalForm`).
  - `natrec` is outside the pure fragment. Its β-faithful erasure needs a fixed-point
    combinator, and that erasure has no normal form.
- **The λ core as a PCA** (`Start/BridgeLambdaPCA.lean`).
  - The term model `LTerm` (terms modulo β-conversion) with `Lambda.K` and `Lambda.S` is a total
    combinatory algebra (`instTCA`; `K_reduces`, `S_reduces`), hence a PCA.
  - Church–Rosser gives common reducts of convertible terms (`conv_common`).
  - Over the term model, with Church numerals as realizers, the morphisms of the natural-number
    assemblies are exactly the computable functions (`TermModel.tracked_iff_computable`).
  - The same holds over Kleene's first algebra (`Kleene.tracked_iff_computable`). So the two
    realizability models have the same arithmetic functions
    (`tracked_termModel_iff_kleene`).

## 2026-10-28 — phase 2: λΠ into MLTT; rigidity foundations

- **λΠ → MLTT with categorical semantics** (`Start/BridgeCwAMLTT.lean`).
  - `LambdaPi.Tm.toPTS` maps `∗` to level `0` and `□` to level `1`. It commutes with
    renaming, substitution and instantiation, and maps β-steps and conversion to those of the
    PTS.
  - `Typing.toPTS` and `Wf.toPTS` send every λΠ derivation in a well-formed context to an
    `MLTT.mlttPTS` derivation: the rules `(∗,∗)` and `(∗,□)` become `(0,0,0)` and `(0,1,1)`.
  - Composed with `MLTT.HasType.toTm`, this gives `Typing.toMLTT`: every λΠ derivation is an
    MLTT derivation.
  - `Typing.mltt_and_model`: the same derivable judgement is also interpreted, uniquely, in
    every CwA model with injective products (`CtxI.total`, `interp_exists_unique`). So the
    categorical semantics of λΠ covers its image in MLTT.
  - No interpretation of MLTT beyond that image is constructed.
- **Rigidity foundations** (`Start/RigidityFoundation.lean`, row M26-UNIFY-RIGIDITY-FOUNDATION).
  - Relativised s-m-n (`exists_index_param`).
  - Consequently, the domain of any function recursive in `A` is decidable in the host jump of
    `A` (`dom_turingReducible_jumpChar`).
  - The two jumps are Turing equivalent for every oracle:
    - host jump ≤ upstream jump, from `jump_re_in` and the upstream `domain_recursive_jump`;
    - upstream jump ≤ host jump, from the upstream `halts_sigma` and the relativised s-m-n.
  - By induction with `jump_mono`, the `n`-th iterates are also equivalent
    (`hostIterate_equiv`).
  - Program translation is uniform in the oracle, in both directions:
    - `exists_index_of_code`: every upstream `OracleCode` has a single host index computing the
      same partial function relative to every oracle (simulations built per constructor);
    - `exists_code_of_index`: every host index `e` has an explicit upstream program
      `phiCode e`. It reads the oracle segment by primitive recursion with queries, searches
      for a converging stage of `Code.evaln`, and reads off the value.
  - Not shown: that these maps are computable as maps between codes. `OracleCode` has no
    `Primcodable` instance.
