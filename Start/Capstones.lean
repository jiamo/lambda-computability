/-
# Capstones: the compiled register of terminal results

A *terminal* module of this library is one whose declarations are not used anywhere else: it is
the end of a chain of statements, not a step in one.  Being terminal is not a defect — a crowning
theorem has no consumers — but an *unregistered* terminal module is indistinguishable from a dead
end.  This module removes that ambiguity: every terminal module is represented here by one or more
`#check`s of the statement it exists to prove.

`#check` is the cheapest registration mechanism Lean offers: it verifies both the name and the
type, and it is checked by the compiler on every build, so the list cannot silently rot.

The mechanical gates that keep this honest live in `scripts/check_closure.py`:

1. **Import closure.**  Every `Start/*.lean` is reachable from `Start.lean` by imports (except a
   consumer of the whole library, such as `Start/Demo.lean`).
2. **Registration.**  Every module is either used by another module or registered here.
3. **Terminal statement first.**  A task is finished when the Lean type it promised appears in
   this file — not when a prose document says so.

Two modules of the library, `Start/TM2Partrec.lean` and `Start/TM2Forward.lean`, track a moving
`Mathlib` interface and are deliberately not registered here; they are used by
`Start/Kolmogorov.lean` and friends, so gate 2 covers them already.
-/

import Start.Boundary
import Start.CreativeIso
import Start.Inseparable
import Start.MyhillIso
import Start.CircuitShift
import Start.CobhamShift
import Start.CookLevinNPHard
import Start.SatToCircuitCob
import Start.ThreeSat
import Start.NPInter
import Start.CwaBiInitial
import Start.CwaLcccOfPi
import Start.CwaStrictFunctor
import Start.CwaStrictSection
import Start.CwaStrictRigid
import Start.CwaStrictLax
import Start.CwaLaxCategory
import Start.CwaLaxWhisker
import Start.CwaLaxInterchange
import Start.CwaLaxBicat
import Start.PbCatBicat
import Start.CwaStrictLaxWhisker
import Start.CwaLaxBiInitial
import Start.CwaStrictFull
import Start.CwaTwoCellUniv
import Start.LambdaPiTypeUnique
import Start.AssemblyCcc
import Start.AssemblyLimits
import Start.AssemblyColimits
import Start.AssemblyNNO
import Start.AssemblyKleene
import Start.AssemblyKleeneBool
import Start.AssemblyProjective
import Start.AsmExRegImage
import Start.AsmExRegRegular
import Start.AsmExRegNotExact
import Start.AsmExRegCoeq
import Start.AsmExRegProj
import Start.AsmExRegEffective
import Start.AssemblySubobject
import Start.AssemblyImage
import Start.AssemblyRegular
import Start.AssemblyGlobalSections
import Start.Modest
import Start.ModestEquiv
import Start.ModestCcc
import Start.ModestColimits
import Start.ModestImage
import Start.ModestNNO
import Start.ModestReflect
import Start.PERNNO
import Start.PERSystemF
import Start.PCAKleene
import Start.KleeneTwoBasic
import Start.KleeneTwo
import Start.PCAMorphism
import Start.Specker
import Start.SpeckerReal
import Start.ComputableReal
import Start.PCATotal
import Start.CwaPiType
import Start.CwaTypeModelSigma
import Start.CwaUnivMorLocal
import Start.DinfWadsworthSharp
import Start.DinfTagBelowSound
import Start.DinfEtaLimit
import Start.GraphNotFullyAbstract
import Start.InfiniteBohmTree
import Start.ScottKoymans
import Start.IntersectionNormalization
import Start.MultiTypes
import Start.KolmogorovPair
import Start.ChaitinIncompleteness
import Start.KolmogorovApprox
import Start.LambdaBetaEta
import Start.LambdaEtaPostpone
import Start.LambdaPiConsistent
import Start.LambdaPiEta
import Start.LambdaPiEtaPostpone
import Start.LambdaPiEtaConfluent
import Start.Rewriting
import Start.LambdaPiInfer
import Start.LambdaPiInitial
import Start.LambdaPiInitialUniv
import Start.LambdaPiInterpTransport
import Start.LambdaPiSelfIso
import Start.LambdaPiSelfMor
import Start.LambdaPiInitialModelHom
import Start.LevinKt
import Start.KolmogorovTime
import Start.LevinSearch
import Start.OracleCone
import Start.LimitLemma
import Start.PostTheoremTwo
import Start.ArithHierarchyProper
import Start.ArithBounded
import Start.ArithComplete
import Start.ArithIndexSets
import Start.OracleJoin
import Start.OracleUniversal
import Start.PostIncomplete
import Start.PostCreative
import Start.RiceCreative
import Start.CreativeCodeSets
import Start.RiceShapiro
import Start.EffectiveOperation
import Start.ScottCurry
import Start.SizeExplosion
import Start.UniformCAInst
import Start.UniformIterateInst
import Start.UniformSigFlat
import Start.UniformStateInst
import Start.UniformStateSubsume
import Start.UniformTMInst
import Start.CwaLaxNotUnique
import Start.LcccPseudofunctor
import Start.LcccBiequivalence
import Start.CwaDemocratic
import Start.CwaLcccOfFull
import Start.CwaStrictifyFull
import Start.CwaStrictifyEquiv
import Start.CwaFamiliesNoStrictify
import Start.KrivineBound
import Start.KrivineHeapCost
import Start.KrivineCobStep
import Start.KrivineCobBin
import Start.KrivineSpaceCalculus
import Start.KleeneNoRetraction
import Start.PCAOrder
import Start.SavitchReach
import Start.SpaceMachine
import Start.SpaceConfigCount
import Start.SavitchVM
import Start.SavitchSpace
import Start.Qbf
import Start.QbfReach
import Start.SpacePadded
import Start.QbfCfgWord
import Start.QbfMachine
import Start.QbfClosed
import Start.QbfPspace
import Start.QbfVarBound
import Start.QbfWord
import Start.QbfWordStream
import Start.CobhamRange
import Start.QbfCobPrefix
import Start.CobhamFields
import Start.QbfCobEqBlock
import Start.QbfCobLevel
import Start.CobhamCond
import Start.CobhamUnary
import Start.CobhamFieldsApp
import Start.QbfMachineDepth
import Start.QbfCobCfg
import Start.QbfCobStepCase
import Start.QbfCobStep
import Start.QbfCobInitAcc
import Start.QbfCobLevels
import Start.QbfCobMachine
import Start.QbfCobReduction
import Start.QbfHard
import Start.QbfCodeSpace
import Start.KrivineSpaceConfig
import Start.OracleCob
import Start.OracleClasses
import Start.OracleSpace
import Start.OracleDiag
import Start.OracleEnum
import Start.BakerGillSolovay
import Start.Relativization
import Start.OracleUse
import Start.Priority

/-! ## Interfaces of the untyped calculus

`Start/Boundary.lean` packages the reduction, encoding and computability development into records
a consumer can use without reaching into the proofs.
-/

#check @ReductionBoundary.roundtrip
#check @EncodingBoundary.fromConcrete
#check @ComputabilityInternalizer.toLambdaComputable

/-! ## Cost of reduction: the size explosion, and a reasonable cost model

`Start/SizeExplosion.lean`: there is a family of terms whose β-normal forms grow exponentially in
the number of steps, so the naive unit-cost model of β-reduction is not reasonable.

`Start/Krivine.lean`, `Start/KrivineDecode.lean` and `Start/KrivineBound.lean` give the positive
half for weak head evaluation.  The Krivine machine keeps the result *shared*, as code together
with an environment, which is what the size explosion forces; its `beta` transitions are exactly
the weak head β-steps of the term it stands for (`Krivine.Trans.decode_wstep`,
`Krivine.Run.decode_reducesIn`), the administrative ones do not change that term
(`Krivine.Trans.decode_eq`), and their number is polynomially bounded
(`Krivine.run_length_le_init`).  So the machine simulates the calculus with polynomial overhead
and the calculus counts the machine's β transitions: `Krivine.eval_cost`.

`Start/KrivineHeap.lean` and `Start/KrivineHeapCost.lean` perform those transitions.  The machine
is implemented on a code table and a heap in which the environments are shared
(`Krivine.Impl.hstep`, correct by `Krivine.Impl.hstep_trans` and `Krivine.Impl.hstep_isNone_iff`);
states are written as words, faithfully (`Krivine.Impl.encState_inj`) and shortly
(`Krivine.Impl.encState_length_le`), and a whole evaluation costs a polynomial in the size of the
term and the number of β-steps, counted in passes over the encoding
(`Krivine.Impl.eval_impl_cost`).

`Start/KrivineCobWord.lean` and `Start/KrivineCobStep.lean` supply the term that performs such a
pass, in the machine model `Complexity.Cob` — Cobham's class of polynomial-time word functions,
the model in which the uniformity of the Cook–Levin reduction is stated here.  Every field of the
encoding is read, skipped or rebuilt by a Cobham term, dereferencing an address is one
(`Krivine.Impl.eval_dropCellsT`), and so is the walk down an environment
(`Krivine.Impl.eval_walkT`).  The transition itself is the single term `Krivine.Impl.stepT`: on
the encoding of a valid state it evaluates to the encoding of the successor state, the empty word
standing for a stuck machine (`Krivine.Impl.eval_stepT`), and its cost in the model — the size of
the Boolean circuits it compiles into — is polynomial in the length of its input
(`Krivine.Impl.stepT_compiles`).  Composed with the transition count, this is the invariance
statement on a machine model of the library: `Krivine.Impl.eval_impl_cob_cost`.

`Start/KrivineSpace.lean` and its satellites do the same for **space**.  The space of an
implementation state is the number of heap cells reachable from its roots, only those cells are
ever read, and the others can be removed (`Start/KrivineSpaceGc.lean`); a collected state is
written in binary with a logarithmic overhead (`Start/KrivineSpaceLog.lean`); and the machine
collected at every transition performs the same run while holding exactly its live data
(`Krivine.Impl.eval_impl_space`).  `Start/KrivineSpaceCalculus.lean` supplies the measure on the
calculus side that this is compared with: the space of a closure is the number of nodes of the
tree that writes it down, and the space of a state is the space of its environment plus that of
the closures on its stack (`Krivine.State.cells`).  The implementation never holds more cells
than the state of the calculus it represents has nodes — sharing can only save
(`Krivine.Impl.space_le_cells_decState`) — so the peak of a collected run is bounded by any
bound on that measure along the run (`Krivine.Impl.gpeak_le_of_cells_le`), and an evaluation
runs in that space, written down with the logarithmic factor
(`Krivine.Impl.eval_impl_space_calculus`).  `Start/KrivineCobBin.lean` closes the loop on the
machine side: a pass over the *binary* encoding, where the fields have fixed width and the
offsets depend only on the width and the length of the stack, is a term of Cobham's class
(`Krivine.Impl.popStackBinT`); it rewrites the encoding of a state with a nonempty stack into
the encoding of the state with its stack popped (`Krivine.Impl.eval_popStackBinT`), and it
compiles into Boolean circuits of size polynomial in the length of its input
(`Krivine.Impl.popStackBinT_compiles`).

`Start/KrivineSpaceConfig.lean` connects that space measure with the machine model of
`Start/SpaceMachine.lean`: the binary word of a collected state is put on the work tape of a
configuration (`Krivine.Impl.spaceConfig`), the memory measure of that configuration is the
length of the word (`Krivine.Impl.spaceConfig_space`), the word still determines the state
(`Krivine.Impl.gcState_eq_of_spaceConfig_eq`), and the tape holds at least one bit per live cell
(`Krivine.Impl.space_le_spaceConfig_space`) and at most `O(S · log S)` bits when the code table,
the stack and the live data fit in a budget `S` (`Krivine.Impl.spaceConfig_space_le_of_budget`),
along a whole collected run in terms of its peak
(`Krivine.Impl.spaceConfig_space_le_of_run_budget`).  This is the memory half of the bridge; a
machine of `Start/SpaceMachine.lean` that *performs* Krivine transitions on that word, which is
what a `Complexity.Space.DSPACE` membership would need, is not formalised.
-/

#check @Lambda.exists_size_explosion
#check @Lambda.exists_size_explosion_steps
#check @Krivine.Trans.deterministic
#check @Krivine.isFinal_iff
#check @Krivine.Trans.decode_eq
#check @Krivine.Trans.decode_wstep
#check @Krivine.Run.decode_reducesIn
#check @Krivine.IsFinal.isWhnf_decode
#check @Krivine.eval_sound
#check @Krivine.exists_final_of_whnIn
#check @Krivine.Trans.maxCode_le
#check @Krivine.Trans.depthBound_le
#check @Krivine.run_length_le
#check @Krivine.run_length_le_init
#check @Krivine.eval_cost
#check @Krivine.Impl.hstep_trans
#check @Krivine.Impl.hstep_isNone_iff
#check @Krivine.Impl.encState_inj
#check @Krivine.Impl.encState_length_le
#check @Krivine.Impl.hstepCost_le
#check @Krivine.Impl.exists_hrun_of_run
#check @Krivine.Impl.eval_impl_cost
#check @Krivine.Impl.eval_dropCellsT
#check @Krivine.Impl.eval_countCellsT
#check @Krivine.Impl.eval_walkT
#check @Krivine.Impl.eval_stepT
#check @Krivine.Impl.stepT_compiles
#check @Krivine.Impl.eval_stepT_hrun
#check @Krivine.Impl.eval_impl_cob_cost
#check @Krivine.State.cells
#check @Krivine.Impl.reach_length_le_cells
#check @Krivine.Impl.space_le_cells_decState
#check @Krivine.Impl.gpeak_le_of_cells_le
#check @Complexity.Cob.eval_takeNT
#check @Krivine.Impl.eval_popStackBinT
#check @Krivine.Impl.popStackBinT_compiles
#check @Krivine.Impl.eval_impl_space_calculus
#check @Krivine.Impl.spaceConfig
#check @Krivine.Impl.spaceConfig_space
#check @Krivine.Impl.gcState_eq_of_spaceConfig_eq
#check @Krivine.Impl.space_le_spaceConfig_space
#check @Krivine.Impl.spaceConfig_space_le_of_budget
#check @Krivine.Impl.spaceConfig_space_le_of_run_budget

/-! ## Recursion theory: Post's problem for many-one reducibility

`Start/PostSimple.lean` and `Start/PostIncomplete.lean`: Post's simple set is recursively
enumerable, its complement is infinite and meets no infinite r.e. set, and it is neither
computable nor many-one complete.  More generally, every simple set (r.e. with immune complement)
is neither computable nor many-one complete.
-/

#check @Lambda.Post.rePred_simpleSet
#check @Lambda.Post.simpleSet_compl_infinite
#check @Lambda.Post.simpleSet_meets_rePred
#check @Lambda.Post.not_computablePred_simpleSet
#check @Lambda.Post.simple_simpleSet
#check @Lambda.Post.Simple.not_computablePred
#check @Lambda.Post.exists_infinite_re_subset
#check @Lambda.Post.Simple.not_manyOneComplete
#check @Lambda.Post.not_manyOneReducible_haltK_simpleSet
#check @Lambda.Post.exists_rePred_not_computable_not_manyOneComplete

/-! ## Recursion theory: creative sets and Myhill's completeness theorem

`Start/PostCreative.lean`: the recursion theorem with parameters; a set whose complement is
productive is many-one complete (Myhill), so every creative set — the halting set in particular —
is many-one equivalent to the halting set and is not simple.  Conversely a many-one complete r.e.
set is creative, so for r.e. sets creativity and many-one completeness coincide.
-/

#check @Lambda.Post.exists_recursion_index
#check @Lambda.Post.creative_haltK
#check @Lambda.Post.manyOneReducible_of_productive_compl
#check @Lambda.Post.Creative.manyOneComplete
#check @Lambda.Post.Creative.manyOneEquiv_haltK
#check @Lambda.Post.creative_iff_manyOneComplete
#check @Lambda.Post.not_creative_simpleSet

/-! ## Recursion theory: the Rice–Shapiro theorem

`Start/RiceShapiro.lean`: an r.e. extensional class of r.e. sets is upward closed and finitely
generated — a set belongs to the class exactly when one of its finite subsets does.  Hence the
class of indices of the empty set, and the class of indices of the total functions, are not r.e.
-/

#check @Lambda.Post.rePred_extensional_mono
#check @Lambda.Post.rePred_extensional_finite_witness
#check @Lambda.Post.rice_shapiro
#check @Lambda.Post.not_rePred_emptyIndex
#check @Lambda.Post.not_rePred_totalIndex

/-! ## Recursion theory: the Myhill–Shepherdson theorem

`Start/EffectiveOperation.lean`: an **effective operation** is a partial computable function on
indices whose value depends only on the partial function named.  Nothing in that definition
restricts the algorithm to reading finitely much of its argument — it is handed a program, a
finite object determining the whole infinite graph — and yet it is forced to behave as if it
did.  An effective operation is **monotone** (`Lambda.Post.effop_mono`) and **compact**
(`Lambda.Post.effop_finite_witness`): a value it takes at an index is already taken at an index
of a finite restriction of the function named.  Together this is Scott continuity
(`Lambda.Post.effop_continuous`).  In particular an operation with a value at the nowhere-defined
function has that value everywhere (`Lambda.Post.effop_const_of_empty`), so no effective
operation can test its argument for divergence.  The proofs are those of Rice–Shapiro: from a
failure one builds a computable family of programs whose membership in the class
`{e | v ∈ Ψ e}` is exactly non-membership in the halting set.
-/

#check @Lambda.Post.phi
#check @Lambda.Post.ExtensionalOp
#check @Lambda.Post.exists_index_eval
#check @Lambda.Post.effop_mono
#check @Lambda.Post.effop_finite_witness
#check @Lambda.Post.effop_continuous
#check @Lambda.Post.effop_const_of_empty

/-! ## Recursion theory: the Scott–Curry theorem

`Start/ScottCurry.lean`: Curry's diagonal term separates nothing.  If two sets of lambda terms
are invariant under convertibility and each contains a closed term, then no computable predicate
on codes answers "yes" on all the codes of the first and "no" on all the codes of the second, so
the two code sets are recursively inseparable.  Scott's theorem, and with it Rice's theorem for
the lambda calculus, is the special case in which the second set is the complement of the first.
Concretely, the codes of the terms convertible with `church m` and those convertible with
`church n` are recursively inseparable whenever `m ≠ n`.
-/

#check @Lambda.scott_curry
#check @Lambda.scott_curry_codeSet
#check @Lambda.not_computablePred_codeSet_of_scott_curry
#check @Lambda.recursivelyInseparable_conv_church

/-! ## Recursion theory: Rice's theorem in effective form

`Start/RiceCreative.lean`: how hard is a convertibility-invariant code set?  If the set contains
no unsolvable term, the diagonal halting set reduces to it many-one — the reduction sends `n` to
the term that searches for a halting stage of the `n`-th machine on the input `n` and then
returns a fixed member of the set, which is unsolvable when the search never succeeds.  Hence
the complement of such a code set is not recursively enumerable, and the code set is creative as
soon as it is recursively enumerable.  Solvability, and convertibility with a Church numeral,
are instances.
-/

#check @Lambda.manyOneReducible_haltK_codeSet
#check @Lambda.not_rePred_compl_codeSet
#check @Lambda.creative_codeSet
#check @Lambda.manyOneReducible_haltK_codeSet_solvable
#check @Lambda.not_rePred_compl_codeSet_solvable
#check @Lambda.manyOneReducible_haltK_codeSet_conv_church

/-! ## Recursion theory: which lambda-calculus code sets are creative

`Start/CreativeCodeSets.lean`: the enumerability half.  Convertibility with a normal term is
reduction to it, so convertibility with a Church numeral is semi-decided by the leftmost run and
the corresponding code set is recursively enumerable; with the effective Rice theorem it is
therefore creative, hence many-one equivalent to Kleene's `K` and not simple.  The
lambda-calculus halting set and the set of codes converging to a numeral are creative for the
same reason, so all of these problems are many-one equivalent.
-/

#check @Lambda.rePred_codeSet_conv_church
#check @Lambda.creative_codeSet_conv_church
#check @Lambda.manyOneEquiv_codeSet_conv_church_haltK
#check @Lambda.creative_codeHasNormalForm
#check @Lambda.creative_codeConverges
#check @Lambda.manyOneEquiv_codeHasNormalForm_codeConverges

/-! ## Algorithmic information theory

`Start/KolmogorovPair.lean`: one half of the symmetry of information, `K(x, y) ≤ K(y) + K(x|y)`
up to an additive constant.

`Start/ChaitinIncompleteness.lean`: Chaitin's incompleteness theorem — a sound, recursively
enumerable system of assertions `K(x) > n` proves only finitely many of them, so from some
threshold on every true assertion `K(x) > c` is unprovable.

`Start/KolmogorovApprox.lean`: Kolmogorov complexity is upper semicomputable — the relation
`K(s) ≤ n` is recursively enumerable (while `n < K(s)` is not), and `K` is the pointwise infimum
of a primitive recursive, non-increasing family of stagewise approximations.

`Start/LevinKt.lean`: Levin complexity `Kt` and its invariance theorem.

`Start/KolmogorovTime.lean`: time-bounded Kolmogorov complexity `K^T` — the least size of a
closed term reducing to the numeral within `T` beta steps — as an instance of the description
systems: it decreases in `T`, lies between plain complexity `K` and the size of the numeral,
agrees with `K` from some bound on, is invariant under a change of interpreter up to an additive
constant and one extra step, is bounded below by Levin's `Kt` minus the logarithm of the bound,
and inherits the counting bound and incompressibility of `K`.

`Start/LevinSearch.lean`: Levin's universal search and its optimality — for any verifiable search
problem the universal search finds a verified answer within a constant factor of any single
program's running time.
-/

#check @Lambda.exists_const_kolm_pair_le
#check @Lambda.exists_const_kolm_pair_le_add
#check @Lambda.chaitin_incompleteness
#check @Lambda.exists_true_unprovable_kolm_lower_bound
#check @Lambda.rePred_kolm_le
#check @Lambda.not_rePred_lt_kolm
#check @Lambda.kolmAt_eventually_eq_kolm
#check @Lambda.kolm_eq_iInf_kolmAt
#check @Lambda.primrec_kolmAt
#check @Lambda.kt_le_ktWith
#check @Lambda.ktime_antitone
#check @Lambda.kolm_le_ktime
#check @Lambda.ktime_le_church
#check @Lambda.ktime_le_iff
#check @Lambda.exists_bound_ktime_eq_kolm
#check @Lambda.ktime_le_ktimeWith
#check @Lambda.ktimeWith_I_le_ktime
#check @Lambda.kt_le_ktime_add_log
#check @Lambda.exists_incompressible_ktime
#check @Lambda.kolm_le_kt
#check @Complexity.levinSearch_sound
#check @Complexity.levin_optimal

/-! ## Complexity: `SAT` and `CIRCUIT-SAT` are `NP`-complete, and P-uniform circuits

`Start/CookLevinNPHard.lean` is the Cook–Levin theorem in the form the library uses: `SAT` is
`NP`-hard, hence `NP`-complete, and `P = NP` iff `SAT ∈ P`.

`Start/CircuitSystem.lean`, `Start/CircuitSatLang.lean`, `Start/SatToCircuit.lean` and
`Start/SatToCircuitCob.lean` add a second `NP`-complete problem, `CIRCUIT-SAT`, with reductions in
both directions: the Tseitin translation reduces it to `SAT`, and the circuit built by the same
right-to-left scan that evaluates a `CNF` reduces `SAT` to it.

`Start/ThreeSat.lean` adds a third: **`k`-SAT** for every `k ≥ 3`, the words that decode to a
satisfiable `CNF` of width at most `k`.  The Tseitin translation has width three, so the term that
reduces `CIRCUIT-SAT` to `SAT` reduces it to `k`-SAT as well; membership in `NP` needs the
finite-state check that a word codes a `CNF` of that width.

`Start/NPInter.lean` closes `NP` under intersection: the witness is the pairing of the two
witnesses — the first component with every bit doubled, the marker `10`, then the second — whose
projections are finite-state transductions, hence Cobham terms.

The remaining modules feed the reduction: renumbering variables of an encoded `CNF`
(`Start/CobhamShift.lean`, `Start/CircuitShift.lean`), and the P-uniformity of the circuit
families produced by the various devices — cellular automata, iterated stages, flat Cobham terms,
finite-state machines and Turing machines.
-/

#check @Complexity.npHard_SAT
#check @Complexity.npComplete_SAT
#check @Complexity.peqNP_iff_inP_SAT
#check @Complexity.CSAT_encCirc_wf
#check @Complexity.polyManyOne_CSAT_SAT
#check @Complexity.Sat.csat_satC_iff
#check @Complexity.Sat.eval_satCircTerm
#check @Complexity.polyManyOne_SAT_CSAT
#check @Complexity.npComplete_CSAT
#check @Complexity.Tseitin.length_le_three_of_mem_toCnf
#check @Complexity.Sat.inP_KCnfWord
#check @Complexity.Sat.inNP_KSAT
#check @Complexity.polyManyOne_CSAT_KSAT
#check @Complexity.npComplete_KSAT
#check @Complexity.npComplete_ThreeSAT
#check @Complexity.fstOf_pairW
#check @Complexity.sndOf_pairW
#check @Complexity.InNP.inter
#check @Complexity.Sat.SAT_eval_shiftTerm
#check @Complexity.Sat.decode_eval_shiftTerm
#check @Complexity.CircCode.eval_shiftCircTerm
#check @Complexity.pUniformDecidable_someOne_of_ca
#check @Complexity.CircCode.out_sregC
#check @Complexity.polyManyOne_SAT_someOne_of_iter
#check @Complexity.sigUniformB_of_flatShape
#check @Complexity.pUniformDecidable_binDiv
#check @Complexity.pUniformDecidable_autoLang_of_state
#check @Complexity.pUniformDecidable_symLang_of_state
#check @Complexity.pUniformDecidable_someOne_of_tm

/-! ## Denotational semantics: the graph model and `D∞`

`Start/GraphNotFullyAbstract.lean`: the graph model is not fully abstract, and `D∞` identifies
strictly more terms than it does.

`Start/DinfTagBelowSound.lean`: **Wadsworth's theorem** — two closed terms are observationally
equivalent, by head normalisation, exactly when they have the same denotation in `D∞`.  The
semantic principle `ScottDinf.TagBelowSound`, which the earlier conditional statements of
`Start/DinfWadsworthSharp.lean` assumed, is proved there: the shape of a finite approximant
(`Start/ApproxShape.lean`) drives a size induction (`ScottDinf.le_ddenot_of_not_tagFail_approx`)
whose only non-structural case, a variable against an infinite η-expansion, is settled by
`Start/DinfTagBelow.lean`.

`Start/DinfEtaLimit.lean`: the infinite η-expansion of the identity, `J = Θ (λ j x y. x (j y))`,
denotes the identity in `D∞`, although it is not β-convertible to it; the two η-limit equations
characterise the identity of `D∞`.
-/

#check @GraphNotFullyAbstract.graph_not_fully_abstract
#check @GraphNotFullyAbstract.dinf_identifies_more_than_graph
#check @ScottDinf.obsEqHnf_iff_ddenot_eq_of_tagBelowSound
#check @ScottDinf.tagBelowSound
#check @ScottDinf.le_ddenot_of_not_tagFail_approx
#check @ScottDinf.le_ddenot_of_not_tagFail_var
#check @ScottDinf.separatesApprox
#check @ScottDinf.ddenot_le_iff_not_tagFail_unconditional
#check @ScottDinf.obsEqHnf_iff_ddenot_eq
#check @ScottDinf.obsEqHnf_iff_not_tagFail
#check @Lambda.approx_direct_shape
#check @ScottDinf.not_ddenot_le_of_tagFail
#check @ScottDinf.eq_dId_of_eta_fixpoint
#check @ScottDinf.ddenot_Jterm_eq_ddenot_id
#check @ScottDinf.not_conv_Jterm_I

/-! ## βη-reduction of the untyped calculus

`Start/LambdaEta.lean`, `Start/LambdaBetaEta.lean`: η-reduction of the untyped calculus
terminates (`Lambda.exists_etaNf`) and is strongly confluent
(`Lambda.etaReduces_church_rosser`); it commutes with β-reduction
(`Lambda.reduces_etaReduces_commute`), and the Hindley–Rosen argument then yields the
**Church–Rosser theorem for βη** (`Lambda.betaEta_church_rosser`), so βη-convertible terms have a
common reduct (`Lambda.betaEtaConv.common_reduct`).  Confluence of β
(`Lambda.confluence_theorem`) and of η separately would not suffice: the union of two confluent
relations need not be confluent, and `Start/LambdaPiEta.lean` exhibits exactly that failure for
the *annotated* terms of `λΠ`.

`Start/LambdaEtaPostpone.lean`: **η can be postponed** — an η-reduction followed by a
β-reduction can be rearranged into a β-reduction followed by an η-reduction
(`Lambda.etaReduces_postpone`), so βη-reduction is exactly `β*` followed by `η*`
(`Lambda.betaEtaReduces_iff`).  The local diagram holds only for a *parallel* η-step
(`Lambda.etaPar`), because a β-redex can be created by a tower of η-expansions.
-/

#check @Lambda.etaReduces_church_rosser
#check @Lambda.exists_etaNf
#check @Lambda.reduces_etaReduces_commute
#check @Lambda.betaEta_church_rosser
#check @Lambda.betaEtaConv.common_reduct
#check @Lambda.betaEtaNf_unique
#check @Lambda.etaReduces_postpone
#check @Lambda.betaEtaReduces_iff

/-! ## Dependent types

`Start/LambdaPiConsistent.lean`: `λΠ` is consistent — the empty context types no variable.

`Start/LambdaPiTypeUnique.lean`: `λΠ` is a **functional** pure type system — two types of the same
term are convertible, so a term is typed by at most one sort, and convertible types of the
syntactic model are equal.

`Start/LambdaPiInfer.lean`: type checking and type inference for `λΠ` are decidable, as running
`Decidable` instances.

`Start/LambdaPiInitial.lean`: **initiality** — the interpretation of `λΠ` in an arbitrary model
with injective products exists and is unique on derivable judgements, and assembles into a
morphism of categories with attributes out of the syntactic model, one that preserves the
universe, the dependent products over it and the codes for those products
(`Start/LambdaPiInitialUniv.lean`), hence compares the two models *as models of `λΠ`* and not
merely as categories with attributes.

`Start/LambdaPiEta.lean`: η-reduction of `λΠ` is confluent and terminating, but **βη-reduction on
raw terms is not confluent**: βη-conversion identifies two abstractions that differ only in their
domain annotation, and Nederpelt's term `λ(x : ∗). ((λ(y : □). y) x)` has two distinct βη-normal
reducts.  This is why the conversion of the calculus is β-only, and why η can enter only through
the *typed* conversion of a model.

`Start/LambdaPiEtaPostpone.lean`: **η can be postponed** — a βη-reduction of `λΠ` is always a
β-reduction followed by an η-reduction (`LambdaPi.betaEtaRed_iff`).  The proof contracts a whole
tower of η-expansions at once, through a parallel η-reduction, which is what repairs the local
diagram that one-step η fails.  Together with β-strong normalization and the fact that an η-step
shrinks a term, postponement gives **strong normalization of `βη`** on typable terms
(`LambdaPi.Typing.betaEta_sn`), so every typable term has a βη-normal form.

`Start/LambdaPiEtaConfluent.lean`: the failure of confluence above is *only* about the domain
annotations.  Erasing every annotation to a fixed dummy sort (`LambdaPi.eraseAnn`), β and η
strongly commute — the critical case, a β-redex directly under an η-redex, is exactly the one
Nederpelt's term refutes for arbitrary annotations — hence `βη` is confluent on erased terms
(`LambdaPi.erased_betaEta_church_rosser`).  Since every term is βη-convertible to its erasure,
two raw terms are βη-convertible exactly when their erasures have a common βη-reduct
(`LambdaPi.betaEtaConv_iff_join`): **Church–Rosser holds for `λΠ` modulo annotations**.  The
consequences the conversion rule needs follow for the η-extended conversion as well: distinct
sorts stay distinct, no sort is convertible to a product, and products are injective in both
arguments.

`Start/Rewriting.lean`: the confluence combinators of all the calculi, proved once for an
arbitrary relation `r : α → α → Prop`.  The reflexive–transitive closure `Rewriting.Star`, the
transitive closure, the union and the generated conversion, with the closure API; the diamond
property implies the strip lemma and confluence (`Rewriting.confluent_of_diamond`); for a
confluent relation conversion is joinability (`Rewriting.conv_iff_joins_of_confluent`); strong
commutation implies commutation of the closures (`Rewriting.commute_of_stronglyCommute`) and two
confluent commuting relations have a confluent union — **Hindley–Rosen**
(`Rewriting.confluent_alt_of_commute`); local postponement through a parallel relation implies
postponement, so that a mixed reduction factors as `r*` then `s*`
(`Rewriting.star_alt_iff_of_postpones`); a relation decreasing a natural-number measure terminates,
and termination transfers to a union along postponement (`Rewriting.sn_alt_of_postponesPlus`); and
**Newman's lemma**, that a terminating locally confluent relation is confluent
(`Rewriting.confluent_of_newman`).  A calculus keeps its own inductive closure and needs only a
bridging lemma `Red t u ↔ Star Step t u` to use all of this.

`Start/LambdaPiModelHom.lean`, `Start/CwaMorVal.lean`, `Start/LambdaPiInterpTransport.lean`:
**the interpretation is natural in the model** — a morphism of models of `λΠ` (a morphism of the
underlying categories with attributes preserving the universe, the products over the small types,
their codes, abstraction and application) carries the interpretation in the source to the
interpretation in the target, for types, for terms and hence for contexts.

`Start/LambdaPiCtxConv.lean`, `Start/LambdaPiSelfIso.lean`, `Start/LambdaPiSelfMor.lean`: **the
syntax of `λΠ` interprets itself by the identity** — a conversion of contexts is an isomorphism of
the syntactic category, the object interpreting a context is isomorphic to that context, and the
self-interpretation is isomorphic, as a morphism of categories with attributes, to the identity
(`LambdaPiSelf.selfIso`).  Transported along the naturality of the interpretation, this gives the
existence half of bi-initiality: every morphism of *models of `λΠ`* out of the syntactic model is
isomorphic to the canonical interpretation (`LambdaPiSelf.isoModelHom`), and between two such
1-cells there is exactly one 2-cell (`LambdaPiSelf.nonempty_unique_twoCell_modelHom`).

`Start/LambdaPiInitialApp.lean`, `Start/LambdaPiInitialModelHom.lean`: **the interpretation is
itself a morphism of models** — application is preserved (`LambdaPiInitial.tmMap_appQ`), the last
clause a morphism of models asks for, so the comparison morphism out of the syntax is a
`LambdaPi.ModelHom` (`LambdaPiInitial.modelHom`).  With the contractibility above, the syntactic
model is **bi-initial** among the models of `λΠ` with injective products
(`LambdaPiInitial.biInitial_syntacticModel`).  The restriction to structure-preserving 1-cells is
necessary:
`LambdaPiBiInitial.not_biInitial_syntacticCModel` shows the syntactic model is not bi-initial among
all coherent models.

`Start/CwaLcccOfPi.lean`: **the converse of the strictification** — a natural Π-structure on the
local-universe model `Cwa.ofPullbacks C` of a category with pullbacks makes `C` locally cartesian
closed (`LcccPullbacks.ofNaturalPiStruct`), so for a category with pullbacks and binary products
the two structures are equivalent (`Cwa.nonempty_naturalPiStruct_ofPullbacks_iff`).  A morphism is
a type, a slice object over its domain is a type over the extended context, and the display map of
their dependent product is the pushforward; naturality of the transposition is the substitution law
of abstraction.

`Start/CwaPiType.lean`, `Start/CwaTypeModelSigma.lean`, `Start/CwaUnivMorLocal.lean`: the
set-theoretic models — the local-universe model of `Type u` has a natural Π-structure, the
universe of small types is closed under dependent sums, and every morphism of a category with
pullbacks is a universe in the strictified model.
-/

#check @LambdaPi.EtaRed.church_rosser
#check @LambdaPi.exists_etaNf
#check @LambdaPi.betaEtaConv_lam_annot
#check @LambdaPi.not_church_rosser_betaEta
#check @LambdaPi.not_typing_var_zero
#check @LambdaPi.Typing.conv_type
#check @LambdaPi.Typing.srt_unique
#check @LambdaPiFull.tyMk_eq_of_conv
#check @LambdaPi.decidableTypable
#check @LambdaPi.decidableTyping
#check @LambdaPi.interp_exists_unique
#check @LambdaPiInitial.functor
#check @LambdaPiInitial.mor
#check @LambdaPiInitial.mor_preservesUniverse
#check @LambdaPiInitial.mor_preservesSmallPi
#check @LambdaPiInitial.mor_preservesPiClosed
#check @LambdaPi.ModelHom
#check @LambdaPi.ModelHom.varVal_map
#check @LambdaPi.TyI.map
#check @LambdaPi.TmI.map
#check @LambdaPi.CtxI.map
#check @LambdaPiSelf.objIso
#check @LambdaPiSelf.selfIso
#check @LambdaPiSelf.isoModelHom
#check @LambdaPiSelf.nonempty_unique_twoCell_modelHom
#check @LambdaPiInitial.tmMap_appQ
#check @LambdaPiInitial.modelHom
#check @LambdaPiInitial.biInitial_syntacticModel
#check @LcccType.luNaturalPiStruct
#check @CwaTypeModel.codeSigma
#check @CwaTypeModel.modelSigma
#check @CwaUniv.preservesUniverseOfHom

/-! ## Intersection types and the filter model

`Start/IntersectionTypes.lean`: the strict intersection type assignment system `λ∩`, whose
strict types are literally the tokens of the graph model.

`Start/FilterModel.lean`: **the graph model is the filter model** — a strict type is assignable
to a term in a basis exactly when the corresponding token belongs to the term's denotation
(`Inter.deriv_iff_mem_denot`).  Subject reduction and subject expansion are immediate, and
typability coincides with head normalisability, hence with solvability
(`Inter.typable_iff_hasHnf`, `Inter.typable_iff_solvable`): "syntactically typable" and
"semantically different from the empty denotation" are the same statement.

`Start/IntersectionNormalization.lean`: **the Coppo–Dezani normalisation theorem** — a term is
typable with an `ω`-free type in an `ω`-free basis exactly when it has a β-normal form
(`Inter.properTypable_iff_hasNormalForm`), and the inclusion is strict
(`Inter.exists_typable_not_properTypable`).
-/

#check @Inter.Deriv
#check @Inter.deriv_iff_mem_denot
#check @Inter.typeSet_eq_denot
#check @Inter.deriv_reduces
#check @Inter.deriv_expansion
#check @Inter.deriv_conv
#check @Inter.typable_iff_hasHnf
#check @Inter.typable_iff_denot_ne_empty
#check @Inter.typable_iff_solvable
#check @Inter.not_typable_omega
#check @Inter.Proper
#check @Inter.hasNormalForm_of_properDeriv
#check @Inter.properDeriv_of_hasNormalForm
#check @Inter.properTypable_iff_hasNormalForm
#check @Inter.exists_typable_not_properTypable

/-! ## Multi types: intersection types that count

`Start/MultiTypes.lean`: the **non-idempotent** intersection types of de Carvalho.  An
intersection is a finite *multiset* of strict types rather than a set, so nothing may be
duplicated for free and each derivation carries a size.  Contexts are outputs, not inputs: there
is no weakening, and an application sums the contexts of its premises.

The engine is the **quantitative substitution lemma** `Multi.substitution`: a derivation of
`M` of size `n` using the multi type `a` at `x`, together with a derivation list for `a` of total
size `m`, yields a derivation of `M[N/x]` of size `p` with `p + |a| = n + m`.  From it,
`Multi.subject_reduction_hstep` shows a head step **strictly decreases** the size of the
derivation, which turns typability into a quantitative statement: `Multi.hnIn_of_deriv` says a
derivation of size `n` reaches a head normal form within `n` head steps, so the type system does
not merely certify termination, it bounds the running time.  Conversely
`Multi.typable_of_isHnf` types every head normal form, and `Multi.not_typable_omega` rules out
`Ω`.

Subject *expansion* is not proved, so de Carvalho's exact equality between derivation size and
head reduction length is not claimed here — only the upper bound.
-/

#check @Multi.Deriv
#check @Multi.substitution
#check @Multi.subject_reduction_hstep
#check @Multi.hasHnf_of_typable
#check @Multi.hnIn_of_deriv
#check @Multi.typable_of_isHnf
#check @Multi.not_typable_omega

/-! ## The lattice of λ-theories

`Start/LambdaTheory.lean`: λ-theories, and the classical chain `B ⊊ Th(𝒫ω) ⊊ Th(D∞) = H*`.
The first inclusion is strict because the graph model equates the unsolvable terms `Ω` and `Ω I`,
which are not β-convertible; the second because `D∞` validates η and the graph model does not;
and the last equality is Wadsworth's theorem.

`Start/InfiniteBohmTree.lean`: the infinite Böhm tree of a term, presented as the directed set of
the direct approximants of its reducts.  Böhm tree equality is an equivalence relation containing
β-conversion strictly and contained in the theory of the graph model.
-/

#check @Lambda.LambdaTheory
#check @Lambda.LambdaTheory.beta
#check @Lambda.LambdaTheory.graph
#check @Lambda.LambdaTheory.dinf
#check @Lambda.LambdaTheory.hstar
#check @Lambda.LambdaTheory.beta_le
#check @Lambda.LambdaTheory.beta_lt_graph
#check @Lambda.LambdaTheory.graph_lt_dinf
#check @Lambda.LambdaTheory.dinf_eq_hstar_closed
#check @Lambda.LambdaTheory.theory_chain
#check @Lambda.LambdaTheory.not_conv_omega_app_omega_I
#check @Lambda.BohmTree
#check @Lambda.BohmEq
#check @Lambda.approx_direct_trans
#check @Lambda.bohmEq_of_conv
#check @Lambda.graph_of_bohmEq
#check @Lambda.exists_bohmEq_not_conv
#check @Lambda.bohmEq_between_beta_and_graph

/-! ## λ-models and reflexive objects: the Scott–Koymans correspondence

`Start/LambdaModel.lean`: the Meyer–Scott axioms of a λ-model, and everything derived from them
— the lifting and substitution lemmas, soundness for β, the combinatory structure, and
extensionality as the validity of η.  `Start/LambdaModelInstances.lean` exhibits the three models
this library builds — the graph model `𝒫ω`, the inverse limit `D∞` and the filter model of the
intersection type system — as instances of that one definition, so their theories are entries in
the lattice above.

`Start/KaroubiLambda.lean`: the **Karoubi envelope** of a λ-model — objects the idempotents
`a ∘ a = a`, morphisms the elements absorbed on both sides — is a cartesian closed category, and
the object `D = λz. z` is **reflexive** in it: `D ⇒ D` is a retract of `D`.

`Start/ReflexiveCcc.lean`: conversely, a reflexive object in an arbitrary cartesian closed
category interprets the untyped terms as morphisms `X ⟶ D` in environments of generalized
elements, and that interpretation is natural in the stage and sound for β-conversion.
`Start/ReflexiveType.lean` is the case of the category of sets, where the interpretation is a
λ-model on the nose, and `Start/ScottKoymans.lean` puts the two directions together and reads off
the λ-theory of a reflexive object.
-/

#check @Lambda.LambdaModel
#check @Lambda.LambdaModel.interp_subst
#check @Lambda.LambdaModel.interp_conv
#check @Lambda.LambdaModel.interp_eta_of_extensional
#check @Lambda.LambdaModel.theory
#check @GraphModel.model
#check @GraphModel.theory_model_eq
#check @ScottDinf.model
#check @ScottDinf.theory_model_eq
#check @Inter.typeSet_eq_model_interp
#check @Lambda.SetReflexive.toModel
#check @Lambda.LambdaModel.karoubiCartesianMonoidal
#check @Lambda.LambdaModel.karoubiMonoidalClosed
#check @Lambda.LambdaModel.reflexive_dRet
#check @Lambda.LambdaModel.toReflexiveObject
#check @ReflexiveCcc.ReflexiveObject
#check @ReflexiveCcc.ReflexiveObject.interp
#check @ReflexiveCcc.ReflexiveObject.interp_reindex
#check @ReflexiveCcc.ReflexiveObject.interp_beta
#check @ReflexiveCcc.ReflexiveObject.interp_conv
#check @ReflexiveCcc.ReflexiveObject.interp_eta_of_iso
#check @ReflexiveCcc.ReflexiveObject.theory

/-! ## Degrees of unsolvability and recursive inseparability

`Start/OracleUniversal.lean`: the relativised enumeration theorem — the partial function
`(e, x) ↦ Φ_e^A(x)` is itself recursive in `A`, so `Φ^A` has a universal index, and the Turing
jump of `A` is recursively enumerable in `A`.

`Start/OracleJoin.lean`: the join of two oracles is the least upper bound of both in the Turing
ordering, so the Turing degrees form an upper semilattice.

`Start/OracleCone.lean`: each oracle computes only countably many partial functions, so there are
uncountably many Turing degrees.

`Start/JumpSigmaOne.lean`: the jump is `Σ₁`-hard, uniformly in the oracle — one computable
reduction sends an r.e. predicate into `A'` for every oracle `A` at once — so every r.e. predicate
is decidable relative to `∅'`.

`Start/JumpApprox.lean`, `Start/LimitLemma.lean`: **Shoenfield's limit lemma** — a set of numbers
is the pointwise limit of a computable sequence of guesses exactly when it is computable from the
halting oracle `∅'`.  Hence every r.e. set is limit computable, and `∅''` is not.

`Start/ArithHierarchy.lean`: the arithmetical hierarchy `Σ⁰ₙ`, `Π⁰ₙ`, `Δ⁰ₙ`, built from the
alternating quantifier prefix over a computable matrix: the prefix dualises, substituting a
computable function into the base argument stays in the class, `Σ⁰ₙ ∪ Π⁰ₙ ⊆ Δ⁰ₙ₊₁`, each level is
closed under conjunction and disjunction, and `Σ⁰ₙ₊₁`, `Π⁰ₙ₊₁` under their own quantifier.  At the
bottom, `Δ⁰₁` is the computable predicates, `Σ⁰₁` the recursively enumerable ones and `Π⁰₁` the
co-r.e. ones.

`Start/PostTheoremTwo.lean`: **Post's theorem at level two** — a predicate is `Δ⁰₂` exactly when it
is the pointwise limit of a computable sequence of guesses, hence (by the limit lemma) exactly
when it is decidable from `∅'`.

`Start/ArithHierarchyProper.lean`: **the arithmetical hierarchy is proper**.  Every level `n + 1`
has a universal predicate — at level one the numbering of the r.e. sets, and one level up by
negating and prefixing an existential quantifier — and the diagonal complement of a universal
`Σ⁰ₙ₊₁` predicate is `Π⁰ₙ₊₁` but not `Σ⁰ₙ₊₁`.  Hence no level equals its own dual, no level is
closed under complement, and each of the three families `Σ⁰ₙ`, `Π⁰ₙ`, `Δ⁰ₙ` grows strictly with
`n`.  The union of the levels — the arithmetical predicates — has no universal predicate at all.

`Start/ArithBounded.lean`: **bounded quantifiers do not raise the level**.  For a computable
bound `b`, each of `Σ⁰ₙ` and `Π⁰ₙ` is closed under `∀ y < b x` and `∃ y < b x`.  The level-zero
case is a primitive recursion over the bound; the induction step uses the collection principle —
finitely many witnesses below a bound can be packed into a single coded list — to pull a bounded
universal quantifier past an existential one, while a bounded existential is absorbed directly
into the outermost existential quantifier.

`Start/ArithComplete.lean`: **completeness at a level of the hierarchy**.  Every level is closed
downwards under many-one reducibility, so it makes sense to call a predicate complete for a level
when it lies in the level and every predicate of the level reduces to it.  The universal
predicates of `Start/ArithHierarchyProper.lean` are complete — hard already for *one-one*
reducibility, by the reduction `x ↦ ⟨e, x⟩` — so every level `n + 1` has complete predicates on
both the `Σ` and the `Π` side.  Complementation exchanges the two notions, completeness travels
upwards along reductions, and any two complete predicates for a level are many-one equivalent.
On the negative side a `Σ⁰ₙ₊₁`-complete predicate is not `Π⁰ₙ₊₁`, not `Δ⁰ₙ₊₁` and not `Σ⁰ₙ`, and in
particular is never computable.  At level one this recovers the halting problem: the set of codes
of terms with a normal form is `Σ⁰₁`-complete, and its complement `Π⁰₁`-complete.  Finally the
union of all levels has no complete predicate at all.

`Start/ArithIndexSets.lean`: **totality is `Π⁰₂`-complete**.  The set of indices whose partial
recursive function is total is `Π⁰₂` — "for every argument there is a halting stage" — and hard
for `Π⁰₂` already under one-one reducibility: a `Π⁰₂` predicate `∀ y, Q ⟨x, y⟩` with `Q`
recursively enumerable is reduced by the s-m-n theorem to the totality of the function that
searches for the enumeration of `⟨x, y⟩`.  Hence totality is not `Σ⁰₂`, not `Δ⁰₂`, neither
recursively enumerable nor co-recursively-enumerable, and its complement is `Σ⁰₂`-complete.  The
halting problem reduces to it but not conversely, so totality is strictly harder than halting.

`Start/Inseparable.lean`: the two halves of the diagonal are disjoint recursively enumerable sets
that no decidable set separates.

`Start/MyhillIso.lean`: one-one equivalent sets of numbers are recursively isomorphic — a
computable bijection of `ℕ` carries one onto the other — and conversely.

`Start/CreativeIso.lean`: a productive set has an injective production function, so a creative set
is one-one complete and therefore recursively isomorphic to Kleene's `K`; conversely a set
recursively isomorphic to `K` is creative, and any two creative sets are recursively isomorphic.
-/

#check @Lambda.Oracle.recursiveIn_universal
#check @Lambda.Oracle.exists_universal_index
#check @Lambda.Oracle.jump_re_in
#check @Lambda.Oracle.joinOracle
#check @Lambda.Oracle.turingReducible_joinOracle_left
#check @Lambda.Oracle.turingReducible_joinOracle_right
#check @Lambda.Oracle.joinOracle_least
#check @Lambda.Oracle.turingDegree_isLUB_join
#check @Lambda.Oracle.countable_cone
#check @Lambda.Oracle.not_countable_turingDegree
#check @Lambda.Oracle.exists_index_repred
#check @Lambda.Oracle.manyOneReducible_jump
#check @Lambda.Oracle.turingReducible_jumpChar_of_repred
#check @Lambda.Oracle.turingReducible_haltingOracle_of_repred
#check @Lambda.Oracle.LimitComputable
#check @Lambda.Oracle.limitComputable_of_turingReducible
#check @Lambda.Oracle.turingReducible_of_limitComputable
#check @Lambda.Oracle.limitComputable_iff_turingReducible_haltingOracle
#check @Lambda.Oracle.limitComputable_of_repred
#check @Lambda.Oracle.not_limitComputable_jumpChar_haltingOracle
#check @Lambda.Arith.SigmaAt
#check @Lambda.Arith.PiAt
#check @Lambda.Arith.DeltaAt
#check @Lambda.Arith.piAt_iff_sigmaAt_not
#check @Lambda.Arith.SigmaAt.of_piAt
#check @Lambda.Arith.sigmaAt_succ_iff
#check @Lambda.Arith.SigmaAt.and
#check @Lambda.Arith.SigmaAt.or
#check @Lambda.Arith.SigmaAt.exists
#check @Lambda.Arith.PiAt.forall
#check @Lambda.Arith.sigmaAt_zero_iff
#check @Lambda.Arith.sigmaAt_one_iff
#check @Lambda.Arith.piAt_one_iff
#check @Lambda.Arith.deltaAt_one_iff
#check @Lambda.Arith.LimitComputablePred
#check @Lambda.Arith.deltaAt_two_iff_limitComputablePred
#check @Lambda.Arith.deltaAt_two_iff_turingReducible_haltingOracle
#check @Lambda.Arith.UnivSigma
#check @Lambda.Arith.UnivPi
#check @Lambda.Arith.univSigma_one
#check @Lambda.Arith.exists_univSigma
#check @Lambda.Arith.UnivSigma.not_sigmaAt_diag
#check @Lambda.Arith.exists_piAt_not_sigmaAt
#check @Lambda.Arith.exists_sigmaAt_not_piAt
#check @Lambda.Arith.sigmaAt_ne_piAt
#check @Lambda.Arith.exists_sigmaAt_not_deltaAt
#check @Lambda.Arith.sigmaAt_proper
#check @Lambda.Arith.piAt_proper
#check @Lambda.Arith.deltaAt_proper
#check @Lambda.Arith.Arithmetical
#check @Lambda.Arith.exists_arithmetical_not_sigmaAt
#check @Lambda.Arith.not_exists_univ_arithmetical
#check @Lambda.Arith.computablePred_ball_lt
#check @Lambda.Arith.computablePred_bex_lt
#check @Lambda.Arith.exists_code_of_ball_exists
#check @Lambda.Arith.SigmaAt.ball_lt
#check @Lambda.Arith.SigmaAt.bex_lt
#check @Lambda.Arith.PiAt.ball_lt
#check @Lambda.Arith.PiAt.bex_lt
#check @Lambda.Arith.SigmaAt.of_manyOne
#check @Lambda.Arith.PiAt.of_manyOne
#check @Lambda.Arith.DeltaAt.of_manyOne
#check @Lambda.Arith.SigmaComplete
#check @Lambda.Arith.PiComplete
#check @Lambda.Arith.UnivSigma.oneOne_hard
#check @Lambda.Arith.UnivSigma.sigmaComplete
#check @Lambda.Arith.UnivPi.piComplete
#check @Lambda.Arith.exists_sigmaComplete
#check @Lambda.Arith.exists_piComplete
#check @Lambda.Arith.exists_sigmaOneOneComplete
#check @Lambda.Arith.exists_piOneOneComplete
#check @Lambda.Arith.SigmaComplete.compl
#check @Lambda.Arith.PiComplete.compl
#check @Lambda.Arith.SigmaComplete.of_manyOne
#check @Lambda.Arith.SigmaComplete.manyOneEquiv
#check @Lambda.Arith.SigmaComplete.not_piAt
#check @Lambda.Arith.SigmaComplete.not_deltaAt
#check @Lambda.Arith.SigmaComplete.not_sigmaAt_lower
#check @Lambda.Arith.PiComplete.not_sigmaAt
#check @Lambda.Arith.SigmaComplete.not_computablePred
#check @Lambda.Arith.sigmaComplete_one_codeHasNormalForm
#check @Lambda.Arith.sigmaComplete_one_codeConverges
#check @Lambda.Arith.piComplete_one_not_codeHasNormalForm
#check @Lambda.Arith.not_exists_arithmetical_complete
#check @Lambda.Arith.Tot
#check @Lambda.Arith.piAt_two_tot
#check @Lambda.Arith.piAt_two_le_one_tot
#check @Lambda.Arith.tot_piComplete
#check @Lambda.Arith.notTot_sigmaComplete
#check @Lambda.Arith.not_sigmaAt_two_tot
#check @Lambda.Arith.not_deltaAt_two_tot
#check @Lambda.Arith.not_rePred_tot
#check @Lambda.Arith.not_rePred_compl_tot
#check @Lambda.Arith.not_computablePred_tot
#check @Lambda.Arith.haltK_le_tot
#check @Lambda.Arith.not_manyOne_tot_haltK
#check @Lambda.Inseparable.diag_disjoint
#check @Lambda.Inseparable.rePred_leftDiag
#check @Lambda.Inseparable.rePred_rightDiag
#check @Lambda.Inseparable.no_computable_separation
#check @Lambda.Inseparable.not_computablePred_leftDiag
#check @Lambda.Inseparable.not_computablePred_rightDiag
#check @Lambda.Myhill.RecIso
#check @Lambda.Myhill.recIso_of_oneOneEquiv
#check @Lambda.Myhill.oneOneEquiv_of_recIso
#check @Lambda.Myhill.recIso_iff_oneOneEquiv
#check @Lambda.Post.exists_injective_productive
#check @Lambda.Post.oneOneReducible_of_productive_compl
#check @Lambda.Post.Creative.oneOneComplete
#check @Lambda.Post.Creative.recIso_haltK
#check @Lambda.Post.Creative.recIso
#check @Lambda.Post.creative_iff_oneOneComplete
#check @Lambda.Post.creative_iff_recIso_haltK
#check @Lambda.recIso_codeSet_conv_church_haltK

/-!
### The 2-category of models, and the rigidity of the interpretation of `λΠ`

`Start/CwaTwoCell.lean`, `Start/CwaBicat.lean` and `Start/CwaBiInitial.lean` add the second
dimension to the models of a dependent type theory: 2-cells between morphisms, the strict
2-category they form, bi-initial objects of a bicategory, and the rigidity of the 2-cells out of
the syntactic model of `λΠ` — a 2-cell is determined by its component at the empty context, so
there is at most one 2-cell into a morphism sending the empty context to a terminal object.

`Start/CwaTwoCellUniv.lean` shows that a 2-cell transports the whole structure an interpretation
of `λΠ` has to respect: the action on terms and on codes, and hence preservation of the universe,
of the dependent products over the small types and of their codes.  The consequence is a
**necessary condition** for a 1-cell out of the syntactic model to be the canonical
interpretation: any 1-cell isomorphic to it preserves the universe and sends the empty context to
a terminal object.
-/

#check @Cwa.TwoCell
#check @Cwa.morCategory
#check @Cwa.TwoCell.whisker_exchange
#check @Cwa.TwoCell.isIso_of_isIso_nat
#check @Cwa.TwoCell.app_ext
#check @Cwa.CModel.instBicategory
#check @Cwa.CModel.instStrict
#check @CategoryTheory.Bicategory.BiInitial
#check @CategoryTheory.Bicategory.BiInitial.nonempty_iso
#check @CategoryTheory.Bicategory.BiInitial.nonempty_equiv
#check @LambdaPiBiInitial.app_eq_of_app_empty
#check @LambdaPiBiInitial.subsingleton_twoCell
#check @LambdaPiBiInitial.nonempty_iso_mor_iff
#check @Cwa.TwoCell.tmMap_eq
#check @Cwa.TwoCell.codeMap_eq
#check @Cwa.TwoCell.preservesUniverse
#check @Cwa.TwoCell.preservesSmallPi
#check @Cwa.TwoCell.preservesPiClosed
#check @LambdaPiBiInitial.preservesUniverse_of_twoCell
#check @LambdaPiBiInitial.isTerminal_empty_of_iso
#check @LambdaPiBiInitial.iso_mor_necessary

/-!
### Strictification is a functor

`Start/CwaStrictFunctor.lean` closes the gap between the two halves of the strictification: a
category with pullbacks is a model of a dependent type theory (`Cwa.ofPullbacks`) and a
pullback-preserving functor is a morphism of the resulting models
(`Cwa.morOfPullbackPreserving`), and these two constructions agree with identities and composites
— the comparison isomorphism of an extended context is the canonical map between two pullbacks,
hence the identity for the identity functor and a composite for a composite.  Categories with
pullbacks and pullback-preserving functors are therefore a category (`Cwa.PbCat`) and
strictification an honest functor from it to the category of models (`Cwa.strictification`).
This is the 1-categorical skeleton of the passage from locally cartesian closed categories to
models of `λΠ`.
-/

#check @Cwa.luExtIso_id
#check @Cwa.luExtIso_comp
#check @Cwa.morOfPreservesPullbacks_id
#check @Cwa.morOfPreservesPullbacks_comp
#check @Cwa.PbCat.instCategory
#check @Cwa.strictification

/-!
### Strictification is a strict section, and it is rigid in the 2-dimensional direction

`Start/CwaStrictSection.lean` reads off the category of contexts of a model functorially
(`Cwa.Model.ctx`) and proves that the round trip through strictification is the underlying-category
functor of `Cwa.PbCat` *on the nose* (`Cwa.strictification_comp_ctx`).  Strictification is
therefore faithful, and it reflects isomorphisms: a pullback-preserving functor whose induced
morphism of models is invertible is already an isomorphism of categories with pullbacks, because
the underlying functor of the inverse morphism is a strict two-sided inverse, hence half of an
equivalence, hence preserves pullbacks.

`Start/CwaStrictRigid.lean` shows that the passage cannot be made 2-functorial for the 2-cells of
`Start/CwaTwoCell.lean`.  A type of a strictified model is a whole local universe, so a 2-cell
between strictified morphisms must carry the local universe of an identity map to that of the
other morphism; this forces the two functors to agree on objects and pins the component of the
2-cell down to the transport along that equality.  Hom-categories of strictified morphisms are
thus discrete, while the natural transformation `Cwa.coyonedaConst` between two
pullback-preserving endofunctors of `Type` admits no 2-cell at all between the induced morphisms
of models.

`Start/CwaLaxTwoCell.lean` and `Start/CwaStrictLax.lean` carry out the weakening this forces.  A
**lax 2-cell** replaces the equality of types of a 2-cell by a map of extended contexts over the
base; a strict 2-cell is the special case of the transport (`Cwa.TwoCell.toLax`), and lax 2-cells
still have identities and vertical composition.  For them the 2-dimensional structure survives: a
natural transformation of pullback-preserving functors induces a lax 2-cell
(`Cwa.laxTwoCellOfNatTrans`), functorially (`Cwa.laxTwoCellOfNatTrans_id`,
`Cwa.laxTwoCellOfNatTrans_comp`), so strictification is 2-functorial for the lax 2-cells; in
particular `Cwa.coyonedaConst`, which admits no strict 2-cell, does induce a lax one
(`Cwa.nonempty_laxTwoCell_id_coyoneda`).

`Start/CwaLaxCategory.lean` checks that the lax 2-cells really organize the morphisms of models
into a category: vertical composition of lax 2-cells is associative and unital
(`Cwa.LaxTwoCell.vcomp_assoc`, `Cwa.LaxTwoCell.id_vcomp`, `Cwa.LaxTwoCell.vcomp_id`), so the
morphisms `T ⟶ S` and the lax 2-cells between them form a category (`Cwa.laxMorCategory`), and the
passage from a strict 2-cell to a lax one is an injective functor out of the hom-category of
strict 2-cells (`Cwa.laxInclusion`, `Cwa.TwoCell.toLax_injective`).  The proofs run through the
functoriality of the substituted map of extended contexts (`Cwa.subOver_id`, `Cwa.subOver_comp`,
`Cwa.subOver_subOver`), which is the lax replacement for the composition of the canonical maps
`Cwa.substCompare_comp` used by the strict 2-cells.

`Start/CwaLaxWhisker.lean` adds the horizontal direction: a lax 2-cell is whiskered by a morphism
of models on either side (`Cwa.LaxTwoCell.whiskerLeft`, `Cwa.LaxTwoCell.whiskerRight`), and both
whiskerings are functorial in the 2-cell (`Cwa.LaxTwoCell.whiskerLeft_id`,
`Cwa.LaxTwoCell.whiskerLeft_vcomp`, `Cwa.LaxTwoCell.whiskerRight_id`,
`Cwa.LaxTwoCell.whiskerRight_vcomp`).  Whiskering on the right transports the comparison through
the morphism, which works because a morphism of models carries the substituted map of extended
contexts to the substituted map of the image (`Cwa.morOver_subOver`).

`Start/CwaLaxRigid.lean` then removes what looked like the obstruction to the interchange law.  The
comparison carried by a lax 2-cell is *not* data: it is the map into the pullback prescribed by the
two laws, so a lax 2-cell is determined by its natural transformation (`Cwa.LaxTwoCell.ext_of_nat`)
and every natural transformation of the functors on contexts underlies exactly one
(`Cwa.LaxTwoCell.ofNat`, `Cwa.LaxTwoCell.equivNatTrans`).  The interchange law is therefore the
interchange law for natural transformations (`Cwa.LaxTwoCell.whisker_exchange` in
`Start/CwaLaxInterchange.lean`), for two arbitrary lax 2-cells and not merely when one of them is
strict.

With it, `Start/CwaLaxBicat.lean` assembles the **2-category of models with the lax 2-cells**
(`Cwa.LaxCModel.instBicategory`, strict by `Cwa.LaxCModel.instStrict`), whose 2-cells are exactly
the natural transformations (`Cwa.LaxCModel.homEquivNatTrans`).  `Start/PbCatBicat.lean` gives the
matching 2-category of categories with pullbacks, and `Start/CwaStrictLaxWhisker.lean` proves that
strictification carries whiskering to whiskering (`Cwa.laxTwoCellOfNatTrans_whiskerLeft`,
`Cwa.laxTwoCellOfNatTrans_whiskerRight`), so it is 2-functorial for the lax 2-cells in both
dimensions.  Finally `Start/CwaLaxBiInitial.lean` states bi-initiality in the lax 2-category and
reduces it to a question about the functors on contexts (`Cwa.LaxCModel.biInitial_iff`); the
syntactic model of `λΠ` is not bi-initial there either
(`LambdaPiLaxBiInitial.not_biInitial_laxSyntacticCModel`), for the same reason as in the strict
case, and for the models with injective products the two existence clauses hold while the
uniqueness clause is reduced to the uniqueness of natural transformations and is not claimed.
-/

#check @Cwa.Model.ctx
#check @Cwa.PbCat.toCat
#check @Cwa.strictification_comp_ctx
#check @Cwa.strictification_faithful
#check @Cwa.strictification_reflects_iso
#check @Cwa.twoCell_strict_obj_eq
#check @Cwa.twoCell_strict_nat_app
#check @Cwa.subsingleton_twoCell_strict
#check @Cwa.twoCell_strict_self_nat
#check @Cwa.isEmpty_twoCell_id_coyoneda
#check @Cwa.LaxTwoCell
#check @Cwa.TwoCell.toLax
#check @Cwa.LaxTwoCell.vcomp
#check @Cwa.laxTwoCellOfNatTrans
#check @Cwa.laxTwoCellOfNatTrans_id
#check @Cwa.laxTwoCellOfNatTrans_comp
#check @Cwa.nonempty_laxTwoCell_id_coyoneda
#check @Cwa.subOver_comp
#check @Cwa.subOver_subOver
#check @Cwa.LaxTwoCell.id_vcomp
#check @Cwa.LaxTwoCell.vcomp_id
#check @Cwa.LaxTwoCell.vcomp_assoc
#check @Cwa.laxMorCategory
#check @Cwa.laxInclusion
#check @Cwa.TwoCell.toLax_injective
#check @Cwa.morOver
#check @Cwa.morOver_subOver
#check @Cwa.LaxTwoCell.whiskerLeft
#check @Cwa.LaxTwoCell.whiskerRight
#check @Cwa.LaxTwoCell.whiskerLeft_vcomp
#check @Cwa.LaxTwoCell.whiskerRight_vcomp
#check @Cwa.LaxTwoCell.ext_of_nat
#check @Cwa.LaxTwoCell.ofNat
#check @Cwa.LaxTwoCell.equivNatTrans
#check @Cwa.LaxTwoCell.whisker_exchange
#check @Cwa.PbCat.instBicategory
#check @Cwa.LaxCModel.instBicategory
#check @Cwa.LaxCModel.instStrict
#check @Cwa.LaxCModel.homEquivNatTrans
#check @Cwa.laxTwoCellOfNatTrans_whiskerLeft
#check @Cwa.laxTwoCellOfNatTrans_whiskerRight
#check @Cwa.LaxCModel.biInitial_iff
#check @LambdaPiLaxBiInitial.not_biInitial_laxSyntacticCModel
#check @LambdaPiLaxBiInitial.nonempty_laxTwoCell_modelHom

/-!
### How far strictification is from an equivalence: fullness

`Start/CwaStrictFull.lean` settles the remaining 1-categorical question about the comparison
between models of a dependent type theory and categories with pullbacks: is strictification
*full*?  The answer has two halves.

On the underlying functors it is.  A morphism of models out of a strictified category carries the
extension square of a local universe to a pullback (`Cwa.isPullback_map_extend`), and *every*
pullback square is isomorphic to one of those, because a morphism `p : Y ⟶ Γ` is presented by the
local universe `LuTy.ofHom p`.  Hence the functor on contexts of an arbitrary morphism of
strictified models preserves pullbacks with no hypothesis at all
(`Cwa.Mor.map_isPullback`, `Cwa.Mor.preservesLimitsOfShape_fnc`), so it is already a morphism of
`Cwa.PbCat` (`Cwa.exists_pbCatHom_fnc`).

On types it is not.  What a morphism of models chooses is a *presentation* of a type, and that is
pinned down only up to isomorphism over the base (`Cwa.tyMapCompareIso`,
`Cwa.tyMapCompareIso_hom_disp`).  In the indiscrete category on two objects (`Cwa.Chaotic`) every
hom-set is a singleton, so replacing the total space of every local universe by the other object
of the category is a morphism of models over the identity functor (`Cwa.chaoticSwapMor`) which no
functor induces: `Cwa.not_full_strictification`.

So the honest 1-categorical statement is that strictification is faithful, reflects isomorphisms,
is full on the underlying functors and full up to a canonical isomorphism of presentations — but
not full on the nose.  Any equivalence with locally cartesian closed categories has to be stated
up to isomorphism of types, just as the failure of 2-functoriality in `Start/CwaStrictRigid.lean`
already indicated for the 2-cells.
-/

#check @Cwa.isPullback_map_extend
#check @Cwa.Mor.map_isPullback
#check @Cwa.Mor.preservesLimitsOfShape_fnc
#check @Cwa.exists_pbCatHom_fnc
#check @Cwa.tyMapCompareIso
#check @Cwa.tyMapCompareIso_hom_disp
#check @Cwa.chaoticSwapMor
#check @Cwa.not_full_strictification

/-!
### Realizability: partial combinatory algebras and assemblies

`Start/PCA.lean` defines partial combinatory algebras and proves combinatory completeness:
bracket abstraction turns any applicative expression into an element of the algebra.
`Start/PCATotal.lean` records that every total combinatory algebra — in particular every λ-model
of `Start/LambdaModel.lean` — is one, and `Start/PCAKleene.lean` builds Kleene's first algebra
`K₁`, the natural numbers under Turing application, using the s-m-n theorem.

`Start/KleeneTwoBasic.lean` and `Start/KleeneTwo.lean` build the other pole of the picture,
**Kleene's second algebra `K₂`**: Baire space `ℕ → ℕ` with the application of *function*
realizability, where `α | β` answers queries about finite initial segments of `β`.  The first
module sets up the application (`Realizability.KleeneTwo.appK`), proves Kleene's continuity
principle — a value of `α | β` is produced by a finite initial segment of `β` — and constructs
the *canonical associate* of a continuous operation on Baire space, which yields the combinator
`k`.  The combinator `s` cannot be produced that way, because the operation
`(α, β) ↦ (associate of γ ↦ (α|γ)|(β|γ))` must itself be continuous in `α` and `β`; the second
module builds it from an explicit finite approximation, proves the approximation sound and
complete, and concludes that `K₂` is a partial combinatory algebra
(`Realizability.KleeneTwo.instPCABaire`).  The application is genuinely partial: an element that
never answers applies to nothing.

`Start/PCAMorphism.lean` adds the morphisms of Longley's programme, **applicative morphisms**:
a total relation assigning to each element of `A` a nonempty set of representatives in `B`,
tracked by a single element of `B`.  Every PCA has an identity morphism, realized by `λ x y. x y`
from combinatory completeness, applicative morphisms compose, and there is a morphism `K₁ → K₂`
sending a number to the constant function with that value: number realizability lands inside
function realizability.  Continuity has a Brouwerian consequence: no element of `K₂` decides
whether its argument is the zero function (`Realizability.KleeneTwo.no_zero_test`).

`Start/KleeneNoRetraction.lean` shows that the inclusion cannot be reversed.  Applicative
morphisms `K₂ → K₁` do exist — the trivial one, where every element of the target represents
every element of the source (`Realizability.AppMorphism.trivialMor`) — so the statement has to
ask that the target read something back, and then there is none
(`Realizability.KleeneTwo.no_separatesBits_morphism`): the projections `β ↦ β n` are continuous,
hence are elements of `K₂`, so a representative of a `0/1`-valued `β` together with the realizer
would determine every value of `β`, and a set of naturals would be named by a natural number.

`Start/PCAOrder.lean` turns this into an order.  Ordering the partial combinatory algebras by the
mere existence of an applicative morphism (`Realizability.PCALe`) gives a preorder that is
**degenerate** — the trivial morphism makes every algebra precede every other one, so all of them
are equivalent (`Realizability.pcaEquiv_of_any`).  The informative order is carried by the
morphisms that *decide* their representatives (`Realizability.AppMorphism.Decides`: one element of
the target tells representatives of the combinator `k` from representatives of `k i`); the
identity decides and decidable morphisms compose, so this is again a preorder
(`Realizability.pcaLeD_refl`, `Realizability.pcaLeD_trans`), and in it the two Kleene algebras are
separated: `Realizability.KleeneTwo.kOneToTwo_decides` makes `K₁ ⪯ K₂`, while
`Realizability.KleeneTwo.not_decides` shows no morphism `K₂ → K₁` decides — a decision of the two
combinators already separates bits — whence `Realizability.KleeneTwo.kleene_strict`: `K₁ < K₂`.

`Start/Specker.lean` takes the first step from function realizability into **computable
analysis**.  A *Specker sequence* is a computable, nondecreasing, bounded sequence of rationals
whose limit is not computable, so the monotone convergence theorem fails effectively.  The
sequence `Lambda.speckerVal` adds `2^{-(k+1)}` for every index `k < n` that has entered the
halting set by stage `n`; it is nondecreasing (`Lambda.speckerVal_monotone`), bounded by `1`
(`Lambda.speckerVal_lt_one`) and computable, its numerators over `2^n` being a computable
function of `n` (`Lambda.computable_speckerNum`, `Lambda.speckerVal_eq`).  Yet it has **no
computable modulus of convergence** (`Lambda.specker_no_computable_modulus`): from one, the
halting set of `Start/KleeneK.lean` would be decidable, contradicting the undecidability of `K`.

`Start/SpeckerReal.lean` takes the limit.  `Lambda.speckerReal` is the supremum of the sequence
in `ℝ`, and `Lambda.specker_limit_not_computable` shows that this real number is **not
computable**: no computable `f : ℕ → ℕ` has `|speckerReal - f m / 2 ^ m| < 2 ^ (-m)` for every
`m`.  The proof searches, with `Nat.rfind`, for a stage of the sequence beyond the lower bound
supplied by `f`; the stage found is close enough to the limit that the elements of the halting
set below the precision have all appeared, so the halting set would be decidable.  This is the
classical statement of Specker's theorem: a computable, nondecreasing, bounded sequence of
rationals can converge to a non-computable real.

`Start/ComputableReal.lean` runs the construction of **computable analysis** on top of `K₂`.  A
real number is presented by a *name* — a sequence of coded rationals converging to it with error
at most `2 ^ (-i)` at stage `i` (`Realizability.KleeneTwo.IsName`) — and a function `f : ℝ → ℝ`
is computable when a single element of `K₂` turns every name of `x` into a name of `f x`
(`Realizability.KleeneTwo.Realizes`).  Such a function is **continuous**, with an explicit
modulus (`Realizability.KleeneTwo.Realizes.exists_modulus`,
`Realizability.KleeneTwo.IsComputableFun.continuous`): the finite initial segment of the name of
`x` that the computation of the `k`-th output rational reads is a modulus, because every point
near enough to `x` has a name beginning with that same segment — this is the gluing lemma
`Realizability.KleeneTwo.glue_isName`, and it is where the spare half of a *fast* name is spent.
So the step function is not computable (`Realizability.KleeneTwo.not_isComputableFun_step`)
although each of its values is a computable real, while the identity and the constants are
(`Realizability.KleeneTwo.isComputableFun_id`,
`Realizability.KleeneTwo.isComputableFun_const`).  This is the type-two counterpart of the
Kreisel–Lacombe–Shoenfield theorem, which is the same statement for Markov computability and is
not proved here.

`Start/Assembly.lean` and `Start/AssemblyCcc.lean` build the category of assemblies over an
arbitrary PCA and show it is cartesian closed: sets with realizers, tracked maps as morphisms,
Church pairs as products and tracked function spaces as exponentials.

`Start/AssemblyLimits.lean` adds equalizers, hence all finite limits, and
`Start/AssemblyNNO.lean` a **natural numbers object**: the assembly of natural numbers realized
by the Church numerals satisfies Lawvere's universal property.

`Start/AssemblyColimits.lean` adds the finite colimits: the empty assembly is initial, the
coproduct is the disjoint union with a boolean tag stored alongside the realizer — the copairing
reads the tag, selects one of the two trackers and applies it, so no branch is evaluated
speculatively — and the coequalizer is the quotient of the codomain carrying the realizers of its
representatives.  So `Asm(A)` is finitely complete and finitely cocomplete.

`Start/AssemblySubobject.lean` classifies the sub-assemblies: the assembly of propositions, on
which every element of the algebra realizes everything, receives from each predicate `P` on `X` a
characteristic map, and the sub-assembly cut out by `P` is the pullback of `true` along it — the
unique map with that property.  This is a classifier for the *regular* subobjects, the ones whose
realizers are inherited from the ambient assembly, not for every mono: `Asm(A)` is not a topos.

`Start/AssemblyImage.lean` identifies the monomorphisms with the injections and the epimorphisms
with the surjections, and factors every morphism through its **image**: the set-theoretic image,
where a point is realized by the realizers of its preimages.  That first factor is a *strong*
epimorphism — in a square against a mono the diagonal filler is computed by the tracker of the
top map — so `Asm(A)` has strong epi-mono factorizations and images.  The image is not in general
the sub-assembly of the codomain on the image set: a point of the image is realized only by the
realizers it inherits from its preimages, which is why the classifier above sees only the regular
subobjects.

`Start/AssemblyRegular.lean` identifies those strong epimorphisms computationally: they are the
morphisms that **lift realizers**, i.e. for which a single element of the algebra turns a realizer
of a point of the codomain into a realizer of one of its preimages.  Lifting combinators are
transported along the explicit pullback — the sub-assembly of the product where the two maps
agree — by applying the tracker of the base map, lifting, and pairing with the realizer one
started from.  So strong epimorphisms are stable under pullback and `Asm(A)` is a regular
category.

`Start/AssemblyGlobalSections.lean` relates assemblies to bare sets: forgetting the realizers is
left adjoint to the indiscrete assembly, in which everything realizes everything; the indiscrete
functor is fully faithful, the carrier of an assembly is its set of global sections — the maps out
of the terminal assembly — and the classifier above is the indiscrete assembly on `Prop`.

`Start/AssemblyKleene.lean` specialises all of this to Kleene's first algebra, where a number
realizes itself.  The morphisms of that standard numbers assembly are **exactly the computable
functions** — one direction is the s-m-n theorem, the other reads a tracker as a code — and the
diagonal function `n ↦ φₙ(n) + 1` is not among them, so the global sections functor is not full
and `Asm(K₁)` is not the category of sets.  The function object of that assembly therefore has the
computable functions as its elements and their indices as its realizers, and out of the product of
two copies of it the tracked maps are exactly the computable functions of two arguments, Church
pairing and the two projection combinators being computable.
Iterating a tracked endomorphism is itself partial recursive, so the standard numbers assembly is
a natural numbers object; since a natural numbers object is unique up to isomorphism, it is
isomorphic to the Church numeral one, which is the effective interconversion of numbers and
numerals.

`Start/AssemblyKleeneBool.lean` adds the booleans of `Asm(K₁)`, `true` realized by `1` and `false`
by `0`, and the same analysis of their maps: a boolean-valued function of the numbers is tracked
exactly when it is computable, so a predicate on the numbers has a characteristic morphism into
the booleans exactly when it is a **computable predicate**.  Self-halting is not computable — the
machine that diverges exactly when a putative decision procedure says "halts" refutes it on its
own index — so it has no characteristic boolean map, in either polarity: unlike the object of
propositions above, the booleans of `Asm(K₁)` classify no sub-assembly cut out by an undecidable
predicate — and self-halting *is* recursively enumerable, a predicate being recursively
enumerable exactly when it is the domain of convergence of an element of `K₁`.  The booleans are
nevertheless the coproduct `1 + 1`: the tag of a boolean can be read off
effectively, so the two points `false` and `true` exhibit the booleans as a coproduct of two
copies of the terminal assembly.

`Start/AssemblyProjective.lean` identifies the objects that are projective for those covers.  An
assembly is **partitioned** when each of its points has exactly one realizer; such an assembly is
projective for the morphisms that lift realizers, because a map out of it is lifted by composing
its tracker with the lifting combinator — this is the constructive content of the axiom of choice
in realizability.  Every assembly is covered by a partitioned one, namely by the pairs `(a, x)`
with `a` a realizer of `x`, so `Asm(A)` has enough regular projectives; and conversely a regular
projective is a retract of that cover, hence isomorphic to a partitioned assembly, so the regular
projectives are exactly the assemblies isomorphic to partitioned ones, a class closed under
binary products.  Projectivity for *all*
epimorphisms is strictly stronger and fails already over `K₁`: the standard numbers assembly is
partitioned, hence regular projective, but the identity map onto the indiscrete assembly on the
numbers is an epimorphism that does not lift realizers, and along it the non-computable diagonal
function has no lift.

`Start/AsmExReg.lean` and its satellites begin the **exact completion** of that regular category,
the construction whose result is the effective topos.  An object is an assembly together with a
pseudo-equivalence relation on it, presented computationally: proofs of `x ~ y` carry realizers,
their two endpoints are computable from the proof, and reflexivity, symmetry and transitivity are
each witnessed by an element of the algebra.  A morphism is a function that transports proofs
uniformly, two such being identified when a single element of the algebra turns a realizer of `x`
into a proof that the two values are related.  The assemblies embed by taking equality, and the
embedding is full and faithful; it preserves the terminal object and binary products.  The
completion has finite limits: binary products are the pairs of proofs, and the equalizer of two
maps carries at each endpoint a witness that they agree there — witnesses that are data, not
merely assumptions, which is what makes the endpoints of a proof computable.  Finally every
object is a quotient of an assembly: the assembly of proofs of a relation has two endpoint maps,
and the canonical map from the base is their coequalizer, so it is a regular epimorphism.  Every
morphism factors as an epimorphism, the identity on points, followed by a monomorphism, the
middle object being the base of the source with the relation pulled back along the map.

The completion is moreover a **regular category**.  Its regular epimorphisms are exactly its
*covers*: the morphisms with a computable section up to the relation, a function `g` on points
together with an element of the algebra which, from a realizer of `y`, computes a realizer of
`g y` and a proof that `f (g y)` is related to `y`.  A cover is a regular epimorphism because
the monomorphism of its image factorization is then invertible, while the epimorphism of that
factorization is regular — composed with the canonical cover of the source it *is* the canonical
cover of the image; conversely a regular epimorphism is strong, so the monomorphism of its
factorization is invertible and the cover data can be read off the inverse.  Covers are stable
under base change because the base of an object, with equality, is projective for them: from a
realizer of a point `x` one computes a point over `f x`, which lifts the canonical cover through
the pullback, and a right factor of a cover is a cover.  With the coequalizers of kernel pairs,
which are the images, this makes the completion regular in the sense of
`CategoryTheory.Regular`.

It is **not exact**, and `Start/AsmExRegNotExact.lean` settles that question in the negative for
every algebra with three distinct elements — in particular for Kleene's first algebra.  The
reason is the one regularity left open: a morphism into an object of the completion picks one
point per point of the source *and* computes a realizer of the chosen point from a realizer of
the source point, uniformly, by a single element of the algebra.  The counterexample attaches to
each element `s` of the algebra a pair of "witnesses" `cw s false`, `cw s true` chosen so that
the element `s` itself fails to normalize the pair — a three-point pigeonhole, since application
is single-valued and no element can map three pairwise distinct elements into a single one of
them.  The object `X` has two points `(s, false)`, `(s, true)` per element, both realized by `s`
alone; the object `R` has, over each such pair, one point per witness, realized by the pair of
`s` and an element computing the constant function at that witness.  The two endpoint maps
`p₁, p₂ : R ⟶ X` are jointly monic and carry a diagonal, a swap and a composition, so they are
an internal equivalence relation in the sense of
`Realizability.ExReg.NotExact.IsInternalEquiv` — a notion every kernel pair satisfies
(`Realizability.ExReg.NotExact.isInternalEquiv_of_isKernelPair`).  Yet they are the kernel pair
of no morphism: the test object of the counterexample maps into `X` twice, the two maps are
equalized after any candidate `k` because their difference is covered by the cross points, and a
lift into `R` would have to choose one witness per index `s` and compute a realizer of the chosen
cross point from `s` — at the index `s = t`, with `t` the tracker of the lift, that is exactly
what the blocking property forbids
(`Realizability.ExReg.NotExact.exists_internalEquiv_not_kernelPair`,
`Realizability.ExReg.NotExact.kleene_exReg_not_exact`).  So the completion of the *assemblies*,
with arbitrary assemblies as bases, is regular but not exact; the effective topos is obtained by
restricting the bases to the regular projectives, the partitioned assemblies.

The other half of exactness does hold, and `Start/AsmExRegCoeq.lean` proves it: **every internal
equivalence relation of the completion has a coequalizer.**  The quotient is the base of `E` with
a coarser relation — a proof that `x` and `y` are related is a point `r` of the base of `R` with
a realizer of it and proofs, in `E`, that `f₁ r` is related to `x` and `f₂ r` to `y`.  Its
reflexivity is the diagonal of the relation, its symmetry the swap, and its transitivity the
composition, applied to the object of *composable pairs*: pairs of points of `R` whose middle
endpoints are related, realized by their realizers together with a proof of that relation.  The
map onto the quotient is the identity on points, so it is an epimorphism, and a map out of `E`
that identifies the two legs descends along it — the descent is tracked by chaining the two
proofs of the quotient datum with the homotopy that identifies the legs
(`Realizability.ExReg.Coeq.coeqCoforkIsColimit`,
`Realizability.ExReg.Coeq.hasCoequalizer_of_isInternalEquiv`).  Together with the counterexample
above: the quotient exists, but the relation one recovers from it can be strictly coarser than
the one one started from.

**Restricting the bases to the regular projectives repairs exactness.**  The regular projectives
of `Asm(A)` are exactly the assemblies isomorphic to partitioned ones, where a point has exactly
one realizer (`Realizability.Assembly.regularProjective_iff`), and
`Start/AsmExRegProj.lean` and `Start/AsmExRegEffective.lean` prove that on the full subcategory
`Realizability.ExReg.ExRegP` of the objects whose base is partitioned **every internal
equivalence relation is effective**: the map onto the quotient above is its coequalizer and it is
that map's kernel pair (`Realizability.ExReg.ExRegP.exists_effective_quotient`,
`Realizability.ExReg.ExRegP.isKernelPair_of_isInternalEquiv`).  Two ingredients make it work,
both supplied by probes — objects whose points *are* their realizers, so that a tracker out of
them may read the data the points carry (`Realizability.ExReg.pairERel`,
`Realizability.ExReg.partitioned_pairERel`, `Realizability.ExReg.homotopic_pair`).  The first is
joint monicity read computationally: probing the relation with the tuples consisting of two
points of `R`, realizers of them and proofs that their images agree turns joint monicity into a
single element of the algebra that manufactures the proof relating the two points
(`Realizability.ExReg.JMTracker`, `Realizability.ExReg.jmTracker_of_jointlyMono`).  The second is
that the composable pairs can be probed as well, so that the transitivity of the quotient
relation only needs composites of maps out of *projective* objects, which is all that the
subcategory supplies (`Realizability.ExReg.compData`, `Realizability.ExReg.EqvDataP`).  With
them the lifting goes through: two maps out of an object with partitioned base which agree in the
quotient factor through the relation, because the single realizer of a point of the source
determines the point of `R` to be chosen and a realizer of it
(`Realizability.ExReg.exists_liftPre`, `Realizability.ExReg.existsUnique_lift`) — exactly what
the counterexample shows to be impossible over an arbitrary base.  What remains open for that
subcategory is its regularity as a category in its own right (closure of the finite limits and
the image factorizations under the restriction), its universal property among exact categories,
its topos structure, and its identification with the effective topos.
-/

#check @Realizability.PCA
#check @Realizability.PCA.lam_app
#check @Realizability.PCA.lam_lam_app
#check @Realizability.PCA.pairComb_app
#check @Realizability.TCA.toPCA
#check @Realizability.Lambda.lambdaModelPCA
#check @Realizability.Kleene.instPCANat
#check @Realizability.Kleene.k1_app
#check @Realizability.KleeneTwo.appK
#check @Realizability.KleeneTwo.appK_continuous
#check @Realizability.KleeneTwo.appK_zero_eq_none
#check @Realizability.KleeneTwo.instPCABaire
#check @Realizability.KleeneTwo.k2_k_app
#check @Realizability.KleeneTwo.k2_s_dom
#check @Realizability.KleeneTwo.k2_s_app
#check @Realizability.AppMorphism
#check @Realizability.AppMorphism.id
#check @Realizability.AppMorphism.comp
#check @Realizability.KleeneTwo.no_zero_test
#check @Realizability.KleeneTwo.kOneToTwo
#check @Realizability.KleeneTwo.evalAssoc_app
#check @Realizability.AppMorphism.trivialMor
#check @Realizability.KleeneTwo.projAssoc
#check @Realizability.KleeneTwo.appK_projAssoc
#check @Realizability.KleeneTwo.no_separatesBits_morphism
#check @Realizability.pcaLe_trans
#check @Realizability.pcaEquiv_of_any
#check @Realizability.pcaLeD_trans
#check @Realizability.KleeneTwo.kOneToTwo_decides
#check @Realizability.KleeneTwo.not_decides
#check @Realizability.KleeneTwo.kleene_strict
#check @Realizability.KleeneTwo.no_readsNumerals_morphism
#check @Lambda.speckerVal
#check @Lambda.speckerVal_monotone
#check @Lambda.speckerVal_lt_one
#check @Lambda.computable_speckerNum
#check @Lambda.specker_no_computable_modulus
#check @Lambda.speckerReal
#check @Lambda.speckerVal_le_speckerReal
#check @Lambda.speckerReal_le_one
#check @Lambda.specker_limit_not_computable
#check @Realizability.KleeneTwo.IsName
#check @Realizability.KleeneTwo.Realizes
#check @Realizability.KleeneTwo.IsComputableFun
#check @Realizability.KleeneTwo.Realizes.exists_modulus
#check @Realizability.KleeneTwo.IsComputableFun.continuous
#check @Realizability.KleeneTwo.not_isComputableFun_step
#check @Realizability.KleeneTwo.isComputableFun_id
#check @Realizability.Assembly
#check @Realizability.Assembly.instCategory
#check @Realizability.Assembly.isTerminalUnitAsm
#check @Realizability.Assembly.prodFanIsLimit
#check @Realizability.Assembly.curryEquiv
#check @Realizability.Assembly.instClosed
#check @Realizability.Assembly.monoidalClosed
#check @Realizability.Assembly.eqForkIsLimit
#check @Realizability.Assembly.instHasFiniteLimits
#check @Realizability.Assembly.isInitialEmptyAsm
#check @Realizability.Assembly.coprodCofanIsColimit
#check @Realizability.Assembly.coeqCoforkIsColimit
#check @Realizability.Assembly.instHasFiniteColimits
#check @Realizability.Assembly.isNNO_natAsm
#check @Realizability.Assembly.propAsm
#check @Realizability.Assembly.homPropEquiv
#check @Realizability.Assembly.isPullback_subAsm
#check @Realizability.Assembly.mono_iff_injective
#check @Realizability.Assembly.epi_iff_surjective
#check @Realizability.Assembly.strongEpi_imageFactor
#check @Realizability.Assembly.instHasImages
#check @Realizability.Assembly.strongEpi_iff_liftsRealizers
#check @Realizability.Assembly.isPullback_pbAsm
#check @Realizability.Assembly.strongEpi_of_isPullback
#check @Realizability.Assembly.exists_unique_charMap
#check @Realizability.Assembly.gammaNablaAdj
#check @Realizability.Assembly.nablaFullyFaithful
#check @Realizability.Assembly.globalSectionsEquiv
#check @Realizability.Kleene.natK1
#check @Realizability.Kleene.tracked_natK1_iff
#check @Realizability.Kleene.natK1EndEquiv
#check @Realizability.Kleene.exists_not_tracked_natK1
#check @Realizability.Kleene.not_full_gammaFunctor
#check @Realizability.Kleene.tracked_prod_natK1_iff
#check @Realizability.Kleene.realizes_expAsm_natK1
#check @Realizability.Kleene.expAsmNatK1Equiv
#check @Realizability.Kleene.isNNO_natK1
#check @Realizability.Kleene.natK1IsoNatAsm
#check @Realizability.Kleene.boolK1
#check @Realizability.Kleene.tracked_boolK1_iff
#check @Realizability.Kleene.boolHomEquiv
#check @Realizability.Kleene.exists_charBool_iff
#check @Realizability.Kleene.not_computable_selfHalt
#check @Realizability.Kleene.no_charBool_selfHalt
#check @Realizability.Kleene.boolK1_not_classifier
#check @Realizability.Kleene.rePred_iff_exists_index
#check @Realizability.Kleene.not_computablePred_selfHalt
#check @Realizability.Kleene.boolK1IsoCoprod
#check @Realizability.Kleene.boolCofanIsColimit
#check @Realizability.Assembly.Partitioned
#check @Realizability.Assembly.Partitioned.regularProjective
#check @Realizability.Assembly.exists_partitioned_cover
#check @Realizability.Assembly.regularProjective_iff
#check @Realizability.Assembly.RegularProjective.prod
#check @Realizability.Kleene.regularProjective_natK1
#check @Realizability.Kleene.not_projective_natK1
#check @Realizability.Kleene.not_liftsRealizers_natToNabla
#check @CategoryTheory.Limits.IsNNO.iso
#check @Realizability.ExReg.ERel
#check @Realizability.ExReg.instCategory
#check @Realizability.ExReg.instFullEmb
#check @Realizability.ExReg.instFaithfulEmb
#check @Realizability.ExReg.isTerminalTerm
#check @Realizability.ExReg.epi_quot
#check @Realizability.ExReg.prodFanIsLimit
#check @Realizability.ExReg.embProdIso
#check @Realizability.ExReg.embTermIso
#check @Realizability.ExReg.eqForkIsLimit
#check @Realizability.ExReg.instHasFiniteLimits
#check @Realizability.ExReg.quotIsColimit
#check @Realizability.ExReg.regularEpi_quot
#check @Realizability.ExReg.imgFac_comp_imgIncl
#check @Realizability.ExReg.epi_imgFac
#check @Realizability.ExReg.mono_imgIncl
#check @Realizability.ExReg.cover_iff_isRegularEpi
#check @Realizability.ExReg.regularEpi_imgFac
#check @Realizability.ExReg.isIso_imgIncl_of_cover
#check @Realizability.ExReg.cover_of_isPullback
#check @Realizability.ExReg.hasCoequalizer_of_isKernelPair
#check @Realizability.ExReg.instRegular
#check @Realizability.ExReg.NotExact.IsInternalEquiv
#check @Realizability.ExReg.NotExact.isInternalEquiv_of_isKernelPair
#check @Realizability.ExReg.NotExact.exists_internalEquiv_not_kernelPair
#check @Realizability.ExReg.NotExact.kleene_exReg_not_exact
#check @Realizability.ExReg.Coeq.EqvData
#check @Realizability.ExReg.Coeq.eqvData_of_isInternalEquiv
#check @Realizability.ExReg.Coeq.compERel
#check @Realizability.ExReg.Coeq.coeqObj
#check @Realizability.ExReg.Coeq.coeqCoforkIsColimit
#check @Realizability.ExReg.Coeq.hasCoequalizer_of_isInternalEquiv
#check @Realizability.ExReg.ProjBase
#check @Realizability.ExReg.ExRegP
#check @Realizability.ExReg.pairERel
#check @Realizability.ExReg.partitioned_pairERel
#check @Realizability.ExReg.homotopic_pair
#check @Realizability.ExReg.JMTracker
#check @Realizability.ExReg.jmTracker_of_jointlyMono
#check @Realizability.ExReg.compData
#check @Realizability.ExReg.EqvDataP
#check @Realizability.ExReg.eqvDataP_of_isInternalEquiv
#check @Realizability.ExReg.coeqObjP
#check @Realizability.ExReg.exists_liftPre
#check @Realizability.ExReg.existsUnique_lift
#check @Realizability.ExReg.ExRegP.regularProjective_base
#check @Realizability.ExReg.ExRegP.exists_effective_quotient
#check @Realizability.ExReg.ExRegP.isKernelPair_of_isInternalEquiv

/-!
### PERs, modest sets and the PER model of System F

`Start/PER.lean` defines partial equivalence relations over a PCA, their function space and the
intersection of an *arbitrary* family — the ingredient impredicative quantification needs.
`Start/Modest.lean` shows the cartesian closed structure of `Asm(A)` restricts to modest
assemblies, the assemblies presented by PERs.

`Start/ModestEquiv.lean` turns that dictionary into an equivalence of categories: PERs with the
tracked maps of their quotients are the same thing as the modest assemblies, and under the
equivalence the arrow PER is the exponential of the two assemblies.  `Start/ModestCcc.lean` draws
the categorical consequence: the modest assemblies, hence the PERs, form a cartesian closed
category in their own right.  `Start/ModestColimits.lean` completes that with the remaining
finite (co)limits: sub-assemblies and quotients of modest assemblies are modest, and so are
coproducts as soon as the algebra has more than one element — which is exactly when its two
boolean tags are distinguishable — so the modest assemblies, hence the PERs, are finitely
complete and finitely cocomplete.

`Start/ModestImage.lean` restricts the regular structure of `Asm(A)` to the subcategory: the image
of a modest assembly is modest, because a realizer of a point of the image realizes a preimage of
it and modesty of the domain determines that preimage.  Since the subcategory is full, the
diagonal fillers and the pullbacks of `Asm(A)` stay inside it, so the modest assemblies — hence
the PERs — have images and are a regular category, with the same computational description of the
strong epimorphisms.

`Start/ModestReflect.lean` goes back the other way: identifying the elements of an assembly that
share a realizer makes it modest, universally so, because a morphism into a modest assembly cannot
separate two such elements — its tracker computes a single value on the common realizer.  The
quotient is therefore left adjoint to the inclusion, and the modest assemblies, equivalently the
PERs, are a **reflective** subcategory of the assemblies.

`Start/ModestNNO.lean` adds the last piece of first-order structure: the assembly of natural
numbers of `Start/AssemblyNNO.lean` is itself modest once the algebra has more than one element.
A realizer of `n` must send the tagging combinator `λx. pair k x` and the base point `k` to the
tower of `n` nested pairs over `k`, and those towers are pairwise distinct, so no element can
realize two different numbers.  The modest assemblies therefore have a natural numbers object,
the same one as `Asm(A)`.  `Start/PERNNO.lean` carries it over to the partial equivalence
relations, through the general observation that an equivalence of categories preserves natural
numbers objects: a recursion datum is pulled back along the counit isomorphism, solved on the
other side, and pushed forward again.

`Start/PERSystemF.lean` is the payoff: over any λ-model, System F types are interpreted by PERs,
`∀` by the intersection over all PERs, and every typable term is related to itself — a semantic
model of System F, independent of the reducibility-candidate argument of `Start/SystemF.lean`.
-/

#check @Realizability.PER
#check @Realizability.PER.arrow
#check @Realizability.PER.iInter
#check @Realizability.PER.modest_toAsm
#check @Realizability.Assembly.modest_unitAsm
#check @Realizability.Assembly.Modest.prod
#check @Realizability.Assembly.Modest.exp
#check @Realizability.Assembly.toPER
#check @Realizability.PER.tracked_iff
#check @Realizability.Assembly.toPERIso
#check @Realizability.PER.toModestFullyFaithful
#check @Realizability.perEquivModest
#check @Realizability.PER.arrowIso
#check @Realizability.Assembly.Modest.of_iso
#check @Realizability.Modest.instMonoidalClosed
#check @Realizability.PER.instMonoidalClosed
#check @Realizability.PER.toModestArrowIso
#check @Realizability.PCA.k_ne_kI
#check @Realizability.Assembly.Modest.coprod
#check @Realizability.Assembly.Modest.coeq
#check @Realizability.Modest.instHasFiniteLimits
#check @Realizability.Modest.instHasFiniteColimits
#check @Realizability.PER.instHasFiniteLimits
#check @Realizability.PER.instHasFiniteColimits
#check @Realizability.Assembly.Modest.image
#check @Realizability.Modest.instHasImages
#check @Realizability.Modest.strongEpi_iff_liftsRealizers
#check @Realizability.Modest.strongEpi_of_isPullback
#check @Realizability.Assembly.modest_modestQuot
#check @Realizability.Assembly.modestLift_uniq
#check @Realizability.Modest.reflectorAdj
#check @Realizability.Modest.instReflective
#check @Realizability.PER.reflectorAdj
#check @Realizability.PCA.k_ne_pairEl_k
#check @Realizability.Assembly.modest_natAsm
#check @Realizability.Modest.isNNO_natModest
#check @CategoryTheory.Limits.IsNNO.ofEquivalence
#check @Realizability.PER.isNNO_natPER
#check @SystemF.Per.tyPer
#check @SystemF.Per.tyPer_tyInst
#check @SystemF.Per.sound
#check @SystemF.Per.dom_interp_of_typing
#check @SystemF.Per.dom_interp_idTy
#check @LambdaPi.EtaPar
#check @LambdaPi.betaEtaRed_iff
#check @LambdaPi.Typing.betaEta_sn
#check @LambdaPi.Typing.hasBetaEtaNormalForm
#check @LambdaPi.erased_step_eta_comm
#check @LambdaPi.erased_betaEta_church_rosser
#check @LambdaPi.betaEtaConv_eraseAnn
#check @LambdaPi.betaEtaConv_iff_join
#check @LambdaPi.betaEtaConv_sort_inj
#check @LambdaPi.not_betaEtaConv_sort_pi
#check @LambdaPi.betaEtaConv_pi_inv
#check @Rewriting.Star
#check @Rewriting.Conv
#check @Rewriting.confluent_of_diamond
#check @Rewriting.conv_iff_joins_of_confluent
#check @Rewriting.commute_of_stronglyCommute
#check @Rewriting.confluent_alt_of_commute
#check @Rewriting.postpones_of_par
#check @Rewriting.star_alt_iff_of_postpones
#check @Rewriting.terminating_of_measure
#check @Rewriting.sn_alt_of_postponesPlus
#check @Rewriting.confluent_of_newman
#check @LuTy.homOverEquivTm
#check @LcccPullbacks.ofNaturalPiStruct
#check @Cwa.nonempty_naturalPiStruct_ofPullbacks_iff

/-! ## The 2-categorical semantics of the dependent product

`Start/CwaLaxNotUnique.lean` settles the uniqueness clause of lax bi-initiality in the negative,
by a model of λΠ on pointed sets, and `Start/LcccPseudofunctor.lean` carries strictification
across to the 2-category of locally cartesian closed categories.

`Start/CwaDemocratic.lean` and `Start/CwaLcccOfFull.lean` describe the models so compared by
properties rather than by construction: a *full* model presents every morphism of contexts as a
display map, its category of contexts has pullbacks, and — the second half, proved here — that
category is locally cartesian closed as soon as the model carries a natural Π-structure whose
substitution on extended contexts is coherent (`LcccPullbacks.ofIsFull`).  The generic bijection
between the maps into a display map lying over a substitution and the terms of the substituted
type is `Start/CwaHomOver.lean`.

`Start/CwaStrictifyFull.lean` compares a full model with the strictification of its own category
of contexts: there is a morphism of models `Cwa.fullStrictify` out of the strictification, the
identity on contexts, bijective on terms, and every type of the model is in its image up to an
isomorphism of extended contexts over the base; for a full *democratic* model with dependent
products the strictification of its contexts is again a model with dependent products
(`Cwa.nonempty_naturalPiStruct_ofPullbacks_of_isFull`).

Whether that comparison is an *equivalence* is settled by `Start/CwaStrictifyEquiv.lean` and
`Start/CwaFamiliesNoStrictify.lean`.  In the lax 2-category a 2-cell is exactly a natural
transformation of the functors on contexts, so an isomorphism of 1-cells is an isomorphism of
those functors (`Cwa.laxIsoOfNatIso`): all that an equivalence needs is a morphism of models back,
and one that is the identity on contexts suffices (`Cwa.fullStrictify_comp_iso_id`,
`Cwa.comp_fullStrictify_iso_id`).  Such a morphism is a universe naming every type, and a full
democratic model need not have one: the standard model of families
(`CwaType.isFull_families`, `CwaType.isDemocratic_families`) admits **no** morphism to the
strictification of its contexts whose functor on contexts is an equivalence
(`CwaType.false_of_mor_isEquivalence`), because every type of `Type u` would then embed into a
single one; so it is **not** equivalent to that strictification
(`CwaType.not_equivalent_ofPullbacks`).
-/

#check @PointedModel.not_subsingleton_laxTwoCell_modelHom
#check @Cwa.lcccPseudofunctor
#check @Cwa.lcccNaturalPiStruct
#check @Cwa.nonempty_naturalPiStruct_toLaxCModel_iff
#check @Cwa.lcccPseudofunctor_map₂_bijective
#check @Cwa.lcccStrictification
#check @Cwa.lcccCtx
#check @Cwa.lcccCtx_map_lcccStrictification_map
#check @Cwa.lcccStrictificationMapCtxMapIso
#check @Cwa.lcccModelCat_biequivalent
#check @Cwa.IsFull
#check @Cwa.IsDemocratic
#check @Cwa.hasPullbacks_of_isFull
#check @Cwa.isFull_ofPullbacks
#check @Cwa.isDemocratic_ofPullbacks
#check @Cwa.homOverEquivTm
#check @Cwa.LcccOfFull.transpose
#check @Cwa.LcccOfFull.transpose_naturality
#check @LcccPullbacks.ofIsFull
#check @Cwa.fullStrictify
#check @Cwa.fullStrictify_tmMap_bijective
#check @Cwa.fullStrictify_essSurj
#check @Cwa.nonempty_naturalPiStruct_ofPullbacks_of_isFull
#check @Cwa.laxIsoOfNatIso
#check @Cwa.fullStrictify_comp_iso_id
#check @Cwa.comp_fullStrictify_iso_id
#check @CwaType.isFull_families
#check @CwaType.isDemocratic_families
#check @CwaType.extCoherent_families
#check @CwaType.false_of_mor_isEquivalence
#check @CwaType.not_equivalent_ofPullbacks

/-!
## Space-bounded computation and Savitch's theorem

Time in this library is Cobham's class, where composition is a constructor; space has to be a
machine, because a space bound is a statement about storage and not about the length of the
computation.  `Start/SpaceMachine.lean` gives the standard model for sublinear space — a
read-only input tape whose head is clamped to the input and its end marker, one binary work tape
whose used length is what the bound constrains, and a transition function returning the *list* of
available instructions, so that determinism (`Complexity.Space.Machine.Deterministic`) is a
property and not a separate model.  On top of it sit `Complexity.Space.DSPACE`,
`Complexity.Space.NSPACE`, `Complexity.Space.LOGSPACE`, `Complexity.Space.PSPACE` and
`Complexity.Space.NPSPACE`, with the inclusions one expects
(`Complexity.Space.nspace_of_dspace`, `Complexity.Space.pspace_of_logspace`) and a machine that
witnesses non-vacuity (`Complexity.Space.dspace_const_decidable`).

`Start/SpaceConfigCount.lean` counts the configurations: a machine running in space `s` on an
input of length `n` has at most `q · (n+1) · (s+1)² · 2 ^ s` of them
(`Complexity.Space.card_boundedCfg_le`), they form a finite graph under the one-step relation,
and acceptance is reachability in that graph
(`Complexity.Space.accepts_iff_exists_reachable_accepting`), so an accepting run can always be
taken shorter than the number of configurations
(`Complexity.Space.exists_short_accepting_run`).

`Start/SavitchReach.lean` is the graph-theoretic core: reachability within `2 ^ (k+1)` steps is
the existence of a midpoint reachable within `2 ^ k` from one side and reaching the target within
`2 ^ k` from the other (`Complexity.Reach.reachLe_succ_iff`); a walk in a finite graph shortens to
one of length below the number of vertices (`Complexity.Reach.exists_steps_lt_card`); so the
midpoint recursion of depth `k` decides reachability as soon as `2 ^ k` is at least the number of
vertices (`Complexity.Reach.reachB_iff_exists_steps`).

Savitch's theorem is the claim that this recursion can be *executed* in small memory, which is a
statement about an implementation, so `Start/SavitchVM.lean` gives one: a deterministic stack
machine whose activation records hold the two endpoints of a subproblem, its depth, an index into
an enumeration of the vertices and one bit.  It returns the value of the recursion and never
holds more than `k` records (`Complexity.Savitch.trace_call`), hence runs in
`(k + 1) · (2 w + 2 d + 1)` bits (`Complexity.Savitch.memBits_le_of_visited`).  Instantiated at
the configuration graph, `Start/SavitchSpace.lean` gives the theorem: the decision
`Complexity.Space.savitchDecide` is correct (`Complexity.Space.savitch_accepts_iff`), each of its
queries is run by the stack machine (`Complexity.Space.savitch_trace`) within
`(k + 1) · (4 k + 3)` bits (`Complexity.Space.savitch_memBits_le`), and
`k ≤ log₂ q + log₂ (n+1) + 2 log₂ (s+1) + s` (`Complexity.Space.savitchDepth_le`) — Savitch's
`O(s²)`.  For a language in `NPSPACE` the memory of the simulation is therefore polynomially
bounded (`Complexity.Space.savitch_poly_memory`).

The honest boundary: the deterministic simulation is exhibited on the stack machine and its
memory is counted in bits of activation records; compiling that machine into an offline Turing
machine of `Start/SpaceMachine.lean` — the routine half of the model-independence of space — is
not formalized, so `NPSPACE = PSPACE` is not claimed as a theorem about
`Complexity.Space.DSPACE`.
-/

#check @Complexity.Space.Machine.SpaceBounded
#check @Complexity.Space.nspace_of_dspace
#check @Complexity.Space.npspace_of_pspace
#check @Complexity.Space.pspace_of_logspace
#check @Complexity.Space.dspace_const_decidable
#check @Complexity.Space.card_boundedCfg_le
#check @Complexity.Space.accepts_iff_exists_reachable_accepting
#check @Complexity.Space.exists_short_accepting_run
#check @Complexity.Reach.reachLe_succ_iff
#check @Complexity.Reach.exists_steps_lt_card
#check @Complexity.Reach.reachB_iff
#check @Complexity.Reach.reachB_iff_exists_steps
#check @Complexity.Savitch.reachL_eq_reachB
#check @Complexity.Savitch.trace_call
#check @Complexity.Savitch.memBits_le_of_visited
#check @Complexity.Space.savitchDepth_le
#check @Complexity.Space.savitch_accepts_iff
#check @Complexity.Space.savitch_trace
#check @Complexity.Space.savitch_memBits_le
#check @Complexity.Space.savitch_poly_memory

/-!
## Quantified Boolean formulas, and the easy half of their PSPACE-completeness

`Start/Qbf.lean` defines quantified Boolean formulas (`Complexity.Qbf.QBF`), their value under an
assignment (`Complexity.Qbf.QBF.eval`), and the true closed ones (`Complexity.Qbf.TQBF`), which is
well defined because the value of a closed formula does not depend on the assignment
(`Complexity.Qbf.QBF.eval_closed`).

The evaluator is again a deterministic stack machine (`Complexity.Qbf.step`), and the theorem
about it is the shape of its memory: started on a formula it returns the formula's value, hands
back the assignment it was given — each quantifier restores the bit it overwrote — and never holds
more than `height p` activation records (`Complexity.Qbf.trace_eval`).  Counting one bit per
variable for the assignment, a pointer and a variable index per record
(`Complexity.Qbf.memBits`), deciding a closed formula costs at most
`varBound p + (height p + 1) · (2 w + 2)` bits (`Complexity.Qbf.tqbf_memBits_le`), which is
quadratic in the size of the formula (`Complexity.Qbf.tqbf_memBits_le_size`): the easy half of the
PSPACE-completeness of `TQBF`.  The hard half — a generic reduction from a space-bounded machine
to a quantified Boolean formula — is not formalized.
-/

#check @Complexity.Qbf.QBF.eval
#check @Complexity.Qbf.QBF.eval_congr
#check @Complexity.Qbf.QBF.eval_closed
#check @Complexity.Qbf.TQBF
#check @Complexity.Qbf.trace_eval
#check @Complexity.Qbf.tqbf_trace
#check @Complexity.Qbf.tqbf_memBits_le
#check @Complexity.Qbf.tqbf_memBits_le_size

/-!
## Bounded reachability as a quantified Boolean formula

`Start/QbfReach.lean` writes the midpoint recursion of `Start/SavitchReach.lean` as a formula.
Vertices are words of `m` bits held in *blocks* of variables (`Complexity.Qbf.blockVal`), and the
edge relation enters as a family of formulas `stepF a b`, one per pair of blocks.  The formula
`Complexity.Qbf.QBF.reachF stepF m k a b t` quantifies over a midpoint and then, universally over
a pair of endpoints, makes a *single* recursive call stand for both legs, so that it grows by one
block of quantifiers per level rather than doubling.

It is correct — it holds exactly when the word in block `a` reaches the word in block `b` within
`2 ^ k` steps, in the sense of `Complexity.Reach.reachLe`
(`Complexity.Qbf.QBF.eval_reachF`) — and small: its size is bounded by the size of one step
formula plus `k * (43 * m + 21) + 10 * m + 5` (`Complexity.Qbf.QBF.size_reachF_le`), so it is
polynomial in the width of a vertex and the depth of the recursion.

This is the formula half of the PSPACE-hardness of `TQBF`.  What is still missing for the
hardness theorem itself is the machine half: that the configuration graph of a space-bounded
machine of `Start/SpaceMachine.lean` admits such a family of step formulas, computed from the
input in polynomial time.
-/

#check @Complexity.Qbf.blockVal
#check @Complexity.Qbf.QBF.reachF
#check @Complexity.Qbf.QBF.eval_reachF
#check @Complexity.Qbf.QBF.size_reachF_le

/-!
## From a space-bounded machine to a quantified Boolean formula

`Start/SpacePadded.lean` normalises a configuration to a fixed width: for a machine running in
space `s`, `Complexity.Space.pad` pads the work tape to `s` cells, `Complexity.Space.Fits`
recognises the configurations of that width inside the bound, and `Complexity.Space.padStep` is
the one-step relation between them.  Padding is a bisimulation, so acceptance is reachability in
the padded graph within `2 ^ savitchDepth` steps
(`Complexity.Space.accepts_iff_reachLe_padStep`).

`Start/QbfCfgWord.lean` writes such a configuration as a word of
`Complexity.Qbf.cfgWidth M x s = q + (n + 1) + 2 s` bits — control state and the two head
positions in unary, the work tape bit by bit.  The encoding is injective on configurations of
that width (`Complexity.Qbf.cfgWord_injective`), so bounded reachability of words is bounded
reachability of configurations (`Complexity.Qbf.reachLe_wordStep_iff`).

`Start/QbfMachine.lean` supplies the step formula that `Start/QbfReach.lean` asks for.  It is a
disjunction over the situations of the machine — a control state, a position of each head and the
bit read — of the constraints one instruction imposes on two blocks; unary heads keep every
constraint a literal or a copy, so one situation costs `O(width)`
(`Complexity.Qbf.QBF.size_stepF_le`) and the formula expresses exactly one step of the machine
(`Complexity.Qbf.QBF.eval_stepF`).  The cases run over the instructions a situation can possibly
offer (`Complexity.Qbf.QBF.allInstr`) rather than over the transition function's own list, so the
size bound holds for every machine, deterministic or not.  Feeding it to the midpoint recursion
gives the *closed* formula `Complexity.Qbf.QBF.machineF M x s`, true exactly when the machine
accepts the input (`Complexity.Qbf.QBF.eval_machineF`), of size polynomial in the number of
states, the length of the input, the space bound and the branching of the transition function
(`Complexity.Qbf.QBF.size_machineF_le`).

`Start/QbfClosed.lean` tracks the free variables of every piece of the construction and concludes
that the formula is *closed* (`Complexity.Qbf.QBF.closed_machineF`), so it is an instance of
`Complexity.Qbf.TQBF`, true exactly when the machine accepts the input
(`Complexity.Qbf.QBF.tqbf_machineF_iff`).  Reading that off for a whole class,
`Start/QbfPspace.lean` gives: **every language in `NPSPACE` — hence every language in `PSPACE` —
has a family of closed quantified Boolean formulas of polynomial size, one per input, true exactly
on the members of the language** (`Complexity.Qbf.QBF.npspace_polySize_tqbf`,
`Complexity.Qbf.QBF.pspace_polySize_tqbf`).

The honest boundary: the map from an input to its formula is not shown here to be computable in
polynomial time, so this is a polynomial-size reduction of membership to `TQBF`, and not yet the
`PSPACE`-hardness of `TQBF`.
-/

#check @Complexity.Space.accepts_iff_reachLe_padStep
#check @Complexity.Qbf.cfgWord
#check @Complexity.Qbf.reachLe_wordStep_iff
#check @Complexity.Qbf.QBF.stepF
#check @Complexity.Qbf.QBF.eval_stepF
#check @Complexity.Qbf.QBF.size_stepF_le
#check @Complexity.Qbf.QBF.machineF
#check @Complexity.Qbf.QBF.eval_machineF
#check @Complexity.Qbf.QBF.size_machineF_le
#check @Complexity.Qbf.QBF.closed_machineF
#check @Complexity.Qbf.QBF.tqbf_machineF_iff
#check @Complexity.Qbf.QBF.npspace_polySize_tqbf
#check @Complexity.Qbf.QBF.pspace_polySize_tqbf

/-!
### `TQBF` as a language of words, and the reduction as a map of words

The classes of `Start/SpaceMachine.lean` are classes of *languages* — sets of binary words — so
stating the hardness of `TQBF` first needs the formulas themselves written down as words.
`Start/QbfWord.lean` gives a self-delimiting binary code: three tag bits per node (two for a
variable or a negation), variable indices in unary (`Complexity.Qbf.QBF.enc`).  A decoder driven
by a fuel bound reads a formula back off the front of a word
(`Complexity.Qbf.QBF.dec_enc_append`), so the code is injective
(`Complexity.Qbf.QBF.enc_injective`), and the code of a formula of size `n` with variables below
`v` is at most `n * (v + 3)` bits long (`Complexity.Qbf.QBF.length_enc_le`).  The codes of the
true closed formulas form the language `Complexity.Qbf.tqbfLang`
(`Complexity.Qbf.tqbfLang_enc_iff`).

`Start/QbfVarBound.lean` bounds every variable of the reduction formula by
`(3 k + 5) * cfgWidth M x s` (`Complexity.Qbf.QBF.varBound_machineF_le`), which together with the
size bound of `Start/QbfPspace.lean` bounds the *length of its code*
(`Complexity.Qbf.QBF.length_enc_machineF_le`) by a polynomial in the input length
(`Complexity.Qbf.QBF.polyBound_wordBound`).  Hence: **every language in `NPSPACE`, and so every
language in `PSPACE`, is mapped into `tqbfLang` by one map of words whose output length is bounded
by a single polynomial in the input length** (`Complexity.Qbf.QBF.npspace_polyLength_tqbfWord`,
`Complexity.Qbf.QBF.pspace_polyLength_tqbfWord`).

The honest boundary is now the only thing between this and the `PSPACE`-hardness of `TQBF`: that
map of words is not shown to be computable in polynomial time, i.e. to be the value of a term of
`Complexity.Cob`.
-/

#check @Complexity.Qbf.QBF.enc
#check @Complexity.Qbf.QBF.dec_enc_append
#check @Complexity.Qbf.QBF.enc_injective
#check @Complexity.Qbf.QBF.length_enc_le
#check @Complexity.Qbf.tqbfLang
#check @Complexity.Qbf.tqbfLang_enc_iff
#check @Complexity.Qbf.QBF.varBound_machineF_le
#check @Complexity.Qbf.QBF.length_enc_machineF_le
#check @Complexity.Qbf.QBF.polyBound_wordBound
#check @Complexity.Qbf.QBF.npspace_polyLength_tqbfWord
#check @Complexity.Qbf.QBF.pspace_polyLength_tqbfWord

/-!
### The code of the reduction formula as a stream of blocks

What a polynomial-time reduction would have to *write* is the word of the previous section, and
the Cobham toolkit of this library writes a word by sweeping one once and emitting a block at
every position (`Complexity.eval_blkRunTerm`, `Complexity.eval_lrunTerm`).
`Start/QbfWordStream.lean` puts the code in exactly that shape.  Quantifier prefixes are
concatenations over a range (`Complexity.Qbf.QBF.enc_exBits`, `Complexity.Qbf.QBF.enc_allBits`),
finite conjunctions and disjunctions are concatenations over their case lists
(`Complexity.Qbf.QBF.enc_conjAll`, `Complexity.Qbf.QBF.enc_disjAny`), and the midpoint recursion —
the only genuinely recursive part of the formula, and one with a *single* recursive call —
contributes one block per level: `Complexity.Qbf.QBF.enc_reachF` writes the code of the
reachability formula as `k` copies of `Complexity.Qbf.QBF.reachPre` whose block indices at level
`j` are the closed expressions `Complexity.Qbf.QBF.aAt`, `Complexity.Qbf.QBF.bAt` and `2 + 3 j`,
followed by the code of the base case.  Assembling the pieces,
`Complexity.Qbf.QBF.enc_machineF_stream` exhibits the whole code as a fixed prefix, the codes of
the two machine constraints, the blocks of the levels and the code of the base case.

This is the uniformity statement a compiler needs, and no more: the blocks are still *described*
rather than produced by a Cobham term, so the `PSPACE`-hardness of `TQBF` remains open.
-/

#check @Complexity.Qbf.QBF.enc_exBits
#check @Complexity.Qbf.QBF.enc_allBits
#check @Complexity.Qbf.QBF.enc_conjAll
#check @Complexity.Qbf.QBF.enc_disjAny
#check @Complexity.Qbf.QBF.reachPre
#check @Complexity.Qbf.QBF.enc_reachF_succ
#check @Complexity.Qbf.QBF.enc_reachF
#check @Complexity.Qbf.QBF.enc_machineF_stream

/-!
### Writing a range of blocks, and the quantifier prefixes of the code

`Start/CobhamRange.lean` packages the block-emitting recursion of `Start/CobhamBlock.lean` for the
shape the reduction needs: a word `(List.range n).flatMap W`, one block per index of a range.  The
sweep runs from the right, so the index of a block has to be recovered from the counter, which is
what `Complexity.Cob.dropN` does — dropping as many bits as its first argument is long is a Cobham
function (`Complexity.Cob.eval_dropN`), and on unary words that is truncated subtraction.  The
result is `Complexity.eval_rangeEmitTerm`: **writing one block per index of a range is a Cobham
function** of `1^n` and of a parameter word whose leading ones carry `n`.

`Start/QbfCobPrefix.lean` applies it to the first piece of the code of the reduction formula.
`Complexity.Qbf.QBF.quantPrefixTerm` writes the code of a nest of `n` quantifiers over the
variables `o, …, o + n - 1` from the width and the offset in unary
(`Complexity.Qbf.QBF.eval_quantPrefixTerm`), so the code of `exBits` and of `allBits` is that
value followed by the code of the body (`Complexity.Qbf.QBF.enc_exBits_eval`,
`Complexity.Qbf.QBF.enc_allBits_eval`).
-/

#check @Complexity.Cob.dropN
#check @Complexity.Cob.eval_dropN
#check @Complexity.rangeEmitTerm
#check @Complexity.eval_rangeEmitTerm
#check @Complexity.Qbf.QBF.quantPrefixTerm
#check @Complexity.Qbf.QBF.eval_quantPrefixTerm
#check @Complexity.Qbf.QBF.enc_exBits_eval
#check @Complexity.Qbf.QBF.enc_allBits_eval

/-!
### Unary fields, and the block-equality formula as a Cobham term

A block of the code needs several numbers at once — a width, two block indices, an offset — so
`Start/CobhamFields.lean` fixes a format for the parameter word of the emitter: a list of naturals
written in unary, each field terminated by a zero bit (`Complexity.fieldsWord`), with
`Complexity.Cob.fieldTerm` reading the `k`-th of them
(`Complexity.Cob.eval_fieldTerm`).

`Start/QbfCobEqBlock.lean` uses it for the workhorse of the reduction formula,
`Complexity.Qbf.QBF.eqBlock m i j`, which says that two blocks of `m` variables carry the same
word and of which every level of the midpoint recursion contains four.  Its code is one block per
position, holding the variable indices `i * m + l` and `j * m + l` in unary.  The two products are
computed once, outside the sweep, and travel in the parameter word, so that the block written at a
position stays short and the padding constant of the term does not depend on the instance:
`Complexity.Qbf.QBF.idxTerm` writes an index (`Complexity.Qbf.QBF.eval_idxTerm`) and
`Complexity.Qbf.QBF.enc_eqBlock_eval` shows that **the code of `eqBlock m i j` is the value of one
Cobham term at `1^m` and the unary fields `m, i * m, j * m`**, followed by the code of the constant
that closes the conjunction.
-/

#check @Complexity.fieldsWord
#check @Complexity.Cob.fieldTerm
#check @Complexity.Cob.eval_fieldTerm
#check @Complexity.Qbf.QBF.idxTerm
#check @Complexity.Qbf.QBF.eval_idxTerm
#check @Complexity.Qbf.QBF.eqBlockTerm
#check @Complexity.Qbf.QBF.enc_eqBlock_eval

/-!
### The block of a level of the midpoint recursion as a Cobham term

`Start/QbfCobLevel.lean` composes the two previous pieces into the block that one level of the
midpoint recursion contributes to the code, `Complexity.Qbf.QBF.reachPre m a b t`: the three
quantifier prefixes over the scratch blocks and the four block equalities of its antecedent.  The
parameter word of a level (`Complexity.Qbf.QBF.levelParam`) carries the width and the five
products of a block index with the width in unary — the multiplications happen once, outside every
sweep — and the pieces assemble the parameter words they expect out of those fields
(`Complexity.Qbf.QBF.eval_prefixArg`, `Complexity.Qbf.QBF.eval_eqArg`).  The result is
`Complexity.Qbf.QBF.reachPre_eval`: **the block of a level is the value of one Cobham term**,
`Complexity.Qbf.QBF.levelTerm`, at the width in unary and the parameter word of the level, with
padding constants that do not depend on the instance.
-/

#check @Complexity.Qbf.QBF.levelParam
#check @Complexity.Qbf.QBF.eval_prefixArg
#check @Complexity.Qbf.QBF.eval_eqArg
#check @Complexity.Qbf.QBF.levelTerm
#check @Complexity.Qbf.QBF.reachPre_eval

/-!
### The arithmetic the compiler of the reduction needs

The blocks of the reduction depend on *tests* — where a position lies in a configuration, which
position a head marks, which bit of the input is read — so the compiler needs arithmetic, not only
control structure.  `Start/CobhamCond.lean` supplies it: the normalised truth value of a term
(`Complexity.Cob.eval_boolT`), the comparison of two numbers given in unary
(`Complexity.Cob.eval_ltU`, `.eval_leU`, `Complexity.Cob.eval_eqU`) and the reading of the bit of
a word at a unary position (`Complexity.Cob.eval_bitU`).  `Start/CobhamUnary.lean` adds unary
successor, predecessor, sum and minimum, and the assembly of a parameter word out of terms
computing its fields (`Complexity.Cob.eval_fieldsT`); `Start/CobhamFieldsApp.lean` lets such a
parameter word carry a word after its fields, so that the input of the simulated machine travels
inside it (`Complexity.Cob.eval_fieldTerm_app`, `Complexity.Cob.eval_tailWord`).
-/

#check @Complexity.Cob.eval_boolT
#check @Complexity.Cob.eval_ltU
#check @Complexity.Cob.eval_leU
#check @Complexity.Cob.eval_eqU
#check @Complexity.Cob.eval_bitU
#check @Complexity.Cob.eval_uSucc
#check @Complexity.Cob.eval_uAdd
#check @Complexity.Cob.eval_fieldsT
#check @Complexity.Cob.eval_fieldTerm_app
#check @Complexity.Cob.eval_tailWord

/-!
### The reduction formula at an arbitrary depth

`Start/QbfMachineDepth.lean` frees the reduction formula from the exact depth of the midpoint
recursion: `Complexity.Qbf.QBF.machineFk M x s k` is correct at every depth `k` at or above
`Complexity.Qbf.savitchDepth` (`Complexity.Qbf.QBF.eval_machineFk`), it is closed
(`Complexity.Qbf.QBF.closed_machineFk`), and it is a true closed formula exactly when the machine
accepts the input (`Complexity.Qbf.QBF.tqbf_machineFk_iff`).  This is what lets the compiler use a
depth which is a convenient polynomial of the length of the input rather than the exact one.
-/

#check @Complexity.Qbf.QBF.eval_machineFk
#check @Complexity.Qbf.QBF.closed_machineFk
#check @Complexity.Qbf.QBF.tqbf_machineFk_iff

/-!
### Every constraint of the reduction is written by a Cobham term

The code of the reduction formula is a concatenation of blocks, and each family of blocks is now
*computed*, by one term whose padding constants do not depend on the instance, so that a single
term serves every machine, width, block index and level.

* `Start/QbfCobCfg.lean` — the configuration-block formulas, one conjunct per position of a block:
  `Complexity.Qbf.QBF.enc_cfgF_eval` and `Complexity.Qbf.QBF.enc_tgtF_eval`.
* `Start/QbfCobStepCase.lean` — one case of the step formula, guarded by the transition relation:
  `Complexity.Qbf.QBF.eval_stepCaseTerm`, and `Complexity.Qbf.QBF.eval_caseTerm`, which contributes
  the block exactly when the case belongs to the list of cases.
* `Start/QbfCobStep.lean` — the sweeps over the situations assemble the whole step formula:
  `Complexity.Qbf.QBF.enc_stepF_eval`.
* `Start/QbfCobInitAcc.lean` — the initial and the accepting constraints:
  `Complexity.Qbf.QBF.enc_initF_eval`, `Complexity.Qbf.QBF.enc_accF_eval`.
* `Start/QbfCobLevels.lean` — the sweep over the levels of the midpoint recursion, whose six fields
  are affine in the level: `Complexity.Qbf.QBF.eval_levelsT`.
* `Start/QbfCobMachine.lean` — the concatenation of all of them:
  `Complexity.Qbf.QBF.enc_machineFk_eval`, **the code of the reduction formula is the value of one
  Cobham term** at the input and a parameter word.
-/

#check @Complexity.Qbf.QBF.enc_cfgF_eval
#check @Complexity.Qbf.QBF.enc_tgtF_eval
#check @Complexity.Qbf.QBF.eval_stepCaseTerm
#check @Complexity.Qbf.QBF.eval_caseTerm
#check @Complexity.Qbf.QBF.enc_stepF_eval
#check @Complexity.Qbf.QBF.enc_initF_eval
#check @Complexity.Qbf.QBF.enc_accF_eval
#check @Complexity.Qbf.QBF.eval_levelsT
#check @Complexity.Qbf.QBF.enc_machineFk_eval

/-!
### `TQBF` is `PSPACE`-hard

`Start/QbfCobReduction.lean` removes the parameter word.  For a machine running in polynomial
space every field of that word is a polynomial in the length of the input, and a polynomial in
unary is a Cobham function of the input (`Complexity.Cob.eval_onesT`, `.eval_powT`, `.eval_nsmulT`),
so the reduction is a single Cobham term applied to the input alone
(`Complexity.Qbf.QBF.redTerm`, `Complexity.Qbf.QBF.eval_redTerm`) — that is, a polynomial-time
many-one reduction in the sense of `Complexity.PolyManyOne`.  Hence
`Complexity.Qbf.QBF.npspaceHard_tqbfLang` and `Complexity.Qbf.QBF.pspaceHard_tqbfLang`: **every
language in (nondeterministic) polynomial space reduces to `TQBF` in polynomial time.**
-/

#check @Complexity.Cob.eval_onesT
#check @Complexity.Cob.eval_powT
#check @Complexity.Cob.eval_nsmulT
#check @Complexity.Qbf.QBF.redTerm
#check @Complexity.Qbf.QBF.eval_redTerm
#check @Complexity.Qbf.QBF.npspaceHard_tqbfLang
#check @Complexity.Qbf.QBF.pspaceHard_tqbfLang

/-!
### What hardness buys

`Start/QbfHard.lean` packages hardness as a property of a language
(`Complexity.Space.PSPACEHard`, `.NPSPACEHard`, and `Complexity.Space.PSPACEComplete` for hardness
together with membership) and draws the consequences.  Hardness travels along reductions
(`Complexity.Space.PSPACEHard.of_reduction`), so every language `TQBF` reduces to is hard as well;
and a hard language decided in polynomial time decides the whole class
(`Complexity.Space.PSPACEHard.inP_of_inP`).  For `TQBF` itself,
`Complexity.Space.pspace_inP_of_tqbf_inP` says that a polynomial-time algorithm for `TQBF` would
decide every language of polynomial space in polynomial time, and
`Complexity.Space.tqbf_not_inP` is the contrapositive.

The boundary, recorded here as everywhere: `Complexity.Space.PSPACEComplete
Complexity.Qbf.tqbfLang` is *not* proved, because the membership `TQBF ∈ PSPACE` would need the
evaluating stack machine of `Start/Qbf.lean` compiled into the offline machine of
`Start/SpaceMachine.lean`.
-/

#check @Complexity.Space.PSPACEHard
#check @Complexity.Space.NPSPACEHard
#check @Complexity.Space.PSPACEComplete
#check @Complexity.Space.pspaceHard_tqbfLang'
#check @Complexity.Space.npspaceHard_tqbfLang'
#check @Complexity.Space.PSPACEHard.of_reduction
#check @Complexity.Space.PSPACEHard.inP_of_inP
#check @Complexity.Space.pspace_inP_of_tqbf_inP
#check @Complexity.Space.tqbf_not_inP

/-!
### The memory of the evaluator, measured against the length of the code

A membership `TQBF ∈ PSPACE` is a statement about the *code* of a formula, so the memory of the
evaluating stack machine has to be bounded by a polynomial in the length of that code and not only
in the size of the formula.  `Start/QbfCodeSpace.lean` supplies the comparison: the code spends at
least one bit per node and writes every variable index in unary, so the size, the variable bound
and the height of a formula are all bounded by the length of its code
(`Complexity.Qbf.QBF.size_le_length_enc`, `.varBound_le_length_enc`, `.height_lt_length_enc`), and
therefore deciding a closed formula costs at most `2 n² + 3 n` bits for `n` the length of its code
(`Complexity.Qbf.tqbf_memBits_le_length_enc`, `Complexity.Qbf.tqbf_memBits_le_length`).  What is
still missing for the membership itself is the compilation of that stack machine into the offline
machine of `Start/SpaceMachine.lean`.
-/

#check @Complexity.Qbf.QBF.size_le_length_enc
#check @Complexity.Qbf.QBF.varBound_le_length_enc
#check @Complexity.Qbf.QBF.height_lt_length_enc
#check @Complexity.Qbf.tqbf_memBits_le_length_enc
#check @Complexity.Qbf.tqbf_memBits_le_length

/-!
### Relativization: polynomial time with an oracle

`Start/OracleCob.lean` relativizes the time side of the library.  Polynomial time is Cobham's
class here, so an oracle machine is a Cobham term with one extra constructor, `Complexity.CobQ`,
whose `query` asks the oracle about its first argument.  Evaluation returns the value *and* the
list of words the oracle was asked about (`Complexity.CobQ.run`, `.eval`, `.queries`), because a
diagonalization needs the queries and not only the answer.  Three bounds hold with constants that
do not depend on the oracle: the output is polynomially long (`Complexity.CobQ.polyLen`), the
**number** of queries is polynomially bounded (`Complexity.CobQ.polyQueryCount`) — this is what
makes the queried set too small to exhaust the words of a given length — and every queried word is
polynomially long (`Complexity.CobQ.polyQueryLen`).  The **use principle** is
`Complexity.CobQ.run_congr`: two oracles agreeing on the words actually queried give the same run.

`Start/OracleClasses.lean` defines the relativized classes `Complexity.InP_rel` and
`Complexity.InNP_rel` and shows that they relativize the unrelativized ones: an ordinary Cobham
term is an oracle term that asks nothing (`Complexity.CobQ.eval_ofCob`), an oracle term run with
the empty oracle is an ordinary Cobham term (`Complexity.CobQ.eval_erase`), and hence
`Complexity.inP_rel_empty_iff` and `Complexity.inNP_rel_empty_iff` give back `P` and `NP`, while
`Complexity.InP.to_rel` and `Complexity.InNP.to_rel` give `P ⊆ P^A` and `NP ⊆ NP^A` for every `A`.
`Complexity.inNP_rel_of_inP_rel` is `P^A ⊆ NP^A`, and `Complexity.inP_rel_oracle` is the point of
the exercise: the oracle itself is decided in `P^A`.

`Start/OracleSpace.lean` relativizes the space side: the offline machine of
`Start/SpaceMachine.lean` with a query tape that counts towards the space bound
(`Complexity.Space.OMachine`), the classes `Complexity.Space.ODSPACE`,
`Complexity.Space.InPSPACE_rel`, and the embedding of the unrelativized model as the machines that
never query (`Complexity.Space.ofMachine_accepts_iff`), whence
`Complexity.Space.inPSPACE_rel_of_pspace` : `PSPACE ⊆ PSPACE^A` for every oracle.
-/

#check @Complexity.CobQ.run
#check @Complexity.CobQ.eval
#check @Complexity.CobQ.queries
#check @Complexity.CobQ.polyLen
#check @Complexity.CobQ.polyQueryCount
#check @Complexity.CobQ.polyQueryLen
#check @Complexity.CobQ.run_congr
#check @Complexity.CobQ.eval_ofCob
#check @Complexity.CobQ.eval_erase
#check @Complexity.InP_rel
#check @Complexity.InNP_rel
#check @Complexity.inP_rel_empty_iff
#check @Complexity.inNP_rel_empty_iff
#check @Complexity.InP.to_rel
#check @Complexity.InNP.to_rel
#check @Complexity.inNP_rel_of_inP_rel
#check @Complexity.inP_rel_oracle
#check @Complexity.Space.OMachine
#check @Complexity.Space.ODSPACE
#check @Complexity.Space.InPSPACE_rel
#check @Complexity.Space.ofMachine_accepts_iff
#check @Complexity.Space.inPSPACE_rel_of_pspace

/-!
### The counting step of a diagonalization against oracle machines

`Start/OracleDiag.lean` proves the combinatorial fact a separating oracle is built on: a
polynomial-time oracle machine, on arguments of length at most `n`, asks the oracle about fewer
than `2 ^ n` words once `n` is large, so some word of length `n` is never asked about and remains
free to be decided afterwards.  It rests on `Complexity.PolyMono.lt_two_pow` (a monotone
polynomial bound is eventually below the exponential), on `Complexity.card_words_of_length` (there
are `2 ^ n` words of length `n`) and on the query count of `Complexity.CobQ.polyQueryCount`; the
statement is `Complexity.CobQ.exists_word_not_queried`, with
`Complexity.CobQ.exists_word_not_queried_unary` for the unary inputs that the
Baker–Gill–Solovay language uses.
-/

#check @Complexity.exists_mul_pow_lt_two_pow
#check @Complexity.PolyMono.lt_two_pow
#check @Complexity.card_words_of_length
#check @Complexity.exists_word_length_not_mem
#check @Complexity.CobQ.exists_word_not_queried
#check @Complexity.CobQ.exists_word_not_queried_unary

/-!
### The oracle machines are enumerated

`Start/OracleEnum.lean` codes the oracle Cobham terms by naturals (`Complexity.CobQ.code`, the
constructor paired with the codes of the parts, the list of a composition coded by the encoding of
lists of naturals) and proves the code injective (`Complexity.CobQ.code_injective`).  The type is a
nested inductive, so the `Countable` deriving handler does not apply to it; with the code, the
terms are countable and hence enumerated by a surjection `ℕ → Complexity.CobQ`
(`Complexity.CobQ.exists_enumeration`), which is what a stage-wise diagonalization runs through.
-/

#check @Complexity.CobQ.code
#check @Complexity.CobQ.code_injective
#check @Complexity.CobQ.exists_enumeration

/-!
### An oracle that separates: `P^B ≠ NP^B`

`Start/BakerGillSolovay.lean` carries out the separating half of Baker–Gill–Solovay.  The language
is the standard one, `Complexity.BGS.langB`: an input `x` is accepted when some word of length
`|x|` lies in the oracle.  It is in `NP^B` for every oracle — guess the word and ask
(`Complexity.BGS.inNP_rel_langB`).  The oracle itself is built in stages
(`Complexity.BGS.stage`) against the enumeration of `Start/OracleEnum.lean`: at stage `e + 1` the
`e`-th oracle Cobham term is run on the unary input `1 ^ n` for an `n` above everything decided so
far, with the finite oracle built up to that point; if it accepts, no word of length `n` is ever
added, and if it rejects, a word of length `n` that the run never asked about is added
(`Complexity.CobQ.exists_word_not_queried_unary`).  The run does not notice the change, by the use
principle `Complexity.CobQ.run_congr`, so the term fails to decide the language at `1 ^ n`; since
the enumeration is onto, no term decides it (`Complexity.BGS.not_inP_rel_langB`).  Hence
`Complexity.bgs_different`: there is an oracle `B` with `P^B ≠ NP^B`.
-/

#check @Complexity.BGS.langB
#check @Complexity.BGS.stage
#check @Complexity.BGS.oracleB
#check @Complexity.BGS.inNP_rel_langB
#check @Complexity.BGS.not_inP_rel_langB
#check @Complexity.bgs_different

/-!
### The relativization barrier

`Start/Relativization.lean` says what it means for a statement about the classes to relativize
(`Complexity.Relativizes`: it holds with every oracle attached) and draws the consequence of the
separating oracle: `Complexity.peqnp_does_not_relativize`, no argument whose conclusion survives
every oracle proves `P = NP`.  The companion half is conditional, because the collapsing oracle is
not in the library: given any oracle with `P^A = NP^A`, `Complexity.no_relativizing_resolution`
gives the barrier in full — neither `P = NP` nor `P ≠ NP` relativizes.
-/

#check @Complexity.Relativizes
#check @Complexity.PneNP_rel
#check @Complexity.peqnp_does_not_relativize
#check @Complexity.pnenp_does_not_relativize
#check @Complexity.no_relativizing_resolution

/-!
### The use of an oracle computation

`Start/OracleUse.lean` turns the existential use principle of `Start/OracleMachine.lean` into a
function.  `Lambda.Oracle.useStage` is the least stage at which the search defining
`Lambda.Oracle.evalOracle` succeeds and `Lambda.Oracle.use` is one more than it;
`Lambda.Oracle.useStage_le_of_isSome` is its minimality,
`Lambda.Oracle.evalOracle_eq_of_agree_below_use` is the use principle with that explicit bound —
an oracle agreeing below the use gives the same computation — and
`Lambda.Oracle.use_eq_of_agree_below_use` adds that the use itself is unchanged, which is what a
strategy protecting a computation needs.
-/

#check @Lambda.Oracle.Converges
#check @Lambda.Oracle.useStage
#check @Lambda.Oracle.use
#check @Lambda.Oracle.useStage_le_of_isSome
#check @Lambda.Oracle.evalOracle_eq_of_agree_below_use
#check @Lambda.Oracle.use_eq_of_agree_below_use

/-!
### Requirements, injury and the finite injury lemma

`Start/Priority.lean` is the frame a priority construction runs in.  A construction
(`Lambda.Priority.Construction`) is a primitive recursive increasing sequence of finite
approximations, and the set it enumerates is c.e. (`Lambda.Priority.Construction.rePred_set`).  A
requirement (`Lambda.Priority.Requirement`) is a predicate on the approximation; it is *met at* a
stage when the approximation satisfies it, *injured at* a stage when it is satisfied there and no
longer at the next stage, and *met* when it is satisfied from some stage on — and a requirement
satisfied once and never injured again is met
(`Lambda.Priority.Requirement.met_of_not_injured`).

`Lambda.Priority.Injury` packages the priority ordering: requirements are indexed by the naturals,
a smaller index having the higher priority, a requirement is injured exactly when one of higher
priority acts, and the single hypothesis is that a requirement acts twice only with an injury in
between.  From that, `Lambda.Priority.Injury.acts_finite` — **each requirement acts only finitely
often** — and hence `Lambda.Priority.Injury.injured_finite` and
`Lambda.Priority.Injury.exists_final_stage`: from some stage on a requirement neither acts nor is
injured, which is the hypothesis `Lambda.Priority.Injury.requirements_met` turns into "every
requirement is met".
-/

#check @Lambda.Priority.Construction
#check @Lambda.Priority.Construction.rePred_set
#check @Lambda.Priority.Requirement
#check @Lambda.Priority.Requirement.InjuredAt
#check @Lambda.Priority.Requirement.met_of_not_injured
#check @Lambda.Priority.Injury
#check @Lambda.Priority.Injury.acts_finite
#check @Lambda.Priority.Injury.injured_finite
#check @Lambda.Priority.Injury.exists_final_stage
#check @Lambda.Priority.Injury.requirements_met
