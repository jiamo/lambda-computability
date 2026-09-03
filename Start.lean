/-
Canonical entry point for the `Start` library.

The development is split into focused modules; importing `Start` pulls in the
whole lambda-calculus formalization, including the boundary/interface records.
-/

-- Core layers
import Start.Tactics
import Start.Syntax
import Start.Reduction
import Start.LambdaEta
import Start.LambdaBetaEta
import Start.LambdaEtaPostpone
import Start.Church
import Start.Encoding

-- Arithmetization and computability
import Start.CodeOps
import Start.Computability
import Start.CodePrimrec
import Start.EvalSound
import Start.Arithmetic

-- Lambda-definable functions
import Start.Combinators
import Start.Sqrt
import Start.Pairing
import Start.Recursion
import Start.Realizer
import Start.Minimization
import Start.PartrecLambda

-- Interface records
import Start.EvalCorrect
import Start.GrossKnuth
import Start.EvalGK
import Start.Boundary

-- Compatibility: `Start.Basic` now only re-exports the modules above.
import Start.Basic

-- Weak head reduction, standardization, and divergence of minimisation
import Start.WeakHead
import Start.Standardization
import Start.Divergence
import Start.Leftmost
import Start.PartialCapstone

-- Fixed points, undecidability of convergence, and the second recursion theorem
import Start.FixedPoint
import Start.Undecidable
import Start.SecondRecursion
import Start.NormalizationUndecidable
import Start.Scott
import Start.ScottCurry
import Start.RiceCreative
import Start.CreativeCodeSets
import Start.Solvability
import Start.Bohm
import Start.BohmOut
import Start.BohmEta
import Start.HeadSpine
import Start.TagFail
import Start.SMN
import Start.SelfInterpreter
import Start.RecursionParams

-- Machine side: TM2-computable implies partial recursive, and the machine equivalence
import Start.TM2Partrec
import Start.TM2Restrict
import Start.TM2Forward
import Start.TM2Capstone
import Start.Encodings
import Start.TM2PolyTime
import Start.AlgorithmRepresentation

-- Size explosion / reasonable cost models
import Start.TermSize
import Start.SizeExplosion

-- Kolmogorov complexity
import Start.KolmogorovDef
import Start.Kolmogorov
import Start.KolmogorovCond
import Start.KolmogorovBinary
import Start.Kraft
import Start.ChaitinOmega
import Start.CodeArith
import Start.LeftmostRun
import Start.BusyBeaver
import Start.PlainVsPrefix
import Start.KolmogorovHalting
import Start.OmegaUncomputable

import Start.OmegaOracle
import Start.OmegaIncompressible
import Start.MartinLof

import Start.HaltingComplete
import Start.BLC
import Start.SimpleTypes
import Start.SystemF
import Start.SystemFSubst
import Start.SystemFSR
import Start.SystemFChurch
import Start.SystemFC
import Start.SystemFCSR
import Start.SystemFCSubst
import Start.SystemFCConfluence
import Start.SystemFParam
import Start.SystemTSyntax
import Start.SystemT
import Start.SystemTCanon
import Start.SystemTConfluence
import Start.SystemTDenot
import Start.Stlc
import Start.StlcCcc
import Start.CccModel
import Start.KleeneK
import Start.PostSimple
import Start.PostIncomplete
import Start.PostCreative
import Start.RiceShapiro
import Start.KraftConverse
import Start.StepComplexity
import Start.GapTheorem
import Start.BitString
import Start.KCMachine
import Start.KCComputable
import Start.OmegaUIncompressible
import Start.OmegaURandom
import Start.LevinSchnorr
import Start.KUOptimal

-- Representation bridges: de Bruijn <-> locally nameless (cslib) <-> BLC
import Start.Representation

-- Complexity classes: P, NP, polynomial-time many-one reductions, NP-completeness
import Start.ComplexityClasses
-- SAT as a language of binary words, and the proof that it is in NP
import Start.Sat
-- Boolean circuits and the Tseitin transformation into CNF
import Start.Tseitin
-- Cook-Levin: what is proved, and the compilation step that remains
import Start.CobhamCircuit
import Start.CobhamBRec
-- Polynomial-time functions are computed by polynomial-size circuits (P ⊆ P/poly)
import Start.PolyCircuit
import Start.CookLevin
-- Reading the instance off the circuit input, pinning it by unit clauses, and the resulting
-- Cook-Levin reduction from a length-indexed advice
import Start.InputSegment
import Start.PinnedCnf
import Start.PinnedCircuit
import Start.CobhamPin
import Start.CookLevinUniform
-- Cobham programming toolkit: finite-state transducers are polynomial-time functions
import Start.CobhamTransducer
-- Renumbering the variables of an encoded CNF in polynomial time
import Start.CobhamShift
-- Block-emitting finite-state recursions are polynomial-time functions
import Start.CobhamBlock
-- Circuits as words, and the Tseitin translation as a polynomial-time function
import Start.CircuitCode
import Start.CobhamTseitin
-- Cook-Levin from P-uniformity of the circuit descriptions
import Start.CookLevinCode
-- The P-uniformity hypothesis is inhabited by an explicit circuit family
import Start.CodeUniformExample
-- Cobham terms are countable, and the remaining Cook-Levin hypothesis in non-vacuous form
import Start.CobCountable
import Start.CookLevinExists
-- Closure properties of P-uniform circuit descriptions
import Start.UniformCircuit
-- Relocating a circuit, and stacking two P-uniform families
import Start.UniformShift
-- Composing circuits, and composing P-uniform families
import Start.UniformCompose
-- A nontrivial P-uniform family: the conjunction circuits
import Start.UniformAnd
-- The loop rule: layers driven by an automaton, and blocks of a fixed size
import Start.UniformBlock
-- Writing gate tokens, and a P-uniform family whose blocks carry an accumulator
import Start.UniformLoop
-- Division in unary, and grids of blocks whose width grows with the instance
import Start.UniformGrid
-- Boolean combinations of P-uniform circuit families
import Start.UniformBool
-- Languages decided by P-uniform families, and their unconditional reduction to SAT
import Start.UniformDecide

-- Kolmogorov complexity is independent of the representation of lambda terms
import Start.KolmogorovRepresentation

-- Denotational semantics: Scott's graph model as a reflexive object, and soundness of beta
import Start.GraphModel
import Start.GraphModelSemantics

-- Scott's D-infinity: the inverse limit of the tower D0 = Bool, D(n+1) = [Dn -> Dn],
-- the isomorphism D-infinity = [D-infinity -> D-infinity], and the induced lambda-eta model
import Start.ScottTower
import Start.ScottDinf
import Start.ScottPsi
import Start.ScottDinfIso
import Start.ScottDinfModel
import Start.ScottDinfOmega

-- Dependent type theory: the calculus lambda-Pi, its syntactic category, categories with
-- attributes, and the locally cartesian closed structure of Type
import Start.LambdaPi
import Start.LambdaPiEta
import Start.LambdaPiTyping
import Start.LambdaPiBound
import Start.LambdaPiUnique
import Start.LambdaPiSkeleton
import Start.LambdaPiSimple
import Start.LambdaPiSN
import Start.LambdaPiConsistent
import Start.LambdaPiNormalize
import Start.LambdaPiInfer
import Start.LambdaPiCat
import Start.Cwa
import Start.CwaLocalUniverse
import Start.CwaMor
import Start.CwaType
import Start.Lccc
import Start.LcccType
import Start.CwaPi
import Start.CwaPiSub
import Start.CwaPiType
import Start.LambdaPiCwa
import Start.CwaUniverse
import Start.LambdaPiFull
import Start.LambdaPiTypeUnique
import Start.LambdaPiUniv
import Start.CwaUnivLocal
import Start.CwaSubFunctorial
import Start.LambdaPiCoherent
import Start.CwaMorUniv
import Start.CwaCat
import Start.CwaStrictFunctor
import Start.CwaStrictSection
import Start.CwaStrictRigid
import Start.CwaStrictFull
import Start.CwaTwoCell
import Start.CwaBicat
import Start.CwaBiInitial
import Start.CwaUnivMorLocal
import Start.CwaSmall
import Start.LambdaPiSmallCompare
import Start.CookLevinBound
import Start.UniformAuto
import Start.UniformMaj
import Start.UniformSym
import Start.UniformState
import Start.UniformStateCode
import Start.UniformStateInst
import Start.UniformStateSubsume
import Start.UniformCA
import Start.UniformCACode
import Start.UniformCAInst
import Start.UniformTM
import Start.UniformTMInst
import Start.UniformLayerPad
import Start.UniformSelect
import Start.UniformIterate
import Start.UniformIterLang
import Start.UniformIterateInst
import Start.UniformPar
import Start.UniformSignal
import Start.UniformSigComp
import Start.UniformSigApp
import Start.UniformSigLayer
import Start.UniformSigCompile
import Start.UniformSigBound
import Start.UniformSigSmash
import Start.UniformSigFlat
import Start.UniformSigIter
import Start.UniformSigSel
import Start.UniformSigWire
import Start.UniformSigGadget
import Start.UniformSigRev
import Start.UniformSigRec
import Start.UniformSigAll
import Start.UniformSigLang
import Start.UniformSigNorm
import Start.UniformSegDec
import Start.CookLevinNPHard
import Start.HeadNormal
import Start.ParallelSubst
import Start.GraphAdequacy
import Start.GraphObs
import Start.FreeVars
import Start.HnfSolvable
import Start.HeadReduction
import Start.HeadSolvable
import Start.DinfHnf
import Start.DinfAdequacy
import Start.GraphNotFullyAbstract
import Start.GraphApprox
import Start.GraphApproxTheorem
import Start.DinfApprox
import Start.DinfEtaLimit
import Start.DinfApply
import Start.DinfBohmEta
import Start.DinfNormalFullAbstraction
import Start.DinfWadsworth
import Start.DinfWadsworthSharp
import Start.ApproxShape
import Start.HeadSpine
import Start.TagFail
import Start.DinfSpine
import Start.DinfTagBelow
import Start.DinfTagBelowSound
import Start.IntersectionTypes
import Start.FilterModel
import Start.IntersectionNormalization
import Start.LambdaTheory
import Start.InfiniteBohmTree
import Start.LambdaModel
import Start.LambdaModelInstances
import Start.LambdaModelComb
import Start.ReflexiveType
import Start.KaroubiLambda
import Start.ReflexiveCcc
import Start.ScottKoymans
import Start.CwaCodePi
import Start.CwaUnivNotClosed
import Start.CwaTypeModel
import Start.CwaCodeSigma
import Start.CwaTypeModelSigma
import Start.CircuitShift
import Start.KolmogorovPair
import Start.ChaitinIncompleteness
import Start.KolmogorovApprox
import Start.ReducesIn
import Start.LevinKt
import Start.LevinSearch
import Start.CwaVar
import Start.LambdaPiInterp
import Start.LambdaPiInterpFun
import Start.LambdaPiInterpSub
import Start.LambdaPiInterpConv
import Start.LambdaPiInterpTotal
import Start.LambdaPiInterpHom
import Start.LambdaPiSyntacticModel
import Start.LambdaPiInitial
import Start.LambdaPiInitialUniv
import Start.LambdaPiInitialNatural
import Start.LambdaPiSelfInterp
import Start.LambdaPiCtxConv
import Start.LambdaPiSelfIso
import Start.LambdaPiSelfMor
import Start.CwaTwoCellUniv
import Start.CwaMorVal
import Start.LambdaPiModelHom
import Start.LambdaPiInterpTransport
import Start.OracleSegment
import Start.OracleMachine
import Start.OracleSim
import Start.OracleJump
import Start.OracleSound
import Start.OracleForcing
import Start.KleenePost
import Start.OracleJoin
import Start.OracleUniversal
import Start.OracleCone
import Start.JumpSigmaOne
import Start.JumpApprox
import Start.LimitLemma
import Start.ArithHierarchy
import Start.PostTheoremTwo
import Start.ArithHierarchyProper
import Start.ArithBounded
import Start.ArithComplete
import Start.ArithIndexSets
import Start.Inseparable
import Start.MyhillIso
import Start.CreativeIso
import Start.PCA
import Start.PCATotal
import Start.PCAKleene
import Start.Assembly
import Start.AssemblyCcc
import Start.AssemblyLimits
import Start.AssemblyColimits
import Start.AssemblyNNO
import Start.AssemblySubobject
import Start.AssemblyImage
import Start.AssemblyRegular
import Start.AssemblyGlobalSections
import Start.AssemblyKleene
import Start.AssemblyKleeneBool
import Start.AssemblyProjective
import Start.PER
import Start.Modest
import Start.ModestEquiv
import Start.ModestCcc
import Start.ModestColimits
import Start.ModestImage
import Start.ModestNNO
import Start.ModestReflect
import Start.PERNNO
import Start.PERSystemF
import Start.Capstones
