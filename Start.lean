/-
Canonical entry point for the `Start` library.

The development is split into focused modules; importing `Start` pulls in the
whole lambda-calculus formalization, including the boundary/interface records.
-/

-- Core layers
import Start.Tactics
import Start.Syntax
import Start.Reduction
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
import Start.Solvability
import Start.Bohm
import Start.BohmOut
import Start.BohmEta
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

-- Kolmogorov complexity
import Start.Kolmogorov
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
import Start.SystemTSyntax
import Start.SystemT
import Start.SystemTCanon
import Start.SystemTConfluence
import Start.SystemTDenot
import Start.Stlc
import Start.StlcCcc
import Start.CccModel
import Start.KleeneK
import Start.KraftConverse
import Start.StepComplexity
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
