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
import Start.SMN
import Start.SelfInterpreter

-- Machine side: TM2-computable implies partial recursive, and the machine equivalence
import Start.TM2Partrec
import Start.TM2Restrict
import Start.TM2Forward
import Start.TM2Capstone
