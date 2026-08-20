/-
Compatibility layer for the historical monolithic development.

The lambda-calculus development now lives in dedicated modules; this file only
re-exports them so that `import Start.Basic` keeps working for downstream users.

Module map:
* `Start.Tactics`      – shared tactic helpers
* `Start.Syntax`       – terms, lifting, substitution
* `Start.Reduction`    – beta reduction, parallel reduction, confluence
* `Start.Church`       – Church numerals and the successor combinator
* `Start.Encoding`     – encoding/decoding of terms as natural numbers
* `Start.CodeOps`      – code-level operations and their primitive recursiveness
* `Start.Computability`– code evaluation, `Lambda.compute_fun`
* `Start.CodePrimrec`  – primitive recursiveness of the arithmetized operations
* `Start.EvalSound`    – soundness of code-level evaluation
* `Start.Arithmetic`   – Church arithmetic and the bridge to `Partrec`
* `Start.Combinators`  – booleans, pairs, predecessor, subtraction, comparisons
* `Start.Sqrt`         – fixed-point recursion and integer square root
* `Start.Pairing`      – pairing/unpairing and composition combinators
* `Start.Recursion`    – primitive recursion and minimisation combinators
* `Start.Realizer`     – lambda realizers and the primitive-recursion compiler
* `Start.Minimization` – correctness of the minimisation combinator
* `Start.PartrecLambda`– computable functions are lambda-computable (capstone equivalence)
* `Start.EvalCorrect`  – correctness analysis of the two code-level evaluators
* `Start.GrossKnuth`   – normalization of the complete-development strategy
* `Start.EvalGK`       – the Gross–Knuth evaluator and the unconditional `Partrec` bridge

The later modules (`Start.WeakHead`, `Start.Standardization`, `Start.Divergence`,
`Start.Leftmost`, `Start.PartialCapstone` and the machine-side modules `Start.TM2Partrec`,
`Start.TM2Restrict`, `Start.TM2Forward`, `Start.TM2Capstone`) are not re-exported here; import
`Start` for the whole development.
-/

import Start.Tactics
import Start.Syntax
import Start.Reduction
import Start.Church
import Start.Encoding
import Start.CodeOps
import Start.Computability
import Start.CodePrimrec
import Start.EvalSound
import Start.Arithmetic
import Start.Combinators
import Start.Sqrt
import Start.Pairing
import Start.Recursion
import Start.Realizer
import Start.Minimization
import Start.PartrecLambda
import Start.EvalCorrect
import Start.GrossKnuth
import Start.EvalGK
