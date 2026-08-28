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
import Start.CircuitShift
import Start.CobhamShift
import Start.CookLevinNPHard
import Start.CwaPiType
import Start.CwaTypeModelSigma
import Start.CwaUnivMorLocal
import Start.DinfWadsworthSharp
import Start.DinfTagBelowSound
import Start.DinfEtaLimit
import Start.GraphNotFullyAbstract
import Start.KolmogorovPair
import Start.LambdaPiConsistent
import Start.LambdaPiInfer
import Start.LevinKt
import Start.LevinSearch
import Start.SizeExplosion
import Start.UniformCAInst
import Start.UniformIterateInst
import Start.UniformSigFlat
import Start.UniformStateInst
import Start.UniformStateSubsume
import Start.UniformTMInst

/-! ## Interfaces of the untyped calculus

`Start/Boundary.lean` packages the reduction, encoding and computability development into records
a consumer can use without reaching into the proofs.
-/

#check @ReductionBoundary.roundtrip
#check @EncodingBoundary.fromConcrete
#check @ComputabilityInternalizer.toLambdaComputable

/-! ## Cost of reduction: the size explosion

`Start/SizeExplosion.lean`: there is a family of terms whose β-normal forms grow exponentially in
the number of steps, so the naive unit-cost model of β-reduction is not reasonable.
-/

#check @Lambda.exists_size_explosion
#check @Lambda.exists_size_explosion_steps

/-! ## Algorithmic information theory

`Start/KolmogorovPair.lean`: one half of the symmetry of information, `K(x, y) ≤ K(y) + K(x|y)`
up to an additive constant.

`Start/LevinKt.lean`: Levin complexity `Kt` and its invariance theorem.

`Start/LevinSearch.lean`: Levin's universal search and its optimality — for any verifiable search
problem the universal search finds a verified answer within a constant factor of any single
program's running time.
-/

#check @Lambda.exists_const_kolm_pair_le
#check @Lambda.exists_const_kolm_pair_le_add
#check @Lambda.kt_le_ktWith
#check @Lambda.kolm_le_kt
#check @Complexity.levinSearch_sound
#check @Complexity.levin_optimal

/-! ## Complexity: `SAT` is `NP`-complete, and P-uniform circuits

`Start/CookLevinNPHard.lean` is the Cook–Levin theorem in the form the library uses: `SAT` is
`NP`-hard, hence `NP`-complete, and `P = NP` iff `SAT ∈ P`.

The remaining modules feed the reduction: renumbering variables of an encoded `CNF`
(`Start/CobhamShift.lean`, `Start/CircuitShift.lean`), and the P-uniformity of the circuit
families produced by the various devices — cellular automata, iterated stages, flat Cobham terms,
finite-state machines and Turing machines.
-/

#check @Complexity.npHard_SAT
#check @Complexity.npComplete_SAT
#check @Complexity.peqNP_iff_inP_SAT
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

/-! ## Dependent types

`Start/LambdaPiConsistent.lean`: `λΠ` is consistent — the empty context types no variable.

`Start/LambdaPiInfer.lean`: type checking and type inference for `λΠ` are decidable, as running
`Decidable` instances.

`Start/CwaPiType.lean`, `Start/CwaTypeModelSigma.lean`, `Start/CwaUnivMorLocal.lean`: the
set-theoretic models — the local-universe model of `Type u` has a natural Π-structure, the
universe of small types is closed under dependent sums, and every morphism of a category with
pullbacks is a universe in the strictified model.
-/

#check @LambdaPi.not_typing_var_zero
#check @LambdaPi.decidableTypable
#check @LambdaPi.decidableTyping
#check @LcccType.luNaturalPiStruct
#check @CwaTypeModel.codeSigma
#check @CwaTypeModel.modelSigma
#check @CwaUniv.preservesUniverseOfHom
