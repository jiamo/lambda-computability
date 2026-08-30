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
import Start.CwaPiType
import Start.CwaTypeModelSigma
import Start.CwaUnivMorLocal
import Start.DinfWadsworthSharp
import Start.DinfTagBelowSound
import Start.DinfEtaLimit
import Start.GraphNotFullyAbstract
import Start.InfiniteBohmTree
import Start.IntersectionNormalization
import Start.KolmogorovPair
import Start.ChaitinIncompleteness
import Start.KolmogorovApprox
import Start.LambdaBetaEta
import Start.LambdaEtaPostpone
import Start.LambdaPiConsistent
import Start.LambdaPiEta
import Start.LambdaPiInfer
import Start.LambdaPiInitial
import Start.LambdaPiInitialUniv
import Start.LevinKt
import Start.LevinSearch
import Start.OracleCone
import Start.LimitLemma
import Start.PostTheoremTwo
import Start.OracleJoin
import Start.OracleUniversal
import Start.PostIncomplete
import Start.PostCreative
import Start.RiceCreative
import Start.CreativeCodeSets
import Start.RiceShapiro
import Start.ScottCurry
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
#check @LambdaPi.decidableTypable
#check @LambdaPi.decidableTyping
#check @LambdaPi.interp_exists_unique
#check @LambdaPiInitial.functor
#check @LambdaPiInitial.mor
#check @LambdaPiInitial.mor_preservesUniverse
#check @LambdaPiInitial.mor_preservesSmallPi
#check @LambdaPiInitial.mor_preservesPiClosed
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
