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
#check @Lambda.speckerVal
#check @Lambda.speckerVal_monotone
#check @Lambda.speckerVal_lt_one
#check @Lambda.computable_speckerNum
#check @Lambda.specker_no_computable_modulus
#check @Lambda.speckerReal
#check @Lambda.speckerVal_le_speckerReal
#check @Lambda.speckerReal_le_one
#check @Lambda.specker_limit_not_computable
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
