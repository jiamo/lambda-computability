/-
# Lambda Calculus Computability -- Demo

This file showcases the main results of the library:
a development of untyped lambda calculus with De Bruijn indices,
a proof of the Church-Rosser theorem (confluence), Church encodings
of arithmetic, the connection between Lambda-computability and partial
recursive functions, and the corresponding statement for Turing machines.
-/

import Start

/-! ## 1. Syntax -- De Bruijn Lambda Calculus -/

-- The three constructors: variables, application, abstraction.
#check Lambda.var   -- ℕ → Lambda
#check Lambda.app   -- Lambda → Lambda → Lambda
#check Lambda.lam   -- Lambda → Lambda

-- Example: the identity combinator  λx. x  is  `lam (var 0)`
#check Lambda.I     -- Lambda.lam (Lambda.var 0)

-- Example: the K combinator  λx. λy. x
#check Lambda.K     -- Lambda.lam (Lambda.lam (Lambda.var 1))

-- Lifting and capture-avoiding substitution.
#check Lambda.lift  -- (n k : ℕ) → Lambda → Lambda
#check Lambda.subst -- (s : Lambda) → (x : ℕ) → Lambda → Lambda

/-! ## 2. Reduction -/

-- Single-step beta reduction (contextual closure of beta).
#check Lambda.step    -- Lambda → Lambda → Prop

-- Parallel reduction (Tait-Martin-Löf).
#check Lambda.step_p  -- Lambda → Lambda → Prop

-- Reflexive-transitive closure of single-step reduction.
#check Lambda.reduces -- Lambda → Lambda → Prop

/-! ## 3. De Bruijn Substitution Lemmas

A complete library of substitution/lifting identities needed for
metatheory.  All fully proved, no sorry. -/

#check Lambda.lift_zero      -- lift 0 k t = t
#check Lambda.lift_add       -- lift (n+m) k t = lift n k (lift m k t)  (under conditions)
#check Lambda.lift_lift      -- commutation of two lifts
#check Lambda.lift_subst     -- lift distributes over subst
#check Lambda.subst_lift     -- subst after lift cancels
#check Lambda.subst_subst    -- substitution composition

/-! ## 4. Confluence (Church-Rosser Theorem)

Proved via Takahashi's method:
  parallel reduction → diamond property → strip lemma → confluence. -/

-- Parallel reduction is preserved under lifting.
#check Lambda.step_p_lift

-- Parallel reduction is preserved under substitution.
#check Lambda.step_p_subst

-- The diamond property for parallel reduction.
#check Lambda.step_p_diamond
-- ∀ {t t1 t2}, step_p t t1 → step_p t t2 → ∃ t3, step_p t1 t3 ∧ step_p t2 t3

-- Strip lemma: one parallel step vs. many single steps still join.
#check Lambda.strip_lemma

-- **Church-Rosser / Confluence** -- the main theorem.
#check Lambda.confluence_theorem
-- Lambda.Confluence
-- = ∀ {t t1 t2}, reduces t t1 → reduces t t2 → ∃ t3, reduces t1 t3 ∧ reduces t2 t3

/-! ## 5. Church Numerals and Lambda-Computability -/

-- Church numeral: `church n = λf. λx. f (f (... (f x)...))` with n applications.
#check Lambda.church  -- ℕ → Lambda

-- A partial function is Lambda-computable when a closed term realises it
-- on Church numerals.
#check LambdaComputable
-- (f : ℕ →. ℕ) → Prop
-- ∃ F, ∀ n m, f n = Part.some m ↔ reduces (app F (church n)) (church m)

-- Binary version for two-argument functions.
#check LambdaComputable2

/-! ## 6. Encoding Lambda Terms as Natural Numbers

A Gödel numbering of lambda terms into ℕ (via `Nat.pair`),
together with Primrec proofs for all encoding/decoding operations. -/

#check Lambda.encode       -- Lambda → ℕ
#check Lambda.decode       -- ℕ → Lambda
#check Lambda.church_code  -- ℕ → ℕ   (encoding of church n)

/-! ## 7. Church Arithmetic -- Correctness Theorems

Each arithmetic operation has a lambda term and a proof that it
correctly computes on Church numerals. -/

section Arithmetic

-- Successor: succ (church n) ⟶* church (n+1)
#check Lambda.succ_works
-- ∀ n, reduces (app succ (church n)) (church (n + 1))

-- Addition: add (church n) (church m) ⟶* church (n+m)
#check Lambda.add_works
-- ∀ n m, reduces (app (app add (church n)) (church m)) (church (n + m))

-- Multiplication: mult (church n) (church m) ⟶* church (n*m)
#check Lambda.mult_works
-- ∀ n m, reduces (app (app mult (church n)) (church m)) (church (n * m))

-- Predecessor: pred (church n) ⟶* church (n-1)
#check Lambda.pred_works
-- ∀ n, reduces (app pred (church n)) (church (n - 1))

-- Subtraction: sub (church n) (church m) ⟶* church (n-m)
#check Lambda.sub_works
-- ∀ n m, reduces (app (app sub (church n)) (church m)) (church (n - m))

-- Square root: sqrt_v2 (church n) ⟶* church (√n)
#check Lambda.sqrt_v2_works
-- ∀ n, reduces (app sqrt_v2 (church n)) (church (Nat.sqrt n))

-- Pairing: natPair' (church n) (church m) ⟶* church (Nat.pair n m)
#check Lambda.natPair'_works
-- ∀ n m, reduces (app (app natPair' (church n)) (church m)) (church (Nat.pair n m))

-- Left unpair: unpairLeft (church n) ⟶* church (n.unpair.1)
#check Lambda.unpairLeft_works

-- Right unpair: unpairRight (church n) ⟶* church (n.unpair.2)
#check Lambda.unpairRight_works

end Arithmetic

/-! ## 8. Lambda-Computable Functions

Using confluence + the arithmetic correctness theorems, we derive
that each basic function is Lambda-computable. -/

section Computable

-- The constant-zero function is Lambda-computable.
#check LambdaComputable.zero
-- LambdaComputable (fun _ => Part.some 0)

-- Successor is Lambda-computable.
#check LambdaComputable.succ
-- Confluence → LambdaComputable (fun n => Part.some (n + 1))

-- Predecessor is Lambda-computable.
#check LambdaComputable.pred
-- Confluence → LambdaComputable (fun n => Part.some (n - 1))

-- Square root is Lambda-computable.
#check LambdaComputable.sqrt
-- Confluence → LambdaComputable (fun n => Part.some (Nat.sqrt n))

-- Left projection (unpair) is Lambda-computable.
#check LambdaComputable.unpairLeft
-- Confluence → LambdaComputable (fun n => Part.some n.unpair.1)

-- Right projection (unpair) is Lambda-computable.
#check LambdaComputable.unpairRight
-- Confluence → LambdaComputable (fun n => Part.some n.unpair.2)

-- Addition is Lambda-computable (binary).
#check LambdaComputable2.add
-- Confluence → LambdaComputable2 (fun n m => Part.some (n + m))

-- Multiplication is Lambda-computable (binary).
#check LambdaComputable2.mult
-- Confluence → LambdaComputable2 (fun n m => Part.some (n * m))

-- Subtraction is Lambda-computable (binary).
#check LambdaComputable2.sub
-- Confluence → LambdaComputable2 (fun n m => Part.some (n - m))

-- Pairing is Lambda-computable (binary).
#check LambdaComputable2.pair
-- Confluence → LambdaComputable2 (fun n m => Part.some (Nat.pair n m))

end Computable

/-! ## 9. Connection to Partial Recursive Functions

The evaluation function `Lambda.eval` interprets encoded lambda terms
and is itself partial-recursive.  This gives one direction of the
equivalence: Lambda-computable → Partrec. -/

-- eval : ℕ →. ℕ  -- evaluates an encoded lambda term to normal form.
#check Lambda.eval

-- eval is a partial recursive function.
#check Lambda.eval_partrec  -- Partrec Lambda.eval

-- **LambdaComputable → Partrec**  (assuming eval-correctness).
#check LambdaComputable_imp_Partrec
-- EvalCorrectness → LambdaComputable f → Partrec f

-- The Gross–Knuth evaluator iterates the complete development `Lambda.rho` to a fixed point;
-- it is proved correct, so the bridge to `Partrec` needs no hypothesis at all.
#check Lambda.evalCorrectnessGK
-- ∀ t n, reduces t (church n) ↔ eval_gk (encode t) = Part.some (church_code n)

#check LambdaComputable_imp_Partrec_unconditional
-- LambdaComputable f → Partrec f

/-! ## 10. The reverse direction and the capstone equivalence -/

-- Every primitive recursive function has a closed lambda realizer.
#check @Lambda.exists_realizer_of_primrec
-- Nat.Primrec f → ∃ F, Lambda.Realizes F f

-- Minimisation is correct when a witness exists.
#check Lambda.muCorrectness
-- Lambda.MuCorrectness

-- Kleene normal form turns the two into a realizer for every total computable function.
#check @Lambda.exists_realizer_of_computable
-- Computable f → ∃ F, Lambda.Realizes F f

-- **Lambda-definable iff recursive**, for total functions.
#check @lambdaComputable_iff_computable
-- LambdaComputable (fun n => Part.some (f n)) ↔ Computable f

/-! ## 11. Weak head reduction, standardization and the partial capstone -/

-- Standardization: every reduction can be rearranged into a standard one.
#check @Lambda.sred_of_reduces
-- Lambda.reduces M N → Lambda.SRed true M N

-- Hence the weak head strategy is normalizing.
#check @Lambda.hasWhnfEval_of_reduces_whnf
-- Lambda.reduces t u → Lambda.IsWhnf u → Lambda.HasWhnfEval t

-- The divergence half of minimisation: with no witness, the search reduces to no numeral.
#check Lambda.muDivergence
-- Lambda.MuDivergence

-- **Lambda-definable iff partial recursive**, for arbitrary partial functions.
#check @lambdaComputable_iff_partrec
-- LambdaComputable f ↔ Partrec f

/-! ## 12. The machine side -/

-- The code-level behaviour of any bundled Turing machine with finite stack alphabets is
-- a partial recursive function.
#check @TM2Partrec.partrec_evalCode
-- Partrec (TM2Partrec.evalCode tm)

-- Conversely, every partial recursive function is computed by such a machine.
#check @TM2Partrec.tm2ComputableNat_of_partrec
-- Partrec f → TM2Partrec.TM2ComputableNat f

-- **Machine computable iff partial recursive.**
#check @TM2Partrec.tm2Computable_iff_partrec
-- TM2Partrec.TM2ComputableNat f ↔ Partrec f

-- **The two models agree.**
#check @lambdaComputable_iff_tm2Computable
-- LambdaComputable f ↔ TM2Partrec.TM2ComputableNat f

/-! ## 13. Fixed points, Scott's theorem and Rice's theorem -/

-- Kleene's second recursion theorem: every closed `F` has an `X` with `X ↠ F ⌜X⌝`.
#check @Lambda.exists_code_fixed_point
-- Lambda.IsClosed F → ∃ X, Lambda.reduces X (F.app (Lambda.church X.encode))

-- **Scott's theorem**: no closed term decides a non-trivial convertibility-invariant property.
#check @Lambda.scott_theorem
-- ConvInvariant A → closed witnesses inside and outside A → ¬ Lambda.Decides F A

-- **Rice's theorem for the lambda calculus**: its code set is not computable.
#check @Lambda.not_computablePred_codeSet
-- ¬ ComputablePred (Lambda.CodeSet A)

-- A concrete instance: convertibility with `church 0` is undecidable.
#check @Lambda.not_computablePred_codeSet_conv_church_zero

-- **The Scott–Curry theorem**: two convertibility-invariant sets of terms, each with a closed
-- member, have recursively inseparable code sets.
#check @Lambda.scott_curry
#check @Lambda.scott_curry_codeSet
-- Concretely, for `m ≠ n` the codes of the terms convertible with `church m` cannot be
-- separated from the codes of those convertible with `church n`.
#check @Lambda.recursivelyInseparable_conv_church

-- **Rice's theorem, effective form**: a convertibility-invariant set of terms that contains no
-- unsolvable term has a code set many-one above the halting problem, hence a complement that is
-- not r.e., and is creative as soon as it is r.e.
#check @Lambda.manyOneReducible_haltK_codeSet
#check @Lambda.not_rePred_compl_codeSet
#check @Lambda.creative_codeSet

-- Which of these code sets are actually creative?  Convertibility with a Church numeral, the
-- lambda-calculus halting set and convergence to a numeral all are, hence all are many-one
-- equivalent to Kleene's `K`.
#check @Lambda.creative_codeSet_conv_church
#check @Lambda.creative_codeHasNormalForm
#check @Lambda.creative_codeConverges
#check @Lambda.manyOneEquiv_codeHasNormalForm_codeConverges
-- For instance the codes of the solvable terms.
#check @Lambda.manyOneReducible_haltK_codeSet_solvable
#check @Lambda.not_rePred_compl_codeSet_solvable

-- **Myhill's isomorphism theorem**: one-one equivalence is the same as recursive isomorphism, so
-- one-one equivalent sets are computably in bijection with one another.
#check @Lambda.Myhill.recIso_iff_oneOneEquiv

-- A productive set has an *injective* production function, so a creative set is one-one complete
-- and therefore recursively isomorphic to `K`: all the code sets above are computably in
-- bijection with the halting set, and any two creative sets with one another.
#check @Lambda.Post.exists_injective_productive
#check @Lambda.Post.Creative.oneOneComplete
#check @Lambda.Post.Creative.recIso_haltK
#check @Lambda.Post.Creative.recIso
#check @Lambda.recIso_codeSet_conv_church_haltK
-- In fact the creative sets are exactly the sets recursively isomorphic to `K`.
#check @Lambda.Post.creative_iff_recIso_haltK

-- The uniform s-m-n theorem for this coding.
#check @Lambda.exists_smn
-- ∃ s, Primrec₂ s ∧ ∀ F n, Lambda.decode (s F.encode n) = some (F.app (Lambda.church n))

/-! ## 13b. A self-interpreter

The arithmetized evaluator works on codes.  On the lambda level there is a single closed term `E`
that turns the *numeral of the code* of a closed term back into the term itself — and it does so by
reduction, not merely up to conversion. -/

#check @Lambda.exists_self_interpreter
-- ∃ E, E.IsClosed ∧ ∀ M, M.IsClosed → (E.app (Lambda.church M.encode)).reduces M

-- The general form: on an arbitrary term, in an environment realizing `u`, the interpreter
-- produces the parallel substitution `substEnv u t`.
#check @Lambda.selfEval_correct

-- The converse fails: quoting is not lambda-definable.
#check @Lambda.not_exists_quote

/-! ## 13c. Recursion with parameters, other encodings, complexity, solvability, algorithms -/

-- Kleene's recursion theorem **with parameters**: a primitive recursive `s` such that the term
-- coded by `s y` reduces to `F ⌜s y⌝ ⌜y⌝`.
#check @Lambda.exists_recursion_with_parameters

-- The model equivalence for binary (curried) functions.
#check @lambdaComputable2_iff_partrec₂
#check @lambdaComputable2_iff_tm2Computable

-- ... and for an arbitrary `Primcodable` input type, via its encoding.
#check @lambdaComputableEnc_iff_tm2ComputableEnc

-- Time-bounded machines: a machine running in polynomial time computes a lambda-definable
-- function (the converse direction, a resource-preserving compilation, is not formalized).
#check @TM2Partrec.lambdaComputable_of_tm2ComputableNatInPolyTime
-- A bridge to Mathlib's own polynomial-time notion.
#check @TM2Partrec.partrec_of_tm2ComputableInPolyTime

-- Solvability: `Ω` is unsolvable, solvable terms reach any closed term, and solvability is
-- undecidable.
#check @Lambda.not_solvable_omega
#check @Lambda.exists_args_conv_of_solvable
#check @Lambda.not_computablePred_codeSet_solvable

-- Böhm's separation theorem: the normal terms are exactly the denotations of the finite Böhm
-- trees, and two closed normal forms whose trees are not η-equal are separated by a list of
-- closed arguments, which sends the first term to `true` and the second to `false`.
#check @Lambda.is_normal_iff_exists_bohmNF
#check @Lambda.BohmNF.toTerm_injective
#check @Lambda.separable_toTerm_of_not_tagEq
-- The Böhm-out step, which brings a difference deep inside the two trees up to the root.
#check @Lambda.separable_of_tagDiffer

-- A Dershowitz–Gurevich style **representation theorem**: the input-output function of a
-- bounded-exploration sequential algorithm is partial recursive, hence lambda-definable.
-- This is a theorem about the stated axioms, not a proof of the Church–Turing thesis.
#check @SeqAlgorithm.Algorithm.partrec_run
#check @SeqAlgorithm.Algorithm.lambdaComputable_run

/-! ## 13d. Kolmogorov complexity

Program length is the syntactic size of a closed term reducing to a Church numeral. -/

#check @Lambda.kolm
-- Lambda.kolm : ℕ → ℕ, the least size of a closed term reducing to `church s`

-- Incompressible numbers exist (a counting argument).
#check @Lambda.exists_incompressible
-- ∀ n, ∃ s, n ≤ Lambda.kolm s

-- Berry's paradox through the second recursion theorem: the relation `K s ≤ n` is undecidable,
-- and `K` is not computable.
#check @Lambda.not_computablePred_kolm_le
#check @Lambda.not_computable_kolm

-- Invariance: a fixed closed interpreter changes `K` by at most an additive constant, ...
#check @Lambda.kolm_le_kolmWith

-- ... and every partial recursive (equivalently, Turing machine computable) description system is
-- bounded by `K` up to a constant — with compact binary numerals, in terms of *bit length*.
#check @Lambda.exists_const_kolm_le_of_partrec
#check @Lambda.exists_const_kolm_le_size_of_tm2

-- Chaitin's incompleteness theorem: read `S x n` as "the system proves `K x > n`".  A sound,
-- recursively enumerable system proves only boundedly many such lower bounds, so from some
-- threshold on it proves none of them, although they are true.
#check @Lambda.chaitin_incompleteness
#check @Lambda.exists_true_unprovable_kolm_lower_bound

-- `K` is upper semicomputable: `K s ≤ n` is recursively enumerable, the opposite relation
-- `n < K s` is not, and `K` is the infimum of a primitive recursive decreasing approximation.
#check @Lambda.rePred_kolm_le
#check @Lambda.not_rePred_lt_kolm
#check @Lambda.kolmAt_eventually_eq_kolm
#check @Lambda.kolm_eq_iInf_kolmAt
#check @Lambda.primrec_kolmAt

/-! ## 14. Prefix complexity and Chaitin's Omega -/

-- The binary lambda calculus coding of terms is prefix free, ...
#check @Lambda.bits_prefixFree

-- ... so Kraft's inequality applies: prefix complexity satisfies `∑ 2 ^ (-K(s)) ≤ 1`, ...
#check @Kraft.tsum_wt_le_one
#check @Lambda.kraft_kolmP

-- ... and conversely, for non-decreasing lengths Kraft's inequality is exactly the condition
-- for a prefix free coding with those lengths to exist.
#check @Kraft.prefixFreeCoding_kraftCode
#check @Kraft.exists_prefixFree_iff

-- ... and the halting probability is a convergent sum lying strictly between 0 and 1.
#check @Lambda.summable_haltingWeight
#check @Lambda.chaitinOmega_mem_Ioo

-- `Ω` is not a computable real, hence irrational, ...
#check @Lambda.not_realComputable_chaitinOmega
#check @Lambda.irrational_chaitinOmega

-- ... its first `n` bits decide the halting problem for every program of at most `n - 2` bits, ...
#check @Lambda.chaitinOmega_prefix_decides_halting

-- ... and those bits are incompressible: `K(Ω ↾ n) ≥ n - O(1)` (Chaitin's theorem).
#check @Lambda.dodge_spec
#check @Lambda.exists_const_le_kolmP_omegaPrefix

/-! ## 14b. Martin-Löf randomness -/

-- The uniform measure on Cantor space and the measure of a cylinder, ...
#check @Lambda.cantorMeasure
#check @Lambda.cantorMeasure_cylinder

-- ... Martin-Löf tests and Martin-Löf randomness, ...
#check @Lambda.MLTest
#check @Lambda.MLRandom

-- ... no computable sequence is random, ...
#check @Lambda.not_mlRandom_of_computable

-- ... and random sequences have incompressible prefixes (the easy half of Levin-Schnorr).
#check @Lambda.exists_const_le_kolmP_prefix_of_mlRandom

-- For the Kraft-Chaitin universal prefix machine both halves hold, so Martin-Löf randomness
-- *is* incompressibility of all prefixes (the Levin-Schnorr theorem), ...
#check @KC.exists_const_le_KU_prefix_of_mlRandom
#check @KC.mlRandom_of_exists_const_le_KU
#check @KC.mlRandom_iff_exists_const_le_KU

-- ... and the bit sequence of Chaitin's `Ω` is Martin-Löf random.
#check @KC.mlRandom_omegaSeq

-- The Kraft-Chaitin machine is optimal for the lambda prefix machine: `KU` is below the
-- lambda prefix complexity up to an additive constant.
#check @KC.exists_const_KU_le_kolmP

/-! ## 14c. The halting set in the arithmetical hierarchy -/

-- Halting is r.e., every r.e. predicate reduces to it, so it is Σ₁-complete, ...
#check @Lambda.rePred_codeHasNormalForm
#check @Lambda.rePred_le_codeHasNormalForm
#check @Lambda.codeHasNormalForm_sigma1_complete

-- ... in fact one-one complete, ...
#check @Lambda.codeHasNormalForm_one_complete

-- ... and by Post's theorem its complement is not r.e.
#check @Lambda.not_rePred_not_codeHasNormalForm

-- Kleene's diagonal halting set is one-one complete too, hence the two halting problems
-- are one and the same problem.
#check @Lambda.haltK_one_complete
#check @Lambda.oneOneEquiv_haltK_codeHasNormalForm

/-! ## 14c''. Post's problem for many-one reducibility -/

-- Post's simple set: r.e., with an infinite complement, ...
#check @Lambda.Post.rePred_simpleSet
#check @Lambda.Post.simpleSet_compl_infinite

-- ... which meets every infinite r.e. set, so it is not computable.
#check @Lambda.Post.simpleSet_meets_rePred
#check @Lambda.Post.not_computablePred_simpleSet

-- A productive set contains an infinite r.e. subset, so a simple set is not complete:
-- there is an r.e. set which is neither computable nor many-one complete.
#check @Lambda.Post.exists_infinite_re_subset
#check @Lambda.Post.exists_rePred_not_computable_not_manyOneComplete

-- The other extreme: by Myhill's theorem a creative set (r.e. with productive complement) is
-- many-one complete, hence many-one equivalent to the halting set and never simple.
#check @Lambda.Post.exists_recursion_index
#check @Lambda.Post.creative_haltK
#check @Lambda.Post.Creative.manyOneEquiv_haltK
#check @Lambda.Post.creative_iff_manyOneComplete
#check @Lambda.Post.not_creative_simpleSet

-- Rice–Shapiro: an r.e. extensional class of r.e. sets is generated by its finite members, so
-- the indices of the empty set and the indices of the total functions are not r.e.
#check @Lambda.Post.rice_shapiro
#check @Lambda.Post.not_rePred_emptyIndex
#check @Lambda.Post.not_rePred_totalIndex

/-! ## 14c'''. Relative computability, the jump and the arithmetical hierarchy -/

-- Oracle machines: a universal machine, the join of two oracles as the least upper bound of two
-- degrees, and the counting argument giving uncountably many Turing degrees.
#check @Lambda.Oracle.exists_universal_index
#check @Lambda.Oracle.turingDegree_isLUB_join
#check @Lambda.Oracle.not_countable_turingDegree

-- The Turing jump is Σ₁-hard, uniformly in the oracle: one computable reduction sends an r.e.
-- predicate into `A'` for every oracle `A` at once, so every r.e. predicate is decidable
-- relative to `∅'`.
#check @Lambda.Oracle.exists_index_repred
#check @Lambda.Oracle.turingReducible_haltingOracle_of_repred

-- Shoenfield's limit lemma: a set is the pointwise limit of a computable sequence of guesses
-- exactly when it is computable from `∅'`.  Hence every r.e. set is limit computable, `∅''` is
-- not.
#check @Lambda.Oracle.LimitComputable
#check @Lambda.Oracle.limitComputable_iff_turingReducible_haltingOracle
#check @Lambda.Oracle.limitComputable_of_repred
#check @Lambda.Oracle.not_limitComputable_jumpChar_haltingOracle

-- The arithmetical hierarchy: alternating quantifier prefixes over a computable matrix, with
-- duality, the inclusions `Σ⁰ₙ ∪ Π⁰ₙ ⊆ Δ⁰ₙ₊₁` and the closure properties.
#check @Lambda.Arith.SigmaAt
#check @Lambda.Arith.PiAt
#check @Lambda.Arith.DeltaAt
#check @Lambda.Arith.piAt_iff_sigmaAt_not
#check @Lambda.Arith.SigmaAt.of_piAt
#check @Lambda.Arith.SigmaAt.and
#check @Lambda.Arith.SigmaAt.exists
#check @Lambda.Arith.PiAt.forall

-- Its bottom levels are the computable, the r.e. and the co-r.e. predicates.
#check @Lambda.Arith.sigmaAt_zero_iff
#check @Lambda.Arith.sigmaAt_one_iff
#check @Lambda.Arith.piAt_one_iff
#check @Lambda.Arith.deltaAt_one_iff

-- Post's theorem at level two: `Δ⁰₂` is exactly the limit computable predicates, hence exactly
-- the predicates decidable from `∅'`.
#check @Lambda.Arith.LimitComputablePred
#check @Lambda.Arith.deltaAt_two_iff_limitComputablePred
#check @Lambda.Arith.deltaAt_two_iff_turingReducible_haltingOracle

-- The hierarchy is proper: every level `n + 1` has a universal predicate, whose diagonal
-- complement separates the level from its dual, so the three families grow strictly.
#check @Lambda.Arith.UnivSigma
#check @Lambda.Arith.exists_univSigma
#check @Lambda.Arith.UnivSigma.not_sigmaAt_diag
#check @Lambda.Arith.sigmaAt_ne_piAt
#check @Lambda.Arith.sigmaAt_proper
#check @Lambda.Arith.piAt_proper
#check @Lambda.Arith.deltaAt_proper

-- The union of the levels, the arithmetical predicates, has no universal predicate.
#check @Lambda.Arith.Arithmetical
#check @Lambda.Arith.exists_arithmetical_not_sigmaAt
#check @Lambda.Arith.not_exists_univ_arithmetical

-- Bounded quantifiers, with a computable bound, do not raise the level.
#check @Lambda.Arith.computablePred_ball_lt
#check @Lambda.Arith.exists_code_of_ball_exists
#check @Lambda.Arith.SigmaAt.ball_lt
#check @Lambda.Arith.SigmaAt.bex_lt
#check @Lambda.Arith.PiAt.ball_lt
#check @Lambda.Arith.PiAt.bex_lt

/-! ## 14c'. A Blum complexity measure and a diagonal hierarchy -/

-- Fuel counting is a Blum complexity measure: defined exactly on the domain, decidably bounded.
#check @Complexity.steps_dom_iff
#check @Complexity.primrec_stepsLe

-- No computable bound suffices for every computable function.
#check @Complexity.exists_computable_not_withinFuel
#check @Complexity.exists_computable_steps_gt

/-! ## 14d. Binary lambda calculus: decoding bit strings back into terms -/

-- The BLC code is invertible, giving a bijection between terms and valid bit strings.
#check @Lambda.blcDecodeFull_eq_some_iff
#check @Lambda.bitsEquiv

/-! ## 14e. Typed calculi: simple types and Gödel's System T -/

-- Simply typed terms are strongly normalizing, and `omega` is untypable.
#check @Lambda.sn_of_typing
#check @Lambda.not_typing_omega

-- System T: strong normalization, subject reduction, and canonicity.
#check @GodelT.sn_of_typing
#check @GodelT.typing_reduces
#check @GodelT.exists_reduces_num
#check @GodelT.reduces_addTm

/-! ## 14f. Denotational semantics: the graph model and Scott's `D∞` -/

-- Scott's graph model is a reflexive object: the continuous function space is a retract of `D`.
#check @GraphModel.appD_graph
#check @GraphModel.graph_appD_ne

-- Soundness of the interpretation, and a semantic consistency proof for the beta calculus.
#check @GraphModel.denot_conv
#check @GraphModel.denot_omega
#check @GraphModel.not_conv_omega_I

-- Adequacy: a nonempty denotation means a head normal form, and for a closed term the least
-- element is reached exactly by the unsolvable terms.
#check @GraphModel.hasHnf_of_mem_denot
#check @GraphModel.denot_ne_empty_iff_hasHnf
#check @Lambda.solvable_iff_hasHnf
#check @GraphModel.denot_ne_empty_iff_solvable

-- Hence denotational equality implies observational equivalence at head normalization.
#check @GraphModel.obsEqHnf_of_denot_eq

-- Head reduction: the head strategy is normalizing, which gives the structural laws of head
-- normalizability and a syntactic proof that solvable terms have a head normal form.
#check @Lambda.hstep
#check @Lambda.isHnf_iff_no_hstep
#check @Lambda.hasHnf_iff_hasHeadEval
#check @Lambda.hasHnf_of_hasHnf_subst
#check @Lambda.HasHnf.app_left
#check @Lambda.hasHnf_of_solvable

-- Scott's `D∞`: every element is the supremum of its finite approximations, and `D∞` is
-- isomorphic to its own space of continuous self-maps.
#check @ScottDinf.ωSup_thetaChain
#check @ScottDinf.dinfOrderIso
#check @ScottDinf.dinf_nontrivial

-- The induced model of the lambda calculus is extensional: it validates beta *and* eta.
#check @ScottDinf.ddenot_conv
#check @ScottDinf.ddenot_eta

-- `Ω` denotes the least element, so `Ω` and `I` are not βη-convertible: the λη calculus is
-- consistent, again by a purely semantic argument.
#check @ScottDinf.ddenot_omega
#check @ScottDinf.not_convBE_omega_I

-- `D∞` identifies a term with its *infinite* η-expansion: `J = Θ (λ j x y. x (j y))` denotes the
-- identity, although the two are not β-convertible.
#check @ScottDinf.eq_dId_of_eta_fixpoint
#check @ScottDinf.ddenot_Jterm_eq_ddenot_id
#check @ScottDinf.obsEqHnf_Jterm_id
#check @ScottDinf.not_conv_Jterm_I

-- **Wadsworth's theorem**: two closed terms are observationally equivalent, by head
-- normalisation, exactly when they have the same denotation in `D∞`.  Equivalently, the `D∞`
-- order between closed terms is the absence of a finite failure witness `Lambda.TagFail`.
#check @ScottDinf.obsEqHnf_iff_ddenot_eq
#check @ScottDinf.tagBelowSound
#check @ScottDinf.ddenot_le_iff_not_tagFail_unconditional
#check @ScottDinf.le_ddenot_of_not_tagFail_approx
#check @ScottDinf.le_ddenot_of_not_tagFail_var

-- Conversely, in `D∞` a head normalizable term is somewhere different from the least element,
-- so a term denoting `⊥` in every environment has no head normal form and is unsolvable.
#check @ScottDinf.exists_ddenot_ne_botDinf_of_hasHnf
#check @ScottDinf.not_hasHnf_of_ddenot_eq_botDinf
#check @ScottDinf.not_solvable_of_ddenot_eq_botDinf

/-! ## 14f'. Intersection types and the filter model -/

-- The strict types of the Coppo–Dezani system are the tokens of the graph model, and type
-- assignment *is* membership in the denotation: the graph model is the filter model.
#check @Inter.Deriv
#check @Inter.deriv_iff_mem_denot
#check @Inter.typeSet_eq_denot

-- Subject reduction and subject expansion, hence invariance of the type set under conversion.
#check @Inter.deriv_reduces
#check @Inter.deriv_expansion
#check @Inter.deriv_conv

-- Typable = nonempty denotation = has a head normal form = solvable.
#check @Inter.typable_iff_hasHnf
#check @Inter.typable_iff_denot_ne_empty
#check @Inter.typable_iff_solvable
#check @Inter.not_typable_omega

-- The Coppo–Dezani normalisation theorem: `ω`-free typability is exactly normalisation, and the
-- inclusion into typability is strict.
#check @Inter.Proper
#check @Inter.properTypable_iff_hasNormalForm
#check @Inter.exists_typable_not_properTypable

/-! ## 14f''. The lattice of λ-theories, and infinite Böhm trees -/

-- A λ-theory is a context-closed equivalence relation containing β-conversion.  Four of them:
-- β itself, the theory of the graph model, the theory of `D∞`, and observational equivalence.
#check @Lambda.LambdaTheory
#check @Lambda.LambdaTheory.beta
#check @Lambda.LambdaTheory.graph
#check @Lambda.LambdaTheory.dinf
#check @Lambda.LambdaTheory.hstar

-- The classical picture, on closed terms: `B ⊊ Th(𝒫ω) ⊊ Th(D∞) = H*`.  The first inclusion is
-- strict because the graph model equates `Ω` and `Ω I`, which are not β-convertible; the second
-- because `D∞` validates η; the last equality is Wadsworth's theorem.
#check @Lambda.LambdaTheory.beta_le
#check @Lambda.LambdaTheory.not_conv_omega_app_omega_I
#check @Lambda.LambdaTheory.beta_lt_graph
#check @Lambda.LambdaTheory.graph_lt_dinf
#check @Lambda.LambdaTheory.dinf_eq_hstar_closed
#check @Lambda.LambdaTheory.theory_chain

-- The infinite Böhm tree of a term, as the directed set of the direct approximants of its
-- reducts; the approximation order is transitive on those, so Böhm tree equality is an
-- equivalence relation, strictly above β and below the theory of the graph model.
#check @Lambda.BohmTree
#check @Lambda.approx_direct_trans
#check @Lambda.BohmEq
#check @Lambda.bohmEq_of_conv
#check @Lambda.graph_of_bohmEq
#check @Lambda.exists_bohmEq_not_conv
#check @Lambda.bohmEq_between_beta_and_graph

/-! ## 14f'''. λ-models and reflexive objects -/

-- A λ-model in the sense of Meyer and Scott: an applicative structure with a compositional,
-- β-satisfying, weakly extensional interpretation.  Soundness and the λ-theory of a model come
-- from the axioms alone.
#check @Lambda.LambdaModel
#check @Lambda.LambdaModel.interp_conv
#check @Lambda.LambdaModel.theory

-- The three models this library builds are instances of that one definition, and their theories
-- are the entries `Th(𝒫ω)` and `Th(D∞)` of the lattice above.
#check @GraphModel.model
#check @GraphModel.theory_model_eq
#check @ScottDinf.model
#check @ScottDinf.theory_model_eq
#check @Inter.typeSet_eq_model_interp

-- Scott–Koymans, one direction: the Karoubi envelope of a λ-model — idempotents as objects — is
-- a cartesian closed category in which `D = λz. z` is a reflexive object, `D ⇒ D` a retract
-- of `D`.
#check @Lambda.LambdaModel.karoubiMonoidalClosed
#check @Lambda.LambdaModel.reflexive_dRet
#check @Lambda.LambdaModel.toReflexiveObject

-- The other direction: a reflexive object in any cartesian closed category interprets untyped
-- terms as morphisms in environments of generalized elements, soundly for β; in the category of
-- sets that interpretation is a λ-model.
#check @ReflexiveCcc.ReflexiveObject
#check @ReflexiveCcc.ReflexiveObject.interp_beta
#check @ReflexiveCcc.ReflexiveObject.interp_conv
#check @ReflexiveCcc.ReflexiveObject.theory
#check @Lambda.SetReflexive.toModel

/-! ## 14g. Adequacy for Goedel's System T -/

-- Reduction is confluent, so a typable term reduces to at most one numeral.
#check @GodelT.confluence_of_typing
#check @GodelT.eq_of_reduces_num_of_typing

-- The set-theoretic denotational semantics, and adequacy: a closed term of type `nat` reduces to
-- the numeral of its denotation.
#check @GodelT.denot
#check @GodelT.adequacy

-- Hence at base type, equal denotations, convertibility and observational equivalence coincide.
#check @GodelT.denot_eq_iff_joins
#check @GodelT.obsEq_of_denot_eq
#check @GodelT.denot_eq_iff_obsEq_nat

/-! ## 14h. Curry-Howard-Lambek: STLC and cartesian closed categories -/

-- The syntactic category: types as objects, terms with one free variable modulo beta-eta
-- conversion as morphisms, substitution as composition.
#check @Stlc.category
#check @Stlc.comp_def

-- It has finite products, and the function type is an exponential: it is cartesian closed.
#check @Stlc.isTerminalUnit
#check @Stlc.prodCone
#check @Stlc.cartesianMonoidal
#check @Stlc.curryEquiv
#check @Stlc.monoidalClosed

-- Conversely, every cartesian closed category is a model: terms become morphisms, substitution
-- becomes composition, conversion is sound, and the interpretation is functorial.
#check @Stlc.tmMor
#check @Stlc.tmMor_sub
#check @Stlc.tmMor_conv
#check @Stlc.interpFunctor

-- That functor preserves the cartesian closed structure.
#check @Stlc.interpFunctor_map_projFst
#check @Stlc.interpFunctor_map_pairHom
#check @Stlc.interpFunctor_map_curryHom

/-! ## 15. Summary

### Fully proved (no sorry):
- Church-Rosser theorem (confluence) via Takahashi's parallel reduction
- Complete De Bruijn substitution calculus (lift/subst lemmas)
- Church encoding of all basic arithmetic operations
- Lambda-computability of: 0, succ, pred, +, -, *, √, pair, fst, snd
- Evaluation function is Partrec
- LambdaComputable → Partrec (unconditionally, via the Gross–Knuth evaluator)
- Normalization of the Gross–Knuth (complete development) strategy
- A compiler from `Nat.Primrec` into closed lambda terms
- Correctness of minimisation when a witness exists
- Computable → LambdaComputable, and the equivalence for total functions
- Standardization, normalization of the weak head and normal order strategies
- Divergence of minimisation without a witness, and the equivalence
  `LambdaComputable f ↔ Partrec f` for arbitrary partial functions
- Arithmetization of bundled Turing machines and the equivalence
  `TM2ComputableNat f ↔ Partrec f`, hence `LambdaComputable f ↔ TM2ComputableNat f`
- Kleene's second recursion theorem, Scott's theorem and Rice's theorem for the lambda calculus,
  the Scott–Curry theorem (two convertibility-invariant sets of terms have recursively
  inseparable code sets), the effective form of Rice's theorem (such a code set is many-one
  above the halting problem, has a non-r.e. complement, and is creative when r.e.), the
  creativity of the lambda-calculus halting set, of convergence to a numeral and of
  convertibility with a Church numeral, and the uniform s-m-n theorem
- A self-interpreter: a closed term `E` with `E ⌜M⌝ ↠ M` for every closed term `M`, together with
  the failure of the converse (quoting is not lambda-definable)
- The recursion theorem with parameters, the model equivalences for binary functions and for
  arbitrary `Primcodable` inputs, polynomial-time machine realizations, solvability theory
  (unsolvability of `Ω`, generic reachability, undecidability of solvability) and a
  representation theorem for bounded-exploration sequential algorithms
- Kolmogorov complexity for the lambda calculus: existence of incompressible numbers,
  non-computability of `K` (Berry's paradox via the second recursion theorem), the undecidability
  of the relation `K s ≤ n`, and the invariance theorem — for interpreters (additively) and for
  partial recursive / Turing machine description systems (in terms of bit length, via compact
  binary numerals)
- A self-delimiting (prefix free) binary coding of terms with Kraft's inequality, prefix
  complexity, and Chaitin's halting probability `Ω` as a convergent sum with `0 < Ω < 1`
- The converse of Kraft's inequality for non-decreasing lengths, giving the exact
  characterization of the realizable length sequences of a prefix free coding
- `Ω` is not a computable real and is irrational; its first `n` bits decide the halting problem
  for all programs of at most `n - 2` bits; and Chaitin's incompressibility theorem, that the
  prefix complexity of those `n` bits is at least `n - O(1)`
- The uniform measure on Cantor space, Martin-Löf tests and Martin-Löf randomness: no computable
  sequence is random, and every random sequence has prefix complexity at least `n - O(1)` on its
  length-`n` prefixes (the easy half of the Levin-Schnorr theorem)
- The lambda halting set is Σ₁-complete, indeed one-one complete: it is r.e., every r.e. predicate
  reduces to it by an injective computable function, and (by Post's theorem) its complement is
  not r.e.; Kleene's diagonal halting set is one-one complete as well, so the two halting
  problems are one-one equivalent
- A decoder for the binary lambda calculus bit-string code, inverse to the encoder, and the
  resulting bijection between terms and valid bit strings
- A Blum complexity measure (fuel counting) on the partial recursive codes, with both Blum
  axioms, and the diagonal result that no computable bound captures all computable functions
- The simply typed lambda calculus over the same de Bruijn syntax: Tait strong normalization,
  and the untypability of `omega`
- Gödel's System T: strong normalization, weakening and substitution for the typing relation,
  subject reduction, and canonicity — every closed term of type `nat` reduces to a numeral
- Böhm's separation theorem: the normal terms are exactly the denotations of the finite Böhm
  trees, faithfully, and two closed normal forms whose Böhm trees are not η-equal are separated
  by a single list of closed arguments (the Böhm-out transformation via tagged tuples)
- Denotational semantics: Scott's graph model as a reflexive object, with soundness of beta and
  a semantic consistency proof (`Ω` is not convertible to `I`); its adequacy — a term with a
  nonempty denotation has a head normal form, for closed terms the least element is exactly the
  unsolvable terms, and denotational equality implies observational equivalence at head
  normalization; and Scott's `D∞` as the inverse
  limit of the tower `D₀ = Bool`, `Dₙ₊₁ = [Dₙ →𝒄 Dₙ]`, with the isomorphism
  `D∞ ≅ [D∞ →𝒄 D∞]` and an extensional model of the lambda calculus validating beta and eta;
  in that model `Ω` denotes the least element, so the λη calculus is consistent, and conversely
  every head normalizable term is somewhere different from the least element
- Wadsworth's theorem: `D∞` is fully abstract for the untyped calculus — two closed terms are
  observationally equivalent, by head normalisation, exactly when they have the same denotation;
  while the graph model is not fully abstract
- Intersection types and the filter model: the strict types of the Coppo–Dezani system are the
  tokens of the graph model and type assignment is membership in the denotation, so the graph
  model is the filter model; hence subject reduction and expansion, typability = nonempty
  denotation = head normalisability = solvability, and the normalisation theorem — `ω`-free
  typability is exactly having a β-normal form, strictly stronger than typability
- The lattice of λ-theories: `B ⊊ Th(𝒫ω) ⊊ Th(D∞) = H*` on closed terms, with the infinite Böhm
  tree — the directed set of the direct approximants of the reducts — giving a theory strictly
  above β-conversion and below the theory of the graph model
- λ-models and the Scott–Koymans correspondence: the graph model, `D∞` and the filter model are
  three instances of the Meyer–Scott axioms; the Karoubi envelope of any λ-model is a cartesian
  closed category with a reflexive object, and conversely a reflexive object in any cartesian
  closed category interprets the untyped calculus soundly for β
- Head reduction: the head strategy is deterministic and normalizing — a term has a head normal
  form exactly when the strategy terminates on it — whence head divergence is stable under
  substitution, head normalizability of an application is inherited by its function part, and
  every solvable term has a head normal form, syntactically
- Confluence of System T reduction, its set-theoretic denotational semantics, and adequacy: a
  closed term of type `nat` reduces to the numeral of its denotation, so at base type equality of
  denotations, convertibility and observational equivalence coincide
- Curry-Howard-Lambek: the syntactic category of the simply typed lambda calculus (types as
  objects, terms modulo beta-eta conversion as morphisms) is cartesian closed, and conversely
  every cartesian closed category interprets the calculus soundly, giving a functor out of the
  syntactic category
- Myhill's isomorphism theorem: two sets of numbers are recursively isomorphic — carried onto one
  another by a computable bijection of `ℕ` — exactly when they are one-one equivalent; and the
  classification of the creative sets: a productive set has an injective production function, so
  every creative set is one-one complete and recursively isomorphic to Kleene's `K`
- Relative computability: oracle machines with a universal machine, the join of two oracles as the
  least upper bound of two Turing degrees, the Kleene–Post construction of two incomparable
  degrees, uncountably many degrees, and the Σ₁-hardness of the Turing jump, uniformly in the
  oracle
- Shoenfield's limit lemma: a set is the pointwise limit of a computable sequence of guesses
  exactly when it is computable from the halting oracle `∅'`
- The arithmetical hierarchy `Σ⁰ₙ`, `Π⁰ₙ`, `Δ⁰ₙ` with its structural theory — duality,
  substitution, `Σ⁰ₙ ∪ Π⁰ₙ ⊆ Δ⁰ₙ₊₁`, closure under conjunction, disjunction and the matching
  quantifier — bottoming out at the computable, r.e. and co-r.e. predicates; and Post's theorem at
  level two: `Δ⁰₂` is exactly the limit computable predicates, hence exactly the predicates
  decidable from `∅'`
- The properness of the arithmetical hierarchy: every level `n + 1` has a universal predicate,
  whose diagonal complement is `Π⁰ₙ₊₁` but not `Σ⁰ₙ₊₁`, so `Σ⁰ₙ₊₁ ≠ Π⁰ₙ₊₁` and each of `Σ⁰ₙ`,
  `Π⁰ₙ`, `Δ⁰ₙ` grows strictly with `n`, while the union of the levels has no universal predicate
- The closure of every level of the arithmetical hierarchy under bounded quantification with a
  computable bound, via the collection principle

### Architecture (≈ 8000 lines):
1. Lambda syntax + lift/subst               (De Bruijn indices)
2. Parallel reduction + diamond property     (Tait-Martin-Löf)
3. Strip lemma → Confluence                  (Church-Rosser)
4. Gödel encoding Λ → ℕ + Primrec proofs    (computability)
5. Eval function + Partrec proof             (evaluation)
6. Church arithmetic proofs                  (succ, add, mult, pred, sub, √, pair, unpair)
7. LambdaComputable results                  (all basic functions)
8. LambdaComputable → Partrec               (forward direction)
9. Realizers + Kleene normal form            (reverse direction, total functions)
10. Weak head normal forms + standardization (divergence, partial functions)
11. Arithmetized Turing machines             (machine side of Church-Turing)
-/
