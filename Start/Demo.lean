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
  and the uniform s-m-n theorem
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
  a semantic consistency proof (`Ω` is not convertible to `I`); and Scott's `D∞` as the inverse
  limit of the tower `D₀ = Bool`, `Dₙ₊₁ = [Dₙ →𝒄 Dₙ]`, with the isomorphism
  `D∞ ≅ [D∞ →𝒄 D∞]` and an extensional model of the lambda calculus validating beta and eta;
  in that model `Ω` denotes the least element, so the λη calculus is consistent
- Confluence of System T reduction, its set-theoretic denotational semantics, and adequacy: a
  closed term of type `nat` reduces to the numeral of its denotation, so at base type equality of
  denotations, convertibility and observational equivalence coincide
- Curry-Howard-Lambek: the syntactic category of the simply typed lambda calculus (types as
  objects, terms modulo beta-eta conversion as morphisms) is cartesian closed, and conversely
  every cartesian closed category interprets the calculus soundly, giving a functor out of the
  syntactic category

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
