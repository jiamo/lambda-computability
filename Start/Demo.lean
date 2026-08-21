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
-- undecidable.  (Böhm's separation theorem itself is *not* proved here.)
#check @Lambda.not_solvable_omega
#check @Lambda.exists_args_conv_of_solvable
#check @Lambda.not_computablePred_codeSet_solvable

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
- `Ω` is not a computable real and is irrational; its first `n` bits decide the halting problem
  for all programs of at most `n - 2` bits; and Chaitin's incompressibility theorem, that the
  prefix complexity of those `n` bits is at least `n - O(1)`
- The uniform measure on Cantor space, Martin-Löf tests and Martin-Löf randomness: no computable
  sequence is random, and every random sequence has prefix complexity at least `n - O(1)` on its
  length-`n` prefixes (the easy half of the Levin-Schnorr theorem)

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
