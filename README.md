This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# lambda-computability

A `sorry`-free Lean 4 formalization of **computability theory and algorithmic information
theory, done inside the untyped lambda calculus**: from de Bruijn syntax and confluence, through
the Church–Turing equivalence with partial recursive functions and Turing machines, up to
Kolmogorov complexity, Chaitin's `Ω`, Martin-Löf randomness and Böhm's separation theorem.

[![CI](../../actions/workflows/lean_action_ci.yml/badge.svg)](../../actions/workflows/lean_action_ci.yml)
![Lean](https://img.shields.io/badge/Lean-v4.28.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-blue)
![sorry-free](https://img.shields.io/badge/sorry--free-yes-brightgreen)
![tasks](https://img.shields.io/badge/task%20board-154%2F158%20DONE__STRONG-brightgreen)

Everything below is proved in `Start/`; the whole library compiles with `lake build`, contains no
`sorry` and no `axiom`, and the headline results depend only on `propext`, `Classical.choice` and
`Quot.sound`.

## Headline theorems

Signatures below are the actual statements in the library (printed with `#check`; the guided tour
in `Start/Demo.lean` checks them all).

### Church–Turing equivalence

```lean
-- The lambda calculus computes exactly the partial recursive functions.
lambdaComputable_iff_partrec :
    ∀ {f : ℕ →. ℕ}, LambdaComputable f ↔ Partrec f

-- … which are exactly the functions computed by (bundled, finite) TM2 machines.
TM2Partrec.tm2Computable_iff_partrec :
    ∀ {f : ℕ →. ℕ}, TM2Partrec.TM2ComputableNat f ↔ Partrec f

lambdaComputable_iff_tm2Computable :
    ∀ {f : ℕ →. ℕ}, LambdaComputable f ↔ TM2Partrec.TM2ComputableNat f
```

### Recursion theory

```lean
-- Rice/Scott: no closed term decides a nontrivial conversion-invariant set.
Lambda.scott_theorem :
    ∀ {A : Lambda → Prop}, Lambda.ConvInvariant A →
      ∀ {M N : Lambda}, M.IsClosed → N.IsClosed → A M → ¬ A N →
        ∀ {F : Lambda}, F.IsClosed → ¬ F.Decides A

-- s-m-n: fixing a parameter is primitive recursive on codes.
Lambda.exists_smn :
    ∃ s, Primrec₂ s ∧ ∀ (F : Lambda) (n : ℕ),
      Lambda.decode (s F.encode n) = some (F.app (Lambda.church n))

-- A self-interpreter: E ⌜M⌝ ↠ M for every closed M.
Lambda.exists_self_interpreter :
    ∃ E, E.IsClosed ∧ ∀ M : Lambda, M.IsClosed →
      (E.app (Lambda.church M.encode)).reduces M

-- Kleene's second recursion theorem with parameters.
Lambda.exists_recursion_with_parameters :
    ∀ {F : Lambda}, F.IsClosed →
      ∃ s, Primrec s ∧ ∀ y : ℕ, ∃ X, Lambda.decode (s y) = some X ∧
        X.reduces ((F.app (Lambda.church (s y))).app (Lambda.church y))

-- The lambda halting set is one-one complete among r.e. predicates.
Lambda.codeHasNormalForm_one_complete :
    REPred Lambda.CodeHasNormalForm ∧
      ∀ p : ℕ → Prop, REPred p → p ≤₁ Lambda.CodeHasNormalForm

-- Post's simple set: r.e., with an infinite complement that meets no infinite r.e. set.
Lambda.Post.rePred_simpleSet        : REPred Lambda.Post.simpleSet
Lambda.Post.simpleSet_compl_infinite : {x : ℕ | ¬ Lambda.Post.simpleSet x}.Infinite
Lambda.Post.simpleSet_meets_rePred :
    ∀ {p : ℕ → Prop}, REPred p → {x : ℕ | p x}.Infinite → ∃ x, p x ∧ Lambda.Post.simpleSet x

-- Post's problem for many-one reducibility: an r.e. set that is neither
-- computable nor many-one complete.
Lambda.Post.exists_rePred_not_computable_not_manyOneComplete :
    ∃ p : ℕ → Prop, REPred p ∧ ¬ ComputablePred p ∧ ¬ ∀ q : ℕ → Prop, REPred q → q ≤₀ p

-- Myhill's theorem, the other extreme: a creative set (r.e. with productive
-- complement) is many-one complete, hence many-one equivalent to the halting
-- set and never simple.
Lambda.Post.manyOneReducible_of_productive_compl :
    ∀ {C A : ℕ → Prop}, Lambda.Post.Productive (fun x => ¬ C x) → REPred A → A ≤₀ C
Lambda.Post.Creative.manyOneEquiv_haltK :
    ∀ {C : ℕ → Prop}, Lambda.Post.Creative C → ManyOneEquiv C Lambda.HaltK
Lambda.Post.creative_iff_manyOneComplete :
    ∀ {C : ℕ → Prop}, Lambda.Post.Creative C ↔ REPred C ∧ ∀ q : ℕ → Prop, REPred q → q ≤₀ C
Lambda.Post.not_creative_simpleSet : ¬ Lambda.Post.Creative Lambda.Post.simpleSet

-- Myhill's isomorphism theorem: one-one equivalence is recursive isomorphism,
-- where `RecIso A B` means `∃ h, Computable h ∧ Function.Bijective h ∧ ∀ x, A x ↔ B (h x)`.
Lambda.Myhill.recIso_iff_oneOneEquiv :
    ∀ {A B : ℕ → Prop}, Lambda.Myhill.RecIso A B ↔ OneOneEquiv A B

-- Hence the classification of the creative sets: a productive set has an
-- injective production function, so a creative set is one-one complete and
-- recursively isomorphic to `K`.
Lambda.Post.exists_injective_productive :
    ∀ {P : ℕ → Prop}, Lambda.Post.Productive P → ∃ q : ℕ → ℕ, Computable q ∧
      Function.Injective q ∧ ∀ e, (∀ x, Lambda.Post.Wset e x → P x) →
        P (q e) ∧ ¬ Lambda.Post.Wset e (q e)
Lambda.Post.Creative.recIso_haltK :
    ∀ {C : ℕ → Prop}, Lambda.Post.Creative C → Lambda.Myhill.RecIso C Lambda.HaltK
Lambda.Post.Creative.recIso :
    ∀ {C D : ℕ → Prop}, Lambda.Post.Creative C → Lambda.Post.Creative D →
      Lambda.Myhill.RecIso C D
Lambda.Post.creative_iff_recIso_haltK :
    ∀ {C : ℕ → Prop}, Lambda.Post.Creative C ↔ Lambda.Myhill.RecIso C Lambda.HaltK

-- Rice–Shapiro: an r.e. extensional class of r.e. sets is generated by its
-- finite members.  Hence the indices of the empty set, and the indices of the
-- total functions, are not r.e.
Lambda.Post.rice_shapiro :
    ∀ {A : ℕ → Prop}, REPred A → Lambda.Post.Extensional A → ∀ e : ℕ,
      (A e ↔ ∃ d : ℕ, {x : ℕ | Lambda.Post.Wset d x}.Finite ∧
        (∀ x, Lambda.Post.Wset d x → Lambda.Post.Wset e x) ∧ A d)
Lambda.Post.not_rePred_emptyIndex : ¬ REPred fun d => ∀ x, ¬ Lambda.Post.Wset d x
Lambda.Post.not_rePred_totalIndex : ¬ REPred fun d => ∀ x, Lambda.Post.Wset d x

-- Myhill–Shepherdson: an effective operation — a partial computable function on
-- indices whose value depends only on the partial function named — is Scott
-- continuous: monotone, and already determined by a finite restriction.
Lambda.Post.effop_continuous :
    ∀ {Psi : ℕ →. ℕ}, Partrec Psi → Lambda.Post.ExtensionalOp Psi → ∀ e v : ℕ,
      (v ∈ Psi e ↔ ∃ d : ℕ, Lambda.Post.SubFun d e ∧ Lambda.Post.FiniteDom d ∧ v ∈ Psi d)
```

### Relative computability, the jump, and the arithmetical hierarchy

```lean
-- There are uncountably many Turing degrees (each oracle computes only
-- countably many partial functions).
Lambda.Oracle.not_countable_turingDegree :
    ¬ Countable (Antisymmetrization (ℕ →. ℕ) TuringReducible)

-- The jump is Σ₁-hard, uniformly in the oracle: one computable reduction works
-- for every oracle at once.
Lambda.Oracle.exists_index_repred :
    ∀ {P : ℕ → Prop}, REPred P →
      ∃ k, Computable k ∧ ∀ (A : ℕ → Bool) (x : ℕ), P x ↔ Lambda.Oracle.Jump A (k x)

-- Shoenfield's limit lemma: limit computable = computable from ∅′.
Lambda.Oracle.limitComputable_iff_turingReducible_haltingOracle :
    ∀ A : ℕ → Bool, Lambda.Oracle.LimitComputable A ↔
      TuringReducible (Lambda.Oracle.oracleFun A)
        (Lambda.Oracle.oracleFun Lambda.Oracle.haltingOracle)
Lambda.Oracle.not_limitComputable_jumpChar_haltingOracle :
    ¬ Lambda.Oracle.LimitComputable (Lambda.Oracle.jumpChar Lambda.Oracle.haltingOracle)

-- The arithmetical hierarchy: Σ⁰ₙ, Π⁰ₙ, Δ⁰ₙ as alternating quantifier prefixes
-- over a computable matrix.  Its bottom levels are the familiar classes.
Lambda.Arith.deltaAt_one_iff : ∀ {P : ℕ → Prop}, Lambda.Arith.DeltaAt 1 P ↔ ComputablePred P
Lambda.Arith.sigmaAt_one_iff : ∀ {P : ℕ → Prop}, Lambda.Arith.SigmaAt 1 P ↔ REPred P
Lambda.Arith.piAt_one_iff :
    ∀ {P : ℕ → Prop}, Lambda.Arith.PiAt 1 P ↔ REPred fun x => ¬ P x
Lambda.Arith.SigmaAt.exists :
    ∀ {n : ℕ} {Q : ℕ → Prop}, Lambda.Arith.SigmaAt (n + 1) Q →
      Lambda.Arith.SigmaAt (n + 1) fun x => ∃ y, Q (Nat.pair x y)

-- Post's theorem at level two: Δ⁰₂ = limit computable = decidable from ∅′.
Lambda.Arith.deltaAt_two_iff_limitComputablePred :
    ∀ {P : ℕ → Prop}, Lambda.Arith.DeltaAt 2 P ↔ Lambda.Arith.LimitComputablePred P
Lambda.Arith.deltaAt_two_iff_turingReducible_haltingOracle :
    ∀ {P : ℕ → Prop}, Lambda.Arith.DeltaAt 2 P ↔
      ∃ A, (∀ x, P x ↔ A x = Bool.true) ∧
        TuringReducible (Lambda.Oracle.oracleFun A)
          (Lambda.Oracle.oracleFun Lambda.Oracle.haltingOracle)

-- The hierarchy is proper: every level has a universal predicate, no level equals its
-- dual, and all three families grow strictly.
Lambda.Arith.exists_univSigma : ∀ (n : ℕ), ∃ U, Lambda.Arith.UnivSigma (n + 1) U
Lambda.Arith.sigmaAt_ne_piAt :
    ∀ (n : ℕ), ¬∀ (P : ℕ → Prop), Lambda.Arith.SigmaAt (n + 1) P ↔ Lambda.Arith.PiAt (n + 1) P
Lambda.Arith.sigmaAt_proper :
    ∀ (n : ℕ), ∃ P, Lambda.Arith.SigmaAt (n + 2) P ∧ ¬Lambda.Arith.SigmaAt (n + 1) P
Lambda.Arith.deltaAt_proper :
    ∀ (n : ℕ), ∃ P, Lambda.Arith.DeltaAt (n + 2) P ∧ ¬Lambda.Arith.DeltaAt (n + 1) P
Lambda.Arith.not_exists_univ_arithmetical :
    ¬∃ T, Lambda.Arith.Arithmetical T ∧
      ∀ (P : ℕ → Prop), Lambda.Arith.Arithmetical P → ∃ e, ∀ (x : ℕ), P x ↔ T (Nat.pair e x)

-- Bounded quantifiers do not raise the level.
Lambda.Arith.SigmaAt.ball_lt :
    ∀ {n : ℕ} {Q : ℕ → Prop}, Lambda.Arith.SigmaAt n Q → ∀ {b : ℕ → ℕ}, Computable b →
      Lambda.Arith.SigmaAt n fun x => ∀ y < b x, Q (Nat.pair x y)
Lambda.Arith.PiAt.bex_lt :
    ∀ {n : ℕ} {Q : ℕ → Prop}, Lambda.Arith.PiAt n Q → ∀ {b : ℕ → ℕ}, Computable b →
      Lambda.Arith.PiAt n fun x => ∃ y < b x, Q (Nat.pair x y)
```

### Algorithmic information theory

```lean
-- Berry's paradox: Kolmogorov complexity is not computable, and is unbounded.
Lambda.not_computable_kolm  : ¬ Computable Lambda.kolm
Lambda.exists_incompressible : ∀ n : ℕ, ∃ s, n ≤ Lambda.kolm s

-- Chaitin's incompleteness theorem: a sound, recursively enumerable system of assertions
-- "K x > n" proves only boundedly many of them, so from some threshold on none at all.
Lambda.chaitin_incompleteness :
    ∀ {S : ℕ → ℕ → Prop}, REPred (fun q : ℕ × ℕ => S q.1 q.2) →
      (∀ x n, S x n → n < Lambda.kolm x) → ∃ c, ∀ x n, S x n → n < c

-- Kraft's inequality for a prefix-free code.
Kraft.tsum_wt_le_one :
    ∀ {ι : Type u} {c : ι → List Bool}, Kraft.PrefixFreeCoding c → ∑' i, Kraft.wt (c i) ≤ 1

-- Chaitin's Ω is a genuine probability, uncomputable and irrational.
Lambda.chaitinOmega_mem_Ioo    : Lambda.chaitinOmega ∈ Set.Ioo 0 1
Lambda.irrational_chaitinOmega : Irrational Lambda.chaitinOmega

-- Every Martin-Löf random sequence has incompressible prefixes
-- (the easy half of Levin–Schnorr for the lambda-calculus prefix complexity).
Lambda.exists_const_le_kolmP_prefix_of_mlRandom :
    ∀ {X : ℕ → Bool}, Lambda.MLRandom X →
      ∃ c, ∀ n : ℕ, n ≤ Lambda.kolmP (Encodable.encode (Lambda.prefixList X n)) + c

-- The Levin–Schnorr theorem for the universal prefix machine `KC.KU`:
-- Martin-Löf randomness is exactly incompressibility of every prefix.
KC.mlRandom_iff_exists_const_le_KU :
    ∀ {X : ℕ → Bool},
      Lambda.MLRandom X ↔ ∃ c, ∀ n : ℕ, n ≤ KC.KU (Encodable.encode (Lambda.prefixList X n)) + c

-- The bits of Ω are Martin-Löf random -- now a corollary of the converse half
-- applied to Chaitin's incompressibility theorem for Ω.
KC.mlRandom_omegaSeq : Lambda.MLRandom KC.omegaSeq

-- The Kraft-Chaitin machine is optimal for the lambda prefix machine.
KC.exists_const_KU_le_kolmP : ∃ c, ∀ s, KC.KU s ≤ Lambda.kolmP s + c
```

### Lambda calculus theory

```lean
-- Confluence (Church–Rosser) via parallel reduction.
Lambda.confluence_theorem : Lambda.Confluence

-- η-reduction terminates and commutes with β, so βη is confluent as well.
Lambda.reduces_etaReduces_commute :
    Lambda.reduces t u → Lambda.etaReduces t v →
      ∃ w, Lambda.etaReduces u w ∧ Lambda.reduces v w
Lambda.betaEta_church_rosser :
    Lambda.betaEtaReduces t u → Lambda.betaEtaReduces t v →
      ∃ w, Lambda.betaEtaReduces u w ∧ Lambda.betaEtaReduces v w

-- η-postponement: βη-reduction is β-reduction followed by η-reduction.
Lambda.betaEtaReduces_iff :
    Lambda.betaEtaReduces t u ↔ ∃ m, Lambda.reduces t m ∧ Lambda.etaReduces m u

-- Böhm's separation theorem: two closed normal forms whose Böhm trees are not
-- η-equal are separable by one list of closed arguments.
Lambda.separable_toTerm_of_not_tagEq :
    ∀ {x y : Lambda.BohmNF},
      Lambda.BohmNF.FreeVarsBelow 0 x → Lambda.BohmNF.FreeVarsBelow 0 y →
      ¬ Lambda.TagEq 0 (fun _ => 0) x (fun _ => 0) y → x.toTerm.Separable y.toTerm

-- Binary lambda calculus: terms are in bijection with the valid BLC bit strings.
Lambda.bitsEquiv : Lambda ≃ { bs // Lambda.isBLC bs = true }

-- The de Bruijn terms of this library and the locally nameless terms of `cslib`
-- are the same calculus: the closed terms correspond, and beta-reduction is
-- carried across in both directions, so each library's confluence theorem
-- implies the other's.
Lambda.closedEquiv : { t : Lambda // Lambda.freeMax t = 0 } ≃ { M : Lambda.LNTerm // M.LC ∧ M.fv = ∅ }
Lambda.confluence_of_cslib : Lambda.Confluence
Lambda.cslib_confluence_of_lambda :
    ∀ (D : ℕ) (M M₁ M₂ : Lambda.LNTerm), Term.LcAt 0 M = true → (∀ a ∈ M.fv, a < D) →
      (M ↠βᶠ M₁) → (M ↠βᶠ M₂) → ∃ M₃, (M₁ ↠βᶠ M₃) ∧ (M₂ ↠βᶠ M₃)
```

### Types, proof theory and complexity

```lean
-- Tait strong normalization for the simply typed lambda calculus.
Lambda.sn_of_typing :
    ∀ {Γ : List Lambda.Ty} {t : Lambda} {A : Lambda.Ty}, Lambda.Typing Γ t A → t.SN

-- Strong normalization for System F, by Girard's reducibility candidates.
SystemF.sn_of_typing :
    ∀ {Γ : List SystemF.FTy} {t : Lambda} {A : SystemF.FTy}, SystemF.Typing Γ t A → t.SN

-- Canonicity for Gödel's System T: every closed term of type nat reduces to a numeral.
GodelT.exists_reduces_num :
    ∀ {t : GodelT.Tm}, GodelT.Typing [] t GodelT.Ty.nat → ∃ n, GodelT.reduces t (GodelT.num n)

-- Blum-style complexity: no computable time bound captures every computable function.
Complexity.exists_computable_steps_gt :
    ∀ {t : ℕ → ℕ}, Computable t →
      ∃ f, Computable f ∧ ∀ c : Nat.Partrec.Code,
        (∀ x : ℕ, c.eval x = Part.some (f x)) → ∃ x, ¬ Complexity.StepsLe c x (t x)

-- P, NP, polynomial-time many-one reductions and NP-completeness over binary
-- words, with polynomial time for functions defined by Cobham's axioms.
Complexity.inNP_of_inP : ∀ {L : Complexity.Language}, Complexity.InP L → Complexity.InNP L
Complexity.InNP.of_reduction :
    ∀ {L₁ L₂ : Complexity.Language},
      Complexity.PolyManyOne L₁ L₂ → Complexity.InNP L₂ → Complexity.InNP L₁
Complexity.peqNP_of_npComplete_of_inP :
    ∀ {L : Complexity.Language}, Complexity.NPComplete L → Complexity.InP L → Complexity.PeqNP

-- Cook–Levin: SAT is NP-hard, hence NP-complete; so P = NP iff SAT is in P.
Complexity.npHard_SAT : Complexity.NPHard Complexity.Sat.SAT
Complexity.npComplete_SAT : Complexity.NPComplete Complexity.Sat.SAT
Complexity.peqNP_iff_inP_SAT : Complexity.PeqNP ↔ Complexity.InP Complexity.Sat.SAT

-- CIRCUIT-SAT: a second NP-complete problem, with reductions in both directions.
Complexity.polyManyOne_CSAT_SAT : Complexity.PolyManyOne Complexity.CSAT Complexity.Sat.SAT
Complexity.polyManyOne_SAT_CSAT : Complexity.PolyManyOne Complexity.Sat.SAT Complexity.CSAT
Complexity.npComplete_CSAT : Complexity.NPComplete Complexity.CSAT

-- k-SAT: the codes of satisfiable CNFs of width at most k are NP-complete for every k ≥ 3.
Complexity.Sat.inP_KCnfWord : ∀ (w : ℕ), Complexity.InP (Complexity.Sat.KCnfWord w)
Complexity.polyManyOne_CSAT_KSAT :
    ∀ {k : ℕ}, 3 ≤ k → Complexity.PolyManyOne Complexity.CSAT (Complexity.Sat.KSAT k)
Complexity.npComplete_KSAT : ∀ {k : ℕ}, 3 ≤ k → Complexity.NPComplete (Complexity.Sat.KSAT k)
Complexity.npComplete_ThreeSAT : Complexity.NPComplete Complexity.Sat.ThreeSAT

-- NP is closed under intersection: the witness is the pairing of the two witnesses.
Complexity.InNP.inter :
    ∀ {L₁ L₂ : Complexity.Language}, Complexity.InNP L₁ → Complexity.InNP L₂ →
      Complexity.InNP fun x => L₁ x ∧ L₂ x

-- The number of β-steps is a reasonable time cost model for weak head evaluation: the Krivine
-- machine performs exactly the weak head β-steps, and its administrative transitions are
-- polynomially many in the size of the term and the number of β-steps.
Krivine.Trans.decode_wstep :
    ∀ {s s' : Krivine.State}, Krivine.Trans Krivine.Label.beta s s' →
      Lambda.wstep s.decode s'.decode
Krivine.run_length_le_init :
    ∀ {t : Lambda} {n b : ℕ} {s : Krivine.State}, Krivine.Run n b (Krivine.State.init t) s →
      n ≤ b + Lambda.size t * (1 + b * (b + 1))
Krivine.eval_cost :
    ∀ {t : Lambda} {k : ℕ}, Lambda.WHNIn k t →
      ∃ (n b : ℕ) (s : Krivine.State), Krivine.Run n b (Krivine.State.init t) s ∧
        Krivine.IsFinal s ∧ b ≤ k ∧ n ≤ b + Lambda.size t * (1 + b * (b + 1)) ∧
        Lambda.reducesIn b t s.decode ∧ Lambda.IsWhnf s.decode

-- ... and those transitions are performed on words: the machine implemented on a code table and
-- a heap with shared environments evaluates the term from the encoded initial state to a stuck
-- state at a cost polynomial in the size of the term and the number of β-steps, counted in
-- sequential passes over the encoded state; one such pass is a single Cobham term
-- (`Krivine.Impl.stepT`, `Krivine.Impl.eval_stepT`, `Krivine.Impl.stepT_compiles`), and
-- `Krivine.Impl.eval_impl_cob_cost` composes the two.
Krivine.Impl.eval_impl_cost :
    ∀ {t : Lambda} {k : ℕ}, Lambda.WHNIn k t →
      ∃ (n b : ℕ) (s : Krivine.Impl.HState),
        Krivine.Impl.hrun (Krivine.Impl.tabOf t) n (Krivine.Impl.initState t) = some s ∧
        Krivine.Impl.hstep (Krivine.Impl.tabOf t) s = none ∧ b ≤ k ∧
        n ≤ b + Lambda.size t * (1 + b * (b + 1)) ∧ … ∧
        Krivine.Impl.hrunCost (Krivine.Impl.tabOf t) n (Krivine.Impl.initState t) ≤
          n * ((n + 2) * (Krivine.Impl.encBound t.nodes n + 1))

-- Kleene's first algebra embeds in the second, and the embedding is not reversible: no
-- applicative morphism K₂ → K₁ can even read one bit back off a representative (morphisms do
-- exist — the trivial one — which is why the hypothesis is needed).
Realizability.KleeneTwo.no_separatesBits_morphism :
    ∀ (δ : Realizability.AppMorphism (ℕ → ℕ) ℕ), ¬ Realizability.KleeneTwo.SeparatesBits δ
```

### Space-bounded computation and Savitch's theorem

Space is measured on a machine — `Start/SpaceMachine.lean`: an offline Turing machine with a
read-only input tape whose head is clamped to the input and its end marker, and one binary work
tape whose used length is what the bound constrains.  The transition function returns the *list*
of available instructions, so determinism is a property of the same model.  On it sit
`Complexity.Space.DSPACE`, `.NSPACE`, `.LOGSPACE`, `.PSPACE` and `.NPSPACE` (polynomials are the
`Complexity.PolyBound` of the time half of the library), with `DSPACE ⊆ NSPACE`, `L ⊆ PSPACE`
and monotonicity in the bound.

```lean
-- A machine running in space `s` on an input of length `n` has at most
-- `q · (n+1) · (s+1)² · 2 ^ s` configurations, and acceptance is reachability among them.
Complexity.Space.card_boundedCfg_le :
    ∀ (M : Complexity.Space.Machine) (x : List Bool) (s : ℕ),
      Fintype.card (Complexity.Space.BoundedCfg M x s) ≤ Complexity.Space.cfgBound M x s

-- Savitch's recursion: reachability within `2 ^ (k+1)` steps is a midpoint with two legs of
-- `2 ^ k`; a deterministic stack machine executes it holding at most `k` activation records.
Complexity.Savitch.trace_call :
    ∀ (r : C → C → Bool) (cs : List C) (k : ℕ) (a b : C) (st : List (Complexity.Savitch.Frame C)),
      Complexity.Savitch.Trace r cs (st.length + k) ⟨.call a b k, st⟩
        ⟨.ret (Complexity.Savitch.reachL r cs k a b), st⟩

-- Savitch's theorem, in that cost model: the deterministic decision is correct, and runs in
-- `(k+1)·(4k+3)` bits with `k ≤ log₂ q + log₂ (n+1) + 2 log₂ (s+1) + s`.
Complexity.Space.savitch_accepts_iff :
    ∀ (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s),
      M.Accepts x ↔ Complexity.Space.savitchDecide hwf hsp = true
Complexity.Space.savitch_poly_memory :
    ∀ {L : Complexity.Space.Language}, Complexity.Space.NPSPACE L → …  -- polynomial memory
```

Two further pieces sit on top of that.  `Start/QbfReach.lean` writes the midpoint recursion as a
*formula*: vertices are words of `m` bits held in blocks of variables, the edge relation enters as
a family of step formulas, and each level quantifies over a midpoint and then, universally over a
pair of endpoints, makes a single recursive call stand for both legs.  The formula is correct
(`Complexity.Qbf.QBF.eval_reachF`) and its size is at most `c + 10m + 5 + k · (43m + 21)`
(`Complexity.Qbf.QBF.size_reachF_le`) — the formula half of the PSPACE-hardness of `TQBF`.
`Start/QbfMachine.lean` supplies the missing step formulas: a configuration of a machine running
in space `s` is a word of `q + (n+1) + 2s` bits (control state and both head positions in unary,
the work tape bit by bit, `Start/SpacePadded.lean` and `Start/QbfCfgWord.lean`), and one
transition is a disjunction over the situations of the machine of literal and copy constraints on
two blocks.  The step formula expresses exactly one step (`Complexity.Qbf.QBF.eval_stepF`) and is
of size `O(q · (n+1) · s · d · width)` (`Complexity.Qbf.QBF.size_stepF_le`), so the midpoint
recursion built on it is a *closed* formula, true exactly when the machine accepts its input
(`Complexity.Qbf.QBF.eval_machineF`), of size polynomial in `q`, `n`, `s` and the branching `d`
(`Complexity.Qbf.QBF.size_machineF_le`).  `Start/QbfClosed.lean` tracks free variables through the
construction and proves the formula closed (`Complexity.Qbf.QBF.closed_machineF`), so it is an
instance of `TQBF` (`Complexity.Qbf.QBF.tqbf_machineF_iff`), and `Start/QbfPspace.lean` reads that
off for a whole class: every language in `NPSPACE`, hence every language in `PSPACE`, has one
polynomial `p` and, for each input `x`, a closed formula of size at most `p |x|` which is a true
quantified Boolean formula exactly when `x` is in the language
(`Complexity.Qbf.QBF.npspace_polySize_tqbf`, `Complexity.Qbf.QBF.pspace_polySize_tqbf`).
`Start/QbfWord.lean` writes the formulas themselves as binary words — a self-delimiting code with
a decoder, so the code is injective and short (`Complexity.Qbf.QBF.enc_injective`,
`Complexity.Qbf.QBF.length_enc_le`) — which turns `TQBF` into a language of words
(`Complexity.Qbf.tqbfLang`) and the reduction into a map of words of polynomially bounded output
length (`Complexity.Qbf.QBF.pspace_polyLength_tqbfWord`).  `Start/QbfWordStream.lean` then puts
that word in the shape a polynomial-time compiler needs: a concatenation of blocks, one per index
of a range, with the midpoint recursion contributing exactly one block per level
(`Complexity.Qbf.QBF.enc_reachF`, `Complexity.Qbf.QBF.enc_machineF_stream`).  The first blocks are
already written by Cobham terms: `Start/CobhamRange.lean` makes the emission of one block per
index of a range a Cobham function (`Complexity.eval_rangeEmitTerm`, with the truncated
subtraction `Complexity.Cob.eval_dropN`), `Start/CobhamFields.lean` reads the unary fields of the
parameter word (`Complexity.Cob.eval_fieldTerm`), and `Start/QbfCobPrefix.lean` and
`Start/QbfCobEqBlock.lean` write the quantifier prefixes and the block-equality formulas
(`Complexity.Qbf.QBF.eval_quantPrefixTerm`, `Complexity.Qbf.QBF.enc_eqBlock_eval`).
`Start/KrivineSpaceConfig.lean` puts the binary word of a collected Krivine state on the work tape
of a configuration of this model, so that the cell measure of the λ-machine and the bit measure of
the tape are compared directly: the word determines the state, holds at least one bit per live
cell, and at most `(4S+4)·(log₂(3S)+2)` bits along a run whose code table, stacks and peak live
data fit in `S` (`Krivine.Impl.spaceConfig_space_le_of_run_budget`).

The honest boundary: the deterministic simulation is exhibited on the stack machine, whose memory
is counted in bits of activation records, and not as an offline Turing machine; compiling it into
that model — the routine half of the model-independence of space — is not formalized, so
`NPSPACE = PSPACE` is not claimed as a theorem about `Complexity.Space.DSPACE`.  For the same
reason the two space results above stop where they do: `TQBF` is not proved PSPACE-hard (what is
missing now is only that the map from an input to its formula is computed in polynomial time),
and the Krivine bound is a statement about the memory
measure, not yet a `DSPACE` membership (the missing half is a machine of that model performing
Krivine transitions on the word).

### Relativization: the classes with an oracle

Both cost models are relativized.  On the time side (`Start/OracleCob.lean`) an oracle machine is
a Cobham term with one extra constructor, `Complexity.CobQ.query`, which asks the oracle about its
first argument; evaluation returns the value **and** the list of words the oracle was asked about,
because a diagonalization needs the queries and not only the answer.  With constants independent
of the oracle, the value is polynomially long, the *number* of queries is polynomially bounded and
every queried word is polynomially long, and two oracles that agree on the words actually queried
give the same run — the use principle.

```lean
-- The number of queries of a polynomial-time oracle machine is polynomially bounded.
Complexity.CobQ.polyQueryCount :
    ∀ (t : Complexity.CobQ), ∃ p : ℕ → ℕ, Complexity.PolyMono p ∧
      ∀ (A : Complexity.Oracle) (args : List Complexity.Word),
        (Complexity.CobQ.queries A t args).length ≤ p (Complexity.maxLen args)

-- The use principle.
Complexity.CobQ.run_congr :
    ∀ (t : Complexity.CobQ) (A B : Complexity.Oracle) (args : List Complexity.Word),
      (∀ w ∈ Complexity.CobQ.queries A t args, A w = B w) →
        Complexity.CobQ.run A t args = Complexity.CobQ.run B t args

-- The empty oracle gives back the unrelativized classes.
Complexity.inP_rel_empty_iff :
    ∀ {L : Complexity.Language},
      Complexity.InP_rel Complexity.CobQ.emptyOracle L ↔ Complexity.InP L
```

On the space side (`Start/OracleSpace.lean`) the offline machine gains a query tape, which counts
towards the space bound; an ordinary machine is an oracle machine with no query state, with the
same runs, so `PSPACE ⊆ PSPACE^A` for every oracle.  `Start/OracleClasses.lean` carries the
classes themselves (`Complexity.InP_rel`, `Complexity.InNP_rel`,
`Complexity.Space.InPSPACE_rel`), the inclusions `P ⊆ P^A`, `NP ⊆ NP^A`, `P^A ⊆ NP^A`, the closure
properties of `P^A`, and the fact that the oracle itself is decided in `P^A`.  The honest
boundary: `NP^A ⊆ PSPACE^A` is not proved, because time and space are measured on different models
here and even the unrelativized `P ⊆ PSPACE` would need a compiler from Cobham terms to
space-bounded machines.

### An oracle that separates: `P^B ≠ NP^B`

`Start/BakerGillSolovay.lean` builds the separating oracle of Baker–Gill–Solovay.  The language is
the standard one — an input is accepted when some word of its length lies in the oracle — which is
in `NP^B` for every `B`: guess the word and ask.  The oracle is built in stages against the
enumeration of the oracle Cobham terms of `Start/OracleEnum.lean`: at stage `e + 1` the `e`-th term
is run on `1 ^ n` for an `n` above everything settled so far, and the word of length `n` that the
run never asked about (`Complexity.CobQ.exists_word_not_queried_unary`) is added exactly when the
run rejects.  By the use principle the run does not notice, so the term decides the language
wrongly at `1 ^ n`, and the enumeration is onto.

```lean
-- The separating half of Baker–Gill–Solovay.
Complexity.bgs_different : ∃ B : Complexity.Oracle, ¬ Complexity.PeqNP_rel B
```

Since every oracle Cobham term is polynomial-time by construction, no separate uniform time bound
in the index is needed for the diagonalization.

`Start/Relativization.lean` draws the barrier from it.  A statement about the classes
*relativizes* when it holds with every oracle attached (`Complexity.Relativizes`); the separating
oracle says that `P = NP` does not
(`Complexity.peqnp_does_not_relativize : ¬ Complexity.Relativizes Complexity.PeqNP_rel`), so no
relativizing argument proves `P = NP`.  The other half is stated conditionally,
`Complexity.no_relativizing_resolution`: from any oracle with `P^A = NP^A` it follows that neither
side of the question is settled by a relativizing argument.  That collapsing oracle — classically
a `PSPACE`-complete one — is the part the library does not have, for the same reason that
`NP^A ⊆ PSPACE^A` is missing: time here is Cobham's class and space is the offline machine.

### The frame a priority construction runs in

Nothing in the library is yet built by a priority argument; `Start/OracleUse.lean` and
`Start/Priority.lean` build the frame for one.  The use of an oracle computation becomes a
function — `Lambda.Oracle.use`, one more than the least stage at which the computation converges —
and the use principle takes the form a strategy needs: an oracle agreeing below the use gives the
same computation *and* the same use.  A construction is a primitive recursive increasing sequence
of finite approximations, and the set it enumerates is c.e.; a requirement is a predicate on the
approximation, injured at a stage when it holds there and fails at the next.

```lean
-- The finite injury lemma, for requirements ordered by priority, where between two actions of a
-- requirement one of higher priority acts.
Lambda.Priority.Injury.acts_finite :
    ∀ (I : Lambda.Priority.Injury) (i : ℕ), {s | I.acts i s}.Finite

Lambda.Priority.Injury.exists_final_stage :
    ∀ (I : Lambda.Priority.Injury) (i : ℕ),
      ∃ t, ∀ s, t ≤ s → ¬ I.acts i s ∧ ¬ I.injured i s
```

The lemma is proved for an arbitrary instance of the frame; feeding a concrete construction to it
— Friedberg–Muchnik — is the next step and is not done here.

## Related work, and what is specific to this project

Public Lean 4 developments in this area, and how they relate (repository file listings checked
2026-08; none of the statements below is a claim about unpublished or private work):

| Project | What it covers | Relation to this library |
| --- | --- | --- |
| [`leanprover/cslib`](https://github.com/leanprover/cslib) | Lambda calculus in **locally nameless** style (β/η confluence, standardization, strong normalization), STLC, Fsub, automata, CCS, linear logic | Same metatheory, different representation: here everything is **de Bruijn**, and the development continues into computability and AIT, which `Cslib/Languages/LambdaCalculus/` does not cover (no Böhm trees, no Kolmogorov complexity, no `Ω`). `cslib` is a dependency of this repo, and `Start/Representation.lean` proves the two representations equivalent, transporting confluence in both directions (see [`docs/representations.md`](docs/representations.md)) |
| [`cameronfreer/algorithmic-randomness`](https://github.com/cameronfreer/algorithmic-randomness) | Algorithmic randomness over **program codes**: prefix machines, Kraft–Chaitin, Levin–Schnorr, Schnorr/Kurtz randomness, martingales | Complementary: the AIT here is defined through **lambda terms** (`Lambda.kolm`, `Lambda.kolmP`, `Lambda.chaitinOmega`), so the two developments meet at the level of statements rather than definitions; here the lambda complexity is compared with a machine-based one only in this repo's own terms (`KC.exists_const_KU_le_kolmP`), and no bridge to that repo's definitions is formalized on either side |
| [`a9lim/blam`](https://github.com/a9lim/blam) | Computational experiments in binary lambda calculus (censuses, BBλ, Ω/K measurements) | Numerical/experimental rather than a formalization; `Start/BLC.lean` proves the BLC decoder correct and gives the bijection `Lambda ≃ {bs // isBLC bs}` |
| `Mathlib.Computability` | Partial recursive functions, `Nat.Partrec.Code`, TM0/TM1/TM2, `Turing.PartrecToTM2` | Used as the base: the equivalences above are stated against mathlib's `Partrec`, `Computable`, `REPred` and `Turing.FinTM2`, not against a private notion of computability |

## Map of the library

`Start/` is self-contained; `Start.lean` imports everything.

- **Syntax, reduction, confluence, standardization** — `Start/Syntax.lean`,
  `Start/Reduction.lean`, `Start/GrossKnuth.lean`, `Start/Standardization.lean`,
  `Start/WeakHead.lean`, `Start/Leftmost.lean`.
- **The cost of reduction** — the size explosion (`Start/SizeExplosion.lean`) shows that no
  evaluator writing the result down can be fast; the Krivine machine keeps it shared
  (`Start/Krivine.lean`), performs exactly the weak head β-steps (`Start/KrivineDecode.lean`) and
  needs only polynomially many administrative transitions (`Start/KrivineBound.lean`), which is
  the invariance statement `Krivine.eval_cost`.  `Start/KrivineHeap.lean` implements those
  transitions on a code table and a heap with sharing and proves the implementation bisimilar to
  the machine, and `Start/KrivineHeapCost.lean` writes the states as words and bounds the cost of
  a whole evaluation (`Krivine.Impl.eval_impl_cost`); the cost is counted in passes over the
  encoding, and `Start/KrivineCobWord.lean` and `Start/KrivineCobStep.lean` perform one such pass
  on a machine model of the library — the transition is the single Cobham term
  `Krivine.Impl.stepT` (`Krivine.Impl.eval_stepT`), whose cost in that model is polynomial
  (`Krivine.Impl.stepT_compiles`), giving `Krivine.Impl.eval_impl_cob_cost`.
- **Church–Turing equivalence** — the lambda calculus computes exactly the partial
  recursive functions (`Start/PartialCapstone.lean`, `Start/PartrecLambda.lean`), which are
  exactly the Turing machine computable ones (`Start/TM2Forward.lean`, `Start/TM2Partrec.lean`,
  `Start/TM2Capstone.lean`), with multi-argument and arbitrary-`Primcodable` versions in
  `Start/Encodings.lean`.
- **Recursion theory** — fixed points (`Start/FixedPoint.lean`), the s-m-n theorem
  (`Start/SMN.lean`), Kleene's second recursion theorem with parameters
  (`Start/SecondRecursion.lean`, `Start/RecursionParams.lean`), a self-interpreter
  (`Start/SelfInterpreter.lean`), Rice's theorem (`Start/Scott.lean`), the Scott–Curry theorem
  on recursively inseparable code sets (`Start/ScottCurry.lean`), the effective form of Rice's
  theorem exhibiting creative code sets (`Start/RiceCreative.lean`, `Start/CreativeCodeSets.lean`),
  undecidability of
  convergence, of normalization and of solvability (`Start/Undecidable.lean`,
  `Start/NormalizationUndecidable.lean`, `Start/Solvability.lean`).
- **Algorithmic information theory** — Kolmogorov complexity and Berry's paradox
  (`Start/Kolmogorov.lean`, `Start/KolmogorovBinary.lean`), Kraft's inequality
  (`Start/Kraft.lean`) together with its converse for non-decreasing lengths
  (`Start/KraftConverse.lean`), prefix complexity and Chaitin's `Ω` (`Start/ChaitinOmega.lean`,
  `Start/PlainVsPrefix.lean`), the busy beaver (`Start/BusyBeaver.lean`), the halting/`K`
  bridge (`Start/KolmogorovHalting.lean`), `Ω` as an uncomputable, irrational halting
  oracle (`Start/OmegaUncomputable.lean`, `Start/OmegaOracle.lean`), Chaitin's
  incompressibility theorem `n ≤ kolmP (omegaPrefix n) + c` (`Start/OmegaIncompressible.lean`),
  Chaitin's incompleteness theorem for complexity lower bounds
  (`Start/ChaitinIncompleteness.lean`), the upper semicomputability of `K` — `K s ≤ n` is
  recursively enumerable, `n < K s` is not, and `K` is the infimum of a primitive recursive
  decreasing approximation (`Start/KolmogorovApprox.lean`), the time-bounded complexity `K^T` —
  the least size of a closed term reducing to the numeral within `T` beta steps — with its
  monotonicity in `T`, its position between `K` and the size of the numeral, its convergence to
  `K` and its invariance under a change of interpreter (`Start/KolmogorovTime.lean`),
  and the randomness of `Ω` itself (`Start/OmegaURandom.lean`, `Start/KCComputable.lean`).
- **Algorithmic randomness** — the uniform measure on Cantor space, Martin-Löf tests and
  Martin-Löf randomness (`Start/MartinLof.lean`): no computable sequence is random, and every
  random sequence has incompressible prefixes (the easy half of the Levin–Schnorr theorem).
  For the universal prefix machine `KC.KU` both halves are proved, giving the Levin–Schnorr
  theorem `KC.mlRandom_iff_exists_const_le_KU` (`Start/LevinSchnorr.lean`), of which the
  randomness of `Ω` is a corollary.  `Start/KUOptimal.lean` compares the two complexities:
  `KU s ≤ Lambda.kolmP s + c`, by running the lambda programs as a Kraft–Chaitin request stream.
- **Degrees of unsolvability** — the lambda halting set is Σ₁-complete, indeed one-one complete
  (`Start/HaltingComplete.lean`, on top of mathlib's `REPred`); Kleene's diagonal halting set is
  one-one complete as well, so the two halting problems are one-one equivalent
  (`Start/KleeneK.lean`).  **Myhill's isomorphism theorem** upgrades one-one equivalence to
  recursive isomorphism: `Lambda.Myhill.recIso_iff_oneOneEquiv` (`Start/MyhillIso.lean`).  Every
  productive set has an injective production function, so the creative sets are exactly the sets
  recursively isomorphic to `K`, and any two of them are recursively isomorphic to each other
  (`Start/CreativeIso.lean`).
- **Relative computability and the jump** — oracle machines and relative recursiveness
  (`Start/OracleSound.lean`, `Start/OracleUniversal.lean`), the join of two oracles as the least
  upper bound of two degrees (`Start/OracleJoin.lean`), the Kleene–Post construction
  (`Start/KleenePost.lean`), and the counting argument giving uncountably many Turing degrees
  (`Start/OracleCone.lean`).  The Turing jump is Σ₁-hard uniformly in the oracle
  (`Start/JumpSigmaOne.lean`), and, with a primitive recursive stagewise approximation of `∅′`
  (`Start/JumpApprox.lean`), **Shoenfield's limit lemma** identifies the limit computable sets
  with the sets computable from `∅′` (`Start/LimitLemma.lean`).
- **The arithmetical hierarchy** — `Σ⁰ₙ`, `Π⁰ₙ` and `Δ⁰ₙ` as alternating quantifier prefixes over
  a computable matrix, with duality, substitution, the inclusions `Σ⁰ₙ ∪ Π⁰ₙ ⊆ Δ⁰ₙ₊₁` and the
  closure properties, bottoming out at the computable, r.e. and co-r.e. predicates
  (`Start/ArithHierarchy.lean`); and **Post's theorem at level two**: `Δ⁰₂` is exactly the class
  of limit computable predicates, hence exactly the predicates decidable from `∅′`
  (`Start/PostTheoremTwo.lean`).  The hierarchy is **proper**: every level `n + 1` carries a
  universal predicate, whose diagonal complement is `Π⁰ₙ₊₁` but not `Σ⁰ₙ₊₁`, so no level equals
  its dual or is closed under complement and all three families grow strictly; the union of the
  levels, the arithmetical predicates, has no universal predicate
  (`Start/ArithHierarchyProper.lean`).  Every level is closed under **bounded** quantification
  with a computable bound, proved by one induction using the collection principle
  (`Start/ArithBounded.lean`).  Every level is closed downwards under many-one reducibility, and
  its universal predicate is **complete** for it — hard already for one-one reducibility — so each
  level `n + 1` has complete predicates on both sides, exchanged by complementation and pairwise
  many-one equivalent; a complete predicate escapes the dual level, the lower levels and
  computability, at level one it is the halting problem, and the union of the levels has no
  complete predicate (`Start/ArithComplete.lean`).  At level two the complete predicate is
  concrete: the index set of the **total** functions is `Π⁰₂`-complete, so it is neither
  recursively enumerable nor co-r.e., and the halting problem reduces to it but not conversely
  (`Start/ArithIndexSets.lean`).
- **Binary lambda calculus** — a decoder for the BLC bit-string code and the resulting
  bijection between terms and valid bit strings (`Start/BLC.lean`).
- **Representation bridges** — de Bruijn ⟺ locally nameless (`cslib`) ⟺ BLC: mutually inverse
  translations, substitution/reduction preservation in both directions, and confluence
  transported each way (`Start/Representation.lean`, note in
  [`docs/representations.md`](docs/representations.md)).
- **Complexity** — a Blum complexity measure (fuel counting) on the partial recursive codes,
  with both Blum axioms, and the diagonal result that no computable bound captures every
  computable function (`Start/StepComplexity.lean`); polynomial-time bounded machines in
  `Start/TM2PolyTime.lean`; and the classes `P` and `NP` over binary words with polynomial-time
  many-one reductions and NP-completeness (`Start/ComplexityClasses.lean`).  **SAT is in NP**:
  CNFs are encoded as binary words and an explicit Cobham verifier evaluates them
  (`Start/Sat.lean`), and the **Tseitin translation** from Boolean circuits to CNF is proved to
  preserve satisfiability and to have linear size (`Start/Tseitin.lean`).  Every Cobham term is
  compiled into a Boolean circuit of polynomial size, which gives `P ⊆ P/poly` and, for every
  language in NP, a polynomial-size circuit family satisfiable exactly on the language
  (`Start/CobhamCircuit.lean`, `Start/CobhamBRec.lean`, `Start/PolyCircuit.lean`).  **SAT is
  NP-hard, and NP-complete** — `Complexity.npHard_SAT`, `Complexity.npComplete_SAT` and hence
  `Complexity.peqNP_iff_inP_SAT` (`P = NP` iff SAT is in `P`) — unconditionally
  (`Start/CookLevinNPHard.lean`); the missing uniformity of the acceptance families is supplied
  there by `Complexity.stdUniformAcceptFamilies`, built from the segment decoder of
  `Start/UniformSegDec.lean` and the verifier compiler of `Start/UniformSigAll.lean`.  The route
  to it was incremental, and the intermediate implications are kept: the dependence on the
  instance was removed first — the acceptance circuits read the instance off their own input
  (`Start/PinnedCircuit.lean`), the instance is written into the formula by unit clauses
  (`Start/PinnedCnf.lean`) and those are emitted by an explicit Cobham term
  (`Start/CobhamPin.lean`), which reduced the problem to the usual P-uniformity of a
  *length-indexed* circuit family (`Start/CookLevinUniform.lean`, `Start/CookLevinBound.lean`).
  A **second NP-complete problem** is then derived: `CIRCUIT-SAT`, the words whose gate system is
  satisfiable (`Complexity.CSAT`, `Start/CircuitSystem.lean`, `Start/CircuitSatLang.lean`), which
  reduces to SAT by the Tseitin term and to which SAT reduces by the circuit that the same
  right-to-left scan builds while evaluating a CNF (`Start/SatToCircuit.lean`,
  `Start/SatToCircuitCob.lean`), giving `Complexity.npComplete_CSAT`.
  A **third** one is `k`-SAT for every `k ≥ 3` (`Start/ThreeSat.lean`): the Tseitin translation
  only ever emits clauses of at most three literals, so the same term reduces `CIRCUIT-SAT` to the
  codes of satisfiable CNFs of width `k`, while membership in `NP` comes from the finite-state
  check that a word codes such a CNF — `Complexity.npComplete_KSAT`, and
  `Complexity.npComplete_ThreeSAT` for `3-SAT`.
  On the other side,
  the reduction to SAT is unconditional for every language decided by a P-uniform circuit family
  (`Start/UniformDecide.lean`), a class that contains every regular language
  (`Start/UniformAuto.lean`) and every symmetric language whose count predicate is decided in
  unary by a Cobham term — majority, exactly half, count divisible by `k`
  (`Start/UniformMaj.lean`, `Start/UniformSym.lean`).  Both are subsumed by the language of any
  automaton with *polynomially many* states whose number of states, transition function and
  acceptance predicate are computed in unary by Cobham terms (`Start/UniformState.lean`,
  `Start/UniformStateCode.lean`), and both earlier families are derived from it
  (`Start/UniformStateSubsume.lean`); a further instance decides whether the binary value of a word is
  divisible by its length plus one, a language that is neither regular nor symmetric
  (`Start/UniformStateInst.lean`).  The Cook–Levin tableau itself is formalized: the space–time
  diagram of a cellular automaton run on a Cobham-computable width and time is a P-uniform circuit
  family (`Start/UniformCA.lean`, `Start/UniformCACode.lean`), and so is the language of a one-tape
  deterministic Turing machine with finitely many states under the same bounds
  (`Start/UniformTM.lean`).  A further loop rule stacks polynomially many copies of a P-uniform
  *stage* circuit over a P-uniform base, each copy rewired to the outputs of the copy below — the
  shape the unrolling of a bounded recursion has — and proves the stack P-uniform
  (`Start/UniformIterate.lean`), the gates of a copy being read off the description of the stage by
  a Cobham term (`Start/UniformSelect.lean`).  The compiler itself is in place for the whole
  non-recursive fragment of the Cobham algebra: every term built from projections, the empty
  word, appending a bit, concatenation and composition is turned into a P-uniform circuit family
  computing it, together with a polynomial length bound
  (`Start/UniformSigCompile.lean`, `Start/UniformSigFlat.lean`), leaving bounded recursion
  (`Cob.bRec`) as the only shape for which the device must still be produced by hand.
- **Space complexity** — space is measured on an offline machine with a read-only input tape and
  one binary work tape (`Start/SpaceMachine.lean`), which carries `DSPACE`, `NSPACE`, `LOGSPACE`,
  `PSPACE` and `NPSPACE`.  A machine running in space `s` has at most `q · (n+1) · (s+1)² · 2 ^ s`
  configurations and acceptance is reachability among them (`Start/SpaceConfigCount.lean`);
  reachability within `2 ^ (k+1)` steps is a midpoint with two legs of `2 ^ k`
  (`Start/SavitchReach.lean`); and a deterministic stack machine executes that recursion holding
  at most `k` activation records (`Start/SavitchVM.lean`).  Together they give **Savitch's
  theorem** in that cost model: the deterministic decision is correct and runs in `(k+1)·(4k+3)`
  bits with `k ≤ log₂ q + log₂ (n+1) + 2 log₂ (s+1) + s`, so polynomially bounded memory for a
  language in `NPSPACE` (`Start/SavitchSpace.lean`).  Compiling the stack machine back into the
  offline model, which is what `NPSPACE = PSPACE` as a statement about `DSPACE` would need, is not
  formalized.  In the same cost model, quantified Boolean formulas are evaluated by a stack
  machine that holds one activation record per level of the formula and one bit per variable, so
  a closed formula is decided in memory quadratic in its size (`Start/Qbf.lean`) — the easy half
  of the PSPACE-completeness of `TQBF`.  Of the hard half, the formula side is done: the midpoint
  recursion is written as a quantified Boolean formula over blocks of variables, correct and of
  size polynomial in the width of a vertex and the depth (`Start/QbfReach.lean`), and so is the
  machine side: configurations of a space-bounded machine are words of `q + (n+1) + 2s` bits, one
  transition is a formula of size linear in that width per situation, and the resulting closed
  formula is true exactly when the machine accepts its input and has polynomial size
  (`Start/SpacePadded.lean`, `Start/QbfCfgWord.lean`, `Start/QbfMachine.lean`), and that formula
  is closed, so every language in `NPSPACE` (hence in `PSPACE`) reduces to `TQBF` by a map of
  polynomial size
  (`Start/QbfClosed.lean`, `Start/QbfPspace.lean`), indeed by a map of *words* of polynomially
  bounded length into the language of the codes of true closed formulas (`Start/QbfWord.lean`),
  whose value is a concatenation of blocks, one per level of the recursion
  (`Start/QbfWordStream.lean`), the first of which are written by Cobham terms
  (`Start/CobhamRange.lean`, `Start/CobhamFields.lean`, `Start/QbfCobPrefix.lean`,
  `Start/QbfCobEqBlock.lean`).  What is still missing for hardness is that the whole map from an
  input to its formula is computed in polynomial time.  On the λ-calculus side the word of a collected
  Krivine state is a work tape of that machine model, with the memory it costs bounded by
  `O(S · log S)` in the live data of the run (`Start/KrivineSpaceConfig.lean`); a machine of the
  model that performs Krivine transitions on the word, which a `DSPACE` membership would need, is
  not formalized.
- **Typed calculi and proof theory** — the simply typed lambda calculus over the same de Bruijn
  syntax, with Tait strong normalization and the untypability of `omega`
  (`Start/SimpleTypes.lean`); **System F**, the polymorphic lambda calculus in Curry style over
  the same terms, with Girard's reducibility candidates and strong normalization
  (`Start/SystemF.lean`), the substitution lemmas and subject reduction with its generation lemma
  (`Start/SystemFSubst.lean`, `Start/SystemFSR.lean`), and the polymorphic Church numerals,
  self-application — typable in System F but not in the simply typed calculus — and unique normal
  forms (`Start/SystemFChurch.lean`), with the Church-style presentation and its strong
  normalization by erasure, together with its subject reduction (`Start/SystemFC.lean`,
  `Start/SystemFCSR.lean`) and the confluence of its annotated reduction, both β and type-β, by
  parallel reduction (`Start/SystemFCSubst.lean`, `Start/SystemFCConfluence.lean`); and Gödel's
  System T with strong
  normalization, subject reduction and canonicity (`Start/SystemTSyntax.lean`, `Start/SystemT.lean`,
  `Start/SystemTCanon.lean`).
  Reduction in System T is confluent (`Start/SystemTConfluence.lean`), and the set-theoretic
  denotational semantics of System T is **adequate**: a closed term of type `nat` reduces to the
  numeral of its denotation, so at base type equality of denotations, convertibility and
  observational equivalence all coincide (`Start/SystemTDenot.lean`).
- **Curry–Howard–Lambek** — an intrinsically typed simply typed lambda calculus with a unit type,
  binary products and function types, with its substitution calculus and βη-conversion
  (`Start/Stlc.lean`).  Its *syntactic category* — types as objects, terms with one free variable
  modulo conversion as morphisms, substitution as composition — has finite products and an
  exponential, i.e. it is **cartesian closed** (`Start/StlcCcc.lean`).  Conversely, every
  cartesian closed category interprets the calculus, conversion is sound for that interpretation,
  and the interpretation assembles into a functor out of the syntactic category
  (`Start/CccModel.lean`).
- **Dependent types: `λΠ` and locally cartesian closed categories** — the layer above
  Curry–Howard–Lambek, where a type may depend on a term.  The calculus `λΠ` is formalized as a
  pure type system: raw syntax with a full parallel-substitution calculus and **Church–Rosser**
  for β (`Start/LambdaPi.lean`), and the typing judgement with weakening, the substitution lemma,
  the five inversion lemmas, validity, context conversion and **subject reduction**
  (`Start/LambdaPiTyping.lean`, `Start/LambdaPiBound.lean`).  The calculus is then normalized:
  types are unique up to conversion and the terms split into kinds, families and objects
  (`Start/LambdaPiUnique.lean`); forgetting the dependency sends a type to its **skeleton**, a
  simple type, which depends only on the type variables and is therefore invariant under
  conversion (`Start/LambdaPiSkeleton.lean`); a dependent derivation erases to a simply typed one
  over the skeletons (`Start/LambdaPiSimple.lean`); and Tait's reducibility method, in the Kripke
  form that the type annotations force, gives **strong normalization** for `λΠ`
  (`LambdaPi.Typing.sn`, `Start/LambdaPiSN.lean`).  Reading the calculus as a logic, this yields
  **consistency**: in the context declaring a type variable `α : ∗` no term has type `α`
  (`LambdaPi.not_typing_var_zero`, `Start/LambdaPiConsistent.lean`).  The other rule for
  functions, η, is settled in `Start/LambdaPiEta.lean`: on raw terms η-reduction terminates and is
  **confluent** (`LambdaPi.EtaRed.church_rosser`), but βη-reduction is **not**
  (`LambdaPi.not_church_rosser_betaEta`) — βη-conversion identifies two abstractions that differ
  only in their domain annotation (`LambdaPi.betaEtaConv_lam_annot`), and Nederpelt's term
  `λ(x : ∗). ((λ(y : □). y) x)` has the two distinct βη-normal reducts `λ(x : ∗). x` and
  `λ(y : □). y`.  So η can enter a Church-style calculus only through *typed* conversion; for the
  *untyped* calculus, whose abstractions carry no annotation, η instead terminates and **commutes
  with β** (`Lambda.reduces_etaReduces_commute`), so βη is confluent there
  (`Lambda.betaEta_church_rosser`, `Start/LambdaEta.lean`, `Start/LambdaBetaEta.lean`), and η can
  even be **postponed**: βη-reduction is β-reduction followed by η-reduction
  (`Lambda.betaEtaReduces_iff`, `Start/LambdaEtaPostpone.lean`).  The same parallel-η argument
  works for `λΠ`: η can be postponed there too, so a βη-reduction is a β-reduction followed by an
  η-reduction (`LambdaPi.betaEtaRed_iff`), and since η shrinks a term this upgrades strong
  normalization from β to **βη on typable terms** (`LambdaPi.Typing.betaEta_sn`,
  `Start/LambdaPiEtaPostpone.lean`).  The failure of confluence is, moreover, *only* about the
  annotations: erasing every domain annotation to a dummy sort, β and η strongly commute and βη is
  confluent (`LambdaPi.erased_betaEta_church_rosser`), so two raw terms are βη-convertible exactly
  when their erasures have a common βη-reduct (`LambdaPi.betaEtaConv_iff_join`) — **Church–Rosser
  modulo annotations**, with the consequences the conversion rule needs: distinct sorts stay
  distinct, no sort is convertible to a product, and products are injective
  (`Start/LambdaPiEtaConfluent.lean`).  All of these arguments are instances of one abstract
  rewriting theory, proved once for an arbitrary relation in `Start/Rewriting.lean` and used by
  each calculus through a single bridging lemma `Red t u ↔ Star Step t u`: the diamond
  property implies confluence, conversion of a confluent relation is joinability, strong
  commutation implies commutation, two confluent commuting relations have a confluent union
  (Hindley–Rosen), local postponement gives the factorization `(r ∪ s)* = r* ; s*`, a measure gives
  termination, and a terminating locally confluent relation is confluent (Newman).  Termination
  and confluence
  together make the calculus effective: a verified reduction strategy computes the normal form of
  a strongly normalizing term, so conversion of typable terms is **decidable**
  (`Start/LambdaPiNormalize.lean`), and the type-inference algorithm — written as a function that
  returns a type *together with a derivation*, hence sound by construction, and proved complete —
  decides typability and type checking (`LambdaPi.infer`, `LambdaPi.decidableTyping`,
  `Start/LambdaPiInfer.lean`).  Its **syntactic category** —
  objects
  the well-formed contexts, morphisms the well-typed substitutions modulo conversion — has a
  terminal object, and its context-extension squares are **pullbacks**
  (`Start/LambdaPiCat.lean`), which is the universal property that "a substitution into `A :: Γ`
  is a substitution into `Γ` plus a term of `A`".  On the semantic side, `Start/Cwa.lean` defines
  categories with attributes and their Π-structures, `Start/CwaType.lean` builds the standard
  model of families of types, `Start/Lccc.lean` packages Mathlib's chosen pullbacks and
  exponentiable morphisms into an explicit `LocallyCartesianClosed` class with the adjoint chain
  `Σ_f ⊣ f* ⊣ Π_f`, and `Start/LcccType.lean` proves that `Type u` is locally cartesian closed
  with an explicit dependent product and **identifies that categorical Π with the type-theoretic
  one** of the standard model.  The syntax of `λΠ` itself is a category with attributes with a
  weak Π-structure, and the η-law is proved to fail there (`Start/LambdaPiCwa.lean`).  On the
  semantic side the coherence problem is solved: types are presented by **local universes**, which
  makes substitution strictly functorial, so every category with pullbacks is a category with
  attributes and no slice object is lost (`Start/CwaLocalUniverse.lean`).  That strictified model
  also carries **both quantifiers**: for a locally cartesian closed category, the dependent product
  is built generically — its base is the pushforward classifying the pair `(A, B)`, its total space
  the pushforward of the display map of the generic `B` — so it is *strictly* stable under
  substitution, and abstraction and application are the two legs of one bijection, hence satisfy
  **β and η** (`Cwa.piStructOfLccc`); the dependent sum comes with it (`Cwa.sigmaStructOfLccc`), and
  `Type u` is an instance (`Start/CwaPi.lean`, `Start/CwaPiType.lean`).  Abstraction and
  application of that dependent product are natural in the context, so the model also validates
  the substitution law `(λ b)[σ] = λ (b[σ⁺])` (`LuTy.lam_sub`, `Start/CwaPiSub.lean`).  The
  comparison is then made **2-dimensional and reversible**: models and their lax 2-cells form a
  strict bicategory, strictification is a pseudofunctor out of the 2-category of locally cartesian
  closed categories (`Cwa.lcccStrictification`), reading off the category of contexts is a
  pseudofunctor back (`Cwa.lcccCtx`), one round trip is the identity on the nose and the other the
  identity up to a canonical invertible 2-cell, and both are biequivalences
  (`Cwa.lcccModelCat_biequivalent`, `Start/LcccBiequivalence.lean`).  `Start/CwaDemocratic.lean`
  begins the intrinsic description of the models so compared: a model is *full* when every
  morphism of contexts is a display map up to isomorphism over its codomain and *democratic* when
  every context is an extension of a terminal one, the contexts of a full model have pullbacks
  (`Cwa.hasPullbacks_of_isFull`), and every strictification is full and democratic.  That
  description is completed on the semantic side by `Start/CwaLcccOfFull.lean`: the category of
  contexts of a **full model with a natural Π-structure** (and coherent substitution on extended
  contexts) is locally cartesian closed (`LcccPullbacks.ofIsFull`) — the dependent product of a
  slice object is the display map of the Π-type of the two presented types, and naturality of the
  transposition is exactly the law `(λ b)[σ] = λ (b[σ⁺])`.  The generic ingredient, that the maps
  into a display map lying over a substitution are the terms of the substituted type, is
  `Cwa.homOverEquivTm` (`Start/CwaHomOver.lean`).  Finally `Start/CwaStrictifyFull.lean` compares a
  full model with the strictification of its own category of contexts: there is a morphism of
  models out of the strictification (`Cwa.fullStrictify`), the identity on contexts, bijective on
  terms, and every type of the model is in its image up to an isomorphism of extended contexts
  over the base (`Cwa.fullStrictify_essSurj`).  That comparison is *not* in general an
  equivalence.  In the lax 2-category a 2-cell is exactly a natural transformation of the functors
  on contexts, so an isomorphism of 1-cells is one of those functors (`Cwa.laxIsoOfNatIso`) and an
  equivalence would need only a morphism of models back that is the identity on contexts
  (`Cwa.fullStrictify_comp_iso_id`, `Cwa.comp_fullStrictify_iso_id`, `Start/CwaStrictifyEquiv.lean`)
  — that is, a universe naming every type.  The standard model of families is full
  (`CwaType.isFull_families`) and democratic (`CwaType.isDemocratic_families`) and has none:
  every type of `Type u` would embed into a single one, so there is no such morphism
  (`CwaType.false_of_mor_isEquivalence`) and the model is not equivalent to the strictification of
  its contexts (`CwaType.not_equivalent_ofPullbacks`, `Start/CwaFamiliesNoStrictify.lean`).  Since the
  types of `λΠ` are the *terms of the sort `∗`* rather than all the types of a model,
  `Start/CwaSmall.lean` extracts from a model with a universe its **small fragment**
  (`Cwa.Universe.smallCwa`): the category with attributes whose types are the codes, with its
  inclusion into the ambient model, the restriction of universe-preserving comparisons to it, and
  — when the universe is closed under products naturally — its own dependent product
  (`Cwa.Universe.smallWeakPi`).  Both sides supply an instance: the model presented by a universe
  object, whose types in a context are the maps into it (`CwaUniv.smallTyEquivHom`), and the small
  fragment of the syntactic model of `λΠ` (`LambdaPiUniv.smallSyntacticPi`), for which the code of
  a product is proved stable under substitution (`LambdaPiUniv.codeQ_sub`).  That small fragment
  is then compared with the model whose types are the small types of the calculus, and the two are
  found to be **the same model**: the identity on contexts is a morphism of categories with
  attributes in each direction (`LambdaPiUniv.smallToCwa` and `LambdaPiUniv.cwaToSmall`), acting on
  types by the bijection between the terms of `∗` and the small types, and the two composites are
  the identity, so the two syntactic models are isomorphic in the category of models
  (`LambdaPiUniv.smallModelIso`, `Start/LambdaPiSmallCompare.lean`).  Finally the syntax is
  interpreted in an **arbitrary** model: `LambdaPi.Model` is the structure a category of contexts
  must carry, the interpretation of raw expressions is given by the relations `LambdaPi.TyI` and
  `LambdaPi.TmI` (`Start/LambdaPiInterp.lean`), it is single-valued in a model whose product former
  is injective (`LambdaPi.functional_of_piInj`), commutes with renaming and substitution
  (`Start/LambdaPiInterpSub.lean`) and is invariant under β-conversion
  (`Start/LambdaPiInterpConv.lean`), and it is total on derivations
  (`LambdaPi.Typing.interp_total`).  Hence **initiality**: a derivable term denotes exactly one term
  of exactly one type (`LambdaPi.interp_exists_unique`), a well-typed substitution is carried by
  exactly one morphism (`LambdaPi.subI_exists_unique`), the interpretation is a functor on the
  syntactic category (`LambdaPiInitial.functor`), and it assembles into a morphism of categories
  with attributes out of the syntactic model (`LambdaPiInitial.mor`, `Start/LambdaPiInitial.lean`).
  That comparison morphism respects the whole structure of a model of `λΠ` and not merely the
  category with attributes: it carries the sort `∗` to the universe of the model and commutes with
  decoding (`LambdaPiInitial.mor_preservesUniverse`), preserves the dependent products over the
  small types (`mor_preservesSmallPi`) and the codes for those products (`mor_preservesPiClosed`,
  `Start/LambdaPiInitialUniv.lean`).  The interpretation is moreover **natural in the model**: a
  morphism of models `LambdaPi.ModelHom` (`Start/LambdaPiModelHom.lean`) transports the whole
  interpretation relation, so if a raw expression denotes a type, a term or a context in `M`, its
  image denotes the transported type, term or context in `N` (`LambdaPi.TyI.map`,
  `LambdaPi.TmI.map`, `LambdaPi.CtxI.map`, `Start/LambdaPiInterpTransport.lean`).  The comparison
  also preserves abstraction and **application** (`LambdaPiInitial.tmMap_appQ`,
  `Start/LambdaPiInitialApp.lean`), so it is itself a morphism of models
  (`LambdaPiInitial.modelHom`); with the rigidity of the hom-category this makes the syntactic
  model **bi-initial** among the models of `λΠ` with injective products
  (`LambdaPiInitial.biInitial_syntacticModel`, `Start/LambdaPiInitialModelHom.lean`).
  Strictification of a category with pullbacks is not 2-functorial for the strict 2-cells of
  models, but it is once the 2-cells are taken **lax** — the equality of types replaced by a map
  of extended contexts over the base (`Cwa.LaxTwoCell`, `Cwa.laxTwoCellOfNatTrans`,
  `Cwa.laxTwoCellOfNatTrans_id`, `Cwa.laxTwoCellOfNatTrans_comp`, `Start/CwaLaxTwoCell.lean`,
  `Start/CwaStrictLax.lean`).  Vertical composition of lax 2-cells is unital and associative, so
  the morphisms of models and the lax 2-cells between them form a category, into which the strict
  2-cells include by an injective functor (`Cwa.laxMorCategory`, `Cwa.laxInclusion`,
  `Cwa.TwoCell.toLax_injective`, `Start/CwaLaxCategory.lean`); a lax 2-cell can be whiskered by a
  morphism of models on either side, functorially in the 2-cell
  (`Cwa.LaxTwoCell.whiskerLeft`, `Cwa.LaxTwoCell.whiskerRight`, `Start/CwaLaxWhisker.lean`).
- **Böhm's separation theorem** — finite Böhm trees of normal forms (`Start/Bohm.lean`), the
  Böhm-out transformation (`Start/BohmOut.lean`), and the separation theorem for trees that are
  not η-equal (`Start/BohmEta.lean`).
- **Denotational semantics** — two models of the untyped calculus.  Scott's *graph model*
  `D = Set Tok` is a reflexive object (the Scott-continuous function space is a retract of `D`,
  `Start/GraphModel.lean`); interpreting terms in it validates β and gives a semantic proof that
  `Ω` is not convertible to `I`, hence that the β-calculus is consistent, without using
  confluence (`Start/GraphModelSemantics.lean`).  Scott's **`D∞`** is built as the inverse limit
  of the tower `D₀ = Bool`, `Dₙ₊₁ = [Dₙ →𝒄 Dₙ]` with its embedding-projection pairs
  (`Start/ScottTower.lean`, `Start/ScottDinf.lean`, `Start/ScottPsi.lean`), and the isomorphism
  `D∞ ≅ [D∞ →𝒄 D∞]` is proved in `Start/ScottDinfIso.lean`; because it is an isomorphism and
  not just a retraction, the induced interpretation is extensional and validates η as well as β
  (`Start/ScottDinfModel.lean`).  In `D∞` the diverging term `Ω` denotes the least element, so
  `Ω` and `I` are not βη-convertible: the **λη calculus is consistent**, again by a purely
  semantic argument (`Start/ScottDinfOmega.lean`).
- **Adequacy of the graph model** — the interpretation in the graph model is not merely sound: a
  term whose denotation contains a token, in any environment, has a **head normal form**
  (`Start/GraphAdequacy.lean`, by a computability argument on the tokens), and conversely a head
  normal form has a nonempty denotation, so for a closed term `⟦t⟧ρ = ∅` exactly when `t` has no
  head normal form.  For closed terms this coincides with unsolvability
  (`Start/HnfSolvable.lean`: a closed head normal form is solvable, by the substitution calculus
  of `Start/Bohm.lean`), so the least element of the model is precisely the unsolvable terms; and
  denotational equality implies **observational equivalence** at head normalization
  (`Start/GraphObs.lean`); the converse fails, see below.
- **Adequacy of `D∞`** — the same holds for the inverse limit.  Every head normalizable term has a
  denotation different from the least element in a suitable environment (`Start/DinfHnf.lean`),
  and conversely a term whose denotation is not the least element, in any environment, has a head
  normal form (`ScottDinf.hasHnf_of_ddenot_ne_botDinf`, `Start/DinfAdequacy.lean`).  The proof is
  the classical computability argument, carried out along the *tower* — `ScottDinf.RelD n z t`
  relates a stage-`n` value to a term, is compatible with the embedding–projection pairs and
  closed under suprema of chains, and the fundamental lemma `ScottDinf.realD_substEnv` shows the
  interpretation preserves it.  Hence `⟦t⟧ρ = ⊥` in every environment exactly when `t` has no head
  normal form, for a closed term exactly when it is unsolvable, and denotational equality implies
  observational equivalence at head normalization (`ScottDinf.obsEqHnf_of_ddenot_eq`).
- **Full abstraction fails for the graph model** (`Start/GraphNotFullyAbstract.lean`) — the
  identity `λx. x` and its eta-expansion `λx. λy. x y` have different graph denotations, the graph
  model not being extensional, but no context distinguishes them, because `D∞` validates eta and
  is adequate.  So the inclusion of denotational into observational equality is strict there
  (`GraphNotFullyAbstract.graph_not_fully_abstract`), and `D∞` identifies strictly more terms than
  the graph model.
- **The approximation theorem for the graph model** (`Start/GraphApprox.lean`,
  `Start/GraphApproxTheorem.lean`) — the direct approximant `ω(M)` keeps the abstraction prefix
  and the variable head of `M` and erases everything under a head redex to `Ω`.  The denotation
  of a term is exactly the union of the denotations of the direct approximants of its reducts,
  `⟦M⟧ρ = ⋃ {⟦ω(M')⟧ρ : M ↠ M'}` (`GraphModel.denot_eq_iUnion_denot_direct`): no information of
  a term is invisible to all of its finite approximants.  The easy inclusion is monotonicity of
  the denotation for the approximation order; the hard one is a Kripke-style computability
  argument on the tokens, whose fundamental lemma `GraphModel.arealAux_substEnv` carries two
  environments, one for the free variables of the term and one for the target context of the
  substitution.
- **The approximation theorem for `D∞`** (`Start/DinfApprox.lean`) — the same statement in the
  order-theoretic form the continuous model calls for: `⟦M⟧ρ` is the least upper bound of
  `{⟦ω(M')⟧ρ : M ↠ M'}` (`ScottDinf.isLUB_ddenot_direct`).  The computability relation is indexed
  by the finite levels of the inverse limit; each level is finite, so a supremum along a chain is
  attained there, and confluence merges the finitely many reducts the different levels produce.
- **Full abstraction of `D∞` on closed normal forms** (`Start/DinfApply.lean`,
  `Start/DinfBohmEta.lean`, `Start/DinfNormalFullAbstraction.lean`) — the finite case of
  Wadsworth's theorem.  `D∞` is extensional (`ScottDinf.dinf_ext_dappN`), which lets two
  denotations be compared by feeding them a common stack of arguments; a size induction mirroring
  the η-general Böhm-out descent then shows that η-equal Böhm trees have the same denotation
  (`ScottDinf.ddenot_toTerm_eq_of_tagEq`).  Conversely separable terms are distinguished by the
  context `X a₁ … aₖ Ω I` (`ScottDinf.not_obsEqHnf_of_separable`).  With Böhm's theorem in its
  η-general form this gives `ScottDinf.obsEqHnf_iff_ddenot_eq_normal`: for closed β-normal forms,
  observational equivalence and equality of `D∞` denotations coincide, and hence
  `ScottDinf.obsEqHnf_iff_ddenot_eq_of_normalizes` for every closed term that has a normal form.
  The general case needs a separation argument for the finite approximants `ω(M')`, which contain
  `Ω`; `Start/DinfWadsworth.lean` makes that gap precise, proving that contexts are monotone in
  their hole (`ScottDinf.ddenot_fill_mono`) and reducing full abstraction to a separation
  principle `ScottDinf.SeparatesApprox`, which the next item discharges.
- **Wadsworth's theorem** (`Start/HeadSpine.lean`, `Start/TagFail.lean`, `Start/ApproxShape.lean`,
  `Start/DinfSpine.lean`, `Start/DinfTagBelow.lean`, `Start/DinfTagBelowSound.lean`) — two closed
  terms are observationally equivalent, by head normalisation, exactly when they have the same
  denotation in `D∞` (`ScottDinf.obsEqHnf_iff_ddenot_eq`).  `Lambda.TagFail` is a *finite failure
  witness* for the comparison of two arbitrary terms, and `Lambda.sepDiv_of_tagFail` is the
  Böhm-out that turns such a witness into closed arguments on which the first term head-converges
  and the second head-diverges; the converse, `ScottDinf.tagBelowSound`, says that absence of a
  witness implies the `D∞` inequality, so the order between closed terms *is* the absence of a
  failure witness (`ScottDinf.ddenot_le_iff_not_tagFail_unconditional`).  Its proof splits at the
  approximation theorem: a finite approximant is put below a term by a size induction on the shape
  of the approximant (`Lambda.approx_direct_shape`,
  `ScottDinf.le_ddenot_of_not_tagFail_approx`), whose only non-structural case — a variable
  against a possibly *infinite* η-expansion of it — is settled level by level in the inverse limit
  (`ScottDinf.le_ddenot_of_not_tagFail_var`).
- **The infinite η-expansion of the identity** (`Start/DinfEtaLimit.lean`) — the reason no relation
  generated by *finite* witnesses can decide the `D∞` order.  Let `J = Θ (λ j x y. x (j y))`, so
  that `J ↠ λx y. x (J y)` (`ScottDinf.Jterm_reduces`): unfolding, `J` is the identity η-expanded
  infinitely often.  `ScottDinf.eq_dId_of_eta_fixpoint` characterises the identity of `D∞` by the
  two η-limit equations `x · y · z = y · (x · z)` and `x · ⊥ = ⊥`, by two simultaneous inductions
  over the levels of the inverse limit; applied to `J` it gives `⟦J⟧ = ⟦I⟧`
  (`ScottDinf.ddenot_Jterm_eq_ddenot_id`), hence `ScottDinf.obsEqHnf_Jterm_id` and
  `ScottDinf.obsEqHnf_app_Jterm` (`J M` is indistinguishable from `M`).  The identification is not
  a β-conversion: the graph model, sound for β and not extensional, separates the two
  (`ScottDinf.not_conv_Jterm_I`).
- **Head reduction** — the head strategy (weak head steps, allowed under a leading abstraction)
  is defined in `Start/HeadReduction.lean` and proved deterministic and *normalizing*: a term has
  a head normal form exactly when the strategy terminates on it
  (`Lambda.hasHnf_iff_hasHeadEval`), by standardization for weak head reduction and confluence.
  This yields the structural laws that arbitrary reductions do not give: head divergence is
  preserved by substitution (`Lambda.hasHnf_of_hasHnf_subst`) and head normalizability of an
  application is inherited by its function part (`Lambda.HasHnf.app_left`).  Hence a purely
  syntactic proof that every solvable term has a head normal form (`Start/HeadSolvable.lean`),
  which makes Wadsworth's characterization of closed solvable terms independent of the graph
  model.
- **Intersection types and the filter model** (`Start/IntersectionTypes.lean`,
  `Start/FilterModel.lean`, `Start/IntersectionNormalization.lean`) — the third model, and the one
  that explains the other two.  The strict types of the Coppo–Dezani system `λ∩` are *literally*
  the tokens of the graph model, and `Inter.deriv_iff_mem_denot` proves the coincidence exact:
  `Γ ⊢ M : σ` holds precisely when the token `σ` lies in the denotation of `M` in the environment
  read off from `Γ`.  The set of types of a term therefore **is** its denotation, so the graph
  model is the filter model of `λ∩`.  Subject reduction and subject expansion are then immediate
  (`Inter.deriv_reduces`, `Inter.deriv_expansion`), and typability coincides with head
  normalisability and with solvability (`Inter.typable_iff_hasHnf`, `Inter.typable_iff_solvable`):
  "syntactically typable" and "semantically different from the empty denotation" are the same
  statement.  Restricting to `ω`-free types gives the **Coppo–Dezani normalisation theorem**
  (`Inter.properTypable_iff_hasNormalForm`): a term is typable without `ω` exactly when it has a
  β-normal form — proved through the approximation theorem rather than by reducibility — and the
  inclusion is strict (`Inter.exists_typable_not_properTypable`, witnessed by `x Ω`).
- **Multi types: intersection types that count** (`Start/MultiTypes.lean`) — the *non-idempotent*
  system of de Carvalho, where an intersection is a finite **multiset** rather than a set.
  Idempotence is exactly what destroys quantitative information: with `σ ∧ σ = σ` a premise may be
  reused for free, and the derivation forgets how often an argument was needed.  Dropping it — no
  weakening, contexts as outputs, an application summing the contexts of its premises — turns the
  derivation into a measurement.  The engine is the quantitative substitution lemma
  `Multi.substitution` (the substituted derivation has size `n + m - |a|`, where `a` is the multi
  type consumed at the substituted variable), from which `Multi.subject_reduction_hstep` shows a
  head step **strictly decreases** the size.  Hence `Multi.hnIn_of_deriv`: a term with a
  derivation of size `n` reaches a head normal form within `n` head steps, so the type system
  bounds the running time and not merely the fact of termination.  Conversely every head normal
  form is typable (`Multi.typable_of_isHnf`) and `Ω` is not (`Multi.not_typable_omega`).
  Subject *expansion* is not proved, so de Carvalho's exact equality between derivation size and
  head reduction length is not claimed — only the bound.

- **λ-models and the Scott–Koymans correspondence** (`Start/LambdaModel.lean`,
  `Start/LambdaModelInstances.lean`, `Start/KaroubiLambda.lean`, `Start/ReflexiveCcc.lean`,
  `Start/ReflexiveType.lean`, `Start/ScottKoymans.lean`) — the definition the three models above
  are instances of.  A **λ-model** (`Lambda.LambdaModel`) is an applicative structure with an
  interpretation `⟦t⟧ρ` satisfying the Meyer–Scott axioms, and from those four axioms alone come
  the lifting and substitution lemmas, soundness for β (`interp_conv`), the combinatory structure
  and the identification of extensionality with η.  The graph model, `D∞` and the filter model
  are instances (`GraphModel.model`, `ScottDinf.model`, `Inter.typeSet_eq_model_interp`), and
  their theories are the entries `Th(𝒫ω)`, `Th(D∞)` of the lattice above
  (`Lambda.LambdaModel.theory`).  Categorically: the **Karoubi envelope** of a λ-model — objects
  the idempotents `a ∘ a = a`, morphisms the elements they absorb — is a cartesian closed
  category (`Lambda.LambdaModel.karoubiMonoidalClosed`) in which `D = λz. z` is a **reflexive
  object**, `D ⇒ D` a retract of `D` (`Lambda.LambdaModel.reflexive_dRet`).  Conversely a
  reflexive object in *any* cartesian closed category interprets the untyped terms as morphisms
  in environments of generalized elements, naturally in the stage and soundly for β
  (`ReflexiveCcc.ReflexiveObject.interp_conv`), with an isomorphism `D ≅ (D ⇒ D)` validating η;
  in the category of sets that interpretation is a λ-model on the nose
  (`Lambda.SetReflexive.toModel`).

- **Realizability: partial combinatory algebras and assemblies** (`Start/PCA.lean`,
  `Start/PCATotal.lean`, `Start/PCAKleene.lean`, `Start/Assembly.lean`, `Start/AssemblyCcc.lean`,
  `Start/AssemblyLimits.lean`, `Start/AssemblyNNO.lean`) — the other categorical semantics of
  computation.  A **PCA** (`Realizability.PCA`) is a set with a partial application and the two
  combinators `k`, `s`; *combinatory completeness* is proved in the form of an abstraction
  operator on applicative expressions with `Realizability.PCA.lam_app`, which is what makes every
  later construction possible.  Kleene's first algebra `K₁` — the naturals with Turing
  application `a · b = φ_a(b)` — is an instance (`Realizability.Kleene.instPCANat`), and so is
  every total combinatory algebra (`Realizability.TCA.toPCA`).  Kleene's **second** algebra `K₂`
  (`Start/KleeneTwoBasic.lean`, `Start/KleeneTwo.lean`) is the other pole of the picture: Baire
  space `ℕ → ℕ` with the application of *function* realizability, where `α | β` answers queries
  about finite initial segments of `β` (`Realizability.KleeneTwo.appK`).  That application is
  continuous — every value is produced by a finite initial segment of the argument, which is
  Kleene's continuity principle (`KleeneTwo.appK_continuous`) — and genuinely partial
  (`KleeneTwo.appK_zero_eq_none`).  The combinator `k` comes from the canonical associate of a
  continuous operation (`KleeneTwo.detAssoc`, `KleeneTwo.appK_detAssoc`); the combinator `s`
  needs an explicit finite approximation of `γ ↦ (α|γ)|(β|γ)`, proved sound and complete
  (`KleeneTwo.compAux_sound`, `KleeneTwo.compAux_complete`), and the two together make `K₂` a PCA
  (`Realizability.KleeneTwo.instPCABaire`).  The two algebras are compared by an **applicative
  morphism** in the sense of Longley (`Start/PCAMorphism.lean`, `Realizability.AppMorphism`):
  every PCA has an identity morphism, morphisms compose (`AppMorphism.comp`), and
  `Realizability.KleeneTwo.kOneToTwo` sends a number to the constant function with that value, so
  number realizability lands inside function realizability.  Continuity has a Brouwerian
  consequence: no element of `K₂` decides whether its argument is the zero function
  (`KleeneTwo.no_zero_test`).  The embedding is not reversible: applicative morphisms `K₂ → K₁`
  do exist — the trivial one, `Realizability.AppMorphism.trivialMor` — but none of them can read
  a single bit back off a representative (`Start/KleeneNoRetraction.lean`,
  `KleeneTwo.no_separatesBits_morphism`).  `Start/PCAOrder.lean` turns this into an order: the
  preorder of algebras under the mere existence of a morphism (`Realizability.PCALe`) is
  degenerate — the trivial morphism makes all algebras equivalent (`Realizability.pcaEquiv_of_any`)
  — whereas the morphisms that *decide* their representatives
  (`Realizability.AppMorphism.Decides`) form a preorder in which `K₁ < K₂` strictly
  (`Realizability.KleeneTwo.kleene_strict`).  Function realizability opens onto **computable
  analysis**, and
  `Start/Specker.lean` takes the first step there with a **Specker sequence**
  (`Lambda.speckerVal`): a sequence of rationals that is nondecreasing
  (`Lambda.speckerVal_monotone`), bounded by `1` (`Lambda.speckerVal_lt_one`) and computable —
  its numerator over `2^n` is a computable function of `n` (`Lambda.computable_speckerNum`,
  `Lambda.speckerVal_eq`) — yet has **no computable modulus of convergence**
  (`Lambda.specker_no_computable_modulus`), since from one the halting set would be decidable.
  Effectively, the monotone convergence theorem fails.  `Start/SpeckerReal.lean` takes the limit
  `Lambda.speckerReal` and proves the classical form of **Specker's theorem**: that real number
  is not computable (`Lambda.specker_limit_not_computable`) — no computable `f : ℕ → ℕ` gives
  dyadic approximations `f m / 2 ^ m` to within `2 ^ (-m)`, since an unbounded search through the
  sequence would then decide the halting set.  `Start/ComputableReal.lean` then runs the standard
  construction of computable analysis on top of `K₂`: a real is presented by a **name**, a
  sequence of coded rationals converging to it with error at most `2 ^ (-i)` at stage `i`
  (`KleeneTwo.IsName`), and `f : ℝ → ℝ` is **computable** when one element of `K₂` turns every
  name of `x` into a name of `f x` (`KleeneTwo.Realizes`).  Such a function is **continuous**,
  with an explicit modulus (`KleeneTwo.Realizes.exists_modulus`,
  `KleeneTwo.IsComputableFun.continuous`): the finite initial segment of the name of `x` read
  when computing the `k`-th output rational is a modulus, because every nearby point has a name
  beginning with the same segment (`KleeneTwo.glue_isName`).  So the step function is not
  computable (`KleeneTwo.not_isComputableFun_step`) although each of its values is a computable
  real, while the identity and the constants are.  This is the type-two counterpart of the
  Kreisel–Lacombe–Shoenfield theorem, which is the same statement for Markov computability and is
  not claimed here.  Over an arbitrary PCA the
  **assemblies** `Realizability.Assembly A` form a category with finite products
  (`Assembly.prodFanIsLimit`) which is cartesian closed, the exponential being the tracked maps
  (`Assembly.monoidalClosed`); it has equalizers, cut out as sub-assemblies, hence **all finite
  limits** (`Assembly.instHasFiniteLimits`); and the naturals, realized by the Curry numerals,
  form a **natural numbers object** (`Assembly.isNNO_natAsm`): iteration of a tracked endomap is
  itself tracked, and the mediating map is unique.  Finally the sub-assemblies are **classified**
  (`Start/AssemblySubobject.lean`): in the assembly of propositions `Assembly.propAsm` every
  element of the algebra realizes every proposition, maps into it are exactly the predicates on
  the carrier (`Assembly.homPropEquiv`), and the sub-assembly cut out by a predicate is the
  pullback of `true` along its characteristic map (`Assembly.isPullback_subAsm`), uniquely so
  (`Assembly.exists_unique_charMap`).  This classifies the *regular* subobjects, the ones whose
  realizers are inherited from the ambient assembly, and not every mono: `Asm(A)` is not a topos.
  Assemblies sit over sets by an adjunction (`Start/AssemblyGlobalSections.lean`): forgetting the
  realizers is left adjoint to the **indiscrete** assembly, in which everything realizes
  everything (`Assembly.gammaNablaAdj`), the indiscrete functor is fully faithful
  (`Assembly.nablaFullyFaithful`), the classifier is the indiscrete assembly on `Prop`, and the
  carrier of an assembly is its set of global sections, the maps out of the terminal assembly
  (`Assembly.globalSectionsEquiv`).
- **Modest sets are partial equivalence relations** (`Start/PER.lean`, `Start/Modest.lean`,
  `Start/ModestEquiv.lean`) — a **PER** over a PCA is a symmetric transitive relation on the
  algebra; it presents the assembly of its quotient (`PER.toAsm`), which is *modest*: realizers
  determine elements.  Taking as morphisms of PERs the functions of the quotients computed by a
  single element of the algebra (`PER.Tracked`, the same condition as being tracked as a map of
  assemblies, `PER.tracked_iff`), PERs form a category, and the comparison functor into the full
  subcategory of the modest assemblies is fully faithful (`PER.toModestFullyFaithful`) and
  essentially surjective — a modest assembly has the same realizers as the assembly of the PER it
  presents (`Assembly.toPERIso`).  So **PERs and modest sets are the same category**
  (`perEquivModest`), and under the correspondence the arrow PER is the exponential
  (`PER.arrowIso`).  Modesty is invariant under isomorphism (`Assembly.Modest.of_iso`), the
  terminal assembly and the products and exponentials of modest assemblies are terminal, products
  and exponentials *in the subcategory*, so the **modest sets are a cartesian closed category**
  (`Modest.instMonoidalClosed`, `Start/ModestCcc.lean`) and so, by transport along the
  equivalence, are the PERs (`PER.instMonoidalClosed`).
- **Realizability over Kleene's first algebra** (`Start/AssemblyKleene.lean`) — over `K₁` the
  naturals carry the *standard* assembly `Realizability.Kleene.natK1`, in which a number realizes
  itself.  A function `ℕ → ℕ` is tracked there **exactly when it is computable**
  (`Kleene.tracked_natK1_iff`), so the endomorphisms of that object are in bijection with the
  computable functions (`Kleene.natK1EndEquiv`; for two arguments,
  `Kleene.tracked_prod_natK1_iff`) and the diagonal function `n ↦ φₙ(n) + 1` is not
  one of them (`Kleene.exists_not_tracked_natK1`): `Asm(K₁)` is not the category of sets.
  Iterating a tracked endomorphism is partial recursive, so the standard numbers assembly is a
  natural numbers object too (`Kleene.isNNO_natK1`); a natural numbers object is unique up to
  isomorphism (`CategoryTheory.Limits.IsNNO.iso`), so it is isomorphic to the Curry numeral one
  (`Kleene.natK1IsoNatAsm`).
- **Booleans and decidable predicates over `K₁`** (`Start/AssemblyKleeneBool.lean`) — the standard
  assembly of booleans `Realizability.Kleene.boolK1` (`true` realized by `1`, `false` by `0`) has
  the computable boolean-valued functions as its maps out of the numbers
  (`Kleene.tracked_boolK1_iff`, `Kleene.boolHomEquiv`), so a predicate on the numbers is cut out
  by a characteristic morphism into the booleans exactly when it is a computable predicate
  (`Kleene.exists_charBool_iff`).  Self-halting is undecidable
  (`Kleene.not_computable_selfHalt`), hence has no characteristic boolean map of either polarity
  (`Kleene.no_charBool_selfHalt`, `Kleene.boolK1_not_classifier`): in `Asm(K₁)` the booleans are
  no classifier of sub-assemblies, unlike the indiscrete assembly on `Prop`.  The booleans are, on
  the other hand, the coproduct `1 + 1` (`Kleene.boolK1IsoCoprod`, `Kleene.boolCofanIsColimit`).
  A predicate is recursively enumerable exactly when it is the domain of convergence of an element
  of `K₁` (`Kleene.rePred_iff_exists_index`), and self-halting is one
  (`Kleene.rePred_selfHalt`): semidecidable, but not decidable
  (`Kleene.not_computablePred_selfHalt`).
- **Projective assemblies** (`Start/AssemblyProjective.lean`) — an assembly is *partitioned*
  (`Realizability.Assembly.Partitioned`) when each point has exactly one realizer.  Partitioned
  assemblies are projective for the covers, i.e. for the morphisms that lift realizers
  (`Assembly.Partitioned.regularProjective`), every assembly is covered by a partitioned one
  (`Assembly.exists_partitioned_cover`), and the regular projectives are exactly the assemblies
  isomorphic to partitioned ones (`Assembly.regularProjective_iff`), a class closed under binary
  products (`Assembly.RegularProjective.prod`).  Projectivity for all
  epimorphisms is strictly stronger: over `K₁` the standard numbers assembly is regular projective
  (`Kleene.regularProjective_natK1`) but not projective (`Kleene.not_projective_natK1`), the
  epimorphism onto the indiscrete assembly on the numbers failing to lift realizers
  (`Kleene.not_liftsRealizers_natToNabla`).
- **The exact completion of the assemblies** (`Start/AsmExReg.lean` and its satellites) — an
  object is an assembly with a *pseudo-equivalence relation* on it presented computationally
  (`Realizability.ExReg.ERel`): proofs of `x ~ y` carry realizers, their two endpoints are
  computable from the proof, and reflexivity, symmetry and transitivity are each witnessed by an
  element of the algebra.  Morphisms are functions transporting proofs, up to homotopy
  (`ExReg.Pre`, `ExReg.Homotopic`, `ExReg.instCategory`).  The assemblies embed fully and
  faithfully by taking equality (`ExReg.instFullEmb`, `ExReg.instFaithfulEmb`), the completion
  has finite limits (`ExReg.instHasFiniteLimits`), every object is a regular quotient of an
  assembly (`ExReg.quotIsColimit`), and every morphism factors as an epimorphism followed by a
  monomorphism (`ExReg.imgFac_comp_imgIncl`).  Its regular epimorphisms are exactly its
  *covers*, the morphisms with a computable section up to the relation
  (`ExReg.cover_iff_isRegularEpi`); covers are stable under base change
  (`ExReg.cover_of_isPullback`) and the completion is a **regular category**
  (`ExReg.instRegular`).  Every internal equivalence relation of the completion has a
  **coequalizer** (`ExReg.Coeq.hasCoequalizer_of_isInternalEquiv`,
  `Start/AsmExRegCoeq.lean`): the base of the object with the relation generated by the two
  legs, whose transitivity is read off the object of composable pairs.  But the completion is
  **not exact** (`Start/AsmExRegNotExact.lean`): over any algebra with three distinct elements,
  in particular over Kleene's first algebra, it carries an internal equivalence relation that is
  the kernel pair of no morphism (`ExReg.NotExact.exists_internalEquiv_not_kernelPair`,
  `ExReg.NotExact.kleene_exReg_not_exact`).  The obstruction is uniformity: a morphism must
  choose one point per point of the source *and* compute a realizer of the chosen point from a
  realizer of the source point, and the counterexample makes the points lying over a related
  pair carry realizers that no single element of the algebra can produce — a three-point
  pigeonhole, since application is single-valued.
- **Exactness on the regular projectives** (`Start/AsmExRegProj.lean`,
  `Start/AsmExRegEffective.lean`) — and that is exactly where exactness is repaired.  On the full
  subcategory `ExReg.ExRegP` of the objects whose base is a **partitioned** assembly, i.e. a
  regular projective of `Asm(A)` (`ExReg.ExRegP.regularProjective_base`), **every internal
  equivalence relation is effective**: the map onto the quotient above is its coequalizer and the
  relation is that map's kernel pair (`ExReg.ExRegP.exists_effective_quotient`,
  `ExReg.ExRegP.isKernelPair_of_isInternalEquiv`).  The proofs run on *probes* — objects whose
  points are their own realizers (`ExReg.pairERel`, `ExReg.partitioned_pairERel`), so that a
  tracker out of them may read the data their points carry.  Probing a jointly monic pair turns
  joint monicity into a single element of the algebra manufacturing the proof that relates two
  points (`ExReg.JMTracker`, `ExReg.jmTracker_of_jointlyMono`), and probing the composable pairs
  makes the quotient available over the weaker data that the subcategory supplies
  (`ExReg.compData`, `ExReg.EqvDataP`, `ExReg.coeqObjP`).  With them the lifting goes through
  (`ExReg.exists_liftPre`, `ExReg.existsUnique_lift`): one realizer per point of the source
  determines both the point of the relation to choose and a realizer of it.  Not claimed:
  regularity of the restricted subcategory in its own right, the universal property of the
  completion among exact categories, the topos structure, and the identification with the
  effective topos.

`Start/Demo.lean` is a guided tour with `#check`s of the headline statements.

## Building

> **Note on the pinned toolchain.**  The library is built against Lean `v4.28.0` and the matching
> Mathlib tag `v4.28.0` (commit `8f9d9cff6b`).  `cslib` is pinned to the last revision built for
> that toolchain (`b13a67207c489f4b3f816cf96fcd3d38855db80f`).  All of `Start/`
> compiles on that toolchain, including the two modules that depend on `cslib`
> (`Start/Representation.lean` and `Start/KolmogorovRepresentation.lean`).

The project pins Lean `v4.28.0` (`lean-toolchain`); `lakefile.toml` requires Mathlib and `cslib`
as git dependencies at the revisions above, and `lake-manifest.json` records exactly those
revisions.  These sources must agree: if they do not, `lake` re-resolves the dependencies on every
invocation and starts compiling all of Mathlib from source, which never finishes in reasonable
time.

From a fresh clone:

```bash
lake exe cache get   # download prebuilt Mathlib artifacts (do this first!)
lake build           # builds the `Start` library
```

`lake exe cache get` is what keeps `lake build` from recompiling Mathlib itself.

The Lake package is called `lambda_computability` (matching the repository name; Lake package
names must be Lean identifiers, hence the underscore).  The Lean library target is `Start`, so
`import Start.…` is unaffected.

## Releases

Library versions (`version` in `lakefile.toml`, currently `0.1.0`) are independent of the Lean
toolchain version, and releases are cut by hand.  See [`docs/RELEASING.md`](docs/RELEASING.md)
for the policy and [`docs/release-notes/`](docs/release-notes) for the notes of each release.

## Task board and evidence

`docs/goal/task-board.yaml` (rendered to `docs/current-goal-state.md`) tracks every result with an
evidence note in `docs/goal/evidence/`, including the honest boundary of each claim.  Of the 159
tasks, 158 are `DONE_STRONG` and the remaining one (`M9-LAMBDAPI-LCCC`, `BACKEND_PARTIAL`) carries
an explicit open boundary; no task is left open.  The consolidation
work that `docs/consolidation-review.md` argues for is done: `Start/Rewriting.lean` proves the
generic rewriting statements once, and the eight calculi named there obtain them through a single
bridging lemma each.  Validate and re-render with:

```bash
python3 scripts/goal_state.py validate
python3 scripts/goal_state.py render
```

## Roadmap

Directions that are **not** formalized here yet, roughly in order of how close the existing
material gets to them:

| Direction | Why it is interesting | Starting point in this repo |
| --- | --- | --- |
| Levin–Schnorr for the lambda-calculus complexity `Lambda.kolmP` | Both halves are proved for the universal prefix machine `KC.KU` (`Start/LevinSchnorr.lean`), and `KU s ≤ kolmP s + c` is proved (`Start/KUOptimal.lean`); the opposite comparison, which is what would transfer the equivalence to `kolmP`, is not formalized and is not expected in that form | `Start/KUOptimal.lean`, `Start/LevinSchnorr.lean` |
| Schnorr randomness, Solovay tests | Deeper randomness notions, not covered by the Martin-Löf framework here | `Start/MartinLof.lean` |
| Cobham's theorem, and a link to machine-level polynomial time | Would connect `Start/ComplexityClasses.lean` (Cobham axioms) to `Start/TM2PolyTime.lean` (bounded TM2 machines) and to mathlib's `Computable` | `Start/ComplexityClasses.lean`, `Start/TM2PolyTime.lean` |
| Full abstraction for the untyped models | Adequacy is proved for the typed setting of System T (`Start/SystemTDenot.lean`) and, for the untyped calculus, for both the graph model (`Start/GraphAdequacy.lean`, `Start/HnfSolvable.lean`, `Start/GraphObs.lean`) and `D∞` (`Start/DinfAdequacy.lean`); for the graph model full abstraction is now *disproved* (`Start/GraphNotFullyAbstract.lean`: the identity and its eta-expansion are observationally equivalent but have different graph denotations); the approximation theorem for the graph model is proved (`Start/GraphApproxTheorem.lean`: a denotation is the union of the denotations of the direct approximants of the reducts); the approximation theorem for `D∞` is proved as well (`Start/DinfApprox.lean`: a denotation is the least upper bound of the denotations of the direct approximants of the reducts), and full abstraction of `D∞` is proved for arbitrary closed terms — Wadsworth's theorem, `ScottDinf.obsEqHnf_iff_ddenot_eq` in `Start/DinfTagBelowSound.lean`, the normal-form case being `Start/DinfNormalFullAbstraction.lean` | `Start/GraphNotFullyAbstract.lean`, `Start/GraphApprox.lean`, `Start/GraphApproxTheorem.lean`, `Start/DinfApprox.lean`, `Start/DinfBohmEta.lean`, `Start/DinfNormalFullAbstraction.lean`, `Start/TagFail.lean`, `Start/ApproxShape.lean`, `Start/DinfTagBelow.lean`, `Start/DinfTagBelowSound.lean`, `Start/DinfAdequacy.lean`, `Start/GraphObs.lean` |
| Gentzen consistency, ordinal analysis up to `ε₀` | Proof theory beyond strong normalization | `Start/SystemT.lean`, `Start/SystemTCanon.lean` |
| Post's problem for **Turing** reducibility (Friedberg–Muchnik) | The many-one case is settled here (`Start/PostSimple.lean`, `Start/PostIncomplete.lean`: a simple set is neither computable nor many-one complete, and `Start/PostCreative.lean`: creative sets are many-one complete); relative computability, the jump and the Kleene–Post construction are formalized (`Start/OracleUniversal.lean`, `Start/KleenePost.lean`, `Start/JumpSigmaOne.lean`), but the Turing case of Post's problem needs a priority construction with injury, which is not formalized | `Start/PostSimple.lean`, `Start/PostIncomplete.lean`, `Start/KleenePost.lean`, `Start/JumpSigmaOne.lean` |
| Post's theorem at every level (`Σ⁰ₙ₊₁` is exactly "r.e. in `∅⁽ⁿ⁾`") | Level one and level two are proved (`Start/ArithHierarchy.lean`, `Start/PostTheoremTwo.lean`); the general case needs the hierarchy relativized to an oracle | `Start/ArithHierarchy.lean`, `Start/PostTheoremTwo.lean`, `Start/JumpSigmaOne.lean` |
| Reverse mathematics (Big Five calibration) | Would connect this development to the reverse-mathematics libraries | `Start/HaltingComplete.lean`, `Start/MartinLof.lean` |
| Bridge to `algorithmic-randomness`: lambda-term randomness ⟺ program-code randomness | Makes the AIT results above reusable outside this repo (the `cslib` representation bridge is now done — `Start/Representation.lean`) | `Start/Kolmogorov.lean` |

## License

Apache License 2.0 — see [`LICENSE`](LICENSE).

## Scratch files

These files are experiments kept from earlier exploration.  They are **not** part of the `Start`
library target, are not built by `lake build`, and still contain `sorry`s and dead ends.  Nothing
in `Start/` depends on them: `temp.lean`, `temp2.lean` (earlier monolithic drafts), `Check.lean`,
`check_subst.lean` (standalone `Primrec`/substitution checks), `MLTestRequests.lean` (a first
draft superseded by `Start/OmegaURandom.lean`) and `Scratch.lean`.

## Provenance and status

The library compiles with `lake build` on the pinned toolchain, contains no `sorry` and no
`axiom` in `Start/`, and its headline results depend only on `propext`, `Classical.choice` and
`Quot.sound`.

This project was edited by [Aristotle](https://aristotle.harmonic.fun).  To cite Aristotle, tag
`@Aristotle-Harmonic` on GitHub PRs/issues, or add it as a commit co-author:

```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
