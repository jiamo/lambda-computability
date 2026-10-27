# M30-MLTT — Martin-Löf type theory: normalization and conversion

Rows: `M30-MLTT-DECL`, `M30-MLTT-LR`, `M30-MLTT-FUND`, `M30-MLTT-NORM` (done),
`M30-MLTT-CONV` (next), `M30-MLTT-CHECK`, `M30-UNIFY-PTS-MLTT` (open).

## 2026-10-28 — normalization (local work, single-file checks; full build by CI)

### The system (`Start/MLTTSyntax.lean`, `Start/MLTTTyping.lean`)

Curry-style de Bruijn terms `MLTT.Tm`: `var`, `univ l`, `pi F G`, `lam b`, `app`, `nat`, `zero`,
`succ`, `natrec P z s n`, `empty`, `emptyrec P e`.  Parallel substitution with the usual
algebra (`subst_subst`, `subst_inst`, `subst_inst2`, …).

One inductive `MLTT.Der : Jd → Prop` over five judgement forms (`wf Γ`, `tyWf Γ A`, `ty Γ t A`,
`tyEq Γ A B`, `eq Γ t u A`), 36 rules:

* a **Russell hierarchy** `U l : U (l+1)`, non-cumulative: `ℕ, ⊥ : U 0`,
  `Π F G : U (max i j)` from `F : U i` and `G : U j`; a term of type `U l` is a type (`el`);
* Π with `lam` (domain well-formed), `app`, `β` and the extensional **η** rule
  (`f, g : Π F G` and `f x ≡ g x : G` in `F :: Γ` give `f ≡ g`);
* ℕ with `zero`, `succ` and the dependent eliminator `natrec` (motive in `ℕ :: Γ`, step in
  `P :: ℕ :: Γ` at `stepTy P`), with both computation rules;
* ⊥ with `emptyrec`;
* conversion, congruence for every former, and equivalence rules at both levels.

`MLTT.Der.ren`: weakening along any well-formed renaming for all five forms.

### Reduction (`Start/MLTTReduction.lean`, `Start/MLTTGenEq.lean`)

Typed weak head reduction `TRed Γ t u A` (β, `natrec` on `zero`/`succ`, head positions of `app`,
`natrec`, `emptyrec`, closed under conversion), its closure `TReds`, and reduction of types
`TyReds`.  `TRed.det` (determinism), `TReds.whnf_unique`.

`MLTT.GenEq` is the **generic equality** interface of Abel, Öhman and Vezzosi (*Decidability of
conversion for type theory in type theory*, POPL 2018): three relations (types, terms, neutrals)
with the closure properties the logical relation needs.  `MLTT.declEq` is the declarative
instance.  The algorithmic instance is the content of `M30-MLTT-CONV`.

### The logical relation (`Start/MLTTLogRel*.lean`)

`MLTT.TyR E l Γ A I`: `A` is reducible at universe level `l`, with interpretation
`I : Interp` (`I.tyEq`, `I.tmEq`).  Induction–recursion is encoded by a graph: the
interpretation is an index of an inductive family `TyRAt`, whose universe case refers to
`TyR` at strictly smaller levels; `TyR` is then defined by well-founded recursion on `l`.
Cases: universe, ℕ (`NatR`: whnf `zero`, `succ`, or neutral), ⊥ (neutral only), neutral types,
Π (Kripke: for every weakening and every related argument pair).

* `TyR.lift`: cumulativity of the relation (no `emb` constructor needed);
* `TyR.good`: in one induction, `I.tmEq` is a PER, invariant under `I.tyEq`-related types
  (`conv`), and `I.tyEq` is symmetric and transitive;
* `TyR.irrel`: two reducibility proofs of the same type give the same relations;
* `TyR.wk`, `TyR.expand`/`reduce` (closure under weak head reduction), `TyR.neutral`
  (neutrals are reducible), `TyR.escapeTm`, `TyR.escapeTyEq`.

### The fundamental theorem (`Start/MLTTValid*.lean`, `Start/MLTTFund*.lean`)

`SubstR E Δ Γ σ σ'`: related substitutions, by recursion on `Γ`.  `ValidTy`, `ValidTm`,
`ValidTyEq`, `ValidEq`: closed under related substitutions.  One validity lemma per rule
(`valid_piT`, `valid_lam`, `valid_beta`, `valid_eta`, `valid_natrec`, …); the ℕ eliminator by
induction on `NatR` (`natrec_core`).

**`MLTT.Der.valid (E : GenEq) {J : Jd} (h : Der J) : J.Valid E`** — every derivable judgement is
valid, for every generic equality.

### Consequences (`Start/MLTTConsequences.lean`), at `E = declEq` and the identity substitution

* `MLTT.HasTy.whnf : HasTy Γ t A → ∃ t', TReds Γ t t' A ∧ Whnf t'` and
  `MLTT.WfTy.whnf : WfTy Γ A → ∃ A', TyReds Γ A A' ∧ Whnf A'` — **weak head normalization**;
* `MLTT.TyEq.pi_inj : TyEq Γ (pi F G) (pi H E') → TyEq Γ F H ∧ TyEq (F :: Γ) G E'`;
* `MLTT.TyEq.univ_inj : TyEq Γ (univ i) (univ j) → i = j`;
* `MLTT.Der.neHead`, `MLTT.Neutral.not_closed` — a typable neutral term has a declared head
  variable, so none is closed;
* `MLTT.canonicity : HasTy [] t nat → ∃ k, DEq [] t (numeral k) nat`;
* `MLTT.consistency : HasTy [] t empty → False`.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only
(`docs/goal/evidence/M30-MLTT-axioms.txt`).  No `sorry` (`scripts/check_sorry.py`).

Size: 15 modules, 4325 lines.

### Checks run

Each module was type-checked on its own (`lake env lean -o …` against the oleans of the modules
it imports, compiled the same way), in dependency order.  Warnings are checked by CI's
`lake build --wfail`.  `#print axioms` was
run on a scratch file importing `Start.MLTTConsequences`.  `python3 scripts/check_closure.py`
and `python3 scripts/goal_state.py validate` pass.  The full `lake build --wfail` is CI's.

## 2026-10-28 — algorithmic conversion: soundness and completeness (`M30-MLTT-INV`, `M30-MLTT-ALG`)

### Syntactic metatheory (`Start/MLTTInversion.lean`)

Derived from `MLTT.Der.valid` at `declEq`, as in Abel, Öhman and Vezzosi's `Typed.Consequences`:

* syntactic validity (`HasTy.wfTy`, `DEq.tyL`, `DEq.tyR`, `TyEq.wfL`, `TyEq.wfR`);
* substitution of one term, or of two equal terms, for `var 0` (`WfTy.inst`, `HasTy.inst`,
  `TyEq.inst`, `DEq.inst`, `WfTy.instEq`);
* context conversion of the last entry (`HasTy.ctxConv` and companions);
* inversion of typing for every term former (`HasTy.inv_univ` … `HasTy.inv_emptyrec`);
* `Neutral.tyUnique`: a neutral term has a unique type up to `TyEq`;
* the heads of `TyEq`-equal weak head normal types agree (`TyEq.univ_whnf`, `nat_whnf`,
  `empty_whnf`, `pi_whnf`, `ne_whnf`).

### The algorithm (`Start/MLTTAlg*.lean`)

Six judgements in one inductive family `MLTT.Alg : AJd → Prop`: neutral comparison inferring a
type (`NeUp`) and with the type reduced (`NeDown`); types (`TyUp`, `TyDown`); terms (`TmUp`,
`TmDown`).  Terms of a universe are compared **as types**, so the algorithm never computes a
universe level.  The variable rule takes a typing premise, as in the Agda development, so that
the relations are stable under context conversion.

* `Alg.sound` — soundness.  The universe case needs, inside the same induction, that two
  algorithmically equal types in `U i` and `U j` have `i = j` and are equal terms of `U i`
  (`UnivSound`); this follows from inversion and `Neutral.tyUnique`.
* `Alg.ren` (weakening), `Alg.stab` (equal contexts, `CtxEq`), `Alg.conv` (equal types).
* `Alg.symm` — into any equal context, with the inferred type of neutrals changing up to `TyEq`.
* `Alg.trans` — by induction on the first derivation and inversion of the second.
* `TyR.liftNe` — algorithmically equal neutrals are algorithmically equal terms at every
  reducible type, by η-expansion along the reducibility proof (declarative instance).
* `algEq : GenEq` — every field of the generic equality.
* **`TyEq.iff_alg : TyEq Γ A B ↔ TyUp Γ A B`** and **`DEq.iff_alg : DEq Γ t u A ↔ TmUp Γ t u A`**:
  completeness is `MLTT.Der.valid algEq` at the identity substitution.

Axioms: `propext`, `Classical.choice`, `Quot.sound` (`docs/goal/evidence/M30-MLTT-axioms.txt`).
Six modules, 1738 lines; each type-checked on its own, in dependency order.

## 2026-10-28 — decidability of conversion (`M30-MLTT-CONV` done)

`Start/MLTTDecideRun.lean`, `Start/MLTTDecideCorrect.lean`, `Start/MLTTDecide.lean` (1374 lines).

The program `MLTT.cRun n` (fuel `n`) has three components:

* `neDn` — compare two neutral terms; it answers the weak head normal form of the inferred
  type (the declared type of the head variable `ctxGet`, through the eliminators), or `none`
  when they differ;
* `tyUp` — reduce both types by untyped weak head normalization with fuel (`whnfF`), then compare
  heads, recursing at products only after the domains compared equal;
* `tmUp` — reduce the type and both terms, then compare by the head of the type:
  - at universes, compare as types;
  - at products, by η-expansion;
  - at `ℕ`, compare `zero`, `succ` or neutrals;
  - at `⊥` and at neutral types, compare as neutrals.

Comparisons inside `natrec` run in sequence, each only after the previous one succeeded:
motive, then base case, then step, then the scrutinee.  So every recursive call is on
well-typed inputs.

* `whnfF_typed`, `whnfF_tyTyped` — on typed inputs, untyped normalization follows the typed
  reduction.  The two stuck endpoints of the deterministic untyped reduction coincide
  (`whSteps_stuck_unique`).
* `cRun_correct` — every answer is correct on typed inputs, by induction on the fuel.
  - Boolean answers `b` satisfy `b = true ↔ TyUp …`, respectively `TmUp …`.
  - A neutral answer is a type at which `NeDown` holds, and `none` means no `NeDown`.
* `Alg.terminates` — the run answers for all large fuels on a left-hand side with an
  algorithmic derivation and a right-hand side with one.
  - It holds in any equal context and at any equal type.
  - Neutral answers are eventually constant.
  - By induction on the left derivation and inversion of the right one.
* **`TyEq.decide_spec`, `DEq.decide_spec`** — combine termination, correctness and
  `TyEq.iff_alg`/`DEq.iff_alg`.  Typed terms have algorithmic derivations by completeness
  (`DEq.alg (Der.refl _)`).
* **`TyEq.decidable`, `DEq.decidable`** — decide with `decideTyEq`, `decideDEq`: the run at
  the least fuel at which it answers (`Nat.find`).  These are executable `def`s; classical logic
  occurs only in proofs.

Axioms: `propext`, `Classical.choice`, `Quot.sound` (`docs/goal/evidence/M30-MLTT-axioms.txt`).
Each module was type-checked on its own; the full build is CI's.

## `M30-UNIFY-PTS-MLTT` (filed in M30, not M26)

The Π-and-universe fragment of MLTT is the PTS with sorts `ℕ`, axioms `(l, l+1)` and rules
`(i, j, max i j)` (`Start/PTSExpansionLocal.lean`'s `natHier`, rules `(m, n, n)` for `n ≤ m`,
is a different hierarchy).  With the absorbed `PureTypeSystem.weak_implies_strong`
(`Start/PTSNormalization.lean`), weak normalization of this PTS gives strong normalization.
The row is filed in milestone M30 because it depends on `M30-MLTT-CONV`, and the board does not
let an M26 row depend on an M30 one.  Its missing pieces are listed in its `open_boundary`.
