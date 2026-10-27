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

## Next: `M30-MLTT-CONV` (algorithmic conversion, decidability)

Plan, following Abel, Öhman and Vezzosi:

1. Algorithmic relations: types compared after reduction to whnf, structurally; terms
   type-directed (η-expand at Π, compare whnfs at ℕ and at `U`, neutrals elsewhere); neutrals
   by spine comparison, inferring the type.
2. Soundness: algorithmic ⇒ declarative (`DEq`, `TyEq`).
3. An algorithmic `GenEq` instance: the relations paired with well-typedness.  The fields that
   need the declarative consequences above are symmetry and transitivity, which need
   Π-injectivity, `univ_inj` and **inversion of typing for neutrals, with uniqueness of the
   type of a neutral up to `TyEq`** (first missing lemma, not yet stated in Lean), and closure
   under typed reduction (`TReds.whnf_unique`, `TRed.det`).
4. Completeness: the fundamental theorem at `E = algEq` gives `DEq Γ t u A → algorithmic`.
5. Decidability: by induction on the two reflexivity derivations of `t` and `u`, as in the
   Agda formalization, or by fuel as in `Start/LambdaPiLFDecide.lean`.

## `M30-UNIFY-PTS-MLTT` (filed in M30, not M26)

The Π-and-universe fragment of MLTT is the PTS with sorts `ℕ`, axioms `(l, l+1)` and rules
`(i, j, max i j)` (`Start/PTSExpansionLocal.lean`'s `natHier`, rules `(m, n, n)` for `n ≤ m`,
is a different hierarchy).  With the absorbed `PureTypeSystem.weak_implies_strong`
(`Start/PTSNormalization.lean`), weak normalization of this PTS gives strong normalization.
The row is filed in milestone M30 because it depends on `M30-MLTT-CONV`, and the board does not
let an M26 row depend on an M30 one.  Its missing pieces are listed in its `open_boundary`.
