# M23-LF-EQUIV — type-directed βη-equivalence for LF (λΠ)

Round 7.  Status **DONE_WEAK**, gap row `M23-LF-EQUIV-COMPLETE`.

Reference: R. Harper and F. Pfenning, *On equivalence and canonical forms in the LF type theory*,
ACM TOCL 6(1), 2005.  The algorithm is the one Agda's conversion checker follows: it is directed by
the (simple) type, η-expands at function types instead of η-contracting, and compares weak head
normal forms structurally at the base type.

Module: `Start/LambdaPiLFEquiv.lean` (imports `Start/LambdaPiEtaConfluent.lean` and
`Start/LambdaPiSimple.lean`).  The calculus is the repository's λΠ (`LambdaPi.Tm`, de Bruijn,
typing `LambdaPi.Typing`), with the simple skeletons `LambdaPi.STy` and `LambdaPi.skel` of
`Start/LambdaPiSkeleton.lean`, as in Harper and Pfenning's erasure to simple types.

## What is proved

| Lean name | Content |
| --- | --- |
| `LambdaPi.WhStep`, `LambdaPi.WhRed` | weak head reduction (head β-step, under the head of an application) |
| `LambdaPi.Eqv`, `AlgEq`, `PathEq` | the algorithm: `Δ ⊢ M ⇔ N : τ` (type-directed) and `Δ ⊢ p ↔ q : τ` (structural, skeleton synthesised) |
| `LambdaPi.Eqv.sound` | **soundness of the algorithm for βη-conversion**: `Eqv k Δ M N τ → BetaEtaConv M N` |
| `LambdaPi.Eqv.rename` | the algorithm is stable under renamings respecting the skeletons (weakening) |
| `LambdaPi.LR` | the **Kripke logical relation** on skeleton types (base: algorithmic equivalence; arrow: related arguments in every extension give related applications) |
| `LambdaPi.LR.escape`, `LambdaPi.LR.reflect` | **escape** (related ⇒ algorithmically equivalent) and **reflection** (structurally equivalent paths are related), by simultaneous induction on the skeleton |
| `LambdaPi.LR.var` | variables are related to themselves |
| `LambdaPi.LR.rename` | monotonicity of the relation under skeleton-respecting renamings |
| `LambdaPi.LR.whExpand_left`, `whExpand_right` | closure of the relation under weak head expansion |
| `LambdaPi.TEq` | the **declarative typed equality judgement** `Γ ⊢ M ≡ N : A` of λΠ, with typed β, typed η, congruences and conversion of the type |
| `LambdaPi.TEq.betaEtaConv` | declaratively equal terms are βη-convertible |

The algorithm's rules:

* arrow skeleton `σ ⇒ τ`: `Δ ⊢ M ⇔ N : σ ⇒ τ` if `σ :: Δ ⊢ M↑ 0 ⇔ N↑ 0 : τ` (extensionality,
  the η-expanding step);
* base skeleton: weak head normalize both sides; then two equal sorts, or two products
  (domains at the base, codomains in the context extended by the domain's skeleton), or two
  paths related structurally;
* paths: a variable with the skeleton of its declaration, or a path at `σ ⇒ τ` applied to
  algorithmically equivalent arguments at `σ`.

Axioms: `docs/goal/evidence/M23-LF-EQUIV-axioms.txt` (at most `propext, Classical.choice,
Quot.sound`).

## The raw βη corollary does not follow in a few lines

The request asked whether decidability of raw βη-conversion of typable terms follows from
`LambdaPi.betaEtaConv_iff_join` (confluence modulo annotations) and `LambdaPi.Typing.betaEta_sn`.
It does not in a few lines: the natural route (normalize, erase annotations, compare) needs that
annotation erasure maps βη-normal forms to βη-normal forms, which is false.  In de Bruijn notation, the term
`λ(A). (var 1) (λ(var 0). var 0) (var 0)` is βη-normal: it is not an η-redex because the bound
variable occurs in the annotation `var 0` of the inner abstraction.  Its erasure
`λ. (var 1) (λ. var 0) (var 0)` is an η-redex.  So a comparison of erased normal forms needs a separate normalization
of the erased term and a proof that it agrees with βη modulo annotations; this is not done and is
not claimed.

## Open (gap row M23-LF-EQUIV-COMPLETE)

Write `Γs := skelCtx Γ` and `⌊A⌋ := skel (skelCtx Γ) A` (`Start/LambdaPiSimple.lean`,
`Start/LambdaPiSkeleton.lean`).

1. **Typed soundness**: `AlgEq Γs M N ⌊A⌋ → Typing Γ M A → Typing Γ N A → TEq Γ M N A` (needs
   subject reduction for weak head reduction and typed η-expansion at arrow skeletons).
2. **Completeness**: the fundamental lemma of the logical relation, `TEq Γ M N A → LR ⌊A⌋ Γs M N`
   (generalised to related substitutions), then `LR.escape`.  The pieces it uses that are
   available: closure under weak head expansion (`LR.whExpand_left/right`), monotonicity
   (`LR.rename`), reflection of variables (`LR.var`), and the invariance of skeletons under
   substitution of objects (`skel_inst`, `skel_subst`) and conversion (`skel_conv`).  The piece
   that is missing first is that `LR τ Δ` is a **partial equivalence relation** (symmetry and
   transitivity), which needs symmetry and transitivity of `Eqv`, hence determinacy of weak head
   normal forms (`WhRed M M₁ → WhRed M M₂ → whnf M₁ → whnf M₂ → M₁ = M₂`).
3. **Termination** on well-typed terms (from completeness and reflexivity, as in Harper and
   Pfenning), hence decidability of `TEq` on well-typed terms.

First missing lemma: `theorem LambdaPi.Eqv.symm` / `Eqv.trans` (the PER property of the
algorithm), then `theorem LambdaPi.LR.fundamental : TEq Γ M N A → LR ⌊A⌋ Γs M N` (with its
substitution generalisation).

## Round 8 — the algorithm is a PER (`Start/LambdaPiLFEquivPER.lean`)

* `WhStep.det` (weak head reduction is deterministic), `IsPath.whnf`, `WhRed.whnf_unique`
  (weak head normal forms are unique), `Eqv.path_isPath`;
* `Eqv.symm`, `Eqv.trans`, `Eqv.path_ty_unique` — **symmetry and transitivity** of algorithmic
  and structural equivalence; `AlgEq.per`;
* `LR.symm`, `LR.trans` — the Kripke logical relation is a PER.

Change to the round-7 algorithm: the product rule `Eqv.basePi` now carries the decidable side
condition `skel Δ A = skel Δ A'`.  Without it the codomains are compared in the context
`skel Δ A :: Δ`, which remembers only the left domain, and symmetry fails at that rule (the
skeleton of a λΠ type is not invariant under untyped β: `skel` of `(λx:C. b) a` uses `skel C`
for `x`, `skel` of `b[a]` uses `skel a`).  For well-typed convertible domains the condition holds
by `skel_conv`, so completeness is unaffected.  `Eqv.sound`, `Eqv.rename`, `LR.escape`,
`LR.reflect`, `LR.rename` and the weak head expansion lemmas are re-proved unchanged in
statement.

Open, in order: `LR.fundamental` generalised to related substitutions — the first missing
lemma, not started this round: `TEq Γ M N A → ∀ σ σ' related at Γ in Δ,
LR (skel (skelCtx Γ) A) Δ (M[σ]) (N[σ'])` — then completeness `TEq Γ M N A → AlgEq`, typed
soundness, termination on well-typed terms, decidability.

## Round 9 — the fundamental lemma for the typing judgement (`Start/LambdaPiLFFundamental.lean`)

New DONE_STRONG row M23-LF-FUNDAMENTAL-TYPING; M23-LF-EQUIV-COMPLETE stays TODO_READY and
M23-LF-EQUIV stays DONE_WEAK.  Axioms in `M23-LF-FUNDAMENTAL-TYPING-axioms.txt`.

Proved:

* `skel_subst_typeLevel` — for a type-level `A` in a well-formed `Γ`, `skel Δ (A[σ]) = skel Γs A`
  as soon as `σ` has the right skeleton at the **kind positions** of `Γ` (object positions are
  irrelevant, as in `skel_irrel`);
* `RelSub Γ Δ σ τ` — related substitutions: `LR (skel A) Δ (σ n) (τ n)` at every declaration
  `n : A`, and the declared skeleton at kind positions; `RelSub.rename`, `RelSub.cons` (extension
  at an object position), `RelSub.up`, `RelSub.ids`;
* **`LR.fundamental`**: `Typing Γ t A → Wf Γ → RelSub Γ Δ σ τ → LR (skel (skelCtx Γ) A) Δ t[σ] t[τ]`,
  all six rules (the product case uses `skel_subst_typeLevel` for the side condition of
  `Eqv.basePi`, the application and conversion cases the skeleton arguments of `Typing.styping`);
* `AlgEq.refl_of_typing` — the algorithm is reflexive on well-typed terms.

**First missing lemma** (completeness for `TEq`): the fundamental lemma for `TEq` needs, at
`TEq.pi`, the side condition `skel Δ (A[σ]) = skel Δ (A'[τ])` for declaratively equal domains,
i.e. `skel_teq : TEq Γ A A' (sort s) → skel (skelCtx Γ) A = skel (skelCtx Γ) A'` together with
`TypeLevel` of both sides.  The skeleton facts are proved for *typed* terms (`skel_conv`,
`skel_irrel` need `TypeLevel`), and `TEq` is not valid for the β-only typing judgement:
`TEq.app` relates `f a` and `f' a'` at `B[a]`, while `f' a'` is typed at `B[a']`, which is only
βη-convertible to `B[a]` when `a` and `a'` differ by η (observation on paper, not formalized).
So the missing lemma is the skeleton invariance under `TEq` at type level, proved by induction on
`TEq` with typing premises for the β-case only, or a validity lemma for `TEq` against a
βη-conversion typing judgement.  Then completeness, typed soundness, termination, decidability
(none proved).

## Round 10 — the skeleton under raw β and η (`Start/LambdaPiLFSkelTEq.lean`)

M23-LF-EQUIV-COMPLETE stays TODO_READY, M23-LF-EQUIV stays DONE_WEAK.  Axioms in
`M23-LF-EQUIV-COMPLETE-axioms.txt`.

The question first: is `skel` invariant under single raw β- and η-steps?

* **η: yes.** `skel_eta : skel Γs (λA. (↑f) 0) = skel Γs f` for every raw `f` (`skel_rename_succ`).
* **β: no.** `skel_beta_raw_counterexample`: the step `(λx:∗. x) (Πy:∗. ∗) ⟶ Πy:∗. ∗` changes the
  skeleton from `base` to `base → base`: the bound variable occurs in a skeleton-relevant (head)
  position of the body and the argument there has an arrow skeleton.  Hence
  `skel_not_betaEta_invariant`: the skeleton is not invariant under raw βη-conversion, and
  `skel_teq` cannot be derived from `TEq.betaEtaConv`.

In a well-typed type-level redex the bound variable is an object variable (λ-domains have sort
`∗`) and never occurs in a skeleton-relevant position; `skel_step` uses exactly this through
`TypeLevel`.  So `skel_teq` needs the typing of every type-level redex in a `TEq` derivation.  The
leaves of `TEq` are typed (`refl`, `beta`, `eta` carry typing premises), but `symm`, `trans` and
the congruences do not propagate typing, so an induction on `TEq` needs validity.

**First missing lemma**: `TEq.typeLevel : TEq Γ M N T → Wf Γ → (T a kind or □) → TypeLevel Γ M ∧
TypeLevel Γ N`.  It is false for the β-conversion typing `Typing` (at `TEq.app`, `f' a'` is typed at
`B[a']`, βη- but not β-convertible to `B[a]`), so it needs a βη-conversion typing judgement with
weakening, substitution, context conversion, type validity and Church–Rosser for βη.  With it,
`skel_teq` follows by induction on `TEq` (`skel_step` at β, `skel_eta` at η), then
`LR.fundamental` for `TEq`, typed soundness, termination and decidability (none proved).

## Series V, round 3, run 1

C1 (M23-LF-EQUIV-COMPLETE): assessed, not attempted in Lean.  `TEq.typeLevel` needs a typing
judgement closed under βη-conversion (with weakening, substitution, context conversion, type
validity and βη Church–Rosser for λΠ), which the library does not have; C's share went to C2
(M23-GROUPOID-SIGMA, `GrpdModel.pairHom_comp` proved).  First missing lemma unchanged:
`TEq.typeLevel`.

## Big round 2, run 1 (M23-LF-EQUIV-COMPLETE, item W2)

**The first missing lemma `TEq.typeLevel` is false** (`Start/LambdaPiLFTEqTypeLevelCounter.lean`).
`TEq` has the η-rule but its typing premises and `Typing` convert types by β only.  In the
well-formed context `A0 : ∗, g : A0 → A0, Q : (A0 → A0) → ∗, c : Π h : A0 → A0. Q h,
F : Q (λy:A0. g y) → ∗` (`LambdaPi.tc_wf`), `TEq.app (TEq.refl F) (TEq.app (TEq.refl c) (TEq.eta g))`
derives `F (c (λy. g y)) ≡ F (c g) : ∗` (`LambdaPi.tc_teq`), `∗` is a kind, and `F (c g)` has no type
(`LambdaPi.tc_N_untyped`: `c g : Q g`, `F` expects `Q (λy. g y)`, two distinct β-normal forms).
Packaged: `LambdaPi.teq_typeLevel_counterexample : ∃ Γ M N T, Wf Γ ∧ TEq Γ M N T ∧ IsKind Γ T ∧
¬ TypeLevel Γ N`.

Consequence for the route: validity of `TEq` cannot hold for β-typing; the skeleton argument needs
a typing judgement with βη-conversion.  New first missing lemma (a Lean statement, the judgement
to be defined): `LambdaPi.TypingE` — `Typing` with `BetaEtaConv` in the conversion rule — and

    theorem LambdaPi.TEq.validityE {Γ : Ctx} {M N A : Tm} (h : TEq Γ M N A) (hΓ : Wf Γ) :
      TypingE Γ M A ∧ TypingE Γ N A

after which `TEq.typeLevel` is to be restated with `TypingE`.  The exit criteria of the row
(completeness by a Kripke logical relation, termination, decidability) are not affected by the
refutation itself.

## Big round 2, run 6 (restoration after the move to a new project)

The big round 2 sections of this note (runs 1 to 3) were lost with the old project and were recreated
in run 6 from its command logs, which record the text that was appended; the Lean modules they cite
were restored from the old project's export, rebuilt with `lake build --wfail`, and their axioms
regenerated (`docs/goal/evidence/*-axioms.txt`, section "Big round 2, run 6").

## Big round 2, run 7 (restoration after the export of run 6)

The platform's export of run 6's project dropped this note; it was put back from the copy of before big round 2 (our tree at ce8fe5e), and the
big round 2 sections that run 6 had restored were added again in run 7 from the command logs of
runs 1 to 3 (the appended text is recorded there verbatim). The axioms files of the big round 2 rows
were regenerated with `#print axioms` in run 7 (section "Big round 2, run 7").
