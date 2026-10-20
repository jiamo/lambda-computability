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
