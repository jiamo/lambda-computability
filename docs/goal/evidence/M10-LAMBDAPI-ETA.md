# M10-LAMBDAPI-ETA

**Status:** DONE_STRONG

Module `Start/LambdaPiEta.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

The scope note of `docs/goal/goal-prompt.md` lists "eta for `λΠ`" among the open items of the
typed-calculi track, and the open boundary of `M9-LAMBDAPI-LCCC` records that the syntactic
category with attributes of `λΠ` has a *weak* Π-structure only: `LambdaPiCwa.not_piStruct_weakPi`
shows that η fails there.  The natural question is whether that failure can be repaired by adding
η to the reduction relation of the raw calculus.  It cannot, and this module proves it, together
with the positive facts about η on its own.

## The rewriting system

`LambdaPi.EtaStep` is one step of η-contraction,

```
λ(x : A). (f x)  ⟶  f      (x not free in f)
```

which in de Bruijn form is the rule `EtaStep (lam A (app (shift t) (var 0))) t`, closed under the
six congruence rules of the syntax.  `LambdaPi.EtaRed` is its reflexive–transitive closure,
`LambdaPi.BetaEtaStep` the union of `LambdaPi.Step` and `EtaStep`, and `LambdaPi.BetaEtaRed`,
`LambdaPi.BetaEtaConv` the induced reduction and conversion.

## Renamings

The de Bruijn side condition "`x` is not free in `f`" is expressed as "`f` is a shift", so the
metatheory needs to *reflect* an η-step through a renaming.  That is `LambdaPi.EtaStep.rename_inv`
(and its special case `LambdaPi.EtaStep.shift_inv`), and it rests on a general factorisation
lemma:

* `LambdaPi.RenSquare ρ θ ρ' θ'` — a commuting square of renamings, `ρ ∘ θ' = θ ∘ ρ'`, whose
  index sets form a pullback: every coincidence `ρ n = θ m` comes from one `k`;
* `LambdaPi.RenSquare.upr` — such squares are stable under going under a binder;
* `LambdaPi.rename_factor` — if `rename ρ t = rename θ s` for such a square, then `t` and `s`
  factor through it: `t = rename θ' t₀` and `rename ρ' t₀ = s`.

`LambdaPi.renSquare_upr_succ` is the square `(upr ρ, succ, ρ, succ)` used for η, and
`LambdaPi.rename_injective` records that renaming along an injective renaming is injective on
terms.

## η alone is well behaved

* `LambdaPi.EtaStep.size_lt` — an η-step strictly decreases `LambdaPi.size`;
* `LambdaPi.exists_etaNf` — hence η-reduction terminates: every term has an η-normal form;
* `LambdaPi.EtaStep.strong_confluence` — two η-steps out of the same term are joined by *at most
  one* η-step on each side.  The only interesting overlap is a top-level η-redex against a step
  inside its function part, and that is where `EtaStep.shift_inv` is used;
* `LambdaPi.EtaStep.strip`, `LambdaPi.EtaRed.church_rosser` — strong confluence tiles, so
  η-reduction is confluent on all raw terms.

## βη on raw terms is not confluent

* `LambdaPi.betaEtaConv_lam_annot` — for *any* `A`, `A'` and `b`, the abstractions `λ(x : A). b`
  and `λ(x : A'). b` are βη-convertible.  The witness is `λ(x : A). ((λ(y : A'). b) x)`, which
  β-reduces to `λ(x : A). b` and η-contracts to `λ(y : A'). b`.  So βη-conversion of raw terms
  forgets the domain annotations altogether.
* `LambdaPi.not_church_rosser_betaEta` — **βη-reduction is not confluent.**  Nederpelt's term
  `λ(x : ∗). ((λ(y : □). y) x)` β-reduces to `λ(x : ∗). x` and η-contracts to `λ(y : □). y`;
  `LambdaPi.betaEtaNf_lam_sort_var` shows both are βη-normal, and they are distinct, so they have
  no common reduct.

Both of `β` (`LambdaPi.church_rosser`) and `η` (`LambdaPi.EtaRed.church_rosser`) are confluent, so
what fails is the commutation of the two relations: a β-step may replace the bound variable of an
abstraction by an argument and keep the *outer* annotation, where the η-step keeps the *inner*
one.  This is a property of Church-style syntax, not of the type theory: in a well-typed term the
two annotations are convertible, which is why η can be added to `λΠ` only at the level of typed
conversion.

## Gates

* `lake build` — the whole library, no error and no warning.
* `python3 scripts/check_closure.py` — 267 modules, all in the import closure of `Start.lean`
  and all registered.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: `LambdaPi.not_church_rosser_betaEta` and `LambdaPi.betaEtaConv_lam_annot` depend
  only on `propext`; `LambdaPi.EtaRed.church_rosser` and `LambdaPi.exists_etaNf` depend only on
  `propext`, `Classical.choice` and `Quot.sound`.
