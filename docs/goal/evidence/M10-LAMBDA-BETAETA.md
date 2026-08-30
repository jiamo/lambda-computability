# M10-LAMBDA-BETAETA

**Status:** DONE_STRONG

Modules `Start/LambdaEta.lean` and `Start/LambdaBetaEta.lean`, imported by `Start.lean` and
registered in `Start/Capstones.lean`.  Both build without `sorry` and without linter warnings.

## What the task asked

`Start/Reduction.lean` proves the Church–Rosser theorem for β on the untyped terms of
`Start/Syntax.lean` (`Lambda.confluence_theorem`), and `Start/LambdaPiEta.lean` settles η for the
Church-style calculus `λΠ`, where βη on *raw* terms turns out **not** to be confluent because the
two rules disagree about the domain annotation of an abstraction.  The obvious question left open
by that pair of results is what happens for the untyped calculus, whose abstractions carry no
annotation.  The answer is the classical one — βη is confluent — and these two modules prove it
from scratch: confluence of β and of η separately is not enough, since the union of two confluent
relations need not be confluent.

## η on untyped terms (`Start/LambdaEta.lean`)

`Lambda.etaStep` is one step of η-contraction,

```
λx. (f x)  ⟶  f      (x not free in f),
```

in de Bruijn form the rule `etaStep (lam (app (lift 1 0 t) (var 0))) t`, closed under the three
congruence rules; `Lambda.etaReduces` is its reflexive–transitive closure.

* `Lambda.lift_one_injective`, `Lambda.lift_factor` — lifting by one is injective, and a term
  lifted at a level above `j` which is also a lifting at level `j` factors as a lifting at level
  `j` of a term, the two liftings exchanging.  This is what lets an η-step under a lifting be
  reflected back through it: `Lambda.etaStep_lift`, `Lambda.etaStep_lift_inv`.
* `Lambda.nodes`, `Lambda.nodes_lift`, `Lambda.etaStep.nodes_lt` — the number of syntax nodes is
  invariant under lifting and strictly decreases along an η-step, so `Lambda.exists_etaNf`:
  **η-reduction terminates**, every term has an η-normal form.
* `Lambda.etaStep.strong_confluence` — two η-steps out of the same term are joined by *at most
  one* η-step on each side; the only interesting overlap is a top-level η-redex against a step
  inside its function part, settled by `etaStep_lift_inv`.  Strong confluence tiles
  (`Lambda.etaStep.strip`), giving `Lambda.etaReduces_church_rosser`: **η-reduction is
  confluent**.

## β and η commute (`Start/LambdaBetaEta.lean`)

The critical pairs between the two rules need two syntactic lemmas:

* `Lambda.subst_var_lift_succ` — `subst (var j) j (lift 1 (j+1) t) = t`, which is what makes the
  overlap `λx. ((λy. b) x)` degenerate: the β-reduct and the η-reduct of that term are *equal*;
* `Lambda.step_lift_inv` (with `Lambda.step_app_inv`, `Lambda.lift_eq_lam`) — a β-step out of a
  lifted term is a lifted β-step.

η is substitutive: `Lambda.etaStep_subst` (η in the term substituted into) and
`Lambda.etaReduces_subst_arg` (η in the term being substituted, propagated to every occurrence).

`Lambda.step_etaStep_commute` is the local diagram: from `t →β u` and `t →η v` there is a `w`
with `u →η* w` and `v →β w` *or* `v = w` — the β-side is always at most one step, which is what
makes the diagram tile.  `Lambda.step_etaReduces_commute` tiles it along an η-sequence and
`Lambda.reduces_etaReduces_commute` along a β-sequence: **β-reduction and η-reduction commute**.

## βη is Church–Rosser

`Lambda.betaEtaStep` is the union of `Lambda.step` and `Lambda.etaStep`, `Lambda.betaEtaReduces`
its reflexive–transitive closure and `Lambda.betaEtaConv` the generated equivalence.  The
Hindley–Rosen argument is run explicitly on the composite relation
`Lambda.betaEtaT t u := ∃ m, reduces t m ∧ etaReduces m u`:

* `Lambda.betaEtaT.diamond` — the composite has the diamond property, by confluence of β
  (`Lambda.confluence_theorem`), commutation, and confluence of η;
* `Lambda.betaEtaTStar.strip`, `Lambda.betaEtaTStar.confluent` — hence its reflexive–transitive
  closure is confluent;
* `Lambda.betaEtaReduces.toTStar`, `Lambda.betaEtaTStar.toBetaEtaReduces` — that closure is
  exactly βη-reduction, so `Lambda.betaEta_church_rosser`: **βη-reduction is confluent**, and
  `Lambda.betaEtaConv.common_reduct`: βη-convertible terms have a common βη-reduct.

The contrast with `Start/LambdaPiEta.lean` is exactly the commutation step: for the annotated
terms of `λΠ` the diagram `t →β u`, `t →η v` cannot be closed, and `M10-LAMBDAPI-ETA` exhibits a
term with two distinct βη-normal reducts.

## Gates

* `lake build` — the whole library, no error and no warning.
* `python3 scripts/check_closure.py` — every module in the import closure of `Start.lean` and
  registered.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: `Lambda.betaEta_church_rosser`, `Lambda.reduces_etaReduces_commute` and
  `Lambda.betaEtaConv.common_reduct` depend only on `propext`, `Classical.choice` and
  `Quot.sound`.
