# M10-PCA-KLEENE

**Status:** DONE_STRONG

Modules `Start/PCA.lean`, `Start/PCATotal.lean` and `Start/PCAKleene.lean`, all imported by
`Start.lean`.  They build without `sorry`; `#print axioms` on the headline declarations reports
only `propext`, `Classical.choice`, `Quot.sound`.

## Partial combinatory algebras — `Start/PCA.lean`

`Realizability.PCA A` has a partial application `app : A → A → Part A`, elements `k` and `s`, and
the usual axioms in Kleene-inequality form: `k a` is defined and `k a b = a`; `s a b` is defined and
`s a b c` is *at least* `(a c) (b c)`, i.e. defined with the same value whenever the right-hand side
is.  `papp`, written `x ⬝ y`, extends application to partial elements, with `papp_some_left`,
`papp_some_right`, `some_le_of_mem`, `mem_papp`, `papp_mono` as its calculus, and `k_papp`,
`s_papp_dom`, `s_papp` as the axioms restated.

Combinatory completeness is proved syntactically.  `Expr A` is the term algebra over variables and
constants from `A`, with `Expr.eval e ρ : Part A`; `Expr.abst n` is bracket abstraction, and

* `Expr.abst_dom` — an abstraction always denotes;
* `Expr.abst_app` — and applying it to `a` recovers `e` evaluated in `ρ` updated at `n`;
* `PCA.lam`, **`PCA.lam_app`** — packaged as an element of `A` with its β-rule, plus `lam_lam_app`
  for iterated abstraction and the convenience layer `lam1`/`lam1_app`, `lam2`/`lam2_app`/
  `lam2_app_app`/`lam2_app_dom` over the environment `env0`.

From combinatory completeness alone: `PCA.i` with `i_app`, `kI`, `comp`/`comp_app`, and the pairing
apparatus `pairEl`, `pairComb`/`pairComb_app`, `pairEl_app`, `fstComb`, `sndComb`, with
`fstComb_pairEl` and `sndComb_pairEl`.

## Total algebras and λ-models — `Start/PCATotal.lean`

`Realizability.TCA` is a total combinatory algebra; `TCA.toPCA` makes it a partial one with
everywhere-defined application, and `TCA.app_eq` identifies the two applications.
`Realizability.Lambda.lambdaModelTCA` and **`lambdaModelPCA`** exhibit every λ-model of the existing
development (via its `K` and `S` and the laws `app_app_K`, `app_app_app_S`) as a total, hence
partial, combinatory algebra.

## Kleene's first algebra — `Start/PCAKleene.lean`

`Realizability.Kleene.natApp a b = eval (ofNat Code a) b` is application by code, and
`partrec_natApp` records that it is partial recursive; `exists_code_of_computable` produces codes.
Explicit combinators are then built: `kFun`, `kCode`, `kEl` with `natApp_kEl` and `natApp_kFun`, and
`sBody`, `sCode`, `sTwo`, `sPairCode`, `sOne`, `sOneCode`, `sEl` with `natApp_sEl`, `natApp_sOne`
and `natApp_sTwo`.  These give **`Realizability.Kleene.instPCANat : PCA ℕ`** (a scoped,
noncomputable instance), with `k1_app` identifying its application with `natApp`.

## Boundary

None for this task.  The algebras built here are used downstream for assemblies and PERs.
