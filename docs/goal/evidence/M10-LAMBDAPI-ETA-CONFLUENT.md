# M10-LAMBDAPI-ETA-CONFLUENT

**Status:** DONE_STRONG

Module `Start/LambdaPiEtaConfluent.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings, and its results
depend only on `propext`, `Classical.choice` and `Quot.sound`.

## What this task adds

`Start/LambdaPiEta.lean` proves that βη-reduction of raw `λΠ` terms is not confluent
(Nederpelt's term).  This module isolates the obstruction: it is *only* the domain annotation of
an abstraction.

- `LambdaPi.eraseAnn`, `LambdaPi.Erased` — erasure of every domain annotation to the fixed dummy
  sort `∗`, and the predicate of being one's own erasure, with `eraseAnn_rename`,
  `eraseAnn_shift`, `eraseAnn_subst`, `eraseAnn_inst`, `eraseAnn_idem` and the inversion lemmas
  for `Erased` at each constructor.
- `LambdaPi.Erased.step`, `.etaStep`, `.red`, `.etaRed` — erasedness is preserved by β and by η.
- **`LambdaPi.erased_step_eta_comm`** — β and η *strongly commute* on erased terms: from a β-step
  and an η-step out of the same erased term, the β-reduct reaches a common term by η-steps and
  the η-reduct by at most one β-step.  The critical case is a β-redex sitting directly under an
  η-redex, `λ(x : A). ((λ(y : A'). b) x)`, which closes up exactly because erasure makes `A` and
  `A'` the same; this is the case Nederpelt's term refutes for arbitrary annotations.
- **`LambdaPi.erased_step_etaRed_comm`**, **`LambdaPi.erased_comm`** — Hindley's argument raises
  strong commutation to commutation of `β*` and `η*` on erased terms.
- **`LambdaPi.erased_betaEta_church_rosser`** — βη-reduction is confluent on erased terms:
  β-confluence, η-confluence, the commutation above and η-postponement
  (`Start/LambdaPiEtaPostpone.lean`) combine in the Hindley–Rosen pattern.
- `LambdaPi.Step.eraseAnn`, `EtaStep.eraseAnn`, `BetaEtaStep.eraseAnn`, `BetaEtaRed.eraseAnn` —
  reductions transport along the erasure; `LambdaPi.BetaEtaConv.appL/appR/lamR/piL/piR` are the
  congruence rules of βη-conversion.
- **`LambdaPi.betaEtaConv_eraseAnn`** — every term is βη-convertible to its erasure.
- **`LambdaPi.betaEtaConv_iff_join`** — two raw terms are βη-convertible exactly when their
  erasures have a common βη-reduct: the Church–Rosser property for `λΠ` modulo annotations.

The consequences the conversion rule of the calculus needs, now for the η-extended conversion:

- `LambdaPi.betaEtaRed_sort_inv`, `LambdaPi.betaEtaRed_pi_inv` — sorts are βη-normal, and a
  product reduces only to a product, componentwise.
- **`LambdaPi.betaEtaConv_sort_inj`** — distinct sorts are not βη-convertible.
- **`LambdaPi.not_betaEtaConv_sort_pi`** — a sort is never βη-convertible to a product.
- **`LambdaPi.betaEtaConv_pi_inv`** — products are injective in both arguments for
  βη-conversion.

## Gates

- `lake build Start.LambdaPiEtaConfluent` — success, no warnings.
- `python3 scripts/check_closure.py` — all modules in the import closure and all registered.
- `python3 scripts/goal_state.py validate` — board validates.
