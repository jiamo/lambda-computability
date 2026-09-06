# M11-KLEENE-TWO-PCA

**Status:** DONE_STRONG

`Start/PCAKleene.lean` built Kleene's *first* algebra `K₁`, the natural numbers under Turing
application.  This task builds the other pole of Longley's picture, Kleene's *second* algebra
`K₂`: Baire space `ℕ → ℕ` under the application of function realizability.  Two modules,
`Start/KleeneTwoBasic.lean` and `Start/KleeneTwo.lean`, both imported from `Start.lean`,
registered in `Start/Capstones.lean`, free of `sorry` and of linter warnings; every headline
result depends only on `propext`, `Classical.choice`, `Quot.sound`.

## The application (first exit criterion)

* `Realizability.KleeneTwo.enc`, `.dec`, `.restr` — codes of finite sequences and the initial
  segment `⟨β 0, …, β (k-1)⟩`;
* `Realizability.KleeneTwo.qv` — the answer of `α` to the query "the argument begins like this";
* `Realizability.KleeneTwo.AppAt`, with `AppAt.unique` — the value of `α | β` at a point is the
  answer at the *least* initial segment that is answered, and it is unique;
* `Realizability.KleeneTwo.appK`, `mem_appK` — the resulting partial application, defined when
  every point has a value.

## Continuity (second exit criterion)

* `Realizability.KleeneTwo.AppAt.exists_modulus` — a value survives every change of `β` beyond
  the initial segment that produced it;
* `Realizability.KleeneTwo.appK_continuous` — hence each value of `α | β` is determined by a
  finite initial segment of `β`: Kleene's continuity principle.

## The canonical associate and the combinator `k` (third exit criterion)

* `Realizability.KleeneTwo.Cont` — continuity of an operation on Baire space;
* `Realizability.KleeneTwo.detAssoc` — its canonical associate: on the query `⟨y, s⟩` answer the
  value `F α y` if it is the same for every `α` extending `s`, and "no information" otherwise;
* `Realizability.KleeneTwo.appK_detAssoc` — the associate computes the operation;
* `Realizability.KleeneTwo.kEl`, `appK_kEl`, `appK_constAssoc`, `k2_k_app` — the combinator `k`.

## The combinator `s` (fourth exit criterion)

The canonical associate cannot produce `s`: the operation `(α, β) ↦ (the associate of
`γ ↦ (α|γ)|(β|γ)`)` has to be continuous in `α` and `β`, and a construction by quantification
over all extensions is not.  The associate is therefore computed by finite approximation.

* `Realizability.KleeneTwo.searchFrom` with `searchFrom_sound`, `_complete`, `_congr` — bounded
  search for the first positive answer;
* `Realizability.KleeneTwo.delA`, `epsA` — the values of `α | γ` and of `β | γ` as far as the
  known initial segments determine them, with `delA_sound`, `delA_complete`, `delA_modulus` and
  `epsA_eq_delA`;
* `Realizability.KleeneTwo.qpts`, `guardB`, `exists_guard` — the finitely many points of `β` the
  approximation can consult, and the test that the known segment covers them;
* `Realizability.KleeneTwo.compAux`, `approx`, `sOne` — the approximation and the element
  `s · α`, with `compAux_modulus` and `cont_sOne` its continuity in `α`;
* `Realizability.KleeneTwo.compAux_sound`, `compAux_complete`, `sOne_value`, `sOne_app_spec` —
  a positive answer is the true value of `(α|γ) | (β|γ)`, and for a long enough initial segment
  of `γ` the true value is answered;
* `Realizability.KleeneTwo.sEl`, `appK_sEl`, `sOne_dom`, `k2_s_dom`, `k2_s_app`.

## The algebra (fifth exit criterion)

* `Realizability.KleeneTwo.instPCABaire` — `K₂` is a partial combinatory algebra;
* `Realizability.KleeneTwo.appK_zero_eq_none` — the application is genuinely partial: the
  element that never answers a query applies to nothing;
* `Realizability.KleeneTwo.no_zero_test` — and, by continuity, no element of `K₂` decides
  whether its argument is the zero function.
