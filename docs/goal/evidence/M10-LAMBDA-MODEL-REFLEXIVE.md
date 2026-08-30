# M10-LAMBDA-MODEL-REFLEXIVE

**Status:** DONE_STRONG

λ-models, the three models of this library as instances, and the Scott–Koymans correspondence
between λ-models and reflexive objects in cartesian closed categories.

## λ-models — `Start/LambdaModel.lean`

`Lambda.LambdaModel` is an applicative structure `(Carrier, app)` with a nonempty carrier and an
interpretation `⟦t⟧ρ` of the untyped de Bruijn terms in environments `ρ : ℕ → Carrier`, subject to
the Meyer–Scott axioms `interp_var`, `interp_app`, `interp_beta` (`⟦λt⟧ρ · d = ⟦t⟧(d :: ρ)`) and
`interp_lam_ext` (**weak extensionality**, the rule ξ).  Everything else is derived from those
four axioms:

* `Lambda.LambdaModel.interp_lift`, `interp_subst`, `interp_beta_subst` — the lifting and
  substitution lemmas, and the syntactic β-rule;
* `Lambda.LambdaModel.interp_step`, `interp_reduces`, **`interp_conv`** — soundness for
  β-conversion;
* `Lambda.LambdaModel.interp_congr_below`, `interp_closed` — the interpretation depends on the
  environment only at the free variables;
* `Lambda.LambdaModel.K`, `.S`, `.eps`, `app_app_K`, `app_app_app_S`, `app_app_eps`, `eps_ext`,
  `app_eps_eps` — every λ-model is a combinatory algebra with a Meyer–Scott ε;
* `Lambda.LambdaModel.IsExtensional`, `interp_eta_of_extensional` — extensional models are
  exactly the ones validating η.

## The three models are instances — `Start/LambdaModelInstances.lean`

* `GraphModel.model` — Scott's graph model `𝒫ω`; `GraphModel.model_not_extensional`;
* `ScottDinf.model` — the inverse limit `D∞`; `ScottDinf.model_extensional`,
  `model_interp_eta`, `model_nontrivial`;
* `Inter.filterModel`, **`Inter.typeSet_eq_model_interp`** — the filter model of the intersection
  type system: the filter of types of a term *is* its value in the λ-model.

`Lambda.LambdaModel.theory` sends a λ-model to a λ-theory in the sense of
`Start/LambdaTheory.lean` (congruence via `interp_fill_congr`), and
`GraphModel.theory_model_eq`, `ScottDinf.theory_model_eq` identify those theories with the
entries `Th(𝒫ω)`, `Th(D∞)` of the lattice `B ⊊ Th(𝒫ω) ⊊ Th(D∞) = H*`.

## Every λ-model is a reflexive object — `Start/LambdaModelComb.lean`, `Start/KaroubiLambda.lean`

`Start/LambdaModelComb.lean` builds the combinators needed inside an arbitrary λ-model — `idE`,
`compE`, `pairE`, `fstE`, `sndE`, `prodE`, `expE`, `curryE`, `uncurryE`, `postCompE`, `topE` —
each as the interpretation of a closed λ-term applied to an environment of constants, together
with the extensionality principle `Lambda.LambdaModel.lamVal_ext`: two λ-values with the same
applicative behaviour are equal.  Every equation between morphisms below is proved pointwise with
that principle.

`Start/KaroubiLambda.lean` is the **Karoubi envelope**: objects `Lambda.LambdaModel.Ret M` are the
idempotents `a ∘ a = a`, and a morphism `a ⟶ b` is an element `f` with `b ∘ f ∘ a = f`.

* `Lambda.LambdaModel.karoubiCategory` — a category;
* `topRet`, `isTerminalTopRet`, `prodRet`, `projFst`, `projSnd`, `pairMor`, `prodCone`,
  `karoubiCartesianMonoidal` — a terminal object and binary products;
* `expRet`, `expFunctor`, `curryMor`, `uncurryMor`, `curryEquiv`, `karoubiClosed`,
  **`karoubiMonoidalClosed`** — exponentials: the category is cartesian closed;
* `dRet`, `dLam`, `dApp`, **`reflexive_dRet`** — the object `D = λz. z` is reflexive: `D ⇒ D` is a
  retract of `D`.

## Reflexive objects interpret the untyped calculus — `Start/ReflexiveCcc.lean`

`ReflexiveCcc.ReflexiveObject C` is an object `D` of a cartesian closed category with
`lam : (D ⇒ D) ⟶ D`, `app : D ⟶ (D ⇒ D)` and `lam ≫ app = 𝟙`.  A term is interpreted at a stage
`X` in an environment of generalized elements `ρ : ℕ → (X ⟶ D)`:

* `ReflexiveCcc.ReflexiveObject.interp`, with `appMor`, `lamMor`, `shift`;
* `appMor_reindex`, `lamMor_reindex`, **`interp_reindex`** — naturality in the stage;
* **`interp_beta`** — `⟦λt⟧ρ` applied to `a` is `⟦t⟧(a :: ρ)`;
* `interp_lift`, `interp_lift_zero_shift`, `interp_subst`, `interp_beta_subst`;
* `interp_step`, `interp_reduces`, **`interp_conv`** — soundness for β-conversion;
* `interp_eta_of_iso` — an isomorphism `D ≅ (D ⇒ D)` validates η as well.

`Start/ReflexiveType.lean` is the case of the category of sets, where the internal hom is the
function type: `Lambda.SetReflexive.toModel` turns such a retraction into a λ-model, extensional
exactly when the retraction is an isomorphism (`toModel_extensional`,
`lam_app_of_extensional`).

## Putting the two directions together — `Start/ScottKoymans.lean`

* **`Lambda.LambdaModel.toReflexiveObject`** — a λ-model, viewed as a reflexive object in its own
  Karoubi envelope;
* `ReflexiveCcc.ReflexiveObject.interp_fill_congr`, **`ReflexiveCcc.ReflexiveObject.theory`** — the
  equations a reflexive object validates at every stage form a λ-theory.

Since the graph model, `D∞` and the filter model are λ-models, each is now also a reflexive object
in a cartesian closed category, and the lattice of λ-theories is a statement about reflexive
objects.

## Gates

* `python3 scripts/goal_state.py validate`
* `python3 scripts/check_closure.py`
* `lake build Start.LambdaModel Start.LambdaModelInstances Start.KaroubiLambda Start.ReflexiveCcc Start.ScottKoymans`
* Axioms: `Lambda.LambdaModel.reflexive_dRet` — `propext, Classical.choice`;
  `Lambda.LambdaModel.interp_conv`, `ReflexiveCcc.ReflexiveObject.interp_conv`,
  `Lambda.LambdaModel.toReflexiveObject`, `GraphModel.theory_model_eq`,
  `ScottDinf.theory_model_eq`, `Inter.typeSet_eq_model_interp` — `propext, Classical.choice,
  Quot.sound`; `Lambda.SetReflexive.toModel` — `Quot.sound`.
