# M5-SOLVABILITY

**Status:** DONE_STRONG

New module `Start/Solvability.lean` (imported by `Start.lean`).

* `Lambda.appList` with `appList_concat`, `reduces_appList`, `conv_appList`, `conv_app_left` —
  application to a list of arguments and its congruences.
* `Lambda.Solvable` — closed arguments turn the term into the identity; `Solvable.of_conv` and
  `convInvariant_solvable` record invariance under convertibility.
* `Lambda.solvable_I`, `Lambda.solvable_church` — solvable witnesses.
* `Lambda.OmegaApp`, `omegaApp_of_step`, `omegaApp_of_reduces`, `not_omegaApp_I`,
  `Lambda.not_solvable_omega` — `Ω` is unsolvable: applications headed by `Ω` are preserved by
  reduction and `I` is not of that shape.
* `Lambda.exists_args_conv_of_solvable` — generic reachability: a solvable term can be driven to
  any closed term.
* `Lambda.not_decides_solvable`, `Lambda.not_computablePred_codeSet_solvable` — undecidability of
  solvability, via Scott's theorem with the witnesses `I` and `Ω`.

Böhm's separation theorem itself is *not* claimed here; what is proved is the solvability layer it
is usually stated on top of, together with the generic-reachability form of separation for
solvable terms.

Gates: `lake build` succeeds; no `sorry`; no linter warnings; `#print axioms` on the headline
results reports only `propext, Classical.choice, Quot.sound`.
