# M10-LAMBDA-ETAPOSTPONE

**Status:** DONE_STRONG

Module `Start/LambdaEtaPostpone.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

`M10-LAMBDA-BETAETA` proves that βη-reduction of untyped terms is confluent, by closing the
composite relation "β-reduce, then η-reduce" under transitivity and running the Hindley–Rosen
argument on it.  That leaves the sharper structural question open: does the composite already
*have* to be closed, i.e. can every βη-reduction be rearranged so that all β-steps come first?
It can — this is η-postponement — and this module proves it.

## Why a parallel η-step is needed

The naive local diagram is false for a single η-step: from `t →η v →β w` one cannot in general
get `t →β⁺ · →η w` with a *single* η-step at the end, because the β-redex `v` contracts may have
been created by a tower of η-expansions inside `t`, each of which has to be contracted.  The
module therefore introduces a *parallel* η-reduction, `Lambda.etaPar`:

* `Lambda.etaPar.refl`, `Lambda.etaStep.toEtaPar`, `Lambda.etaPar.toEtaReduces` — it is
  reflexive, contains one-step η-reduction, and is contained in many-step η-reduction, so its
  transitive closure is exactly `Lambda.etaReduces`;
* `Lambda.etaPar_lift`, `Lambda.etaPar_subst` — it is stable under lifting, and under
  substitution simultaneously in the term and in the argument.

## The critical lemma

`Lambda.etaPar_lam_app_reduces`: if `f` parallel-η-reduces to an abstraction `lam c`, then for
every argument `a` there is a `b` with `app f a →β* subst a 0 b` and `b` parallel-η-reduces to
`c`.  The proof is an induction that peels one η-expansion at a time: for
`f = lam (app (lift 1 0 f₀) (var 0))` the β-step `app f a →β app f₀ a` is available because
`subst a 0 (lift 1 0 f₀) = f₀` (`Lambda.subst_lift`).  This is exactly the statement that a
β-redex created by η was already present, behind the expansions.

## The diagrams

* `Lambda.etaPar_postpone_step` — local postponement: `t ⇒η v →β w` gives an `m` with
  `t →β* m ⇒η w`.  The interesting case is a β-redex in `v` whose function part came from `t`
  through η, which is where `Lambda.etaPar_lam_app_reduces` and `Lambda.etaPar_subst` are used;
  the η-rule case is closed by lifting the β-reduction under the expansion
  (`Lambda.reduces_lift`).
* `Lambda.etaPar_postpone_reduces` — the same with a β-*sequence*, by induction on it.
* `Lambda.etaReduces_postpone` — **η-postponement**: `t →η* v →β* w` gives an `m` with
  `t →β* m →η* w`.
* `Lambda.betaEtaReduces_iff` — **βη-reduction is `β*` followed by `η*`**: `betaEtaReduces t u`
  if and only if there is an `m` with `Lambda.reduces t m` and `etaReduces m u`.
* `Lambda.etaReduces_of_betaEtaReduces_of_betaNf` — consequence: a term that β-reduces only to
  itself cannot acquire a β-reduct through η, so all of its βη-reducts are η-reducts.

`Lambda.reduces_lift` was moved from `Start/SelfInterpreter.lean` to `Start/Reduction.lean`, next
to the parallel-reduction lemmas it is proved from, so that the reduction theory can use it
without depending on the self-interpreter.

## Gates

* `lake build` — the whole library, no error and no warning.
* `python3 scripts/check_closure.py` — every module in the import closure of `Start.lean` and
  registered.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: `Lambda.betaEtaReduces_iff` and `Lambda.etaReduces_postpone` depend only on
  `propext`, `Classical.choice` and `Quot.sound`.
