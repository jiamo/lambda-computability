# M10-LAMBDAPI-ETA-POSTPONE

**Status:** DONE_STRONG

Module `Start/LambdaPiEtaPostpone.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings, and its results
depend only on `propext`, `Classical.choice` and `Quot.sound`.

## What this task adds

`Start/LambdaPiEta.lean` adds η to `λΠ` and shows that the raw system `β ∪ η` is not confluent.
This module proves the structural fact that survives that counterexample: **η can be postponed**.

- `LambdaPi.SRed` — a β-reduction with at least one step, with its congruences, and
  `LambdaPi.Red.head_split`, which splits a nonempty β-reduction at the head.
- `LambdaPi.EtaPar` — parallel η-reduction, contracting a whole family of η-redexes at once, with
  `EtaPar.refl`, `EtaStep.toEtaPar`, `EtaPar.toEtaRed`, and stability under renaming
  (`EtaPar.rename`) and under substitution on both sides (`EtaPar.substs`, `EtaPar.inst`).
- **`LambdaPi.EtaPar.lam_app_sred`** — if `f` parallel-η-reduces to an abstraction `lam A c`, then
  `app f a` β-reduces in at least one step to `b[a]` for some `b` that parallel-η-reduces to `c`:
  the β-redex that η appeared to create was already there, behind a tower of η-expansions.  This
  is the step that fails for the plain one-step η.
- **`LambdaPi.EtaPar.postpone_step`**, `EtaPar.postpone_red`, `EtaPar.postpone_sred`,
  `EtaRed.postpone_sred`, `EtaRed.postpone` — the postponement diagrams, in the plain and in the
  "at least one β-step" form.
- **`LambdaPi.betaEtaRed_iff`** (also `LambdaPi.betaEta_postpone`) — βη-reduction is exactly `β*`
  followed by `η*`.

The typing-layer payoff:

- `LambdaPi.SNBetaEta`, **`LambdaPi.snBetaEta_aux`**, `LambdaPi.snBetaEta_of_sn` — a β-strongly
  normalizing term is βη-strongly normalizing.  The proof is an outer induction on the
  β-accessibility of the term, which absorbs β-steps through postponement, and an inner induction
  on the size, which the η-steps decrease.
- **`LambdaPi.Typing.betaEta_sn`** — strong normalization of `βη` for `λΠ`, from
  `LambdaPi.Typing.sn`.
- `LambdaPi.BetaEtaNormal`, `LambdaPi.hasBetaEtaNormalForm_of_snBetaEta`,
  **`LambdaPi.Typing.hasBetaEtaNormalForm`** — every typable term has a βη-normal form.

## Gates

- `lake build Start.LambdaPiEtaPostpone` — success, no warnings.
- `python3 scripts/check_closure.py` — all modules in the import closure and all registered.
- `python3 scripts/goal_state.py validate` — board validates.
