# M11-KRIVINE-MACHINE

**Status:** DONE_STRONG

`Start/SizeExplosion.lean` records why the number of β-steps is not obviously a legitimate
measure of time: a term of linear size reaches, in linearly many steps, a normal form of
exponential size, so no evaluator that writes the result down can be fast.  The way out is an
environment machine, which keeps the result shared.  `Start/Krivine.lean` defines one.

## The machine (first three exit criteria)

* `Krivine.Clos` — a closure, a piece of code with an environment (a nested inductive type: an
  environment is a list of closures);
* `Krivine.State` — code, environment, and a stack of arguments; `Krivine.State.init` the state
  on a term;
* `Krivine.Label`, `Krivine.Trans` — the transitions, labelled: `app` unloads an application onto
  the stack, `beta` consumes the top of the stack, `var` replaces a variable by the closure the
  environment binds it to.  `Krivine.Label.betaCount` is what a label costs in β-steps;
* `Krivine.Run n b s s'` — a run of `n` transitions, `b` of them β transitions, with
  `Krivine.Run.trans`, `Krivine.Run.single` and `Krivine.Run.beta_le` (`b ≤ n`);
* `Krivine.Run.starN` — the bridge to `Start/Rewriting.lean`: the transitions of a run are the
  counted reflexive–transitive closure `Rewriting.StarN` of `Krivine.Step`, so nothing generic
  about counted rewriting is reproved here.

## Determinism and the final states (fourth exit criterion)

* `Krivine.Trans.deterministic` — a state has at most one transition, with one label, and
  `Krivine.Run.deterministic` — a run is determined by its length;
* `Krivine.isFinal_iff` — the stuck states are exactly the results (an abstraction with an empty
  stack) and the states blocked on a variable the environment does not bind.

## The depth of the environments (fifth exit criterion)

`Krivine.Clos.depth` and `Krivine.envDepth` are defined by mutual structural recursion, and
`Krivine.depth_lt_envDepth_of_mem`, `Krivine.envDepth_env_lt` say that the environment of a
closure of `e` is strictly shallower than `e`.  A `var` transition therefore descends, which is
what makes the administrative transitions terminate (`Start/KrivineDecode.lean`) and is the
source of the quantitative bound (`Start/KrivineBound.lean`).

The module is imported by `Start.lean`, registered in `Start/Capstones.lean`, builds without
`sorry` and without linter warning.
