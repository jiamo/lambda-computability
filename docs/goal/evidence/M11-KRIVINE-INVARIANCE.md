# M11-KRIVINE-INVARIANCE

**Status:** DONE_STRONG

`Start/KrivineBound.lean` bounds the administrative transitions of the machine, which is what
turns the bisimulation of `M11-KRIVINE-SIMULATION` into an invariance statement: the two cost
measures — β-steps of the calculus and transitions of the machine — are polynomially related.

## The two invariants (exit criteria one and two)

* `Krivine.State.maxCode` and `Krivine.Trans.maxCode_le` — no transition ever produces a piece of
  code larger than one the machine already held; along a run every code is therefore bounded by
  the size of the initial term (`Krivine.Run.maxCode_le`).  This is the subterm invariant that
  makes sharing affordable;
* `Krivine.State.depthBound` and `Krivine.Trans.depthBound_le` — only a `beta` transition
  deepens the environments, and it deepens them by one.

## The potential (third exit criterion)

`Krivine.State.potential S s = |code| + S · envDepth env`:

* `Krivine.Trans.potential_lt` — an `app` transition shrinks the code, and a `var` transition
  trades a variable for a code of size at most `S` while descending one level of environment, so
  both strictly decrease the potential;
* `Krivine.Trans.potential_beta_le` — a `beta` transition increases it by at most `S · (B + 1)`.

## The bound (exit criteria four and five)

* `Krivine.run_length_le` — along a run with `b` β transitions out of a state of code bound `S`
  and depth bound `B`, at most `b + potential + b · S · (B + b + 1)` transitions;
* `Krivine.run_length_le_init` — from the initial state on `t`: `n ≤ b + |t| · (1 + b · (b + 1))`;
* `Krivine.eval_cost` — with the bisimulation: a term the weak head strategy normalises in `k`
  steps is evaluated by the machine with at most `k` β transitions and at most
  `k + |t| · (1 + k · (k + 1))` transitions in all, and the state it stops in decodes to the weak
  head normal form, reached in exactly as many β-steps as it made β transitions.  The converse
  inequality `b ≤ n` is `Krivine.Run.beta_le`.

A worked example at the end of the module runs the machine on `(λx. x) (λx. x)`: three
transitions, one of them a β transition, and the final state decodes to the identity.

## The other half

Only the *number of transitions* is bounded here.  A reasonable cost model also needs that a
single transition can be performed in time polynomial in the size of the state on a concrete
machine model.  That half is `M11-KRIVINE-UNIT-COST` (the implementation on a code table and a
heap, and the word encoding of its states) together with `M11-KRIVINE-PASS-MACHINE`
(`Krivine.Impl.stepT`, one transition as a Cobham term, with `Krivine.Impl.eval_stepT` and
`Krivine.Impl.stepT_compiles`); `Krivine.Impl.eval_impl_cob_cost` composes them with the bound
proved here, so this task has no open boundary left.

The module is imported by `Start.lean`, registered in `Start/Capstones.lean`, builds without
`sorry` and without linter warning; the headline results depend only on `propext`,
`Classical.choice`, `Quot.sound`.
