# M25-CBV-MACHINE — call-by-value: an abstract machine, and its simulation

**Status:** DONE_STRONG

## Terminal statements (`Start/CbvMachine.lean`)

```lean
def Lambda.IsValue : Lambda → Prop                 -- var and lam
inductive Lambda.cbvstep                           -- beta_v, appL, appR (left to right)
theorem Lambda.cbvstep_deterministic, Lambda.cbvstep_imp_step
inductive Lambda.cbvIn : ℕ → Lambda → Lambda → Prop

inductive CEK.Frame | arg (u : Lambda) (e : Env) | fn (c : Clos)
inductive CEK.State | eval (t : Lambda) (e : Env) (k : List Frame) | ret (c : Clos) (k : List Frame)
inductive CEK.Trans : Label → State → State → Prop  -- app, lam, var, free, swap (admin); beta

theorem CEK.Trans.decode_eq : Trans .admin s s' → s.decode = s'.decode
theorem CEK.Trans.decode_cbvstep : Trans .beta s s' → s.Good → cbvstep s.decode s'.decode
theorem CEK.Run.decode_cbvIn : Run n b s s' → s.Good → cbvIn b s.decode s'.decode
theorem CEK.IsFinal.cbvNormal_decode : IsFinal s → s.Good → CbvNormal s.decode
theorem CEK.eval_sound : Run n b (State.init t) s → IsFinal s → cbvIn b t s.decode ∧ CbvNormal s.decode
theorem CEK.exists_final_of_cbvIn : s.Good → cbvIn k s.decode N → CbvNormal N →
    ∃ n s', Run n k s s' ∧ IsFinal s' ∧ s'.decode = N
theorem CEK.eval_complete : cbvIn k t N → CbvNormal N →
    ∃ n s, Run n k (State.init t) s ∧ IsFinal s ∧ s.decode = N
```

Closures, environments, `Clos.unfold` and `unfoldEnv` are those of the Krivine machine
(`Start/Krivine.lean`, `Start/KrivineDecode.lean`).

## Notes

* Values are abstractions and variables (Plotkin's `λv`), so that open terms are handled: a free
  variable is returned as a value (`Trans.free`).
* `CEK.State.Good` is the invariant of reachable states: every closure in an environment, in a
  `fn` frame or being returned is a value closure (an abstraction, or a variable its environment
  does not bind), recursively.  It is what makes the continuation an evaluation context and the
  bound values values.
* Final states: `ret c []` (a value), or `ret v (fn x :: k)` with `x` a free variable — the term
  is then stuck (`CEK.Stuck`), which `stuck_plug` propagates through the context.
* Termination of the administrative transitions: the measure `3·size(code) + Σ_{arg u} (3·size u
  + 2)` decreases strictly on each of them (`Trans.measure_lt`).

## Gates

```
lake build
python3 scripts/check_sorry.py
python3 scripts/check_closure.py
python3 scripts/goal_state.py validate
```
