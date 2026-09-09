# M11-KRIVINE-SIMULATION

**Status:** DONE_STRONG

`Start/KrivineDecode.lean` relates the machine of `Start/Krivine.lean` to the calculus, in both
directions.  It reuses the parallel substitution of `Start/SelfInterpreter.lean` and
`Start/ParallelSubst.lean` and the weak head strategy of `Start/WeakHead.lean`.

## The decoding (first exit criterion)

* `Krivine.Clos.unfold` and `Krivine.unfoldEnv` — mutually recursive: a closure stands for its
  code with the environment substituted in, an environment for the parallel substitution it
  induces (the indices it does not bind are shifted down);
* `Krivine.spine`, `Krivine.State.decode` — the unfolded code, applied to the unfolded stack;
* `Krivine.State.decode_init` — the initial state on `t` stands for `t`.

## The machine simulates the calculus (exit criteria two and three)

* `Krivine.Trans.decode_eq` — an `app` or a `var` transition does not change the decoded term: it
  only moves the sharing around.  The `var` case is `Krivine.unfoldEnv_of_getElem?`, that a
  lookup reads off the decoding;
* `Krivine.Trans.decode_wstep` — a `beta` transition is exactly one weak head β-step; the
  equation that computes it is `Lambda.subst_zero_substEnv`, and
  `Krivine.unfoldEnv_cons = Lambda.envScons` matches the extended environment with the extended
  substitution;
* `Krivine.Run.decode_starN`, `Krivine.Run.decode_reducesIn`, `Krivine.Run.decode_eq_of_no_beta`
  — a run with `b` β transitions is a weak head reduction of exactly `b` steps.

## The results are weak head normal forms (fourth exit criterion)

`Krivine.isWhnf_spine` and `Krivine.unfoldEnv_of_getElem?_none` give
`Krivine.IsFinal.isWhnf_decode`, hence `Krivine.eval_sound`: what the machine returns is reached
from the initial term by exactly as many β-steps as it made β transitions, and it has no weak
head redex.

## The machine finds them (fifth exit criterion)

`Krivine.exists_beta_or_final` — from any state, and without any β transition, the machine
reaches either a final state or one about to perform a β transition.  The proof is a double
induction: on the depth of the environment (which a `var` transition strictly decreases) and, at
a fixed depth, on the size of the code (which an `app` transition strictly decreases).  Feeding
that into an induction on the number of weak head steps gives
`Krivine.exists_final_of_whnIn`: a state whose term the weak head strategy normalises in `k`
steps runs to a final state with at most `k` β transitions.

The module is imported by `Start.lean`, registered in `Start/Capstones.lean`, builds without
`sorry` and without linter warning; the headline results depend only on `propext`,
`Classical.choice`, `Quot.sound`.
