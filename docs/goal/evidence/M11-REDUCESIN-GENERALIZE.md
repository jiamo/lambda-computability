# M11-REDUCESIN-GENERALIZE

**Status:** DONE_STRONG

`Start/ReducesIn.lean` carried its own inductive step-counting reduction `Lambda.reducesIn` and
re-proved, for it, the lemmas that `Start/Rewriting.lean` already proves for the uncounted closure:
transitivity, the tail step, monotonicity in the count, and the congruences.  Since the counted
closure is the one structure the abstract interface was missing, it was added there rather than
kept λ-specific.

## The counted closure (`Start/Rewriting.lean`)

* `Rewriting.StarN r n a b` — `a` reduces to `b` in exactly `n` steps of `r`;
* `StarN.single`, `StarN.toStar`, `StarN.trans` (counts add), `StarN.tail`, `StarN.mono`,
  `StarN.map` (image along a relation-preserving map);
* `Rewriting.exists_starN_of_star` and `Rewriting.star_iff_exists_starN` — the uncounted closure is
  the counted one with the count forgotten.

## The bridge

`Lambda.reducesIn_iff_starN : reducesIn n t u ↔ Rewriting.StarN Lambda.step n t u`.

Every lemma of `Start/ReducesIn.lean` is now derived through it; the congruence lemmas are
instances of `Rewriting.StarN.map`.  No public name of the module changed, so its clients
(`Start/LevinKt.lean`, `Start/SizeExplosion.lean`) are untouched.

## Gates

* `python3 scripts/goal_state.py validate`
* `python3 scripts/check_closure.py`
* `lake build Start.ReducesIn`, `lake build Start.SizeExplosion`
