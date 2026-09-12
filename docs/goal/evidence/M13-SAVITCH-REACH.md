# M13-SAVITCH-REACH — bounded reachability and the midpoint identity

`Start/SavitchReach.lean`.  The combinatorial content of Savitch's theorem is about a directed
graph, and this module isolates it.

## Walks

* `Complexity.Reach.steps r n a b` — a walk with exactly `n` edges.
* `Complexity.Reach.steps_add` — walks compose and decompose at any intermediate length; this is
  the only property of walks the midpoint identity needs.
* `Complexity.Reach.IsWalk`, `.exists_isWalk`, `.steps_of_isWalk` — the same walks presented as
  functions on indices, which is the form the pigeonhole argument uses.

## Shortening

* `Complexity.Reach.exists_steps_lt_card` — in a graph with finitely many vertices every walk
  shortens to one of length below the number of vertices.  The proof is a strong induction on the
  length: a walk at least as long as the number of vertices visits some vertex twice
  (`Fintype.exists_ne_map_eq_of_card_lt`), and splicing out the loop gives a strictly shorter
  walk.

## The recursion

* `Complexity.Reach.reachLe r k a b` — reachability by a walk with at most `2 ^ k` edges.
* `Complexity.Reach.reachLe_zero_iff` — at depth `0` this is equality or one edge.
* `Complexity.Reach.reachLe_succ_iff` — **the midpoint identity**: reachability within `2 ^ (k+1)`
  steps is the existence of a midpoint reachable within `2 ^ k` from the source and reaching the
  target within `2 ^ k`.  Both directions are explicit: one splits a walk at `min n (2 ^ k)`, the
  other concatenates.
* `Complexity.Reach.reachB` — the decision procedure the identity suggests, and
  `Complexity.Reach.reachB_iff` proves it decides `reachLe`.
* `Complexity.Reach.reachB_iff_exists_steps` — with `Fintype.card C ≤ 2 ^ k` the recursion decides
  reachability outright, by the shortening lemma.

## Gates

`lake build`, `python3 scripts/check_closure.py`, `python3 scripts/goal_state.py validate`.
