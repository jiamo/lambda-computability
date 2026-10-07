# M21 — `IP ⊆ PSPACE` and `IP = PSPACE` (rows `M21-IP-SUBSET-PSPACE`, `M21-IP-EQ-PSPACE`)

**Status:** DONE_STRONG for both rows.

## Terminal statements

```lean
theorem Complexity.IPSpace.ip_subset_pspace {L : Language} (h : IP L) : Space.PSPACE L
theorem Complexity.IPSpace.ip_eq_pspace {L : Language} : IP L ↔ Space.PSPACE L
theorem Complexity.ip_eq_pspace {L : Complexity.Language} :
    Complexity.IP L ↔ Complexity.Space.PSPACE L
```

`#print axioms Complexity.IPSpace.ip_eq_pspace`: `propext, Classical.choice, Quot.sound`.

## Route

- `Start/IPValue.lean` — the value of the game `Complexity.IPValue.F V x k t` (after transcript
  `t`, with `k` rounds left: sum over the verifier's possible questions, maximum over the answers,
  and at the end the number of coin words consistent with `t` on which the verifier accepts).
  `Complexity.IPValue.accCount_le_F`: every prover's acceptance count is at most `F V x R []`;
  `Complexity.IPValue.exists_F_le_accCount`: some prover attains it.  The recursion is stated on
  acceptance *counts* (numerators over `2^{coins}`) rather than probabilities; the thresholds
  `2/3`, `1/3` are transferred at the end.
- `Start/BinArith.lean`, `Start/TreeEval.lean` — a sum–max tree of positions presented by Cobham
  terms (`Complexity.TreeEval.CTree`) is evaluated by a depth-first traversal whose step is a
  tuple of Cobham terms; `Complexity.TreeEval.sim` (correctness, with every intermediate stack
  polynomially bounded) and `Complexity.TreeEval.pspace_of_ctree` (via
  `Complexity.Space.pspace_of_cobIter`, i.e. on the offline machine): a tree of polynomial depth
  and position size gives a `PSPACE` test of `2^{|thr x|} ≤ 2 · value`.
- `Start/IPSpace.lean` — the game tree of a verifier as a Cobham tree
  (`Complexity.IPSpace.ipTree`), with positions `encs [1^tag, 1^k, t, q, a, s]`;
  `Complexity.IPSpace.cnt_sem`, `ma_sem`, `sq_sem`, `rnd_sem`: below the root the tree is finite
  with depth `coins + 1 + rounds · (4 · msgLen + 3)` and positions of length `bndX`, and its value is
  `F`.  `ip_subset_pspace` instantiates `pspace_of_ctree` with polynomial bounds from
  `Complexity.Cob.polyLen`; `ip_eq_pspace` combines it with `Complexity.Shamir.pspace_subset_ip`.

## Gates

`lake build` (whole library), `python3 scripts/check_sorry.py`, `python3 scripts/check_closure.py`,
`python3 scripts/goal_state.py validate`.
