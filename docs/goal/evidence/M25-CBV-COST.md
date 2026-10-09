# M25-CBV-COST — the call-by-value cost model

**Status:** DONE_WEAK (first criterion proved; the tape-program criterion is the new row
`M25-CBV-STEP-PROG`)

## Proved (`Start/CbvCost.lean`)

```lean
theorem CEK.run_length_le {t : Lambda} {n b : ℕ} {s : State} (h : Run n b (State.init t) s) :
    n ≤ b + 3 * Lambda.size t * (b + 1)
theorem CEK.run_length_le_of_cbvIn (hred : Lambda.cbvIn k t N) (hN : Lambda.CbvNormal N) :
    ∃ n s, Run n k (State.init t) s ∧ IsFinal s ∧ s.decode = N ∧ k ≤ n ∧
      n ≤ k + 3 * Lambda.size t * (k + 1)
```

So the number of CEK transitions is linear in the number of call-by-value steps and in the size of
the term (and at least the number of steps, trivially).  Proof: the measure of
`Start/CbvMachine.lean` decreases on administrative transitions and grows by at most
`3 · size(body)` on a β transition; every code of a reachable state, including those nested in
environments, has size at most `|t|` (`CEK.State.Bounded`).

## Open

Criteria 2 and 3 need a binary encoding of CEK states and a tape program for one transition,
specified through `Complexity.Space.Realizes`: row `M25-CBV-STEP-PROG`.
