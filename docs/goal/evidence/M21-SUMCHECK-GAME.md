# M21-SUMCHECK-GAME — the sum-check protocol as a game

**Status:** DONE_STRONG

## Terminal statements (`Start/SumCheck.lean`)

```lean
def Complexity.Qbf.run (d : ℕ) (P : Strat F) : Op → (ℕ → F) → F → List (List F) → List F →
    Bool × List (List F)
theorem Complexity.Qbf.run_honest (d) : ∀ t, Op.RoundDeg F d t → ∀ a v hist ρ,
    v = t.eval a → (run d (honest d) t a v hist ρ).1 = true
theorem Complexity.Qbf.cntL_run_false (d) : ∀ t, Op.RoundDeg F d t → ∀ P a v hist,
    v ≠ t.eval a →
    cntL t.rounds (fun ρ => (run d P t a v hist ρ).1) * Fintype.card F ≤
      d * t.rounds * Fintype.card F ^ t.rounds
theorem Complexity.Qbf.scProb_le : scProb d P t a v ≤ (d * t.rounds : ℚ) / Fintype.card F
theorem Complexity.Qbf.tqbf_sumcheck_complete / tqbf_sumcheck_sound   -- for toOp N p
```

## The game

A claim is a node `t`, a point `a` and a value `v`.

- **Rounds.** At a quantifier or linearization node the prover sends the coefficient list of a
  polynomial of degree at most `d` (`Complexity.Qbf.evalL`). The verifier checks how it combines
  against `v`, draws a random point `s` and continues with the claim `h(s)` at `a[i := s]`.
- **Conjunctions and disjunctions.** The prover sends both child values. The verifier checks how
  they combine and recurses on both children: first on the left one, then on the right one, with
  the right one seeing the history of the left one.
- **The prover.** It is an arbitrary strategy on the full history. It also receives the current
  node and point, but these are determined by the history.

Soundness is proved by induction on the tree.

- **Rounds.** If the prover's polynomial differs from the true restriction, they agree at no more
  than `d` points (`Polynomial.card_eval_eq_le`). Away from those points the next claim is false.
- **Binary nodes.** One of the two child claims is false, and the count splits along `sumL_append`.

Rows that this delivery opened from here (see `M21-VERIFIER-POLY`):

- `M21-SUMCHECK-REPLAY`: the same run as a small-step replay over the code of the formula.
- `M21-SUMCHECK-COINS`: the transfer from counting over `F` to counting over random bits.
