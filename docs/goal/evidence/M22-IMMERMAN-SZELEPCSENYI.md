# M22-IMMERMAN-SZELEPCSENYI

Immerman–Szelepcsényi (W5). The earlier proposal is in docs/goal/proposed-M21-M24.md.

## Big round 2, run 8

Started, statement only. The run 8 sandbox had no Lean toolchain (and no network), so nothing was
built and the Lean statement below has **not** been type-checked; the next run with a toolchain
should elaborate it first and correct names if needed. No module was added.

Started in big round 2, run 8 (W5), statement only. First missing lemma (not yet type-checked: no Lean toolchain in run 8), the counting recurrence on the bounded configuration graph of Start/SpaceConfigCount.lean: with reachWithin M x s k d := ∃ n ≤ k, Reach.steps (step M x s) n (initB hwf hsp) d and reachCount k := (Finset.univ.filter (reachWithin M x s k)).card, theorem Complexity.Space.reachCount_succ (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s) (k : ℕ) : reachCount (k + 1) = (Finset.univ.filter fun d => ∃ c, reachWithin M x s k c ∧ (c = d ∨ step M x s c d)).card; then the NProg that verifies a count (guess each reachable c with a run of length ≤ k, check the guessed number equals the claimed count) and its Exec specification.
