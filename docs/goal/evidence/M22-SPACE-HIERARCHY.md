# M22-SPACE-HIERARCHY

The deterministic space hierarchy theorem (W4). The earlier proposal is in docs/goal/proposed-M21-M24.md.

## Big round 2, run 8

Started, statement only. The run 8 sandbox had no Lean toolchain (and no network), so nothing was
built and the Lean statement below has **not** been type-checked; the next run with a toolchain
should elaborate it first and correct names if needed. No module was added.

Started in big round 2, run 8 (W4), statement only: the run 8 sandbox had no Lean toolchain, so the statement below is not yet type-checked. First missing lemma (exit criterion 1), on Start/SpaceMachine.lean: a finite binary code def Complexity.Space.Machine.code (M : Machine) : List Bool (states, accept bits and the table delta q a b for q < states, a : Option Bool, b : Bool), a pairing def Complexity.Space.pairCode (u v : List Bool) : List Bool (bit doubling and a separator), and theorem Complexity.Space.exists_universal : ∃ U : Machine, U.WellFormed ∧ U.Deterministic ∧ ∀ M : Machine, M.WellFormed → M.Deterministic → ∃ c : ℕ, ∀ (x : List Bool) (s : ℕ), M.SpaceBoundedOn x s → (U.Accepts (pairCode M.code x) ↔ M.Accepts x) ∧ U.SpaceBoundedOn (pairCode M.code x) (c * (s + Nat.log 2 (x.length + 1) + 1)). Route: a deterministic Prog main loop (Complexity.Space.Prog.dspace_loop) whose body simulates one transition of M on a track of the work tape, then the diagonal language with a step counter of length O(s) for loop detection.
