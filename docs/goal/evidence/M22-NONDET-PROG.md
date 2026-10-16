# M22-NONDET-PROG: nondeterministic tape programs

Exit criterion 1 (earlier delivery): `Start/SpaceNProg.lean` — `NProg` (the structured tape
programs plus `choose p q`), the big-step semantics `NProg.Exec`, the compiled table `NProg.delta`,
the machine `NProg.machine`, compiler correctness `NProg.path_of_exec`, `machine_wellFormed`,
`loop_seg`, `loop_exit`, `accepts_of_exec`.

Exit criterion 2 (this delivery):

* `Start/SpaceNProgConverse.lean`
  * `NProg.exec_of_run`: a run of a machine hosting `p` at base `b` with exit `e` (outside the
    block), which starts at `b` and ends outside the block, passes through `e`; its part up to `e`
    is an execution of `p`.  Induction on `p`; for `loop`, strong induction on the run length.
  * `NProg.exec_of_accepts` (the first missing lemma of the previous delivery):
    `p.machine.Accepts x → ∃ c', NProg.Exec x (fun _ => True) p init c'`.
  * `NProg.nspace_of_exec`: `NSPACE` membership given a space bound on the reachable
    configurations of the compiled machine.
* `Start/SpaceNProgLoop.lean`
  * `NProg.delta_shift`: the table laid out at base `b + k` is the table at `b` with relabelled
    targets.
  * `NProg.loop_reach_inv`: every reachable configuration of the machine of `loop t body` is in
    the test state and satisfies the invariant, or in the final state within the bound, or is a
    configuration reached by `body.machine` on an iteration, shifted by one state.
  * `NProg.nspace_loop` (terminal): membership in `NSPACE s` from the loop form — an invariant `I`
    that holds initially and bounds the space, partial runs of the body from an iteration that stay
    within `B x` cells and restore `I` when they finish, and `L x ↔` the loop has an execution.

Exit criterion 3 (shared prerequisite of M22-IMMERMAN-SZELEPCSENYI and M22-SPACE-HIERARCHY) is the
role of these lemmas.  `#print axioms`: `docs/goal/evidence/M28-A4-axioms.txt`.
