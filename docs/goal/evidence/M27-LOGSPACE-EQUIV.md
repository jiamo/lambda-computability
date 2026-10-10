# M27 — host `LOGSPACE` = `L` = `RL` = `BPL`

Tasks `M27-SPACE-MODEL-COMPILE` (upstream-to-host compiler) and `M27-LOGSPACE-TRANSFER`.
The host-to-upstream direction (`ToLogspace.compile`, `logspace_subset_L`) is recorded in
`M27-LOGSPACE-TRANSFER.md` and credited to `M27-SPACE-MODEL-TOTALIZE`.

## Terminal statements

`Start/LogspaceTransferEquiv.lean`, for every `A : Complexity.Space.Language`
(`= List Bool → Prop`), with `LOGSPACE` the unchanged class of `Start/SpaceMachine.lean`:

```lean
theorem Complexity.Space.mem_L_iff_logspace (A : Language) :
    {x | A x} ∈ ExactDerandomization.L ↔ LOGSPACE A
theorem Complexity.Space.mem_RL_iff_logspace (A : Language) :
    {x | A x} ∈ ExactDerandomization.RL ↔ LOGSPACE A
theorem Complexity.Space.mem_BPL_iff_logspace (A : Language) :
    {x | A x} ∈ ExactDerandomization.BPL ↔ LOGSPACE A
```

`#print axioms` on each of the three: `[propext, Classical.choice, Quot.sound]`.

## The chain (steps a–d of the instruction)

**(a) One transition — `Start/LogspaceToSpaceTransition.lean`.**
`FromLogspace.stepProg M` = `caseUnary` on the unary state register, then `readAll` over the `h`
input heads (`rdInput`: an empty counter is the left end marker, otherwise `readSym` moves the host
input head to the counted position with `seekCounter` and back), then `readAll` over the `w` work
heads (`rdWork`: the last bit of the right window register, popped and pushed back), and at each
leaf `leafProg`: if the state has no output, `actProg` of the action
`M.transition ⟨v, _⟩ syms bits false` (tapes, heads, state, flags: `runs_tapesOp`, `runs_headsOp`,
`runs_setState`, `runs_setFlags`), otherwise `skip`.  The dispatch is a finite tree of programs: every
host step is an ordinary step of the finite compiled control; the source transition is never called
inside a host step.

* `runs_stepProg` : from `lay K (encC M W c)` to `lay K (encC M W (M.step x false c))`, every
  configuration on the way within `B ≥ (N + 3)(2K + 1)` cells, given `(2W + 1).toNat ≤ N`,
  `q + 1 ≤ N`, `log₂ (n + 2) + 1 ≤ N` and the heads of `c` and `M.step x false c` in `[-W, W]`.
  (For a state with output the program does nothing, as `M.step` does.)
* `runs_stepProg_det` : the same for either coin `b`, for a deterministic `M`.

**(b) The loop — `Start/LogspaceToSpaceInit.lean`, `Start/LogspaceToSpaceCompile.lean`.**
`FromLogspace.compile M c₀ = (loop runTest (mvL 3; ite ruler (stepProg M) (initProg M c₀); mvR 3)).machine`.
`initProg` builds `encC` of `M.initial` from the blank tape (ruler; count the input into a
counter; grow every window by `c₀` per counter bit plus once; count back to put the input head at
`0`; state and flags) — `runs_initProg`.  The loop test reads the presence bit of the result
register; a rejecting run loops forever in the same configuration.  The bridge is
`Prog.realizes_loop` with an abstract machine whose states are (input, iteration index, host
configuration) (`absM`, invariant `reaches_inv`).

* `compile_wellFormed`, `compile_deterministic`;
* `compile_accepts_iff` : `M.Decides A → ((compile M c₀).Accepts x ↔ x ∈ A)` (no clock needed).

**(c) The space bound.**
`compile_spaceBoundedOn` : every configuration reachable by the host machine on `x` — including
initialization, counters, seek scratch, dispatch and window registers — uses at most
`spaceB q w h c₀ |x| = (2 winR c₀ n + q + log₂ (n + 2) + 6) (2 (7 + h + 2w) + 1)` cells, where
`winR c₀ n = c₀ ⌈log₂ (n + 2)⌉` (`winR_eq_clog`) is the upstream `LogSpace` bound `s`.  Head
positions stay in the window by `workPos_lt_of_spaceThrough` (the visited cells of a tape contain
the whole interval between `0` and the head).

* `spaceB_le` : `spaceB ≤ C_M (s + log₂ (n + 2) + 1)` with `C_M = 2 (q + 6) (2 (7 + h + 2w) + 1)`;
* `spaceB_le_log` : `spaceB ≤ (2c₀ + q + 7)(2 (7 + h + 2w) + 1) (log₂ (n + 1) + 1)`;
* `logspace_of_L : {x | A x} ∈ ExactDerandomization.L → LOGSPACE A`.

**(d)** `mem_L_iff_logspace` from `logspace_of_L` and `ToLogspace.logspace_subset_L`; `RL` and `BPL`
by rewriting with `exact_logarithmic_space_derandomization`.

## Gates

`lake build`, `scripts/check_manifest.py`, `scripts/check_sorry.py`, `scripts/check_closure.py`,
`scripts/goal_state.py validate`, `scripts/pack_gate.sh HEAD`.

## Notes

No existing module was edited except `Start.lean` and `Start/Capstones.lean` (imports and
registration of the four new modules, as required).  The module docstring of the existing
`Start/LogspaceTransferRandomized.lean` still says the converse is not claimed there; it was left
unchanged.

## Also in this delivery (after the objective)

* `M23-LAMBDAPI-EMBED` (closed): `Start/PTSLambdaPiEmbed.lean`, evidence
  `docs/goal/evidence/M23-LAMBDAPI-EMBED.md`; `M23-PTS` set back to `DONE_STRONG`.
* `M23-FOMEGA` (still open): kind and constructor classification in `Start/PTSFOmegaKinds.lean`,
  evidence `docs/goal/evidence/M23-FOMEGA.md`.
