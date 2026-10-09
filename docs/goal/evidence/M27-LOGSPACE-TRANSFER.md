# M27 — host logarithmic space and the upstream class `L`

Tasks `M27-SPACE-MODEL-COMPILE`, `M27-SPACE-MODEL-TOTALIZE`, `M27-LOGSPACE-TRANSFER`.

## Host → upstream (proved)

`Start/LogspaceFinState.lean`, `Start/SpaceToLogspace.lean`, `Start/SpaceToLogspaceStep.lean`,
`Start/SpaceToLogspaceRun.lean`, `Start/SpaceToLogspaceTransfer.lean`,
`Start/LogspaceTransferRandomized.lean`:

* `Complexity.Space.ToLogspace.compile M k` — a concrete finite-control machine of the upstream
  `ExactDerandomization.Machine` model: work tape 0 copies the host work tape, work tape 1 marks
  the origin, input head 0 follows the host head, input heads `1..k` form an odometer clock in
  base `n + 2` using no work cells.  Every host transition is simulated by a bounded macro step
  of target transitions; no source transition is evaluated for free.
* `compile_decides` — the compiled machine halts on every input and decides the host language
  (expiry of the clock proves rejection, since an accepting run can be shortened below the
  configuration bound `cfgBound`).
* `compile_spaceThrough` — every intermediate configuration uses at most `2 s(|x|)` work cells.
* `cfgBound_le_clock` — `k = clockLen Q a = Q (a+1)² 2^a + a + 3` suffices for space bound
  `a (log₂ (n+1) + 1)`.
* `logspace_subset_L : LOGSPACE A → {x | A x} ∈ ExactDerandomization.L` (space constant
  `2a + 1`), and `logspace_subset_RL`, `logspace_subset_BPL` via the absorbed equality
  `exact_logarithmic_space_derandomization`.

## Upstream → host (open)

The converse `ExactDerandomization.L ⊆ LOGSPACE` is not proved.  The first missing construction
is a host tape program (in `Start/SpaceProg*.lean`) that stores the positions of several upstream
input heads as binary counters on the one-sided host work tape and repositions the single host
input head from such a counter (binary increment/decrement and a counted input scan), together
with a track layout for several two-sided upstream work tapes.  `SpaceProgTracks` has
clear/assign/prepend/append/popBranch/whileNE/copyInput but no binary counter primitive.

### Progress on the converse

Built (all sorry-free and in the import closure):

* `Start/SpaceProgCounter.lean` — `Tracks.ifNE`, `Tracks.whileNE` rules with a moving input head,
  bijective base-two counters `Tracks.bval`, `Tracks.incr`/`Tracks.decr`, and
  `Tracks.seekCounter` (moving the input head to a counted position);
* `Start/SpaceProgDispatch.lean` — `Tracks.seqFor`, `Tracks.appendN`, `Tracks.caseUnary`,
  `Tracks.readAll`;
* `Start/LogspaceToSpaceTape.lean` — a two-sided tape in the window `[-W, W]` held in two
  registers, `Tracks.tapeOp` with `Tracks.runs_tapeOp`;
* `Start/LogspaceToSpace.lean` — the register-file encoding `FromLogspace.encR`;
* `Start/LogspaceToSpaceStep.lean` — `runs_setState`, `runs_setFlags`, `runs_tapesOp`,
  `runs_headsOp`: the phases of one simulated transition.

Missing: the program for one full transition (read the symbols, dispatch, run the phases), its
specification on `encR`, the loop over the run, and the logarithmic bound on the registers.
