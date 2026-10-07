# M21 — `PSPACE ⊆ IP` (rows `M21-SUMCHECK-REPLAY`, `M21-SUMCHECK-COINS`, `M21-VERIFIER-STEP-COB`, `M21-VERIFIER-POLY`, `M21-TQBF-IN-IP`, `M21-PSPACE-SUBSET-IP`)

**Status:** DONE_STRONG for all six rows.

## Terminal statements (`Start/ShamirIP.lean`)

```lean
theorem Complexity.Shamir.shamirV_promise (q : QBF) (hc : q.Closed) :
    (TQBF q → ∃ P : Prover, (2 : ℚ) / 3 ≤ shamirV.accProb P (QBF.enc q)) ∧
    (¬ TQBF q → ∀ P : Prover, shamirV.accProb P (QBF.enc q) ≤ 1 / 3)
theorem Complexity.Shamir.pspace_subset_ip {L : Language} (h : Space.PSPACE L) : IP L
theorem Complexity.Shamir.tqbf_in_ip : IP tqbfLang
```

`#print axioms` for `pspace_subset_ip` and `tqbf_in_ip`: `propext, Classical.choice, Quot.sound`.

## Row by row

- **`M21-SUMCHECK-REPLAY`** — `Start/ShamirMachine.lean` (the machine `Complexity.Shamir.stepW` on
  eight words: rest of the code, linearization counter, point, claim, stack, two flags, rest of
  the transcript), `Start/ShamirSim.lean`, `Start/ShamirReplay.lean`
  (`Complexity.Shamir.replays_toOp`, `Complexity.Shamir.sim`: after `K ≥ size (toOp N q)` steps
  the rejection flag is empty iff `Complexity.Qbf.run` accepts), `Start/ShamirBound.lean`
  (`Complexity.Shamir.Inv.step`, `Complexity.Shamir.inv_iterate`,
  `Complexity.Shamir.Inv.length_le`: every reachable state is polynomially long, whatever the
  transcript).
- **`M21-SUMCHECK-COINS`** — `Start/CoinDecode.lean` (`Complexity.decP`, `Complexity.fiber_le`,
  `Complexity.sumL_blocks_le`, `Complexity.cntL_blocks_le`); the transfer is used in
  `Start/ShamirSoundness.lean` (`Complexity.Shamir.accProb_shamirV_le`) and completeness transfers
  exactly in `Start/ShamirComplete.lean` (`Complexity.Shamir.accProb_shamirV_complete`, probability
  `1`).  Deviation from the wording of the first exit criterion: only the upper bound
  `2^K/p + 1` on the number of preimages of a residue is proved (`fiber_le`); the lower bound
  `⌊2^K/p⌋` is not needed by the soundness or completeness argument and is not formalized.
- **`M21-VERIFIER-STEP-COB`** — `Start/ShamirCob.lean` (`Complexity.Shamir.eval_stepTs`: eight
  Cobham terms compute the step on every state), `Start/ShamirIter.lean`
  (`Complexity.Shamir.eval_stepPT`, `Complexity.Shamir.eval_iterT_run`,
  `Complexity.Shamir.length_packW_le`).
- **`M21-VERIFIER-POLY`** — `Start/ShamirVerifier.lean`, `Start/ShamirAsk.lean`: the verifier
  `Complexity.Shamir.shamirV` is a `Complexity.Verifier`, i.e. five Cobham terms, so polynomial
  time by construction; `Complexity.Shamir.eval_decideT`, `Complexity.Shamir.accepts_shamirV`,
  `Complexity.Shamir.transcript_shamirV`.  The final evaluation of the arithmetized matrix is part
  of the machine's variable step, computed by the same terms.
- **`M21-TQBF-IN-IP`** — `Complexity.Shamir.tqbf_in_ip`.
- **`M21-PSPACE-SUBSET-IP`** — `Complexity.Shamir.pspace_subset_ip`.  Route: a polynomial-space
  language is decided by a machine (`Complexity.Space.npspace_of_pspace`); the Savitch-style
  reduction `Complexity.Qbf.QBF.redTerm` writes the code of a closed formula that is true iff the
  input is in the language (`Complexity.Qbf.QBF.tqbf_machineFk_iff`,
  `Complexity.Qbf.QBF.closed_machineFk`), and Shamir's verifier is run on that output
  (`Complexity.Verifier.precomp`).  So the verifier need only be correct on codes of closed
  formulas, and no code validation is needed.

## Gates

`lake build` (whole library), `python3 scripts/check_sorry.py`, `python3 scripts/check_closure.py`,
`python3 scripts/goal_state.py validate`.
