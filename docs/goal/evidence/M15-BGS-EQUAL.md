# M15-BGS-EQUAL: P^TQBF = NP^TQBF = PSPACE

**Status:** DONE_STRONG (2026-10-30)

Baker, Gill and Solovay's collapsing oracle is a PSPACE-complete language. Here it is `TQBF`.
The library already had a collapsing oracle, `Complexity.bgs_equal` in
`Start/CollapsingOracle.lean`, built by a self-referential construction. This row needs the
classical one.

## What is built

### `Start/OracleElimSpace.lean`

`Complexity.Space.Elim.compileT` compiles an oracle Cobham term (`CobQ`) into a *plain* tape
program. The query becomes a subprogram `G a d fr`, called a gadget. A gadget sets register `d` to
the oracle's answer on register `a`, using scratch registers from `fr` on.

- `GadgetOK A G q T K x B` is the specification of a gadget. It uses `q` scratch registers and at
  most `(T N + 3)(2K + 1)` cells.
- `compileTOK` is the correctness theorem. It holds for every monotone `T` above the identity.
  The compiled program of `c` computes `CobQ.eval A c` within `(T (spaceW c N) + 3)(2K + 1)` cells.
- The proofs are those of `Start/OracleCobSpace.lean`, carried over to plain programs.

### `Start/OracleElimGadget.lean`

`iterGadget` runs the iteration of `Start/CobhamIterate.lean` on the registers from `fr` on, applied
to the query word:
1. copy the query;
2. compute the initial state;
3. loop with `iterBodyAt`;
4. write `[true]`/`[]` into the target register;
5. clear the scratch registers.

`gadgetOK_iter` shows that the iteration is a gadget for any language decided by `pspace_of_cobIter`
data with a monotone bound. Its space function `gadgetT` is polynomial.

### `Start/BgsTqbf.lean`

- `pspace_of_inNP_rel_gadget` proves `NP^A ⊆ PSPACE` for every oracle `A` that has a gadget of
  polynomial space. It uses the witness loop of `Start/OracleNPSpace.lean`, with the verifier
  compiled by `compileT`. No oracle machine remains.
  - In Cobham's model, enumerating the witnesses deterministically suffices; Savitch is not needed.
    The first exit criterion was corrected to say so.
- `tqbf_gadget` gives `TQBF` a gadget: the evaluator iteration of `Start/QbfEvalCob.lean`
  (`Qbf.tqbf_iter`).
- `inP_rel_tqbf_of_pspace` proves `PSPACE ⊆ P^TQBF` with one query on the reduction
  `pspaceHard_tqbfLang'`.
- **`bgs_equal_tqbf`**: `InP_rel tqbfOracle L ↔ InNP_rel tqbfOracle L` and
  `InNP_rel tqbfOracle L ↔ PSPACE L`.
- `peqNP_rel_tqbf`: `PeqNP_rel tqbfOracle`.

## Gates

- Each module was type-checked as a single file.
- `goal_state.py validate`, `check_closure.py`, `check_unification.py --strict` and `check_sorry.py`
  all pass.
- CI runs `lake build --wfail`.
