# M13-SAVITCH-SPACE — Savitch's theorem

`Start/SavitchSpace.lean` instantiates the stack machine of `M13-SAVITCH-VM` at the configuration
graph of `M13-SPACE-CONFIG-COUNT`.

## The depth

* `Complexity.Space.savitchDepth M x s = Nat.clog 2 (cfgBound M x s)` — the depth of the
  recursion.  It is also the number of bits one configuration takes, since the configurations
  inject into `{0, …, 2 ^ savitchDepth - 1}`.
* `Complexity.Space.card_le_two_pow_savitchDepth` — at that depth the recursion decides
  reachability.
* `Complexity.Space.savitchDepth_le` —
  `k ≤ log₂ q + log₂ (n+1) + 2 log₂ (s+1) + s`, proved from the submultiplicativity of `clog`.

## The theorem

* `Complexity.Space.savitchDecide` — the decision: some accepting configuration is reachable from
  the initial one by the midpoint recursion of depth `k`.
* `Complexity.Space.savitch_accepts_iff` — it is correct: it answers `true` exactly on the inputs
  the nondeterministic machine accepts.
* `Complexity.Space.savitch_trace` — each of its reachability queries is run by the deterministic
  stack machine, which never holds more than `k` activation records.
* `Complexity.Space.savitch_memBits_le` — hence each query runs in `(k + 1) · (4 k + 3)` bits,
  which with the bound on `k` is `O((s + log n)²)`: Savitch's `O(s²)`.
* `Complexity.Space.savitch_poly_memory` — for a language in `NPSPACE` the memory the simulation
  uses is bounded by a polynomial in the length of the input.

## Honest boundary

The deterministic simulation is exhibited on the stack machine of `Start/SavitchVM.lean`, and its
memory is counted in bits of activation records.  Compiling that machine into an offline Turing
machine of `Start/SpaceMachine.lean` — the routine, laborious half of the model-independence of
space — is **not** formalized, so the development does **not** claim `NPSPACE = PSPACE` as a
theorem about `Complexity.Space.DSPACE`, and the PSPACE-completeness of TQBF, which would need a
generic reduction from a space-bounded machine to a quantified Boolean formula, is not formalized
either.  Both are recorded here and in the module documentation rather than being implied by the
statements that are proved.

## Gates

`lake build`, `python3 scripts/check_closure.py`, `python3 scripts/goal_state.py validate`.
`#print axioms Complexity.Space.savitch_poly_memory` reports only `propext`, `Classical.choice`,
`Quot.sound`.
