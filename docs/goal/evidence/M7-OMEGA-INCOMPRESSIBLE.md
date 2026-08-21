# M7-OMEGA-INCOMPRESSIBLE

**Status:** DONE_STRONG

Module `Start/OmegaIncompressible.lean`, imported by `Start.lean`.

* `Lambda.omegaPrefix n = Nat.pair n (omegaBits n)` — the first `n` bits of `Ω`, tagged with
  their number, as a single natural number.
* `Lambda.dodge` — one partial recursive procedure (`Lambda.partrec_dodge`) which, fed
  `omegaPrefix n`, terminates and returns a number that no closed program of at most `n - 2`
  bits produces (`Lambda.dodge_spec`).  It is a double `Nat.rfind`:
  * the first search finds a stage `k` certified by the oracle bits, by which every program of
    at most `n - 2` bits that halts at all has halted (`Lambda.StageOk`,
    `Lambda.exists_stageOk`, computability by `Lambda.primrec_stageOk`);
  * the second search finds the least value not produced within `k` leftmost steps by any code
    below `Lambda.encBound n` (`Lambda.Forbidden`, `Lambda.exists_not_forbidden`,
    computability by `Lambda.primrec_forbidden`).
* `Lambda.forbidden_of_isProgramFor` — at such a stage every closed program of at most `n - 2`
  bits has already produced its value, so the dodging value has no such program.
* `Lambda.exists_const_le_kolmP_omegaPrefix : ∃ c, ∀ n, n ≤ kolmP (omegaPrefix n) + c` —
  **Chaitin's incompressibility theorem.**  Prefixing a shortest program for `omegaPrefix n`
  with a fixed closed realizer of `Lambda.dodge` costs only a constant number of bits, so a
  short program for `omegaPrefix n` would give a short program for a number that has none.

Two auxiliary computability lemmas of independent use are proved here:
`Lambda.primrecPred_exists_lt` and `Lambda.primrecPred_forall_lt`, bounded quantifiers over an
arbitrary `Primcodable` parameter (Mathlib's `PrimrecRel.exists_lt` / `forall_lt` only allow a
single `ℕ` parameter).

Gates: `lake build` succeeds; no `sorry`; no linter warnings;
`#print axioms Lambda.exists_const_le_kolmP_omegaPrefix` reports only
`propext, Classical.choice, Quot.sound`.

## Boundary

This is the *incompressibility* half of the algorithmic randomness of `Ω`.  It is **not** the
same as Martin-Löf randomness of `Ω` (see `M7-OMEGA-ML-RANDOM`): deriving ML randomness from
incompressibility is the Levin–Schnorr theorem, which additionally needs a measure-theoretic
layer and a genuinely *universal* prefix machine.  The machine used in this project — closed
λ-terms under the `Lambda.bits` self-delimiting code, with no input stream — is not additively
universal, so Levin–Schnorr is not available from the present statement alone.
