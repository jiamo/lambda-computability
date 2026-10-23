# M28-STARHEIGHT-S3-CORE: the S3-core and the count K3

Earlier evidence for this row (searches for good automata, the modulus-2 instance `PST.K`) is in
`M28-STARHEIGHT-PST-HEIGHT-ONE.md`, `M28-STARHEIGHT-S4-AUX-SEARCH.md` and
`M28-STARHEIGHT-LIFT-R3R4.md`.

## Big round 2, run 4

Item S1 of big round 2. The target is still open, and this run adds a Lean-checked barrier.

`Start/StarHeightK3Metabelian.lean`, namespace `GeneralizedStarHeight.PST`:

- `k3Perm w : Equiv.Perm (Fin 3 × ZMod 3)` is the action of `w` on (state, count modulo 3).
  `k3Perm_apply` says that it sends `(s, c)` to `(stateOf s w, c + b0count s w)`.
- `k3_doubleCommutator` (`decide`): `⁅⁅k3Perm [b,b], k3Perm [a]⁆, ⁅k3Perm [b], k3Perm [a]⁆⁆` is
  the shift `c ↦ c + 2` in every state.
- `K3_not_recognized_metabelian`: let `Γ` be a finite group with `⁅⁅g₁, g₂⁆, ⁅g₃, g₄⁆⁆ = 1` for
  all `gᵢ`. Then no `T : FreeMonoid AB →* Γ` and `F` give `{w | b0count 0 w % 3 = k} = {w | T w ∈ F}`,
  for any `k < 3`. `K3_not_recognized_of_derivedSeries_two` states the same with
  `derivedSeries Γ 2 = ⊥`.

Proof. Let `M = |Γ| · |Perm (Fin 3 × ZMod 3)|`. Then `x^(M-1)` acts as `x⁻¹` both in `Γ` and on
(state, count), so the double-commutator word `W` on `a, b, a, bb` maps to `1` in `Γ`. On the
other hand, it adds `2` to the count from every state. So `(bb)^k W` and `(bb)^k` are identified
by `Γ`, but their counts are `k + 2` and `k` modulo 3.

### What it rules out

The transition group of `K3` is `Z₃ ≀ S₃` (order 162). Its derived length is 3:
`G' = Z ⋊ A₃` and `G'' = D`, the diagonal. The proof above shows directly that no metabelian
group recognizes `K3`.

Every group with an unconditional `GroupHeightOne` instance in M28-STARHEIGHT-GROUP-HEIGHT-ONE
is metabelian. These are: abelian groups; groups with an abelian normal subgroup of prime index;
`A₄`; `Z₂ ≀ Z₄`; `UT4 n`; groups whose commutator-and-`p`-th-power subgroup is abelian; and
abelian exponent-2 normal subgroups by `Z₄`. Metabelian groups are closed under products and
divisors. So the route through `GroupHeightOne.of_dvd_pi` cannot prove `K3`. (This classification
of the instances is a reading of their hypotheses, not a Lean statement.)

A proof of height one for `K3` needs an observer whose transition group is not metabelian. For
`PST.K` this role is played by the `S₄` automaton `s4state`, which has star-free first returns.
Height one itself is neither proved nor refuted: the theorem is about recognizers, not about
star height.

Axioms: `M28-STARHEIGHT-S3-CORE-axioms.txt` (propext, Classical.choice, Quot.sound).

First missing lemma (unchanged):
`theorem GeneralizedStarHeight.PST.K3_height_one (k : ℕ) (hk : k < 3) : HasHeightAtMost {w : List AB | PST.b0count 0 w % 3 = k} 1`.

## Big round 2, run 7 (rebuilt)

The module of run 4 was lost with the old project (its file was written with the file tool, so the
command log does not record it). Run 7 wrote it again from this note and run 4's final message,
with the same terminal theorem names; it builds with `lake build --wfail`, standard axioms only
(regenerated with `#print axioms`, section "Big round 2, run 7" of the axioms file).
