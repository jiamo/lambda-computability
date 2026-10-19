# M28-STARHEIGHT-CORE-MOD-TWO: the core modulo 2, and the order-8 cores

Lean: `Start/StarHeightCoreModTwo.lean`, `Start/StarHeightOrderEightCores.lean`, no `sorry`, axioms
in `M28-STARHEIGHT-CORE-MOD-TWO-axioms.txt` (`propext`, `Classical.choice`, `Quot.sound`).
Computations (Python, not Lean): `M28-STARHEIGHT-CORE-MOD-TWO-search/`.

## R1 (a) Framework

`HCoreModTwo H`: every `hcount ρ g x` of `H` has height ≤ 1 modulo 2 (for `k < 2`).
`HCoreHeightOne.modTwo`, `HCoreModTwo.of_mulEquiv`, `HCoreModTwo.univ` (any universe).
`hcoreModTwo_zmod_four` (from `vcount_z4_mod_two_height` and `hcount_ofAdd_eq_vcount`),
`hcoreModTwo_zmod_prime p` (from `hcore_zmod_prime`).

## R1 (b) The reduction

`height_one_of_exponent_two_normal_of_core_mod_two` (and `_equiv` with `G ⧸ N ≃* H`): `N` abelian,
normal, `x * x = 1` on `N`, `HCoreModTwo (G ⧸ N)` ⇒ every language recognized by `G` has height ≤ 1.
Proof of `height_one_of_abelian_normal_of_core_equiv` with modulus 2 instead of `2·|N|`: `valN`
needs the counts mod 2 (`valN_mod_card`, then `valN_mod_two`), and the flow identity recovers the
final state from the same counts mod 2.  No hypothesis on the fibres of the walk (unlike
`height_one_of_exponent_two_kernel`).

- `height_one_S4_of_core_mod_two`: the Klein kernel has exponent 2 (`S4Klein.ker_sq`, `decide` on
  `kx`), so every `S₄` language follows from `HCoreModTwo (Perm (Fin 3))`.  This weakens
  `height_one_S4_of_core` from every modulus to modulus 2.  The smallest open `S₃`-core instance
  on the board, `K3`, is a count modulo 3: `S₄` does not need it.
- (e) `height_one_of_central_order_two_of_core_mod_two`: `N` central of order 2, `G ⧸ N ≃* H`,
  `HCoreModTwo H` ⇒ every `G`-language.  `height_one_of_central_order_two_over_A4_of_core_mod_two`
  is the case `H = alternatingGroup (Fin 4)`, which covers `SL(2,3)` (centre `{±1}`, quotient `A₄`).
  The isomorphism `SL(2,3) ⧸ Z ≃* A₄` itself is not formalized.

## R1 (c) `aabb` on `Z₄ × Z₂`

- `scount_aabb_eq_psum` (exact, `a ≠ b`): `scount [a,a,b,b] u = Σ_{i : u_i = b} C(A_i,2)·(|u|_b − 1 − B_i)`.
- `scount_aabb_cast_z4z2`: mod 2, `scount [a,a,b,b] u ≡ (|u|_b + 1)·scount [a,a,b] u + hcount ρ g₁ b u
  + hcount ρ g₂ b u`, `ρ = aabbRho a b` (`a ↦ ofAdd (1,0)`, `b ↦ ofAdd (0,1)`, else `1`) into
  `Multiplicative (ZMod 4 × ZMod 2)`, `g₁ = ofAdd (2,1)`, `g₂ = ofAdd (3,1)`.  Induction on `u`;
  the prefix product is `ofAdd (A mod 4, B mod 2)` (`prod_aabbRho`), and the step is the 8-case check
  `z4z2_indicator`.
- `aabb_mod_two_iff_z4z2` (over `Fin 2`) and `goodMod_aabb_iff_z4z2` (any finite alphabet).
- `aabb_mod_two_of_core` and `height_one_two_letters_length_four_mod_two_of_core`: from
  `HCoreModTwo (Multiplicative (ZMod 4 × ZMod 2))`, every two-letter word of length 4 mod 2 (bbaa
  through `goodMod_xxyy_iff`).

## R1 (d) `abac` on `Z₂ ≀ Z₂ ≅ D₄`

`Z2WrZ2 = Multiplicative (ZMod 2 → ZMod 2) ⋊[z2shiftHom2] Multiplicative (ZMod 2)`, `card = 8`
(`rfl`); it is `D₄` by its element orders (`order8_table.py` (C); no Lean isomorphism).
`abacRho a b`: `a ↦ ⟨1, ofAdd 1⟩`, `b ↦ ⟨ofAdd (Pi.single 0 1), 1⟩`, else `1`.  The prefix product
is `⟨(i ↦ #b read at |·|_a ≡ i), |·|_a⟩` (`prod_abacRho`).  `cpair_abac_cast_wreath`: mod 2,
`cpair (parCol a) b c 1 0 u ≡ hcount ρ ⟨f₀₁,1⟩ c u + hcount ρ ⟨f₁₁,1⟩ c u` (only `a ≠ b` needed).
`abac_mod_two_iff_wreath` (over `Fin 3`, via `cpair_mod_two_iff_abac`) and `abac_mod_two_of_core`.

**Result.** Every open case at `p = 2` that we track reduces to `HCoreModTwo` of a small group:
`Z₄ × Z₂` (order 8): `aabb`; `Z₂ ≀ Z₂ ≅ D₄` (order 8): `abac` and the shear (`shear_mod_two_iff_abac`);
`S₃`: every `S₄` language; `A₄`: every central extension of `A₄` by `Z₂`, e.g. `SL(2,3)`.

## R3 (a) The `aabb` search, reproduced

`autosearch.py` is the script of the brief, verbatim except that the timing column is dropped.
`python3 autosearch.py aabb 7` → `autosearch_aabb_7_output.txt`: `H-states 8192 paired 8192`;
`n = 2..7`: pairs `4, 24, 168, 1440, 13680, 151200`, good `3, 10, 39, 171, 830, 4503`, hits 0 each
time.  Identical to your output.  `python3 autosearch.py abab 5` → `autosearch_abab_5_output.txt`:
`paired 0`, hits = good (`3, 10, 39, 171`) at every `n`: the positive control behaves as expected.
So no transitive permutation automaton on ≤ 7 points with star-free first returns at 0, together
with every count mod 2 of words of length ≤ 4 other than `aabb`, `bbaa`, determines `L(aabb, k, 2)`.

## R3 (b) The order-8 table (computational evidence, `order8_table.py`)

The non-cyclic groups of order 8 are the central extensions of `V₄` by `Z₂` with bilinear cocycle
`β`: `0` (`Z₂³`), `x₁y₁ + x₂y₂` (`Z₄ × Z₂`), `x₁y₂` (`D₄`), `x₁y₁ + x₁y₂ + x₂y₂` (`Q₈`) (checked by
element orders, (A)).  A prefix product is `(s, z)` with `z = Σ_{k<j} β(δ_k, δ_j) + Σ ε` (lifts),
additive in `β`; `[z = c] ≡ 1 + c + z`.

| group | `HCoreModTwo` | reductions |
|---|---|---|
| `Z₂³` | proved (`HCoreHeightOne` of `(Z/2)³` by `vcount_height_one_prime`; not restated) | — |
| `Z₄ × Z₂` | open (`aabb` reduces to it, Lean) | — |
| `D₄ = Z₂ ≀ Z₂` | open (`abac` reduces to it, Lean) | — |
| `Q₈` | open | `Q₈ ⟸ D₄ + Z₄ × Z₂`: `z_Q8 = z_D4 + z_{Z4×Z2}` (3000 random words, 0 mismatches, (B)); any two of the three types give the third, mod 2 |
| `Z₈` | open | `Z₈ ⟸ Z₄ (proved) + Z₄ × Z₂ + Z₈-walks without rotation 4` |

`Z₈`: with `s = R + 4C` (`R` the walk with the rotation-4 letters set to 0, `C` their parity),
`[s = q] ≡ [R ≡ q mod 4] + [R = q + 4] + [R ≡ q mod 4]·C` (all 128 cases, (D)).  The first term is
a `Z₄` walk (proved), the third a `Z₄ × Z₂` walk; the second is a `Z₈` walk with fewer rotations
(no letter `4`), which `Z₄ × Z₂` does not give.  So `HCoreModTwo (Z₄ × Z₂)` alone does not give
`Z₈` by this expansion; the extra piece is the rotation-free-of-4 `Z₈` walk.  `Q₈` (centre `Z₂`,
quotient `V₄`) reduces to `D₄` and `Z₄ × Z₂` together.  None of these reductions is in Lean.

## R3 (c) Derived lengths (`derived_table.py`)

For all 15 classes, `|G|, |G'|, |G''|, |Z|`, whether the rows/columns span (the separation step of
the barrier) and the central involutions flipping the count.  `|G''| = 2`: `abac` (128),
`abbc` (512), `abcb` (128), `abcd` (1024), `abca` (512, `|Z| = 4`, 1 of 3 involutions flips);
every other class has `G'' = 1`, e.g. `aabb` (256, `|G'| = 16`), `abab` (16).  See
`M28-STARHEIGHT-LIE-BARRIER.md`.
