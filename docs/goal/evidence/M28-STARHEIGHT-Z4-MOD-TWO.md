# M28-STARHEIGHT-Z4-MOD-TWO: the `Z₄` core modulo 2

Lean: `Start/StarHeightZ4ModTwo.lean`, no `sorry`, axioms in `M28-STARHEIGHT-Z4-MOD-TWO-axioms.txt`
(`propext`, `Classical.choice`, `Quot.sound`).  Computations (Python, not Lean):
`M28-STARHEIGHT-Z4-MOD-TWO-search/`.

## 1. The identity (`vcount_z4_mod_two`)

`δ : α → ZMod 4`, `red = ZMod.castHom (2 ∣ 4) (ZMod 2)`, `δ₁ y = if δ y = 2 then 0 else δ y`,
`δ₂ y = red (δ y)`, `δ₃ y = (red (δ y), if δ y = 2 then 1 else 0)`.  For all `q, x, w`, in `ZMod 2`:

    vcount δ q x w = vcount δ₂ (red q) x w + vcount δ₁ (q + 2) x w + vcount δ₃ (red q, 1) x w

Proof: the state is `s = R + 2C` (`R` the `δ₁`-walk, `C ∈ ZMod 2` the parity of the rotation-2
letters read).  Induction on `w` from arbitrary states `(r, c)` (`vcountFrom_z4_mod_two`): one
letter keeps `s = r + 2c`, maps `red r` to the `δ₂`-walk and `(red r, c)` to the `δ₃`-walk; the
pointwise identity `[r + 2c = q] = [red r = red q] + [r = q + 2] + [(red r, c) = (red q, 1)]` in
`ZMod 2` is checked by `decide` over the 64 triples (`indicator_z4_mod_two`).

## 2. Corollaries

- `vcount_z4_mod_two_height`: every `vcount δ q x` on `ZMod 4`, every state `q`, has height ≤ 1
  modulo 2: the three terms are good (`vcount_height_one_prime` on `ZMod 2` and `ZMod 2 × ZMod 2`;
  `vcount_z4_height_no2`, which already handles every state), and `height_one_of_residues`.
- `z4core_mod_two` (state 0, the statement asked for) and `z4Rot2Abc_mod_two`: the case `n = 2` of
  `Z4CoreRot2` and of `Z4Rot2Abc`, open since the F20 round.
- `height_one_of_abelian_cyclic_index_four_two`: `N` abelian normal, `x * x = 1` on `N`, index 4,
  cyclic quotient.  Same assembly as `height_one_of_abelian_cyclic_index_four` (unchanged), with
  counts modulo 2: `valN` only sees residues modulo 2 (`valN_mod_card`, `valN_mod_two`, already in
  `StarHeightA4Core.lean`).
- `height_one_of_exponent_two_kernel` (R3 (c), proved): for any finite `G`, `N` abelian normal of
  exponent 2 and `T`: if the fibres `{w | ψ w = q}` of the walk in `G ⧸ N` and the residues modulo 2
  of its letter-in-state counts `(tpairs N T 1 w).count (q, a)` have height ≤ 1, every `T⁻¹ F` has
  height ≤ 1.  The hypothesis is about the regular automaton of `G ⧸ N` only.
- `height_one_Z2_wr_Z4`: `Z2WrZ4 = Multiplicative (ZMod 4 → ZMod 2) ⋊[z2shiftHom] Multiplicative
  (ZMod 4)`, `(e·g) i = g (i − e)`, order 64 (`Z2WrZ4.card`, by `rfl`); kernel `base` of the
  projection: abelian, exponent 2, index 4, cyclic quotient.

## 3. Why `Z₂ ≀ Z₄` was not covered before

Checked by `wreath_facts.py` (output `wreath_facts_output.txt`); all three claims of the brief hold:

- nilpotency class 4 (lower central series `64, 8, 4, 2, 1`); so it does not divide `UT₄(Z/n)`
  (class 3, `height_one_UT4`);
- Frattini subgroup `G²[G,G]` of order 16, non-abelian: `height_one_of_frattini_abelian` does not
  apply.  It does not divide `A ⋊ (Z₂)ⁿ`, `A` abelian (PST 1992): a divisor `H/K` has the abelian
  normal subgroup `(H ∩ A)K/K` with elementary abelian quotient, which contains the Frattini
  subgroup, so the Frattini subgroup would be abelian;
- its 3 subgroups of index 2 are non-abelian: no abelian subgroup of prime index
  (`height_one_of_abelian_prime_index` does not apply).  Also: order 64 (not `< 24`), a 2-group
  (the exponent-3 theorems do not apply), centre of order 2, element orders `{1:1, 2:19, 4:28, 8:16}`.

`height_one_of_abelian_cyclic_index_four` covers it only under the open `Z4CoreHeightOne`, and
`..._of_letters` only when the letters avoid one class of the quotient.

Bourne's Question 5.8 for `r = 4` (`AbGrp ∗ Z₄`): this answers it when the abelian group has
exponent 2 (abelian-by-cyclic-of-order-4 with kernel of exponent 2).  Nothing more is claimed.

## 4. R3: how far the characteristic-2 trick goes

Method (`r3_span.py`, output `r3_span_output.txt`): a count `Σ_{u_i = x} g(n(u.take i))` determines
its weight `g`, so linear relations between counts are linear relations between weights; all
weights are 2-power periodic (odd periods drop out by summing over odd shifts), so the test is
exact on the torus `(Z/M)^α`, done for `M = 8` and `M = 16` (same deficiencies).  Pieces: parity
automata, `pcount` with fixed counted letter (every `p`), `pcount` moving for `p = 4`, `Z₄` walks
without rotation 2 or with rotations in `{0, 2}`, and (modulo 2 only) every `Z₄` walk (R1).
Control: `Z4Rot2Abc` modulo 2 with the R1 pieces removed has deficiency 0 (the identity of §1).

- **(a) `Z₈` modulo 2: no.**  `a:1, x:0` is covered (`pcount`, `p = 8`), but `a:1, b:2`,
  `a:1, b:3` and `a:1, x:1` (moving) have deficiency 4, and `a:1, c:4` deficiency 2.  The R1-type
  expansion `s = R + 4C` (`C` = parity of the rotation-4 letters) gives
  `[s = q] ≡ [R ≡ q (4)] + [R = q + 4] + [R ≡ q (4)]·C`; the first term is a `Z₄` walk (R1), the
  second a `Z₈` walk with fewer rotations, and the **first term not covered is the third**, the
  count of `x` at `(R ≡ q mod 4, C odd)` on `Z₄ × Z₂`.  `z8core_mod_two` is not proved.
- **(b) `Z₄ × Z₂` modulo 2: confirmed to fail** (linearly).  For `a:(1,0), c:(0,1), x:(0,0)`, the
  count of `x` at `(r, 1)` has deficiency 1 for each `r`, and the 8 states together deficiency 2
  (also with `x` moving, `x:(1,1)`).  **`Z₄` modulo 4: fails too**: for `Z4Rot2Abc` (pieces good for
  every modulus, R1 excluded) the index of the `Z/4`-span of the pieces in the span with the target
  is 2 (log₂-deficiency 1): twice the target is in the span (that is R1), the target is not.
  Only linear determination was tested; a functional (Boolean) determination was not.
- **(c)** Proved in Lean as `height_one_of_exponent_two_kernel` (§2).  Quotients `Q` for which the
  hypothesis (letter-in-state counts of `Q` modulo 2, and the fibres) is now known: `(Z/2)ʳ`
  (`vcount_height_one_prime`), `Z/p` for odd `p` (`zpcore`), `Z/4` (R1).  Not `Z/8`, not
  `Z/4 × Z/2` (by (a), (b) not reachable by this expansion).
- **(d)** No shear search was run.
