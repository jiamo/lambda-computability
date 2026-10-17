# M28-STARHEIGHT-Z4: abelian-by-Z₄ groups and the Frobenius group F₂₀ (open: ROT2 only)

Rows: M28-STARHEIGHT-INDEX-FOUR (DONE_WEAK), M28-STARHEIGHT-Z4-CORE (DONE_WEAK),
M28-STARHEIGHT-Z4-CORE-ONE-ROTATION (DONE_STRONG), M28-STARHEIGHT-Z4-PM1 (DONE_STRONG),
M28-STARHEIGHT-Z4-ROT2 (open, head of the M28 queue).  The tool used for PM1,
Schützenberger's theorem, is M28-STARHEIGHT-APERIODIC (DONE_STRONG,
`docs/goal/evidence/M28-STARHEIGHT-APERIODIC.md`).

"Height" is generalized star height (`GeneralizedStarHeight.HasHeightAtMost`); "star-free" is
`HasHeightAtMost _ 0`.  `vcount δ q x w` (`Start/StarHeightBourne.lean`) is the number of positions
of `w` reading `x` in state `q` of the translation automaton with displacements `δ`, read from `0`.

## What is proved (lake build --wfail, no sorry, axioms propext, Classical.choice, Quot.sound)

Axioms: `docs/goal/evidence/M28-STARHEIGHT-Z4-axioms.txt` (earlier rows) and
`docs/goal/evidence/M28-STARHEIGHT-Z4-PM1-axioms.txt` (this delivery).

### Reduction to the Z₄ core (`Start/StarHeightIndexFour.lean`)

```
def Z4CoreHeightOne : Prop := ∀ (α : Type) [Fintype α] [DecidableEq α] (δ : α → ZMod 4) (x : α)
    (n k : ℕ), k < n → HasHeightAtMost {w : List α | vcount δ 0 x w % n = k} 1

theorem height_one_of_abelian_cyclic_index_four (hcore : Z4CoreHeightOne) [Finite Alphabet]
    {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hidx : N.index = 4) (hcyc : IsCyclic (G ⧸ N))
    (T : FreeMonoid Alphabet →* G) (F : Set G) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1

theorem height_one_F20_of_core (hcore : Z4CoreHeightOne) {Alphabet : Type u} [Finite Alphabet]
    (T : FreeMonoid Alphabet →* F20) (F : Set F20) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1
```

* `vcount_z4_height_of_core`: under the core, every state `q`, not only `0`: a fresh letter of
  displacement `-q` (alphabet `Option (Fin m)`), a left quotient and an inverse alphabetic morphism
  (`vcountFrom_map`, `vcountFrom_shift`).
* The group theorem is the assembly of `height_one_of_abelian_normal_exponent_three`, with
  `Additive (G ⧸ N) ≃+ ZMod 4` from `zmodAddCyclicAddEquiv` (`vcountFrom_hom` transports the counts).
* `F20`: the affine maps `x ↦ a·x + b` of `ZMod 5`, `a ∈ (ZMod 5)ˣ`, multiplication = composition
  (`F20.toFun_mul`); `F20.card : Fintype.card F20 = 20`, `F20.not_comm`; the translations
  `F20.transl` (kernel of the linear part) are abelian (`F20.transl_comm`), normal, of index 4
  (`F20.transl_index`), with cyclic quotient (`F20.quotient_isCyclic`, as `(ZMod 5)ˣ` is cyclic).

### The core with one nonzero rotation (`Start/StarHeightZ4Core.lean`)

* `z4core_rot01`: every letter has `δ ∈ {0, 1}`.  `vcount_eq_pcount` turns the count into `pcount`
  with `p = 4`.
  - fixed counted letter: `pcount_fixed_height_one` (PST Proposition 6.6; `Blang_height` needs only
    `2 ≤ p`);
  - moving counted letter: `pcount_moving_height_four`, from `Alang_height_four`.  On `(A⁴)∗`,
    `2·cnt₄(h) = cnt₂(h mod 2) + Σₜ cₜ·nₜ` with `cₜ = [t_h] − [t_{h+2}]` (`two_mul_pcount_four_eq`;
    `pcount_two_eq_four` splits the `Z₂` count).  `cnt₂` has height one (`Alang_height`, `p = 2`).
    `cₜ ≠ 0` gives `t_h ≠ t_{h+2}`, so `t` is primitive (`primitive_of_coef4_ne`, by cases) and the
    Transfer Lemma counts the `t`-blocks (`bmod_block_height_four`); the residues are combined as in
    `Vlang_eq` (`Vlang_four_eq`, modulus `2m`).
* `z4core_rot03`: `δ ∈ {0, 3}`, through the automorphism `q ↦ -q` (`vcountFrom_hom`).
* `z4core_rot02`: `δ ∈ {0, 2}` (the `Z₂` case, `pcount_height_one` with `p = 2`).

### The open cases, as propositions, and the conditional theorems

```
def Z4CoreRot2 : Prop := ∀ (α : Type) [Fintype α] [DecidableEq α] (δ : α → ZMod 4) (x : α) (n k : ℕ),
    k < n → (∃ y, δ y = 2) → (∃ y, δ y = 1 ∨ δ y = 3) →
      HasHeightAtMost {w : List α | vcount δ 0 x w % n = k} 1
def Z4CorePM1 : Prop := ∀ (α : Type) [Fintype α] [DecidableEq α] (δ : α → ZMod 4) (x : α) (n k : ℕ),
    k < n → (∀ y, δ y ≠ 2) → (∃ y, δ y = 1) → (∃ y, δ y = 3) →
      HasHeightAtMost {w : List α | vcount δ 0 x w % n = k} 1
def Z4Rot2Abc : Prop := ∀ n k : ℕ, k < n →
    HasHeightAtMost {w : List (Fin 3) | vcount (![0, 1, 2] : Fin 3 → ZMod 4) 0 0 w % n = k} 1

theorem z4core_of_rot2_pm1 (h2 : Z4CoreRot2) (h1 : Z4CorePM1) : Z4CoreHeightOne
theorem height_one_F20_of_rot2_pm1 (h2 : Z4CoreRot2) (h1 : Z4CorePM1) ... (T : FreeMonoid Alphabet →* F20) (F : Set F20) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1
lemma z4Rot2Abc_of_rot2 (h : Z4CoreRot2) : Z4Rot2Abc
```

F₂₀ needs both: `x ↦ −x` has rotation `2`, `x ↦ 2x` rotation `1`, `x ↦ 3x` rotation `3`.
`Z4CorePM1` is now proved (next section), so (`Start/StarHeightZ4PM1.lean`):

```
theorem z4core_pm1 : Z4CorePM1
theorem z4core_of_rot2 (h2 : Z4CoreRot2) : Z4CoreHeightOne
theorem height_one_F20_of_rot2 (h2 : Z4CoreRot2) {Alphabet : Type u} [Finite Alphabet]
    (T : FreeMonoid Alphabet →* F20) (F : Set F20) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1
```

## M28-STARHEIGHT-Z4-PM1 (rotations ±1, no rotation 2): DONE_STRONG

`theorem z4core_pm1 : Z4CorePM1` (`Start/StarHeightZ4PM1.lean`), with
`Start/StarHeightZ4Walk.lean`, `Start/StarHeightZ4Classes.lean`, `Start/StarHeightZ4Moving.lean`.
Alphabet `Fin 3`: letter `0` is the counted letter, `1` is `b` (+1), `2` is `d` (−1);
`σa = ![0, 1, 3]` (case (a), counted letter fixed) and `σm = ![1, 1, 3]` (case (m), counted
letter `a` moving by +1).  `zc σ 0 u` counts the letter `0` read in state `0`.

**Reduction** (`pm1_core_of_nonneg`, `vcountFrom_filterMap_zc`).  Neutral letters other than `x`
are erased and the ±1 letters other than `x` are merged into `b`, `d` by one inverse alphabetic
morphism `α → Option (Fin 3)`; if `δ x = 3`, `q ↦ −q` (`vcountFrom_hom`) gives `δ x = 1`.

**Walk automaton** (`Start/StarHeightZ4Walk.lean`).  `Xc σ` (first-return code to `0`), `NR σ`
(no nonempty prefix in state `0`) and the factorization `splitW σ u = (e₁ … e_r, t)`
(`splitW_spec`, `splitW_flatten`, `Xc_prefixCode`).  A six-state automaton `walk4St σ` recognizes
both (`Xc_eq_walk`, `NR_eq_walk`); its transition monoid is aperiodic, checked by one
`decide +kernel` per displacement map (`walk_cert_m`, `walk_cert_a`), so `Xc σ`, `NR σ` are
star-free (`Xc_starFree_m`, `NR_starFree_m`, `Xc_starFree_a`, via `starFree_of_dfa`).
`zcK_quot`/`zc_height_of_zcK`: all words reduce to words in state `0` by right quotients by `d`.

**Case (a)** (`zcA_height`).  In state `0` the count is the number of blocks `[0]`
(`zcK_a_eq`: `zcK σa n k = bmod (Xc σa) {[0]} n k`); Transfer Lemma with `L₀ = {[0]}`,
`L₁ = Xc σa ∖ {[0]}`, `L₀∗ = {[0]}∗` star-free.

**Case (m)** (`zcM_height`).  The identity, for `u` in state `0`:

```
theorem pm1_identity {u : List (Fin 3)} (h : dsum4 σm u = 0) :
    2 * (zc σm 0 u : ℤ) = (Z2 u : ℤ) + (Ncl 1 u : ℤ) - (Ncl 2 u : ℤ) - (ad2 u : ℤ)
```

* `Z2 u`: letters `a` at even positions (`pcount … 2`), height one (`Z2_height`, `p = 2`);
* `Ncl 1`, `Ncl 2`: blocks of class `C⁺`, `C⁻` (`bcls`, from the first letter and the last two
  letters); counted by `transfer_height_one` (`bmodC_height`) with `C±` and `Xc ∖ C±` star-free
  (`Ccl_starFree`, `Cco_starFree`) and `C±∗` star-free (`Ccl_kstar_starFree`: a scanning automaton
  is compared with a six-state automaton by `pairCheck`, whose monoid is certified aperiodic);
* `ad2 u = ad0 (b b u)` (`ad2_eq`), `ad0` = blocks `ad` of the factorization (`ad0_eq_Nad`);
  two left quotients and the Transfer Lemma for `{ad}` (`kstar_singleton_starFree`).

The identity is an invariant of a scanning automaton (walk state, first/last letter of the current
block, potential), checked on its reachable states by `checkInv` (`id4_check`, kernel `decide`).
Assembly modulo `2n` (`zcK_m_eq`, as `coreK_eq`), then the tail by `zc_height_of_zcK`.

Every kernel `decide` is per automaton (walk σm, walk σa, C⁺ agreement, C⁻ agreement, C⁺ cert,
C⁻ cert, identity).  Memory: see `docs/goal/evidence/M28-STARHEIGHT-APERIODIC.md`.

## M28-STARHEIGHT-Z4-ROT2 (a rotation-2 letter with an odd one): open

First missing lemma (smallest instance; `n = 2` is the group `Z₂ ≀ Z₄`, `n = 5` an F₂₀ instance):

```
theorem z4Rot2Abc : Z4Rot2Abc
-- i.e. ∀ n k, k < n → HasHeightAtMost {w : List (Fin 3) | vcount ![0,1,2] 0 0 w % n = k} 1
```

and in general `theorem z4core_rot2 : Z4CoreRot2`.

### Why the A₄ / PM1 method cannot work here (proof by hand, not in Lean)

Call a code `Y` *state-tracking* if every word in state `0` lies in `Y∗` and every block of `Y`
returns to `0`.  The PM1 identity uses such a code (`X`).

With `c` of rotation `2`, a state-tracking code cannot be star-free:

* `b c^(2i+1) b` returns to `0`, and none of its nonempty proper prefixes does (they are in states
  `1` or `3`), so it is a block of `Y`;
* `b c^(2i) b` ends in state `2`, so it is not a block.

Hence `Y ∩ b c∗ b = b c (cc)∗ b`, which is not star-free (its quotient by `b` on both sides is
`c(cc)∗`).  So every height-one quantity has to see the high bit `h` of the state `2h + p` without a
code whose block boundaries are the returns to `0`.

The user's five attempts (first returns to `{0,2}`, `c ↦ bdb`, abelian counts, the wreath principle,
cluster `{0,1}`) are consistent with this.

### Computations (search script `docs/goal/evidence/M28-STARHEIGHT-Z4-search.py`; not Lean-verified)

On the returning words of length ≤ 8 (2,463 words), the counted quantity `N` is **not** a rational
linear combination of the following family `R`:

* the letter counts;
* all letter-in-state counts of the 21 counters on `ZMod 4` whose displacements take a single
  nonzero value (those covered by `z4core_rot01/03/02`, every counted letter, every state);
* the block classes (first letter, last three letters) of the first-return code to the even
  states, read from the prefixes `''` and `b`.

Including the non-star-free class `b|bb` does not help.  An identity already fails on the words of
length ≤ 6.

Additional runs (scratch, not in the script):

* `R` with factor counts of length ≤ 4 added: still not in the span;
* "factor of length ≤ 3 read in a given state of a single-rotation counter" counts, 2,769 columns
  (not all known to have height one): still not in the span.

By contrast, for the PM1 alphabet the analogous family with the code `X` and `Z₂` counts contains
`N` (the identity above).  Without the `Z₂` counts it does not: on `(aaaa)ᵏ`, `(bbbb)ᵏ`, `(abab)ᵏ`
every star-free class count is bounded, and the letter coefficients would have to satisfy
`4α = 1`, `4β = 0`, `2α + 2β = 1`.

### What would close it

A height-one quantity that separates the characters `i^(B+2C)` (`B` = number of `b`, `C` = number of
`c` before the position) from those of the covered counters, without a state-tracking code.

As far as we know this is open; Bourne's Question 5.8 (`r = 4`) leaves AbGrp ∗ Z₄ open.  No claim is
made either way.
