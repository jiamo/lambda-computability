# M28-STARHEIGHT-Z4: abelian-by-Z₄ groups and the Frobenius group F₂₀ (open)

Rows: M28-STARHEIGHT-INDEX-FOUR (DONE_WEAK), M28-STARHEIGHT-Z4-CORE (DONE_WEAK),
M28-STARHEIGHT-Z4-CORE-ONE-ROTATION (DONE_STRONG), M28-STARHEIGHT-Z4-PM1 (open),
M28-STARHEIGHT-Z4-ROT2 (open, head of the M28 queue).

"Height" is generalized star height (`GeneralizedStarHeight.HasHeightAtMost`); "star-free" is
`HasHeightAtMost _ 0`.  `vcount δ q x w` (`Start/StarHeightBourne.lean`) is the number of positions
of `w` reading `x` in state `q` of the translation automaton with displacements `δ`, read from `0`.

## What is proved (lake build --wfail, no sorry, axioms propext, Classical.choice, Quot.sound)

Axioms: `docs/goal/evidence/M28-STARHEIGHT-Z4-axioms.txt`.

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

## M28-STARHEIGHT-Z4-PM1 (rotations ±1, no rotation 2): open, with an identity found

Neutral letters can be erased by an inverse alphabetic morphism, and `q ↦ −q` swaps `1` and `3`.
So both sub-cases are three-letter problems on `ZMod 4`, with `b` (+1) and `d` (−1):

* fixed counted letter `x` (δ = 0) — the user's case (a);
* moving counted letter `a` (δ = 1) — the `Z₄` analogue of the A₄ core.

**Star-freeness (the common missing lemma).** While a walk with steps `±1` avoids `0`, its integer
partial sums stay in `{1,2,3}` or in `{−3,−2,−1}`, so the restricted automaton is a 3-state path,
whose transition monoid consists of order-preserving partial maps and is aperiodic.  Hence:

* the first-return code `X` to `0` is star-free;
* for case (a), the returns `P` that do not read `x` at `0` are star-free.

This is checked by machine on the minimal automata (search script), but it is not proved in Lean.
There is no Lean theorem "aperiodic ⇒ star-free" in the repository, and the A₄ code used a reset
automaton (`walk_eq_reset`), which a 3-state path is not.  With this lemma, case (a) is exactly
`B0lang_eq`/`V0lang_eq` (PST's `[(P∗ x P∗)ⁿ]∗ S⁻¹`).

**The identity (moving case; computer-found, checked, not Lean-verified).**  Alphabet
`a` (+1, counted), `b` (+1), `d` (−1).  Let `u` be a word in state `0`, and factor it into blocks of
`X`.  Define:

* `Z₂(u)` = the number of `a` at even positions, i.e. `N₀ + N₂`; it has height one by `pcount`
  with `p = 2`;
* `C⁺` = the blocks starting with `a` whose last two letters are not (`a`, then an up letter);
* `C⁻` = the blocks starting with `b` or `d` whose last two letters are `a` then an up letter;
* `ad₂(u)` = the blocks equal to `ad` in the factorization of `bb·u`.  These are the factors `ad`
  whose `a` is read in state `2`, a shifted-start count like A₄'s `acCount`.

Then

    2·N₀(u) = Z₂(u) + #C⁺(u) − #C⁻(u) − ad₂(u).

Proof idea: `N₀ − N₂ = #(blocks starting with a) − N₂`.  An `a` read in state `2` goes to `3` and is
followed either by `d` (an `ad` read in state `2`), or by an up letter that ends the block.  In the
second case it is the penultimate letter of a block ending with an up letter.

The identity holds on all 298,936 returning words of length ≤ 12 (2,690,420 of length ≤ 14 in a
longer run) and on random returning words up to length 400.  The minimal automata of `X`, `C⁺`,
`C⁻`, `C⁺∗`, `C⁻∗` are aperiodic, so the Transfer Lemma applies to `C±` (`L₁ = X ∖ C±`), and
`{ad}∗` is star-free (`ad` is primitive).

Gap (Lean): star-freeness of `X`, `P`, `C±`, `C±∗`; the identity as an automaton invariant (as
`id_check` in A₄); the assembly as in `coreK_eq`.

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
