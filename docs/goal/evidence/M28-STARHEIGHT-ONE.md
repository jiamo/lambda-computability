# M28-STARHEIGHT-ONE: generalized star height one for groups with an abelian normal subgroup of prime index

Rows: M28-STARHEIGHT-ONE-PURE (closed), M28-STARHEIGHT-ONE-A4 (reduced to one language, open),
M28-STARHEIGHT-WREATH-STEP (see that row).

"Height" means generalized star height (`GeneralizedStarHeight.HasHeightAtMost`); "star-free" means
`HasHeightAtMost _ 0`.

## What is proved (all `lake build --wfail`, no `sorry`, standard axioms only)

### Tools (`Start/StarHeightClosure.lean`, `Start/StarHeightTransfer.lean`)

* `HasHeightAtMost.leftQuot`, `HasHeightAtMost.rightQuot`: letter quotients `a⁻¹L`, `La⁻¹` do not
  increase height (PST (T1); structural induction with `a⁻¹(EF) = (a⁻¹E)F ∪ [ε ∈ E]·a⁻¹F`,
  `a⁻¹(E∗) = (a⁻¹E)E∗`).  `HasHeightAtMost.reverse` (reversal) is used for the right quotient.
* `HasHeightAtMost.invAlph`: inverse alphabetic morphisms (`φ : α → Option β`, letters to letters or
  to `ε`) do not increase height (PST Corollary 4.7).
* `transfer_height_one`: the Transfer Lemma (PST Lemma 6.1).  If `L₀`, `L₁` are star-free and
  disjoint, `L₀ ∪ L₁` is a prefix code and `L₀∗` is star-free, then the words of `(L₀ ∪ L₁)∗` with
  `≡ r (mod m)` blocks in `L₀` form a language of height at most one (`bmod (L₀ + L₁) L₀ m r`).
* `kstar_singleton_starFree`, `primitive_of_prime_length`: `t∗` is star-free for primitive `t`;
  every non-constant word of prime length is primitive.

### The main theorem (`Start/StarHeightPrimeCount.lean`, `Start/StarHeightPrimeIndex.lean`)

```
theorem height_one_of_prime_index_pure [Finite Alphabet] {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) {p : ℕ} [Fact p.Prime]
    (hidx : N.index = p) (g : G) (T : FreeMonoid Alphabet →* G)
    (hT : ∀ a, T (FreeMonoid.of a) ∈ N ∨ g⁻¹ * T (FreeMonoid.of a) ∈ N) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1
```

**Every prime `p` is covered.**  The count conditions are `pcount_height_one`:

* moving letters (case (a)): reduced to the alphabet `Bool` by `invAlph`, then the `p`-tuple identity
  `p·cnt_{h,a}(v) = |v|ₐ + Σ_t c_t·n_t(v)` on `(Aᵖ)∗` (`block_identity`), PST Proposition 6.2 in the
  form needed (`Vlang_eq`), and the Transfer Lemma with `L₀ = {t}`, `L₁ = Aᵖ ∖ {t}` for each
  non-constant block `t` (`bmod_block_height`);
* identity letters (case (b)): the first returns `P = D ∪ M(I∗M)ᵖ⁻¹`, Transfer Lemma on `{x} ∪ P`
  (`B0lang_height`), other states by splitting off the shortest prefix reaching the state
  (`Blang_height`).

Corollaries:

* `height_one_of_abelian_index_two`: every finite group with an abelian normal subgroup of index 2
  (no hypothesis on the letters).  This is PST Theorem 7.6 restricted to groups (known).
* `height_one_quaternionGroup` (all `n ≠ 0`), `height_one_quaternionGroup_three` (`Dic3`, order 12).
* `height_one_dihedralGroup` (all `n ≠ 0`).
* `height_one_alternatingGroup_four_pure`: `A₄`, for every `T` whose letters lie in `V ∪ σV`
  (`V` the Klein four subgroup, `σ` any fixed element, e.g. a 3-cycle).

### Reduction of `A₄` to one language (`Start/StarHeightA4Core.lean`)

```
def coreLang (k n : ℕ) : Language (Fin 3) := {u | coreCount u % n = k}
theorem height_one_alternatingGroup_four_of_core
    (hcore : ∀ k < 2, HasHeightAtMost (coreLang k 2) 1) [Finite Alphabet]
    (T : FreeMonoid Alphabet →* alternatingGroup (Fin 4)) (F : Set (alternatingGroup (Fin 4))) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1
```

Here letters `0`, `1` of `Fin 3` add `1` to a state in `ZMod 3`, letter `2` adds `2`, and
`coreCount u` is the number of positions reading `0` in state `0`.  The general form is
`height_one_of_index_three_exponent_two_of_core` (any finite group with a normal subgroup of index 3
and exponent 2, which is then abelian).  Route:

* `V` has exponent 2, so the telescoped product needs the (state, letter) counts only mod 2
  (`valN_mod_two`).
* letters in `V` (`fixed_count_height`): `invAlph` to `Fin 3` with displacements `0, 1, 2`; the first
  returns to state 0 that start with a moving letter form a star-free set `Pblock` (while the walk
  avoids 0 it is a reset automaton: `walk_eq_reset`, `avoid_eq`), `{[0]} ∪ Pblock` is a prefix code
  (`EV_prefixCode`), and the Transfer Lemma counts the `[0]`-blocks (`V0lang_height`).  This is
  proved outright, without the core hypothesis.
* letters in `σV ∪ σ²V` (`moving_count_height`): `invAlph` sends the counted letter to `0`, the
  other letters of its coset to `1`, letters of the other moving coset to `2` and `V`-letters to `ε`;
  for `σ²V` the automorphism `q ↦ -q` of `ZMod 3` swaps the cosets.  Other states by a left quotient
  (`height_of_state_zero`).  This case is exactly `coreLang`.

So Bourne's Question 5.9 for `A₄` reduces to the first missing lemma

```
theorem coreLang_height_one (k : ℕ) (hk : k < 2) : HasHeightAtMost (coreLang k 2) 1
```

(only this direction is formalized: `coreLang_height_one` implies height one for every `A₄`
language).

## Literature

* Pin, Straubing, Thérien, "Some results on the generalized star-height problem", Information and
  Computation 101 (1992).
  - Theorem 7.6: `Gcom ∗ Z/2Z` (abelian-by-`Z2` wreath/semidirect products) has height ≤ 1.
  - Proposition 6.10: the pair trick (counting letters read in a given state of a `Z2` counter by
    counting 2-blocks).  The `p`-tuple identity above is its generalization to every prime `p`.
  - Lemma 6.1: the Transfer Lemma.  Proposition 6.2: linear combinations of counts.
  - §5: wreath product principle; with it, an abelian normal subgroup adds at most one to the height.
* Bourne, PhD thesis (St Andrews, 2017).  Question 5.9 lists `A₄` and `Dic3` (dicyclic of order 12)
  as open for height one.  §4.2.2 treats `AbGrp ⋊ Z3` (height two).
* `Dic3` is already covered by PST Theorem 7.6: its cyclic subgroup of order 6 is normal of index 2,
  so `Dic3 ≤ Z6 ≀ Z2`.  As far as we know, this has not been pointed out in print.  The corollary
  `height_one_quaternionGroup_three` proves it formally.
* The case `p = 3` with a single moving coset (and every prime `p ≥ 3` in that setting) is new as far
  as we know: PST treat `p = 2` only, and Bourne §4.2.2 tries only the general `Z3` case (letters in
  both nontrivial cosets).  This is stated with that caveat; we have not done a complete literature
  search.

## Stretch: attacking `coreLang` (not closed in that delivery; closed below, see "A₄: height one")

Write `a`, `b`, `c` for letters `0`, `1`, `2`.

* The words that return to state 0 factor uniquely into first-return blocks
  `x((a|b)c)∗(c | (a|b)(a|b))` for `x ∈ {a, b}` and `c(c(a|b))∗((a|b) | cc)`; `coreCount` is the
  number of blocks that start with `a`.
* The blocks `a((a|b)c)∗c` never wrap around (integer displacement 0); their star is star-free, so the
  Transfer Lemma counts them.
* Obstruction to PST Proposition 6.2 over finitely many first-return block classes plus letter
  counts: a class containing `aaa` (or `bbb`, `ccc`) has a star that is not star-free (its star
  intersected with `a∗` is `(a³)∗`); along `a(ac)ᵏc` and `a(bc)ᵏc` the `a`-count is unbounded, so
  the letter-count part of any identity must be `α(|u|ₐ + |u|_b − |u|_c)`, that is `α·3·(winding
  number)`; then the block `aaa` forces `α = 1` and the block `bbb` forces `α = 0`.
* So a proof needs other counts (two-level blocks, factors, or another prefix code).  Not attempted in
  Lean in this delivery beyond the reduction; first missing lemma: `coreLang_height_one` above.

## M28-STARHEIGHT-WREATH-STEP (closed)

`Start/StarHeightWreathStep.lean`:

* `height_succ_of_abelian_normal`: if `N` is an abelian normal subgroup of a finite group `G` and
  every language recognized by a morphism into `G ⧸ N` has height at most `k`, then every language
  recognized by a morphism into `G` has height at most `k + 1`.
* `height_two_of_commutator_abelian`: every language recognized by a finite group with abelian
  commutator subgroup has height at most two (with `k = 1` from `height_one_of_comm` for the
  abelianization).

Proof: the telescoped product needs, for each pair (state `q`, letter `a`), the number of positions
reading `a` in state `q` modulo `|N|` (`qcount`).  Factor the word at those positions: after each
the state is `q·ψ(a)`.  With `Z s` the words with no counted position from state `s` (a complement
of `fib(s, q)·a·A∗`, height ≤ `k`) and the block `U a`, `U = Z(qψ(a)) ∩ fib(qψ(a), q)`,
the count condition from state `q·ψ(a)` is `(U a)^r ((U a)^m)∗ Z(qψ(a))` (`qcount_after_mod`) and
from state `1` it is `[r = 0]·Z(1) ∪ (Z(1) ∩ fib(1, q))·a·(…)` (`qcount_mod_eq`): one more star.
This is folklore (the wreath product principle, PST 1992 §5); it generalizes
`height_two_of_abelian_index_three`.

## A₄: height one (M28-STARHEIGHT-ONE-A4, closed)

All results below build under `lake build --wfail`, with no `sorry`; `#print axioms` shows only
`propext`, `Classical.choice` and `Quot.sound` (`docs/goal/evidence/M28-A4-axioms.txt`).

Statements:

* `coreLang_height_one_all (n k : ℕ) (hk : k < n) : HasHeightAtMost (coreLang k n) 1`
* `coreLang_height_one (k : ℕ) (hk : k < 2) : HasHeightAtMost (coreLang k 2) 1`
* `height_one_alternatingGroup_four (T : FreeMonoid Alphabet →* alternatingGroup (Fin 4)) (F) :
  HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1` (from `height_one_alternatingGroup_four_of_core`)

(all in `Start/StarHeightCoreHeight.lean`).

### Notation

Alphabet `Fin 3`; letters `0`, `1` add `1` to the state, letter `2` adds `2` (`step3`); words are
read from state `0`.  `coreCount u` counts the positions reading `0` in state `0`, `|u|₀` the letters
`0`, and `acCount u` the occurrences of the factor `02` whose `0` is read in state `1`.
`Λ = ((0|1)2)*`, `Λ' = (2(0|1))*`.

### The first-return code (`Start/StarHeightCoreCode.lean`)

`coreX` (the nonempty words returning to state `0` for the first time at their end) is a prefix code
(`coreX_prefixCode`); every word factors uniquely as `e₁ ⋯ e_r · t` with `eᵢ ∈ coreX` and `t` with no
nonempty prefix in state `0` (`split_spec`, `split_flatten`); `coreX∗` is the set of words in state
`0`.  `coreX = (0|1)Λ(2 | (0|1)(0|1)) ∪ 2Λ'((0|1) | 22)` is star-free (`coreX_height`): the middle
parts `Λ`, `Λ(0|1)`, `Λ'`, `Λ'2` and the prefix-closures used for the tail language are strictly
locally testable with forbidden factors `{00, 01, 10, 11, 22}`, which is checked on finite automata
(`mid_check`, `avoid_check`).

### The identity (`Start/StarHeightCoreIdentity.lean`)

For a block `w ∈ coreX` let `D(w) = dᵢ` if `w ∈ Fᵢ` and `0` otherwise, with

| class | language | `dᵢ` |
|---|---|---|
| F₁ | `{02}` | +2 |
| F₂ | `0(0|1)2·Λ·2` | +2 |
| F₃ | `0·Λ·01` | +1 |
| F₄ | `0·Λ·10` | +1 |
| F₅ | `0·Λ·11` | +2 |
| F₆ | `1·Λ·00` | −2 |
| F₇ | `1·Λ·01` | −1 |
| F₈ | `1·Λ·10` | −1 |
| F₉ | `{20}` | −1 |
| F₁₀ | `2·Λ'·210` | −1 |
| F₁₁ | `2·Λ'·200` | −2 |
| F₁₂ | `2·Λ'·201` | −1 |

`D` is `0` on the other blocks (`0Λ00`, `1Λ11`, `1Λ2`, `{21}`, `2Λ'211`, `2Λ'22`; these contain the
blocks `000`, `111`, `222`).  In Lean the class of a block is read off its first letter and its
last three letters (`comp`, `cls`).

`core_identity`: for `u` in state `0`, with `Nᵢ(u)` the number of blocks of `u` in `Fᵢ`,

    3·coreCount u + acCount u = |u|₀ + Σᵢ dᵢ·Nᵢ(u)     (in ℤ).

`acCount0_eq`: the occurrences of `02` read from state `0` are exactly the blocks in `F₁`.
Both are proved as one invariant of a finite automaton (walk state and first/last letters of the
current block, with the two potentials), checked on its 33 reachable states (`id_check`).

### The twelve stars (`Start/StarHeightCoreClassCheck.lean`, `Start/StarHeightCoreClasses.lean`)

Each `Fᵢ` and `coreX \ Fᵢ` is star-free (`Fcls_height`, `Fco_height`).  Each `Fᵢ∗` equals the
strictly locally testable language
`{ε} ∪ ((⋃_{p∈Pᵢ} p·A*) ∩ (⋃_{s∈Sᵢ} A*·s) ∩ ⋂_{g∈Gᵢ} (A*·g·A*)ᶜ)` (`Fcls_kstar_eq`), with

| | P | S | G |
|---|---|---|---|
| F₁ | {0} | {2} | {00,1,22} |
| F₂ | {002,012} | {022,122} | {000,001,0200,0201,10,11,1200,1201,2202,221,222} |
| F₃ | {001,002,012} | {001,201} | {000,0012,1010,102,11,200,2012,210,22} |
| F₄ | {002,010,012} | {010,210} | {0000,0001,1002,101,102,11,200,201,22} |
| F₅ | {00,01} | {11} | {000,001,010,102,111,112,200,201,210,22} |
| F₆ | {10,11} | {00} | {000,002,012,101,110,111,201,210,211,22} |
| F₇ | {101,102,112} | {101,201} | {00,010,0112,012,1110,1111,210,211,22} |
| F₈ | {102,110,112} | {110,210} | {00,0101,012,1102,111,201,2102,211,22} |
| F₉ | {2} | {0} | {00,1,22} |
| F₁₀ | {220,221} | {210} | {00,01,1020,1021,11,122,2022,222} |
| F₁₁ | {220,221} | {200} | {000,0020,0021,01,10,11,122,2022,222} |
| F₁₂ | {220,221} | {201} | {00,0120,0121,022,10,11,2122,222} |

All twelve equalities are proved.  Method (uniform, instead of the suggested inductions): every
strictly locally testable language of this shape is star-free (`sltLang_height`) and is recognized by
an automaton remembering the first three and the last three letters (`mem_sltLang_iff`); `Fᵢ∗` is
recognized by the block-reading automaton `fStep i` (`mem_kstar_Fcls_iff`); the two automata agree on
the reachable part of their product (41 to 203 states), checked by `decide +kernel` (`f_check`).

### Heights

* `{u | |u|₀ ≡ r (mod 3n)}`: `countMod_height` (commutative).
* `bmod coreX Fᵢ (3n) r`: the Transfer Lemma with `L₀ = Fᵢ`, `L₁ = coreX \ Fᵢ` (`bmodF_height`).
* `{u | acCount u ≡ r (mod m)}` (`acCount_height`): `acCount u = acCount0 (2 :: u)`
  (`acCount_eq_cons`), and `{v | acCount0 v ≡ r} = bmod coreX F₁ m r · Tail` (`acCount0_lang`), where
  `Tail` (no nonempty prefix in state `0`) is star-free (`NoRet_height`); then a left quotient.
* `coreK_eq`: the words in state `0` with `coreCount ≡ k (mod n)` are the union, over residue tuples
  `(r₀, r', r₁, …, r₁₂)` mod `3n` with `r₀ − r' + Σ dᵢrᵢ ≡ 3k`, of the intersections of the fourteen
  languages above (PST Proposition 6.2).
* `coreLang_eq_quot`: `coreLang k n = K ∪ rightQuot 2 K ∪ rightQuot 1 K` (Bourne's right-quotient
  trick: appending `2` or `1` does not change `coreCount`).

### Why the obstruction above is avoided

The obstruction concerns identities in which only letter counts and counts of first-return block
classes to state `0` occur.  `acCount` is not such a count: an occurrence of `02` read from state
`1` sits inside a block (in its loops `y2`), and its number is not a function of the block classes
of a finite partition of `coreX`.  It is, however, a block count of the first-return code read
from a different start state (`acCount u = acCount0 (2 :: u)`, and `acCount0` counts blocks in
`F₁`), so it still has height one.  With it, the classes containing `000`, `111` and `222` get
coefficient `0`.

### Provenance

The identity, the twelve classes and the strictly locally testable data were supplied with the
instruction.  They were found by computer search and checked by brute force (all words of length
≤ 12) and by minimal-automaton equivalence.  The Lean proof is the verification.

### Claim (with caveat)

As far as we know, this answers Bourne's Question 5.9 (2017) for A₄.  Pin, Straubing and Thérien
1992 cover index two and nilpotent class two, and every group of order 16 has an abelian subgroup of
index two.  With those results, every language recognized by a group of order at most 19 has
generalized star height at most one.  The smallest group not covered is the Frobenius group
Z₅ ⋊ Z₄ of order 20.

## M28-STARHEIGHT-INDEX-THREE (closed)

* `coreLang_height_one_all` is Bourne's Conjecture 4.12 (for `r = 1`).
* `height_one_of_abelian_index_three` (`Start/StarHeightIndexThreeAll.lean`): every language
  recognized by a finite group with an abelian normal subgroup of index `3` has height at most one
  (Bourne's Conjecture 4.11, for groups).  The proof is `height_one_of_index_three_exponent_two_of_core`
  with counts modulo `Nat.card N` instead of `2`: each count "letter `x` read in state `h`" modulo
  `m` reduces to `coreLang k m` (letters outside `N`, by an inverse alphabetic morphism and a left
  quotient) or to the first-return code of the letters in `N` (`zcount_height_one_mod`).

## Bourne's Conjectures 4.11 and 4.12 (M28-STARHEIGHT-BOURNE-411, closed)

Lean: `Start/StarHeightBourne.lean`.

* `vcount δ q x w` is the number of positions `i < |w|` with `w[i] = x` and
  `((w.take i).map δ).sum = q`, for `δ : α → V` and `V` a finite `ZMod 3`-vector space (the cyclic
  automaton on the state set `(Z₃)ʳ`, read from `0`).
* `vcount_height_one`: `{w | vcount δ q x w % n = k}` has height at most one for every `n` and
  `k < n` (Conjecture 4.12 for every `r`).
* `height_one_of_abelian_normal_exponent_three`: if `N` is an abelian normal subgroup of the finite
  group `G` with `x y x⁻¹ y⁻¹ ∈ N` and `x³ ∈ N` for all `x, y` (that is, `G/N` is abelian of
  exponent `3`), every language recognized by `G` has height at most one (Conjecture 4.11).

### The identity (c)

Let `D` be the dual of `V` (the `ZMod 3`-linear maps `V → ZMod 3`) and `|D| = 3c`
(`c = 3^(r-1)` for `r = dim V ≥ 1`).  For `v ∈ V`, `#{φ ∈ D | φ v = 0}` is `3c` if `v = 0` and `c`
otherwise (`card_dual_ker`: for `v ≠ 0` some `φ₁` has `φ₁ v = 1`, and `φ ↦ φ − t·φ₁` maps the
fibre over `t` onto the kernel).  Position by position — a position holding `x` in state `s` is
counted on the left by the `φ` with `φ (s − q) = 0` — this gives, for every word `w`
(`charSum_zcount`):

    Σ_{φ ∈ D} zcount (φ ∘ δ) (φ q) x 0 w  =  c · |w|ₓ  +  2c · vcount δ q x w.

Each `zcount (φ ∘ δ) (φ q) x 0 w` is a state count of an automaton on `ZMod 3`, of height one for
every residue modulo every `m` (`zcount_height_one_mod`, M28-STARHEIGHT-INDEX-THREE), and `|w|ₓ`
is a commutative count.  Taking all counts modulo `M = 2cn`, `vcount δ q x w ≡ k (mod n)` holds iff
`Σ_φ ρ_φ − c·ρ ≡ 2ck (mod M)` for the residues `ρ_φ` and `ρ`, so the language is a finite union of
finite intersections of height-one languages (`height_one_of_residues`).  For `V = 0`, `vcount` is
the letter count.  The group theorem takes the counts of (coset, letter) pairs modulo `|N|`; each
is a `vcount` on `Additive (G ⧸ N)`, a `ZMod 3`-module by the two hypotheses, with `δ y` the class
of `T y`.

### Why the class is exactly AbGrp * Z₃

Let `C` be the class of finite groups `G` with an abelian normal subgroup `N` such that `G/N` is
abelian of exponent dividing `3`.

* Subgroups: for `H ≤ G`, `N ∩ H` is abelian and normal in `H`, and `H/(N ∩ H) ≅ HN/N ≤ G/N`.
* Quotients: for `M ⊴ G`, `NM/M` is abelian and normal in `G/M`, and `(G/M)/(NM/M) ≅ G/NM`, a
  quotient of `G/N`.
* Finite products: `N₁ × N₂` is abelian and normal in `G₁ × G₂`, with quotient `G₁/N₁ × G₂/N₂`.

So `C` is a pseudovariety.  Every `G ∈ C` embeds in the wreath product `N ≀ (G/N)`
(Kaloujnine–Krasner), which lies in AbGrp * Z₃; conversely AbGrp * Z₃ is generated by wreath
products `A ≀ B` with `A` abelian and `B` elementary abelian of exponent `3`, and `A ≀ B ∈ C` (the
base group `A^B` is abelian and normal, with quotient `B`).  Hence `C` = AbGrp * Z₃.

### Claim

As far as we know, this proves Bourne's Conjectures 4.11 and 4.12 (PhD thesis, St Andrews, 2017).

## Groups of order less than 20 (M28-STARHEIGHT-ORDER-LT-20, closed)

Lean: `exists_abelian_normal_index_le_three` (`Start/GroupOrderLtTwenty.lean`) and
`height_one_of_card_lt_twenty` (`Start/StarHeightOrderLtTwenty.lean`).

* Every group of order `n < 20` has an abelian normal subgroup of index at most `3`: orders `1`,
  `p`, `p²` are abelian; for `n ∈ {6, 10, 14, 18}` a subgroup of order `n/2` (prime or `9`) has
  index `2`; for `n = 15` the Sylow `5`-subgroup is normal (their number divides `3` and is `≡ 1`
  mod `5`); for `n = 8, 16` centralizers, via `comm_of_le_central` (a subgroup `H` with a central
  subgroup `K` and `|H| ≤ 2|K|` is abelian) — for `n = 16` and `|Z(G)| = 2` an element `x` whose
  class is central in `G/Z(G)` has at most `2` conjugates, so its centralizer has order `8` and is
  abelian; for `n = 12` either the Sylow `3`-subgroup `⟨a⟩` is normal (the centralizer of `a` has
  index at most `2`), or there are four Sylow `3`-subgroups with eight elements of order `3`, and
  the Sylow `2`-subgroup is the set of the other four elements, hence unique and normal.
* By the index: `height_one_of_comm` (1), `height_one_of_abelian_index_two` (2),
  `height_one_of_abelian_index_three` (3).

As far as we know, every finite group of order less than 20 is now settled.
- Pin, Straubing and Thérien (1992) cover all orders below 12 and every group with an abelian
  normal subgroup of index 2.
- Bourne (2017) left A₄ open (Question 5.9).
- The smallest group not covered is the Frobenius group Z₅ ⋊ Z₄ of order 20.
- At order 24, S₄ and SL(2,3) are not covered either.

## Order 20 (F₂₀): see `docs/goal/evidence/M28-STARHEIGHT-Z4.md`

The reduction of abelian-by-`Z₄` groups (F₂₀ in particular) to the `Z₄` core, the proved cases of
the core and the two open cases are recorded there.
