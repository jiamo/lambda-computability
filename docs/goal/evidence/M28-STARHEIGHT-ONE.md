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

## Stretch: attacking `coreLang` (not closed)

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
