# M28-STARHEIGHT-TWO-CLASS — height two for languages recognized by finite commutative monoids

## The class

`C` = finite commutative monoids: the predicate `∀ x y : M, x * y = y * x` on a finite monoid
`M`. It is algebraic and does not refer to the split construction. It contains
`Multiplicative (ZMod 2)`, a group of order two (`comm_class_nontrivial_subgroup`), and more
generally every finite abelian group, so it contains monoids with nontrivial subgroups.

## Terminal statements (`Start/StarHeightCommutative.lean`)

```lean
theorem singleSplit_of_fiber_height {M : Type} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M)
    (hfib : ∀ d, HasHeightAtMost {w | T (FreeMonoid.ofList w) = d} 1) : SingleSplit T

theorem fiber_height_one_of_comm [Finite Alphabet] {M : Type} [Monoid M] [Fintype M]
    (hM : ∀ x y : M, x * y = y * x) (T : FreeMonoid Alphabet →* M) (d : M) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) = d} 1

theorem singleSplit_of_comm [Finite Alphabet] {M : Type} [Monoid M] [Fintype M]
    (hM : ∀ x y : M, x * y = y * x) (T : FreeMonoid Alphabet →* M) : SingleSplit T

theorem height_two_of_comm [Finite Alphabet] {M : Type} [Monoid M] [Fintype M]
    (hM : ∀ x y : M, x * y = y * x) (T : FreeMonoid Alphabet →* M) (F : Set M) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 2

theorem height_one_of_comm [Finite Alphabet] {M : Type} [Monoid M] [Fintype M]
    (hM : ∀ x y : M, x * y = y * x) (T : FreeMonoid Alphabet →* M) (F : Set M) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1

theorem comm_class_nontrivial_subgroup :
    (∀ x y : Multiplicative (ZMod 2), x * y = y * x) ∧
      ∃ x : Multiplicative (ZMod 2), x ≠ 1 ∧ x * x = 1
```

## Construction

* `singleSplit_of_fiber_height` (any finite monoid): `E` is the first-return code to `1`
  (`firstReturn T`: nonempty words with value `1` and no proper nonempty prefix of value `1`),
  `S = Unit`, `G` constant, `P () = E`, `Q () = 1`. `SplitSound` follows from the prefix-code
  property; `SplitAvailable E 0` holds because `e = e ++ []`; `E∗` lies in the fiber of `1`, so
  the fiber condition holds with `R = univ` (for `d = 1`) or `R = ∅`. Heights:
  `firstReturn T = (fib 1 ⊓ 1ᶜ) ⊓ ((fib 1 ⊓ 1ᶜ) * 1ᶜ)ᶜ` and
  `remainder E = (E * ⊤)ᶜ`, so both reduce to the fibers. This is the observation in the
  instruction: in this form the split does no work.
* `fiber_height_one_of_comm`: in a commutative monoid
  `T w = ∏ a, T a ^ (count a w)`, and `k ↦ x ^ k` is eventually periodic in a finite monoid
  (pigeonhole). So each fiber is a finite union of finite intersections of languages
  `{w | count a w ∈ K}` with `K ⊆ ℕ` eventually periodic. Each of these is a finite union of
  `{count a w = k}` (star-free: built from `(⊤ {a} ⊤)ᶜ`, letters and concatenation) and
  `{count a w ≡ c mod p} ∩ {count a w ≥ m}`, where
  `{count a w ≡ c mod p} = (countBlock a p)∗ · {count a w = c}` has height one.

## Axioms

```
'GeneralizedStarHeight.height_two_of_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'GeneralizedStarHeight.height_one_of_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'GeneralizedStarHeight.singleSplit_of_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'GeneralizedStarHeight.comm_class_nontrivial_subgroup' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Literature, and whether the result is new

**The result is not new.** Languages recognized by finite commutative monoids are Boolean
combinations of the languages "the letter `a` occurs exactly `k` times" and "the letter `a`
occurs `k` modulo `p` times"; the first are star-free and the second have (generalized) star
height one, so every such language has generalized star height at most one. This is classical
and is proved here as `height_one_of_comm`; the height-two statement is weaker.

Pin, Straubing and Thérien (1992, "Some results on the generalized star-height problem",
Information and Computation 101) give height one for languages recognized by further classes
of groups, including nilpotent groups of class two (Theorems 7.3 and 7.8 as cited in the
instruction). Abelian groups are nilpotent of class one, so the group part of `C` lies inside
their class; for commutative monoids with a nontrivial aperiodic part the height-one bound is
the classical argument above. I have not checked the exact statements of Theorems 7.3 and 7.8
against the paper.

I did not reach a class outside these results. In particular, nothing here concerns `S3`
(the smallest group not nilpotent of class two); whether "every language recognized by `S3`
has height at most two" is already in the literature, I am unsure.

## Status

The exit criteria are met literally (an algebraic class containing a nontrivial subgroup, with
height at most two, and this file states the literature). The row is marked `DONE_WEAK`
because the class is inside known height-one results; its open boundary names the next
target (a class with a non-nilpotent group, such as one containing `S3`).

## M28-STARHEIGHT-TWO-GROUPS (groups beyond nilpotency class two)

Module: `Start/StarHeightGroups.lean` (new; no existing module edited).

Step 1 is proved:

```lean
theorem singleSplit_of_firstReturn {M : Type} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M)
    (hE1 : HasHeightAtMost (firstReturn T) 1)
    (hrem : ∀ d, HasHeightAtMost
      {w | w ∈ remainder (firstReturn T) ∧ T (FreeMonoid.ofList w) = d} 1) :
    SingleSplit T

theorem firstReturn_height_of_fiber_one {M : Type} [Monoid M] (T : FreeMonoid Alphabet →* M)
    (h1 : HasHeightAtMost {w | T (FreeMonoid.ofList w) = 1} 1) :
    HasHeightAtMost (firstReturn T) 1

theorem height_two_of_firstReturn [Finite Alphabet] {M : Type} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M) (hE1 : ...) (hrem : ...) (F : Set M) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 2
```

The split is the one of `singleSplit_of_fiber_height`: `E = firstReturn T`, one state, tests
`P () = E`, `Q () = 1`. Only the two listed height-one facts are used.

Step 2 (the height-one facts for `S3` or a larger class of groups) is **not** done, and no group
class has been reached. What the literature gives: height one for nilpotent groups of class at
most two (Pin, Straubing and Thérien). We know of no published bound below three for languages
recognized by `S3`; this should be checked against Bourne's thesis and later work. Under the
stop rule, the first missing lemmas, which with the step-1 theorems give height two for every
language recognized by `S3`, are:

```lean
theorem fiber_one_height_one_perm3 {Alphabet : Type u} [Finite Alphabet]
    (T : FreeMonoid Alphabet →* Equiv.Perm (Fin 3)) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) = 1} 1

theorem remainder_fiber_height_one_perm3 {Alphabet : Type u} [Finite Alphabet]
    (T : FreeMonoid Alphabet →* Equiv.Perm (Fin 3)) (d : Equiv.Perm (Fin 3)) :
    HasHeightAtMost {w | w ∈ remainder (firstReturn T) ∧ T (FreeMonoid.ofList w) = d} 1
```

## M28-STARHEIGHT-TWO-GROUPS closed: an abelian normal subgroup of index 3 (this delivery)

Modules: `Start/StarHeightResetCount.lean` and `Start/StarHeightIndexThree.lean` (new; no existing
module edited).

```lean
theorem height_two_of_abelian_index_three [Finite Alphabet] {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hidx : N.index = 3)
    (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 2

theorem height_two_alternatingGroup_four [Finite Alphabet]
    (T : FreeMonoid Alphabet →* alternatingGroup (Fin 4)) (F : Set (alternatingGroup (Fin 4))) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 2
```

The class contains `A₄` (Klein four subgroup, index 3), which is not nilpotent, so the exit
criterion is met.

### Construction, against the sketch

* (a) Blocks.  `ψ = psi N T : FreeMonoid → G ⧸ N`, `E = firstReturn ψ`;
  `kstar_firstReturn_group : E∗ = ψ⁻¹(1) = T⁻¹(N)`.  `E` and `E∗` have height ≤ 1 because
  `G ⧸ N` has order 3 and is commutative (`q3_comm`, `height_one_of_comm`,
  `firstReturn_height_of_fiber_one`).  (We used height one for `E` instead of an explicit
  star-free expression: it suffices, since only height ≤ 1 of the blocks is needed.)
* (b)/(d) Inside a block the walk in `G ⧸ N ≅ Z/3` avoids `1`, and there it *is* a reset automaton
  (`walk_reset`): a letter with `ψ b = 1` keeps the state, any other letter `b` sends every
  non-identity state to `(ψ b)⁻¹` (the unique state ≠ 1 from which `b` does not return).
  `Start/StarHeightResetCount.lean` proves that "the number of positions reading `a` in state `q`
  is `r` mod `m`" has height ≤ 1 for any reset automaton (`rcountMod_height`, a copy of the
  `countIs`/`countMod` construction with the letter replaced by a (state, letter) pair), and that
  "the state after `v` is `q'`" is star-free (`stateIs_height`).
* (c) Telescoping.  `rep : G ⧸ N → G` with `rep 1 = 1`, `cv q a = rep q · T a · rep (q ψ a)⁻¹ ∈ N`
  (`cv_mem`), `telescope`; in the abelian `N` the product depends only on the counts modulo `|N|`
  (`list_prod_cv`, `valN`).  `block_value`: for a block `x :: (v ++ [y])` with `ψ x ≠ 1`,
  `T(block) = cv 1 x · valN(residues of the counts along v from ψ x) · cv (ψ y)⁻¹ y`;
  `rem_value` is the same for a nonempty remainder, ending with `rep (state)`.
* (d) `Bv_height`: the blocks of each value `g` form a finite union of
  `E ⊓ {[x]}` and `E ⊓ ({[x]} · (⋂ residue conditions) · {[y]})`, of height ≤ 1.
* (e) `bmod_height`: for a prefix code `E` with `E∗` of height ≤ 1 and a subcode `L` of height
  ≤ 1, "the number of `L`-blocks is `r` mod `m`" is `(Y^m)∗ · Y^r · D` with
  `D = E∗ ∩ (E∗ L A∗)ᶜ`, `Y = D L`, of height 2.  `Av_eq`: the words of `E∗` with value `d` are a
  finite union over residue vectors `res : N → Fin |N|` with `∏ g^(res g) = d` of
  `⋂_g bmod E (Bv g) |N| (res g)` (uniqueness of the factorization by `flatten_injective`).
* (f) `Rv_height`: remainders of each value have height ≤ 1 (finite union of
  `remainder E ⊓ ({[x]} · (residue conditions ⊓ final state))`, plus `{[]}` for value 1).
* (g) `height_two_of_split`: as in `height_two_of_singleSplit`, by `factor_remainder`.

The only height-2 star is the block-count star `(Y^m)∗` of (e).

### Literature (checked by the task author; recorded here)

* Henneman (1971): languages recognized by commutative groups have generalized star height ≤ 1.
* Pin, Straubing and Thérien, "Some results on the generalized star-height problem", Information
  and Computation 101 (1992): height ≤ 1 for nilpotent groups of class 2, for every group dividing
  a semidirect product of a commutative group by `(Z/2Z)^n`, and for every group of order < 12.
  So `S₃`, all dihedral groups and every group with an abelian subgroup of index 2 are classical;
  the `S₃` lead of the earlier open boundary is therefore classical and has been dropped.
* T. Bourne, PhD thesis, St Andrews (2017): groups of order 12–15 are resolved except `A₄` and
  `Dic₃` (Question 5.9); Conjecture 4.11 (open): every language recognized by a monoid in
  `AbGrp ∗ Z₃` has height ≤ 1.
* As far as we know, no bound below 3 was known for `A₄`, so height ≤ 2 for `A₄` would be new.
  This is stated with that caveat: we have not surveyed the literature after Bourne's thesis.

### Stretch (stop rule): first missing lemmas

* Height one for `A₄` (Bourne's Question 5.9), row M28-STARHEIGHT-ONE-A4.  The only obstruction
  in our expression is the block-count star.  First missing lemma:

  ```lean
  theorem bmod_height_one {E L : Language Alphabet} (hE : PrefixCode E) (hL : L ≤ E)
      (hEs : HasHeightAtMost E∗ 1) (hLh : HasHeightAtMost L 1) {m r : ℕ} (hr : r < m) :
      HasHeightAtMost (bmod E L m r) 1
  ```

  (for `E = firstReturn (psi N T)` and `L = Bv N T g`; in this generality it is probably false,
  and a proof must use the structure of the blocks).
* Prime index `p ≥ 5`: inside a block the walk in `Z/p ∖ {0}` is no longer a reset automaton
  (`walk_reset` uses `|G ⧸ N| = 3`), and the state is a bounded counter.  First missing lemma:

  ```lean
  theorem walk_count_height {p : ℕ} [Fact p.Prime] (ψ : FreeMonoid Alphabet →* Multiplicative (ZMod p))
      (q qs : Multiplicative (ZMod p)) (a : Alphabet) (m r : ℕ) (hr : r < m) :
      HasHeightAtMost {v | (∀ u, u <+: v → q * ψ (FreeMonoid.ofList u) ≠ 1) ∧
        (countAt ψ q qs a v) % m = r} 1
  ```

  where `countAt ψ q qs a v` counts the positions of `v` reading `a` in the state `qs` of the walk
  from `q`.
* Index 2 by the same proof (optional) was not done; it is classical with height ≤ 1.

`#print axioms`: `docs/goal/evidence/M29-M28-axioms.txt` (only `propext`, `Classical.choice`,
`Quot.sound`).
