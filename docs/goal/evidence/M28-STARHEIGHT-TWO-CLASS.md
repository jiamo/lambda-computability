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
