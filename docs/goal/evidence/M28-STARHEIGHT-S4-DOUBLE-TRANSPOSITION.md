# The double-transposition obstruction (S4, three letters)

## Setting

- `T : FreeMonoid (Fin 3) →* Perm (Fin 4)` is onto, and some letter `x0` has a double
  transposition `a` as its value.  There are 19 such classes; in each, `D = V4`.  Below, Lean
  tables give the images of `0 1 2 3`, and the board's tuples are their inverses.  The classes,
  as listed on the board (the list is closed under inverting the letters):
  `0132 0213 1032, 0132 0213 2301, 0132 0231 1032, 0132 0231 2301, 0132 0231 3210,
  0132 1032 1203, 0132 1032 1230, 0132 1203 2301, 0132 1203 3210, 0132 1230 2301,
  0132 1230 3210, 0231 1032 1230, 0231 1032 1302, 0231 1032 2031, 0231 1032 2310,
  0231 1032 3012, 0231 1032 3201, 1032 1230 1302, 1032 1230 2310`.
- `Good δ q0`: the letters are bijective, and `DFAReturn.retAut δ q0` is aperiodic
  (`f^(N+1) = f^N`).
- `CycleLetters δ q0`: every letter acts as one cycle through `q0`, or as the identity.
- `R(family)` is the set of `T w` over the words `w` that return every automaton of the family
  to its base.  It is a subgroup of S4.  The method determines `T` iff `R ∩ V4 = 1`.

## (a) Proved in Lean: one automaton never suffices

`Start/StarHeightS4DoubleTransposition.lean` (namespace `GeneralizedStarHeight.S4Dbl`):

```
theorem cycleLetters_of_good {δ : Fin n → Fin 3 → Fin n} {q₀ : Fin n} (h : Good δ q₀) :
    CycleLetters δ q₀
theorem dbl_obstruction (hsurj : ∀ σ, ∃ w : List (Fin 3), T (FreeMonoid.ofList w) = σ)
    (x₀ : Fin 3) (ha : T (FreeMonoid.of x₀) ∈ dbl) (hδ : CycleLetters δ q₀)
    {d : Equiv.Perm (Fin 4)} (hd : d = 1 ∨ d ∈ dbl) :
    ∃ w : List (Fin 3), DFAReturn.runQ δ q₀ w = q₀ ∧ T (FreeMonoid.ofList w) = d
theorem not_determined_small (δ : Fin n → Fin 3 → Fin n) (q₀ : Fin n) (hδ : Good δ q₀) :
    ∃ u v : List (Fin 3), Tsmall (FreeMonoid.ofList u) ≠ Tsmall (FreeMonoid.ofList v) ∧
      DFAReturn.runQ δ q₀ u = DFAReturn.runQ δ q₀ v
```

Here `Tsmall` sends the three letters to `(2 3)`, `(1 2)` and `(0 1)(2 3)`.  The general form
for any onto `T` with a double-transposition letter is `not_determined_single`.  Axioms:
`propext, Classical.choice, Quot.sound`.

**Informal proof.**
1. `R` is a subgroup, because `σ^24 = 1`.
2. Let `s = T w` and `q = δ*(q0, w)`.
   - If `x0` fixes `q`: `w v` and `w x0 v` both return, where `v` is a way back.  So
     `s a s⁻¹ ∈ R`.
   - Otherwise `q = x0^k q0`, so some `w x0^j` returns, and `s ∈ R` or `s a ∈ R` (`trichotomy`).
3. `T` is onto, so step 2 holds for every `s ∈ S4`.
4. A 4-cycle `g` with `g² = a` gives `a ∈ R`.
5. For `d ≠ a` in V4, an `h` with `h² = d` and `h a h⁻¹ = a d` gives `d ∈ R` (`mem_of_trichotomy`).

Aperiodicity is used only through the cycle property.

**Open: families of two or more automata.**  The open statement is `FamilyObstruction T`, a
`def` in the same file:

```
∀ (m : ℕ) (ns : Fin m → ℕ) (δs : ∀ i, Fin (ns i) → Fin 3 → Fin (ns i)) (q₀s : ∀ i, Fin (ns i)),
  (∀ i, Good (δs i) (q₀s i)) → ∃ u v : List (Fin 3),
    T (FreeMonoid.ofList u) ≠ T (FreeMonoid.ofList v) ∧
    ∀ i, DFAReturn.runQ (δs i) (q₀s i) u = DFAReturn.runQ (δs i) (q₀s i) v
```

Step 2 fails in a product: coordinates can be mixed (some fixed by `x0`, some on its cycle), and
cycles of different lengths can leave CRT mismatches.

**Reduction to a 4-point automaton (informal, not Lean).**  For any family, `W = 1` iff the
joint state determines the coset `Stab(p)·T w` for some point `p`.  That coset is the state of
the 4-state point automaton `B_p`, in which `x0` acts with no fixed point.
- (⇐) The returning words then have values in `Stab(p)`, and `Stab(p) ∩ V4 = 1`.
- (⇒) If `R ∩ V4 = 1`, then `|R|` divides 6, so `R` is `1`, `⟨(ij)⟩`, `⟨(ijk)⟩` or a point
  stabilizer.  Each of these lies in some `Stab(p)`.  If `w` and `w'` reach the same joint state,
  then `T w' (T w)⁻¹ ∈ R`.

This gives a second proof for one automaton `A` with `CycleLetters`.  `A` maps equivariantly onto
`B_p`.  A point of `A` fixed by `x0` would map to a fixed point of `B_p`, and there is none.  So
`x0` is one cycle through all of `A`, and the image of `A` is a single `x0`-orbit of `B_p`, of size
2, not 4.  For families the same argument shows only that every reachable joint state has some
coordinate on that automaton's `x0`-cycle.

The open question, in this form: can a finite family of good automata jointly determine the
state of the point automaton `B_p`?

**Data** (Python, `M28-STARHEIGHT-S4-search/`; not Lean).  No family with `R ∩ V4 ≠ V4` was
found:
- `r2a.py`: letter-cycle automata, good or not, on n ≤ 4 states, as singles, in all 19 classes.
- `r2b.py`: all pairs of letter-cycle automata with n ≤ 3 (17,689 pairs × 19 classes).
- `r2c.py`: about 1.52 million random families of 2–3 letter-cycle automata on 2–7 states,
  over all 19 classes.

Letter-cycle automata include all good ones (and need not be aperiodic), so these results cover
good families too.

## (b) Richer observers (five classes with an S3 point stabilizer)

`r2obs.py` and `r2exp*.py`.  The classes in board tuples:
`0132 0213 1032`, `0132 0213 2301`, `0132 0231 1032`, `0132 0231 2301`, `0132 0231 3210`.
Each observer, with the good coset automata, was tested for separating `V4`.  No hits:

| observer | range | tested | hits |
|---|---|---|---|
| single good automaton | n ≤ 4 | 16,365 | 0 |
| marker: a good automaton started after the first occurrence of a letter | n ≤ 4 | 49,095 | 0 |
| marker pairs (random) | n ≤ 4 | 3,000 | 0 |
| Transfer-Lemma counter: a good automaton plus parity of the base-to-base blocks lying in one of 20 star-free block codes (starts/ends/contains/avoids `x`, length 1, 2, ≥ 3, factor `xy`) | n ≤ 3 | 14,040 | 0 |
| off-base counters: a good automaton started at `r ≠ 0`, parity of letters of a set `X` read at state `0`; also the pairing automaton, reversed | n ≤ 3, every `r`, `X` | all | 0 |
| good pairs, forward and reversed reading | n ≤ 3 | 68,445 | 0 |

Two findings:

- **The board's formula needs left cosets.**  The board described the V4 part as "counts, in
  each state of the pairing automaton started at `P_a`, of `a`".  In the forward reading this
  does not determine `T w`: there are 2198 conflicts.  What determines it is the parity of the
  `a`'s read while the S3 prefix maps `P_a` to each pairing.  That is a condition on the
  6-element left-coset automaton, with 0 conflicts (`r2exp4.py`).
- **zpcore and Bourne do not apply.**  They need translation letters; these are transpositions.
  For the smallest class the pairing automaton is good only at base `{02|13}`, not at `P_a`.

## (c) Candidate for generalized star height 2

The smallest class has `a = (23)`, `b = (12)`, `c = (01)(23)` (letters 0, 1, 2).  Let
`δ(q, x) = T(x)(q)` on `{0,1,2,3}`, and let `L_q` be the set of words whose run from `q` returns
to `q`.  Then

```
L_0 = (a + b + c(a + b((a+c)b*(a+c))*b)*c)*
L_1 = (a + c(a+b)*c + b((a+c)b*(a+c))*b)*
L_2 = ((a+c)b*(a+c) + b(a + c(a+b)*c)*b)*
K   = {w | T w = 1} = L_0 ∩ L_1 ∩ L_2
```

- `K` is recognised by the 24-state Cayley automaton of S4.
- `L_0` is recognised by the 4-state automaton above, with start and accept state `0`.
- `candidate_check.py` tests these expressions against the automaton on 200,000 random words:
  0 mismatches.
- **Candidate:** `K`, or simply `L_0` (4 states).  By the reduction in (a), the method handles
  `K` iff it handles some `L_p`, i.e. iff a family of good automata determines `B_p`.

What is proved and what is not:
- Proved: no single good automaton separates `V4` for these `T`.
- Not proved: that finite families cannot (`FamilyObstruction`).
- Not proved: any lower bound.  An obstruction to this method is not a lower bound on star
  height: `K` may have height 1 by another argument.
- No earlier candidate of this kind found.  PST's 1992 candidate is now known to have height 1
  (`LPST_height_one`).
