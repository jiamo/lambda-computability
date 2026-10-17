# M28-STARHEIGHT-ROT2-OBSTRUCTION: why the method of the Transfer Lemma does not reach `Z4CoreRot2`

Status of the parts of this note:

- **Lean-verified**: Sections 1 and 2 (`Start/StarHeightStarFreeAperiodic.lean`,
  `Start/StarHeightRot2Obstruction.lean`).
- **Not Lean-verified**: Sections 3 and 4 (an informal argument), and the computations quoted in
  Section 5.

Setting: the smallest instance of `Z4CoreRot2`. The alphabet is `Fin 3`, with letters `a, b, c`
(`0, 1, 2`) and displacements `σr2 = ![0, 1, 2]` in `ZMod 4`. `N₀(u)` is the number of `a` read
in state `0`.

## 1. Star-free implies aperiodic (Lean)

```lean
theorem aperiodic_of_starFree {A : Type u} {L : Language A} (h : HasHeightAtMost L 0) :
    ∃ N : ℕ, ∀ u v w : List A, u ++ wpow v N ++ w ∈ L ↔ u ++ wpow v (N + 1) ++ w ∈ L
```

The proof is by induction on the star-free expression (`pump_of_expression`):

- letters, `∅` and `{ε}` take `N = 2` (`pump_short`);
- union and complement keep `N`;
- a concatenation takes `N₁ + N₂ + 1`, by a pigeonhole on where the cut falls among the copies of
  `v` (`pumpUp_mul`, `pumpDown_mul`).

This is the converse of `Aperiodic.starFree_of_aperiodic` (M28-STARHEIGHT-APERIODIC).

## 2. The two obstruction lemmas (Lean)

```lean
theorem rot2_Xc_not_starFree : ¬ HasHeightAtMost (Xc σr2) 0

theorem rot2_no_long_c_run {Y : Language (Fin 3)} (hY : HasHeightAtMost Y 0)
    (hconst : ∀ y ∈ Y, ∀ z ∈ Y, rot2Weight y % 4 = rot2Weight z % 4) :
    ∃ N : ℕ, ∀ s t : List (Fin 3), s ++ List.replicate N 2 ++ t ∉ Y
```

Here `rot2Weight y = #b(y) + 2·#c(y)`.

- **First lemma.** Take `u = b c`, `v = c`, `w = b`. Then `b c^(M+1) b` is a first return to `0`
  iff `M + 1` is odd (`rot2_bcb_mem_Xc`), so no `N` satisfies the conclusion of
  `aperiodic_of_starFree`.
- **Second lemma.** If `s cᴺ t ∈ Y`, then `s cᴺ⁺¹ t ∈ Y`. One more `c` changes `#b + 2#c` by `2`
  modulo `4`.

## 3. The informal argument (not Lean-verified)

Every proof in this project so far writes the count as a linear combination of quantities the
Transfer Lemma can handle:

- PST Proposition 6.6;
- the `A₄` identity;
- Bourne's Theorem 4.11;
- the `Z₄`-PM1 identity;
- the `Z_p` identity of M28-STARHEIGHT-Z5-CORE.

The quantities are letter counts, counts modulo a prime of "pure" counters, and block counts
`bcount K` of a class `K` of a star-free prefix code `X`, with `K∗` or `(X ∖ K)∗` star-free.
The aim is an identity `N₀ = Σ cⱼ Qⱼ`, exact on all words, or on all words in state `0`.

**Averaging over long runs of `a`.** Insert into a word a long run `aᴸ` at a position in state
`s`, and let `L` grow.

- `N₀` changes by `L·[s = 0]`.
- A star-free quantity `Qⱼ` reads `aᴸ` through an aperiodic automaton, so it changes by `L·κⱼ(s)`
  plus a bounded amount. The coefficient `κⱼ(s)` depends only on the recurrent class of the
  automaton entered on `a`.
- Matching the coefficients of `L` gives `[s = 0] = Σ cⱼ κⱼ(s)` for all reachable `s`.

**Twisted transfer operator.** The function `s ↦ [s = 0]` has a nonzero component along each
nontrivial character `χ` of `ZMod 4`. The relevant one here is `χ(s) = i^s`, on the words in state
`0` where `s = #b + 2#c mod 4`.

- For that component to appear on the right, some code automaton must carry it. Its
  `χ`-twisted transfer operator (the transition matrix weighted by `χ` of the displacement)
  must have eigenvalue `1` on a recurrent class.
- That holds exactly when `χ ∘ displacement` is a coboundary on the class. Equivalently, the
  automaton tracks `i^(#b+2#c)` on that class.
- So the class of blocks `Y` it reads must have `#b + 2#c` constant modulo `4` along a recurrent
  loop.

**Conclusion.** By `rot2_no_long_c_run`, a star-free `Y` with this property contains no long run
of `c`. A complete tracking code, however, must contain the prefixes `b cᵐ b` for every `m`: the
walk from `1` under `c` alternates `1, 3, 1, 3, …` and never returns to `0`. So the star-free
code must cut these words somewhere.

- If it cuts them, the cut pieces contain `cᴺ`, and `Y` no longer tracks the character.
- If it does not cut them, `Y ∩ b c∗ b = b c (cc)∗ b`, and `Y` is not star-free
  (`rot2_Xc_not_starFree`).

Either way, no linear combination of Transfer-Lemma quantities equals `N₀`.

This rules out the method, not the theorem. Height one for `Z4CoreRot2` remains open.

## 4. The same obstruction for `F₂₀` and `S₄` (not Lean-verified)

- **`F₂₀ = AGL(1, 5)`.** Its translation subgroup has quotient `Z₄`. A letter `x ↦ -x + β` acts on
  the quotient as rotation `2`. With a letter of odd rotation, this is exactly the
  `Z4CoreRot2` situation above. `height_one_F20_of_letters` (M28-STARHEIGHT-INDEX-FOUR-LETTERS)
  covers every `F₂₀` alphabet that avoids that combination.
- **`S₄`.** Its abelian normal subgroup `V₄` has quotient `S₃`, which is not cyclic. Tracking the
  base point needs the same kind of code. A transposition swaps two points away from the base
  point, and plays the role of `c`: runs of it never return, and their parity matters. The same
  dichotomy appears: either the code is not star-free, or it cannot track the sign character.

By contrast, for `ZMod p` with `p` prime the first-return code to `0` is star-free, whatever the
rotations (`zpX_starFree`, `Start/StarHeightZpWalk.lean`). A word of nonzero displacement brings
every state back to `0` within `p` copies. This is why M28-STARHEIGHT-Z5-CORE closes for every
prime.

## 5. Computations quoted (not Lean-verified)

These were run by the project maintainers and are reported in the request for this delivery.

- No identity on words of length ≤ 10, in a family with 8 codes and all allowed abelian
  counters, and none modulo `5` (the only modulus `F₂₀` needs).
- Transition monoids of walk automata:
  - `Z₅` with rotations `(1,1,2,3,4)` has 147 elements and is aperiodic;
  - `Z₅` with `(0,1,2,3,4)` has 157 and is aperiodic;
  - `Z₇` with `(1,1,2,3,4,5,6)` has 877 and is aperiodic;
  - `ROT2`'s `(0,1,2)` on `Z₄` gives 47 and is not aperiodic.
- The earlier search recorded in M28-STARHEIGHT-Z4-ROT2: on the returning words of length ≤ 8,
  `N₀` is not in the span of the listed families.
