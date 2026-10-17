# M28-STARHEIGHT-PST-HEIGHT-ONE: `L_PST` has generalized star height exactly 1

`L_PST = (ab*a ∪ ba*b(ab*a)*ba*b)*` (Pin–Straubing–Thérien, Inform. and Comput. 1992, §8, stated
there as an open candidate for height 2) has generalized star height **exactly 1**. Lean, no
`sorry`, no `native_decide`, no new axioms (`M28-STARHEIGHT-PST-HEIGHT-ONE-axioms.txt`). No earlier
proof was found, by us or by a web search.

## 1. Lean results

`Start/StarHeightPSTHeightOne.lean`, namespace `GeneralizedStarHeight.PST`:

- `b0count_mod_two`, `s4state_height`, `K_height_one`;
- `LPST_height_one : HasHeightAtMost LPST 1` (from `K_height_one` by `pst_candidate_iff`);
- `LPST_not_starFree : ¬ HasHeightAtMost LPST 0`: `a^(2k) ∈ L_PST`, `a^(2k+1) ∉ L_PST`, so
  `L_PST` is not aperiodic (`aperiodic_of_starFree`).

`Start/StarHeightDFAReturns.lean` (R2, row M28-STARHEIGHT-STARFREE-RETURNS):
`height_one_of_starFree_returns`, for any automaton `δ : Q → α → Q` (letters need not act
bijectively, `Q` need not be finite). It factors at the last visit to `q₀`:
`{w | q₀·w = q} = (firstReturn δ q₀)∗ · avoidTo δ q₀ q` (`runQ_eq_kstar_mul`). Both factors are
languages of one automaton `retAut` (a copy of `δ` that dies after the first return), so a
`starFree_of_dfa_closed` certificate proves them star-free.

`Start/StarHeightPSTRecognizer.lean` (R3(b)): `recog_languages_height_one`: every language
recognized by the PST morphism `S₄ × Z₂` (`a ↦ ((2 3), 0)`, `b ↦ ((0 1 2 3), 1)`) has height
at most 1. `pstS4_languages_height_one` does the same for its `S₄` part.

## 2. The identity

The `S₃` automaton: `a = (0 1)`, `b = (0 2)`, and `b0count 0 w` is the number of `b` read in state
`0`. The `S₄` automaton `s4state`: `a = (0 1)`, `b = (0 1 2 3)`, start `0`. Let `Qs 0 = {1,2}`,
`Qs 1 = {0,2}`, `Qs 2 = {2,3}`. Then

    b0count 0 w ≡ |w|_b + [s4state w ∈ Qs (stateOf 0 w)]   (mod 2).

Proof: induction on `w`, adding one letter at the end. The step is `qs_step`, a `decide` over
`Fin 2 × Fin 3 × Fin 4 × AB` (48 cases, `Fin`-valued data). Then `K` is the finite union, over the
`(r, s, q)` with `(r + [q ∈ Qs s]) % 2 = 0`, of `{|w|_b ≡ r} ∩ {stateOf 0 w = s} ∩ {s4state w = q}`.

## 3. The three automata

Each automaton has height-one state languages.

- (i) `|w|_b mod 2`: a commutative count (`countIn_height`).
- (ii) `stateOf 0`: `A₃` has prime index in `S₃` (`stateOf_height`).
- (iii) `s4state`: star-free first returns. From `0` both letters go to `1`. From `1`, `a`
  returns and `b` goes to `2`. `a` fixes `2` and `3`, and `b` sends `2 → 3 → 0`. So the code is
  `X4 = (a ∪ b)(a ∪ b a* b a* b)`, and the paths avoiding `0` are
  `P_0 = ε`, `P_1 = a ∪ b`, `P_2 = (a∪b) b a*`, `P_3 = (a∪b) b a* b a*`.
  They are star-free, because `a* = (Σ*bΣ*)ᶜ`. In Lean, a `decide +kernel` certificate on the
  6 reachable states of `retAut move4 0` proves this (`ret4_cert`).

## 4. Why the obstructions do not apply

- Obstruction 2 (`pst_firstReturn_not_starFree`) is about **one** permutation automaton that
  recognizes `L_PST`. None of (i)–(iii) recognizes `L_PST`. Their product does, and its first
  returns are not star-free, as Obstruction 2 says they must not be.
- Obstruction 1 (`pst_not_metabelian`): automaton (iii) has transition group `S₄`, which is not
  metabelian. The method does not go through an abelian normal subgroup.

## 5. The explicit expression

The expression below is consistent with §2 and with the factorization of R2. We checked it
by computer on all words of length ≤ 16. It is **not** stated as a `Language` identity in Lean.

    L_PST = (ab*a ∪ ba*b)* ∩ ( (E ∩ X4*·(ε ∪ (a∪b) b a* b a*))
                             ∪ (Eᶜ ∩ X4*·((a∪b) ∪ (a∪b) b a*)) ),   E = (a* b a* b)* a*.

Every star in it is applied to a star-free language (`(ab*a ∪ ba*b)*` is `{stateOf 0 w = 0}`,
whose first-return code `ab*a ∪ ba*b` is star-free).

## 6. How it was found

The user ran a computer search over Boolean combinations of permutation automata on ≤ 6 points.
Each letter acts as the identity or as a single cycle through the base point, and the "avoid the
base point" monoid is aperiodic. No single automaton and no pair works for `K`. The first hit was
the triple (i)–(iii).

## 7. R3: how far the method reaches (computational, not Lean except (b))

`M28-STARHEIGHT-PST-HEIGHT-ONE-search.py`. "Good" automaton = a transitive permutation automaton
with star-free first returns, or a commutative count.

- **(b) The PST morphism: yes (Lean).** The joint state of `|w|_a mod 2`, `|w|_b mod 2`,
  `stateOf 0` and `s4state` determines `recog w ∈ S₄ × Z₂` (48 joint states, all reachable;
  `recog_eq_of_jstate`). So every language recognized by `recog` is a Boolean combination of
  height-one languages. In the coset test below, the good subgroups of `S₄ × Z₂` meet in `{1}`.
- **Coset test** (`quot`). Let `G` be the transition group of the target automaton. Every good
  automaton whose group is a quotient of `G` is a coset automaton `G/H`. Boolean combinations of
  such automata determine the target iff the intersection `D` of all good `H` fixes it.
  - `K` mod 2: `|G| = 48`, 98 subgroups, `D = 1`: determined.
  - `K3` (`b0count mod 3`): `|G| = 162`, 142 subgroups, only 5 good (indices 1, 2, 3, 3, 6),
    `|D| = 9`: **not determined**.
  - F20 instance `Z4Rot2Abc`, `n = 2` (letters with displacements `0, 1, 2` in `Z₄`): `|G| = 64`,
    129 subgroups, 8 good (indices 1, 2, 4, 8; those of index 4 and 8 only as abelian quotients),
    `|D| = 8`: **not determined**.
  So for `K3` and for `Z4Rot2Abc` (`n = 2`) any combination must use automata whose groups are
  not quotients of the target's group.
- **Free automata search** (`combo`). All 149 transitive 2-letter permutation automata on 2–5
  points with star-free first returns, any letter permutations, up to relabelling. Each
  combination also gets `stateOf 0`, `|w|_a mod 2` and `|w|_b mod 6` (mod 4 for `N = 4`).
  - `K` mod 2: 2 single automata suffice (one is `s4state`).
  - `K3`: no single automaton, none of the 11,026 pairs, and none of the 103,607 triples with
    two automata on ≤ 4 points.
  - `K` mod 4: no single automaton, no pair.
- Not covered: Transfer counts of first-return blocks, automata on ≥ 6 points with arbitrary
  letters, recoded alphabets, and `HCoreHeightOne (Perm (Fin 3))` in general.

## 8. Order < 24 (row M28-STARHEIGHT-ORDER-LT-24)

`mulEquiv_F20_of_centralizer` (`Start/GroupOrderTwentyF20.lean`): if `|G| = 20` and a Sylow
`5`-subgroup `P` has `|C(P)| = 5`, then `G ≃* F20`. `P = ⟨x⟩` is normal and self-centralizing. At
most 5 elements conjugate `x` to `x` and at most 5 to `x⁻¹`, so some `y` conjugates `x` to `x²` or
`x³` (then `y³` gives `x²`). Then `y⁴ = 1`, and `⟨b, a⟩ ↦ x^b y^(log₂ a)` is an injective
morphism. Hence `height_one_of_card_lt_twentyfour` (with `hF : IsEmpty (G ≃* F20)`) and, under
`Z4CoreRot2`, `height_one_of_card_lt_twentyfour_of_rot2` (`Start/StarHeightOrderLtTwentyFourF20.lean`).

## 9. Open

`K3 k = {w | b0count 0 w % 3 = k}` (row M28-STARHEIGHT-S3-CORE), and `Z4Rot2Abc` (F20).
