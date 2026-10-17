# M28-STARHEIGHT-PST-CANDIDATE and M28-STARHEIGHT-S3-CORE

`L_PST = (a b* a ∪ b a* b (a b* a)* b a* b)*` is Pin–Straubing–Thérien's candidate for star
height `2`. The terminal statement `HasHeightAtMost LPST 1` (or its negation) is **open**.

Section 1 is Lean-verified, with no `sorry`, no `native_decide` and no new axioms (see
`M28-STARHEIGHT-ELEMENTARY-axioms.txt`). Sections 2 and 3 are informal or computational.

## 1. Lean results

Files: `Start/StarHeightPSTLanguage.lean`, `StarHeightPST.lean`, `StarHeightPSTObstruction.lean`,
`StarHeightPSTReturns.lean`.

- **The language and its automaton.**
  - `PST.LPST` is the regular expression, built with the operations of `Language` on `AB = {a, b}`.
  - `PST.LPST_eq : LPST = {u | stateOf 0 u = 0 ∧ b0count 0 u % 2 = 0}`, where `a` acts as `(0 1)`,
    `b` acts as `(0 2)`, and `b0count` counts the `b` read in state `0`.
  - The proof factors a returning word into first returns, `ab*a` (no `b` read in `0`) and
    `ba*b` (one).
- **The recognizer.**
  - `PST.LPST_recognized : LPST = {w | recog (ofList w) ∈ {g | decode g = (0, 0)}}`.
  - Here `recog : FreeMonoid AB →* Perm (Fin 4) × Multiplicative (ZMod 2)` sends `a ↦ ((2 3), 0)`
    and `b ↦ ((0 1 2 3), 1)`.
  - `decode` reads the state from `(σ⁻¹ 0, σ⁻¹ 3, z)`.
  - These images were found by computer search. Lean checks them on all pairs, in
    `decode_step_a` and `decode_step_b`.
- **The reductions.**
  - `height_one_prod`: a language recognized by `G × H` is a Boolean combination of languages
    recognized by `G` and by `H`.
  - `PST.pst_candidate_height_one_of_S4 (h : ∀ {A} [Finite A] T F, …Perm (Fin 4)…) : HasHeightAtMost LPST 1`.
  - `PST.pst_candidate_height_one_of_core : HCoreHeightOne (Equiv.Perm (Fin 3)) → HasHeightAtMost LPST 1`.
- **The smallest open instance** (row M28-STARHEIGHT-S3-CORE).
  - `PST.pst_candidate_iff : HasHeightAtMost LPST 1 ↔ HasHeightAtMost K 1`.
  - `K = {w | (hcount rho3 1 b w + hcount rho3 (swap 1 2) b w) % 2 = 0}`, with `rho3 a = (0 1)`
    and `rho3 b = (0 2)`. This is one `S₃`-coset count: the `b` read while the prefix lies in
    `Stab(0) = {1, (1 2)}` (`b0count_eq_hcount`).
  - Direction `K → L_PST`: `L_PST = K ∩ {0·w = 0}`.
  - Direction `L_PST → K`: `K` is the union, over the states `s`, of `{0·w = s}` intersected with
    `L_PST`, `L_PST a⁻¹` or `L_PST b⁻¹`.
  - `{0·w = s}` is an `S₃` language of height one (`A₃` has index `2`): `stateOf_height`.
  - So the PST question is exactly the instance of the `S₃`-core with alphabet `{a, b}`,
    `ρ = rho3`, letter `b`, states `1` and `(1 2)`, and modulus `2`.
- **Obstruction 1** (`pst_not_metabelian`, `pst_not_abelian_by_abelian`).
  - No finite group with `[[x,y],[z,t]] = 1` recognizes `L_PST`.
  - Witness: `W = [[a,b],[a,bb]]`, with `x⁻¹ = x^(M−1)` and `M = 48·|G|`. In `G` it acts as `ε`.
    In `S₄ × Z₂` it is a nontrivial element of `V₄`, so `W ∉ L_PST` while `ε ∈ L_PST`.
  - Products of metabelian groups are metabelian. Hence `L_PST` is no Boolean combination of
    languages recognized by metabelian groups, whatever the moduli. Such languages include:
    - letter counts;
    - every `Z_p` counter (`Z_p ≀ Z_p`);
    - every group covered so far: prime index, elementary abelian quotient, `A₄`, the `Z₄` cases.
- **Obstruction 2** (`pst_firstReturn_not_starFree`).
  - Take any finite automaton whose letters act as permutations and which recognizes `L_PST` from
    `q₀`. Its first-return code to `q₀` is not star-free.
  - Witnesses: `bb aᵉᴺ bᵏ ∈ X` and `bb aᵉᴺ⁺¹ bᵏ ∉ X`, where `e` is the order of `a`.
  - So the route of the `Z_p` core (the stabilizer as the star of a star-free code) fails in
    every recognizer, however large.

## 2. What the ROT2 argument assumes, and what each method breaks

The argument (`M28-STARHEIGHT-ROT2-OBSTRUCTION.md` §3) assumes:

- (A1) an exact **linear** identity;
- (A2) quantities read by **aperiodic** automata on blocks of one code, whose rate along a long
  run depends only on the recurrent class;
- (A3) one code, of returns to **one** state;
- (A4) only the growth along a long run of one letter is used.

| method | breaks | outcome |
|---|---|---|
| linear span (§3, M1) | none | `N` is not in the span |
| Boolean functions of residues (M2) | A1 | collisions modulo 2 and 4; no exact collision up to length 18 |
| any metabelian recognizer (Obstruction 1) | A1, A2, A4 | impossible (Lean) |
| codes of returns to a state of any permutation recognizer, so returns to cosets in any `G`-set recognizing `L_PST` (Obstruction 2) | A3 | never star-free (Lean) |
| returns to `0` with block classes (`X = ab*a ∪ ba*b` is star-free) | A1 kept | the classes `ab⁺a` and `ba⁺b` have star-free stars and are Transfer-countable. The blocks `aa` and `bb` are not (`(aa)*`, `(bb)*`). The gap is the parity of the number of `bb` blocks read from state `0`, the same `S₃` count |
| quotients `u⁻¹L`, `Lv⁻¹` | A3 | they lie in the Boolean algebra of `K` (`pst_candidate_iff` uses them) and have the same recognizer, so obstructions 1 and 2 apply |
| alphabetic morphisms, injective substitutions, recoding runs by length mod 4 | A2 | if `L_PST = φ⁻¹(L')`, the syntactic monoid of `L_PST` divides that of `L'`. Obstruction 1 transfers, and the recoded run language again has transition group `Z₂ ≀ S₃` (order 48) |
| unambiguous products with star-free markers | A1 | not settled. We expect group languages in the polynomial closure of metabelian-group languages to be metabelian-group languages (subgroups of Schützenberger products divide direct products). We did not prove it |

## 3. Computations (`docs/goal/evidence/M28-STARHEIGHT-PST-search.py`, not Lean-verified)

Words are taken on returning words (`0·w = 0`), where `w ∈ L_PST` iff `N(w)` is even.

The families of quantities:

- letters and the `S₃` element;
- factor counts, for factors of length `≤ 3`;
- all `Z₂` and `Z₃` translation counters, at every state;
- the block counts `#ab⁺a`, `#ba⁺b` and `#blocks`;
- the run counts by letter and run length mod 4.

Results:

- **M1, rational span** (elimination mod `2³¹−1`, words of length `≤ 10`):
  - factor length `≤ 2`: rank 38, and 39 with `N` added;
  - factor length `≤ 3`: rank 44, and 45 with `N` added.
  - So `N` is not a linear combination.
- **M2, any Boolean function of the feature values** (collisions = equal features, different
  parity of `N`):
  - single families, exact collisions:
    - letters + `S₃`: `aabb` / `abba`;
    - factors: `aaaabbaa` / `aaabbaaa`;
    - blocks: `aa` / `bb`;
    - runs mod 4: `aabbaba` / `abaabba`;
    - counters: `ababbabbabab` / `bbabaaababbb`.
  - pairs, exact collisions:
    - factors + runs: `ababbbab` / `abbbabab`;
    - factors + blocks: `ababbbaaab` / `abbbaaabab`.
  - all five families together:
    - residues mod 2 collide (words of length 16) (`aaaabaabbaaaabaa` / `aaabaaabbaaabaaa`);
    - residues mod 4 collide (words of length 18) (`aaaaababbbbbaaabbb` / `aaabbbaaaaababbbbb`);
    - there is **no exact collision** up to length 18 (174763 returning words), so larger moduli
      are not excluded at this length.
- `python3 docs/goal/evidence/M28-STARHEIGHT-PST-search.py all 14` reruns M1 (lengths ≤ 10) and the exact test for all families at lengths ≤ 14; the mod-2/mod-4 and length-18 runs use the same feature functions.

## 4. Status

- No height-one expression for `L_PST` or `K` was found. The exact gap is
  `HasHeightAtMost PST.K 1`, which is equivalent to `HasHeightAtMost PST.LPST 1`.
- Any proof must use a quantity that is:
  - neither a metabelian-group language (Obstruction 1);
  - nor a stabilizer, in a permutation recognizer of `L_PST`, written as the star of a star-free
    code (Obstruction 2).
- A proof of height `2` would need an invariant of height-one languages that separates `S₄` from
  the groups handled so far. None is known.
