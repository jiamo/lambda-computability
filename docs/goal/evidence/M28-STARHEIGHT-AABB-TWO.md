# M28-STARHEIGHT-AABB-TWO: `L(aabb, k, 2)`, good groups, and the rest of the `Z₄ × Z₂` core

Lean: `Start/StarHeightAabbTwo.lean` (R1), `Start/StarHeightGroupHeightOne.lean` (R2).
Axioms: `M28-STARHEIGHT-AABB-TWO-axioms.txt` (every new theorem: propext, Classical.choice,
Quot.sound). Scripts and outputs: `M28-STARHEIGHT-AABB-TWO-search/` (computational evidence, not Lean).

## Method

A language recognized by a product of groups is a finite Boolean combination of languages
recognized by the factors, and subgroups and quotients recognize no new languages. So if the
syntactic group of `L` divides a finite product of groups all of whose languages have height
≤ 1, `L` has height ≤ 1. `G(aabb) ≤ UT₅(F₂)` (order 256) has `G' ≅ F₂⁴` and `G/G' ≅ Z₄ × Z₄`;
every such 2-generated group is a quotient of `W = F₂/R'R²`, `R = ker(F₂ → Z₄ × Z₄)`, and
`M = R/R'R² ≅ F₂¹⁷`. Membership in a variety is linear algebra on `M`: `G(aabb)` lies in
`var(Z₂ ≀ Z₄)`, and unwinding six homomorphisms gives identity (I).

## R1 (Lean, proved)

`aabbRhoM a` sends `a ↦ 1` and every other letter to `0`. `aabbRhoP a b` sends `a, b ↦ 1`.
Both map into `Multiplicative (ZMod 4)`. Then `m₁ = hcount (aabbRhoM a) (ofAdd 1) b`,
`p₁ = hcount (aabbRhoP a b) (ofAdd 1) b`, and `r₃ = hcount (aabbRhoM b) (ofAdd 3) a`
(the `ρ_r` of the request is `aabbRhoM b`).

* `aabb_z4z2_cast_z4 (hab : a ≠ b) (u)`: identity (I) modulo 2, by induction from the right. The
  `b`-step is `aabbI_step_b`: it reduces to `(A mod 4, B mod 8)`, which gives 32 cases, each
  closed by `decide`.
* `goodMod_aabb_two [Finite α] (hab : a ≠ b) : GoodMod 2 (scount [a, a, b, b])`. The three counts
  are good by `hcoreModTwo_zmod_four.univ`, and the counter `aabbCtr` by
  `height_one_of_residues_univ` on the letter counts modulo 8. They are combined with
  `goodMod_of_det`. `goodMod_bbaa_two` follows from `goodMod_xxyy_iff`.
* `height_one_aabb_mod_two {k : ℕ} (hk : k < 2) : HasHeightAtMost {u : List (Fin 2) | scount [0, 0, 1, 1] u % 2 = k} 1`.
* `height_one_two_letters_length_four_mod_two_all`: the statement of
  `height_one_two_letters_length_four_mod_two` without `hne`.
* `height_one_two_letters_length_four_mod_prime_all`: every prime `p`, including 2. It assumes
  `[Finite α]` (the odd-prime theorem gets it from its section).
* The conditional theorems of round 4 are unchanged.

## R2 (Lean, proved)

`def GroupHeightOne (G : Type) [Group G] : Prop := ∀ (α : Type) [Finite α] (T : FreeMonoid α →* G) (F : Set G), HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1`.
The alphabet is in `Type`; `GroupHeightOne.univ` gives the same conclusion for alphabets in any
universe (through `Fin m` and `invAlph`).

* Closure:
  * `of_mulEquiv`;
  * `of_injective` (subgroups);
  * `of_surjective` (quotients; each letter is lifted with `Function.surjInv`);
  * `prod` (finite `G`, `H`; from `height_one_prod`);
  * `pi` (index `ι : Type` finite, finite factors);
  * `of_dvd_pi`: a quotient of a subgroup of a finite product of finite good groups is good.
* Instances:
  * `groupHeightOne_of_comm`;
  * `groupHeightOne_Z2WrZ4`;
  * `groupHeightOne_UT4 n`;
  * `groupHeightOne_alternatingGroup_four`;
  * `groupHeightOne_of_abelian_prime_index`;
  * `groupHeightOne_of_frattini_abelian`;
  * `groupHeightOne_of_exponent_two_normal_z4`: an abelian exponent-2 normal `N` with
    `G ⧸ N ≃* Multiplicative (ZMod 4)`.
* The optional second proof of `height_one_aabb_mod_two` through the six homomorphisms was not
  done. It needs a Lean check on the joint group of order 2048.

## R3 (computational evidence, not Lean)

**(a)** `aabb_variety.py` is the script of the request, verbatim. `aabb_variety.out` is identical
to the expected output: ranks 8 of 17 and 4; the same six homomorphisms; joint group 2048, of
which the `Z₂≀Z₄⁶` part is 2048 and determines `G(aabb)`; 0 of 64 step cases fail; 32767 words
give 0 mismatches. In part (4), every state gives 256 (letter `a`) and 1024 (letter `b`), and
none of these groups is in `var(Z₂≀Z₄)`.

**(b)(i)** Yes. Write `c(x,(s,t)) = #{i : u_i = x, A_i ≡ s mod 4, B_i ≡ t mod 2}`.
* Modulo 2 and the good terms, every `b`-count is `≡ c₀ = c(b,(0,1))` and every `a`-count is
  `≡ c(a,(0,0))` (`z4z2_core_span.py`). The quotient (16 counts + good)/good has dimension 2 on
  all words of length ≤ 10, 12 and 14, and no single count is good.
* No products are needed. Each difference is an F₂-sum of `Z₄` counts plus a function of
  `(A mod 4, B mod 8)`. `z4z2_formulas.py` fits the sums on words of length ≤ 12 and checks them
  on length ≤ 14. Notation: `z[ra,rb;g;x] = #{i : u_i = x, ra·A_i + rb·B_i ≡ g mod 4}`.
* Short ones:
  * `c(b,(0,0)) + c₀ = z[1,0;0;b]`;
  * `c(a,(0,1)) + c(a,(0,0)) = z[1,0;0;a]`;
  * `c(a,(3,1)) + c(a,(0,0)) = z[1,0;0;a] + z[1,0;0;b] + [A ≡ 0 mod 4, B odd]`;
  * `c(b,(2,1)) + c₀ = z[0,1;1;b] + z[0,1;2;b] + z[1,0;0;b] + z[1,0;1;b] + z[1,1;0;b] + z[1,1;1;b]`.
* The rest are in `z4z2_formulas.out`. Identity (I) is the case `(2,1) + (3,1)`. So the two-letter
  `Z₄ × Z₂` core modulo 2 comes down to `c₀` and `c(a,(0,0))`, plus `Z₄` counts and counters.

**(ii)** No, for the good groups the repository proves that lie in `A₂A₄` (`c0_variety.py`).
* Families: `Z₂≀Z₄`, `UT₄(F₂)`, and `FA` (every 2-group with abelian `G'G²`, the
  Frattini-abelian theorem). For `FA` the relatively free object is `W/Φ(W)'`, with
  `M ∩ Φ(W)' = (x²−1)M + (y²−1)M + F₂[Q]·[x², y²]`, computed in the Magnus embedding (rank 17,
  faithful).
* `E4` (exponent-2 normal subgroup with quotient `Z₄`) lies inside the `Z₂≀Z₄` span: rank 8.
* Ranks on `M`: `Z₂≀Z₄` 8, `UT₄(F₂)` 3, `FA` 5. Every union has the same rank 8, so `UT₄(F₂)` and
  `FA` add nothing to `Z₂≀Z₄`.
* `c₀` (syntactic group of order 1024, rank 6) and `c(a,(0,0))` (order 256, rank 5) are outside
  every combination, and so are the single counts at `(2,1)` and `(3,1)`.
* So the variety method with these groups cannot reach `c₀`. A new good group is needed whose
  homomorphisms reach the 9-dimensional common kernel in `M`.

**(iii)** Which counts `L(w, k, 2)` with `|w| = 4` have a syntactic group in `A₂A₄`
(`words_a2a4.py`; up to renaming)?
* In `A₂A₄`: `aaab`, `aaba`, `aabb`, `abaa`, `abbb` (all in `var(Z₂≀Z₄ + UT₄(F₂) + FA)`), and the
  three-letter `aabc` and `abcc` (order 512).
* Not in `A₂A₄`: `abab`, `abba` (both proved in Lean anyway), and `abac`, `abbc`, `abca`, `abcb`,
  `abcd`. The Lie-bracket classes are not even metabelian: `A₂A₄` groups are metabelian, which is
  consistent with M28-STARHEIGHT-LIE-BARRIER.
* `aabc`/`abcc` at `p = 2` are open in Lean: `height_one_scount_xyz_mod_prime` needs `i < p`. The
  three-generator W-test (`aabc_wtest.py`, with `M` of rank 129) finds them outside
  `var(Z₂≀Z₄ + UT₄(F₂) + FA)`.
  * Homomorphisms were sampled: 3000 into `Z₂≀Z₄` and 1500 into `UT₄(F₂)`. The ranks were stable
    from the first 500 (28 and 11).
  * `FA` is exact. Sanity check: `aabb` with a trivial or repeated third letter is in.
  * A negative answer from sampled homomorphisms is evidence only.
* The other open board cores were not run through the test:
  * the `D₄` core (its natural recognizer `Z₂ ≀ D₄` has the non-abelian quotient `D₄`);
  * the shear/`abac` core (Lie barrier);
  * the `S₃` core (not a 2-group);
  * the rotation-2 `Z₄` core for `n = 4` (not examined).
* So among the board's open counts, the test applies to `c₀`, `c(a,(0,0))` and `aabc`.
