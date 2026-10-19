# Scattered subword counts and nilpotent groups

`scount w u` = number of occurrences of `w` as a scattered subword of `u`;
`L(w, k, n) = {u | scount w u ≡ k mod n}`.  Lean: `Start/StarHeightNilpotent.lean`,
`Start/StarHeightUT4.lean`, `Start/StarHeightNilpotentFour.lean`.  Axioms of every terminal
theorem: `propext, Classical.choice, Quot.sound` (`M28-STARHEIGHT-NILPOTENT-axioms.txt`).

## R1: length at most 3, every modulus (M28-STARHEIGHT-NILPOTENT-THREE)

**Identity** (`scount_abc_identity`).  For distinct `a, b, c` and `ψ` sending `c` to `a`:

    scount [a,b,c] u + scount [a,a,b] (ψ u) = |u|_c·scount [a,b] u + scount [a,a,b] u + scount [c,c,b] u

Proof: over each `b`, with `A`, `C` the `a`'s and `c`'s before it, `scount [a,b,c] = Σ A·(|u|_c − C)`
and `A·C = C(A+C,2) − C(A,2) − C(C,2)`; `Σ C(A+C,2)` is `scount [a,a,b] (ψ u)`.  In Lean it is an
induction on `u` from two length-2 lemmas: `scount [a,b] (ψ u) = scount [a,b] u + scount [c,b] u`
and `scount [b,c] u + scount [c,b] u = |u|_b·|u|_c`.

**Engine.**  `GoodCount g`: every residue class of `g` modulo every `m` has height ≤ 1.  Good counts
are closed under `+`, `·`, `f + g = h` (`g, h` good ⇒ `f` good) and inverse letter maps; a count
whose residue mod `m` is fixed by residues of finitely many good counts is good
(`goodCount_of_det`, from `height_one_of_residues_univ`).  Position formula
(`scount_rep_eq_sum`): `scount (xⁱ y zʲ) u = Σ_{u_t = y} C(|u_{<t}|_x, i)·C(|u_{>t}|_z, j)`.
`C(s,i) mod n` depends on `s mod N` when `n·i! ∣ N` (`choose_cast_mod`).  With `N = 2n·i!·j!`,
`scount (xⁱ y xʲ) mod n` is a combination of `|u|_x mod N` and the counts of `y` read in each state
of the counter of `x` mod `N`, which are `pcount` counts of a fixed letter
(`pcount_fixed_height_one`, PST Prop. 6.6).  This is PST Theorem 7.4 for every modulus
(`height_one_scount_pst`).

**Shapes** (`goodCount_scount_le_three`):

| `w` | route |
|---|---|
| `[]` | constant 1 |
| `xⁱ` | `C(\|u\|_x, i)`, residue of `\|u\|_x` mod `n·i!` |
| two letters, length 2–3 | `xⁱ y xʲ`: `xy, xxy, xyx, yxx` (PST 7.4) |
| `abc` distinct | the identity: `[a,a,b]` merged, `[a,b]`, `[a,a,b]`, `[c,c,b]`, `\|u\|_c` |

Terminal: `height_one_scount_le_three`, and `height_one_abc_mod_four` (`L(abc,k,4)` over `Fin 3`).

**UT4 corollary** (`height_one_UT4`).  `UT4 n` = upper unitriangular 4×4 matrices over `ZMod n`,
six entries with the matrix law.  `UT4.prod_eq_entries`: the entries of `T w` are `ZMod n`
combinations of `scount v w`, `|v| ≤ 3` (the (1,4) entry is `Σ_x |w|_x t(x)₁₄ + Σ_{x,y}
scount[x,y]w (t(x)₁₂t(y)₂₄ + t(x)₁₃t(y)₃₄) + Σ_{x,y,z} scount[x,y,z]w t(x)₁₂t(y)₂₃t(z)₃₄`).
The general class-3 statement (every group of nilpotency class ≤ 3) follows from Thérien's theorem
(a language is recognized by a finite nilpotent group of class `c` iff it is a Boolean combination
of `L(w,k,n)` with `|w| ≤ c`); that step is cited, not formalized.

**Literature.**  Pin–Straubing–Thérien 1992: Theorem 7.4 (`L(xⁱyxʲ,k,n)`, height ≤ 1, all `n`);
Theorem 7.5 (`L(abc,k,n)`, square-free `n` only); "We were not able to treat completely the case of
words of length 3."  Bourne (thesis, St Andrews 2017), Question 5.2 (non-square-free `n`) and 5.3
(`|w| ≥ 4`).  We found no earlier proof of the length-3 case for all `n`.

## R2: length 4 modulo a prime (M28-STARHEIGHT-NILPOTENT-FOUR, partial)

* `height_one_scount_xyz_mod_prime`: `p` prime, `i, j < p`, letters `x, y, z` (may coincide):
  `L(xⁱ y zʲ, k, p)` has height ≤ 1.  `C(s,i) mod p` depends on `s mod p` (`i!` a unit), and the
  position formula gives a combination of counts of `y` in the states of the translation automaton
  on `(Z/p)²` (`x ↦ (1,0)`, `z ↦ (0,1)`) — `vcount_height_one_prime` — and `|u|_z mod p`.
* `height_one_aabb_mod_prime` (`p ≠ 2`).
* `height_one_two_letters_length_four_mod_prime`: `p` odd, every `w` of length 4 over two letters.
  `xyxy`: `scount[x,y]² = 4xxyy + 2xyxy + 2xxy + 2xyy + xy`; `xyyx`: `|u|_x·scount[y,y,x] =
  xyyx + yxyx + 2yyxx + yyx`.

## R3: the frontier at length 4 (exploration, not Lean-verified)

Scripts: `M28-STARHEIGHT-NILPOTENT-search/` (`span_length4.py` → `span_output.txt`,
`frattini_length4.py` → `frattini_output.txt`, `state_checks.py`).

**(a) Span** (exact: the `scount w`, `|w| ≤ 4`, are a basis over every field — unitriangular;
work modulo lengths ≤ 3; generators: shuffles `v₁ ш v₂`, PST shapes, `x⁴`, for odd `p` the R2
shapes, and pullbacks along all letter maps; "closed" also closes under pullbacks and reversal —
same numbers).  Missing directions per content (one multiset):

| content | p = 3, 5, 7, 10007 | p = 2 |
|---|---|---|
| (4), (3,1) | 0 | 0 |
| (2,2) | 0 | 2: `aabb+bbaa`; `abab+abba+baab+baba` |
| (2,1,1) | 1: `−abac+abca+acab−acba+baac−baca−caab+caba` | 1 (same, all signs +) |
| (1,1,1,1) | 3 | 3 |
| (1,1,1,1) given (2,2), (2,1,1) | 0 | 1 (sum of all 24 permutations) |

This confirms the brief's data and adds the last `p = 2` entry.

**(b) Odd p.**  `height_one_of_abelian_normal_exponent_prime` applies to a `p`-group `G` iff its
Frattini subgroup `Φ(G) = [G,G]Gᵖ` is abelian.  For the group recognizing all `L(w,k,p)` (minimal
Moore automaton), `p = 3`: `Φ` is abelian for every `|w| ≤ 3` and for `aaab, aaba, aabb, aabc,
abab, abba`, and non-abelian exactly for `abac, abbc, abca, abcd` (up to renaming and reversal).
These are exactly the length-4 words with a nonzero coefficient in some `[[x,y],[z,t]]`
(Lie-algebra check, all `p`): for `abac`, `[[a,b],[a,c]]` gives `E₁₅` in `UT(5)`.  So the span
frontier and the failure of the prime-index method coincide.  `H(Z/p)` itself and `UT(4,Z/p)`
(`[G,G]` abelian) are covered by that theorem; the obstruction is one level up.
Heisenberg form (`state_checks.py`, checked): `scount abac u = Σ_{u_t=b} A_t(S − S_t − A_t(C − C_t))`
with `(A,C,S) = (|·|_a, |·|_c, scount[a,c])`, the `H(Z/p)` counter.  Why the known methods stop:
the first-return code of a non-cyclic group is not star-free (an element outside `⟨T w⟩` never
returns), so the `zpcore` fixed-letter argument fails; the character sum fails because the
non-linear characters of `H(Z/p)` vanish off the centre.  Not closed.  If the `H(Z/p)` count were
good mod `p`, (2,1,1) would follow, and then (1,1,1,1) (table, last row): all of length 4 mod odd `p`.

**(c) p = 2.**  `abab`, `abba` have abelian `Φ` (2-group), so `height_one_of_abelian_normal_exponent_two`
would apply to their recognizing groups (group computation not in Lean); with them the
`abab+abba+baab+baba` direction is reached (`span_output.txt`, block "abelian-Frattini words").  `aabb + bbaa` is not:
`scount aabb mod 2` is the count of the moving letter `b` in states `(|·|_a mod 4, |·|_b mod 2)` of
`Z/4 × Z/2`; the cyclic-quotient counts — the Z4 cores for `A` and for `A + 2B` (the latter is the
open `Z4CoreRot2` configuration, cf. `Z4Rot2Abc`) and the `(Z/2)²` counts — have rank 6 in
`F₂⁸`, and the needed `N(2,B) + N(3,B)` is outside (rank 7).  So it does not reduce to the Z4 cores
on the board, even granting `Z4CoreRot2`; it needs a letter-in-state count on `Z/4 × Z/2`.

**(d) Programme.**  Finite nilpotent ⇒ product of `p`-groups; by Eilenberg the `p`-group languages
are Boolean combinations of `L(w,k,p)`.  First cases not reached: `p = 2`, `L(aabb,k,2)` (two
letters); odd `p`, `L(abac,k,3)` (three letters).
