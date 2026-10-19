# M28-STARHEIGHT-SHEAR: `L(abac, k, p)` and the shear count

## 1. Lean (`Start/StarHeightShear.lean`, no `sorry`, axioms in `M28-STARHEIGHT-SHEAR-axioms.txt`)

Letters `a, b, c = 0, 1, 2 : Fin 3`.  `shState p v = (|v|_a, scount [a,c] v) : ZMod p × ZMod p` and
`shcount p q u = #{t | u_t = b ∧ shState p (u.take t) = q}` (Finset form of the requested
definition, same meaning).  With `A, C, S` = `|·|_a, |·|_c, scount[a,c]` of the whole word, proved
modulo every `p` by induction on the last letter:

    scount abac ≡ S·scount ab − Σ_q q₁q₂·shcount q − C·Σ_b A_t² + Σ_b A_t²C_t       (scount_abac_cast)
    scount abca ≡ (A·C − S)·scount ab + Σ_q q₁q₂·shcount q − A·Σ_b A_tC_t          (scount_abca_cast)

`Σ_b A_tⁱC_tʲ = Σ_q q₁ⁱq₂ʲ·vcount (A,C) q b`, letter-in-state counts of the translation automaton
`(A, C)` on `(Z/p)²` (`vcount_height_one_prime`).  Hence `height_one_abac_of_shear` and
`height_one_abca_of_shear`, for every prime `p`, `2` included.

At `p = 2` the reduction is an equivalence (`shear_mod_two_iff_abac`), by

    shcount q ≡ scount acab + (q₂+1)·scount ab + q₁·scount acb + (q₁+1)(q₂+1)·|u|_b   (mod 2)

(`shcount_two_cast`; from `[A = α][S = μ] = (A+α+1)(S+μ+1)` and `A·S = 2·aac + aca + ac`).
`acab` is `abac` with `b ↔ c`.  So for `p = 2`, `shear_height_one` is exactly `L(abac, k, 2)`.

## 2. The obstructions (Python/C in `M28-STARHEIGHT-SHEAR-search/`, not Lean)

`G` = transition group of the automaton of `shcount q mod 2` (states `(A, λ, k)`).

- Confirmed (`group_facts_output.txt`): `|G| = 128` for each `q`, element orders
  `{1:1, 2:43, 4:68, 8:16}`, 576 subgroups, `N = ⟨[x,y], x²⟩` of order 16 and non-abelian.  Same
  numbers for the group of `scount abac mod 2`.  Correction: besides index 1 and 2 (star-free
  returns), the abelian quotients (index 4, 8) are also good; still `D = N`, which does not fix the
  target.
- New (`obstruction_output.txt`, `minimal_counters_output.txt`): `Z(G) = ⟨z⟩` has order 2; all 16
  elements of order 8 have fourth power `z`; `abc, bca, cab, bac` are such words.
- The counters see everything but `z`: the loops of the letter counts mod 2 and of every
  `scount w mod 2`, `|w| ≤ 3`, have image `{1, z}` in `G` (`scount acc, bac, ccc` mod 2 already do).
  Adding all letter-in-state counts mod 2 of the 64 translation automata on `(Z/2)²` changes
  nothing.  Witnesses with equal counters and different parity: `acacbab`/`babcaca` (moduli 2, 4),
  `abcbbacab`/`bacabbcba` (moduli 8, 4) (`counters_output.txt`).
- The order obstruction, with an explicit witness: `(abc)⁴` maps to `z`, and `shcount q ((abc)⁴)` is
  odd for every `q`.  So no family of components on which `(abc)^{4m}` (`m` odd) acts trivially
  determines `shcount q mod 2`: `ε` and `(abc)^{4m}` agree on it.  This covers every family of
  permutation automata on ≤ 7 points together with counters mod 2 (letter counts, `scount` of
  length ≤ 3, translation-automaton counts; groups of exponent dividing 4).
- `p = 3`: the group of `shcount (0,0) mod 3` has order `3¹²`, centre of order 3, element orders
  `1, 3, 9`.  (`3⁸` in the brief is the group of `L(abac, k, 3)`; not recomputed.)  The mod-3
  polynomial-identity result was not rechecked.
- First returns are not star-free on `Sh_2`, nor on the regular `D4` automaton (8 points): `a`
  has 2-cycles away from the base point (`a c²ᵏ a` returns, `a c²ᵏ⁺¹ a` does not).

## 3. What was tried

Determination is tested exactly (`schreier.py`, `imtest8.c`, `imtest_gen.c`): with the counters
included, `Im ⊆ {1, z}`, and the family determines `shcount (0,0) mod 2` iff `z ∉ Im`.  A "good
automaton" is transitive, each letter the identity or one cycle through `0`, with star-free first
returns.  "Base counts" = parities of the letters fixing `0` read in state `0` (a fixed-letter
count at a star-free base point; good by the first-return block count, Lean proof not written).

1. **Covering families with counters.**
   - Good automata on ≤ 5 points, all cycle lengths, ± base counts, mod-2 counters: 0 of 19,756
     (`central_bit_output.txt`; forced by the order obstruction).
   - With `|u|_a, |u|_b, |u|_c mod 8` added (the order obstruction no longer applies): every
     transitive automaton on ≤ 7 points (letters identity or one cycle through 0, any length,
     25,315,365 automata): 0 hits (`imtest_gen_output.txt`).
   - 8 points, cycles of length 1, 2, 4, 8, `a` canonical (110,586,256 triples), transitive and
     aperiodic on words of length ≤ 4: mod-2 counters, without base counts (8-cycle condition,
     1,016,145 survivors) and with base counts (14,223,427): 0 hits; with counts mod 8: 0 hits
     (`search8_output.txt`).  Positive control: the target automaton itself gives `Im = 1`.
   - Greedy families (`greedy.py`: counters with moduli 8 and 4, two 4-point automata): no
     witness within 1.5·10⁶ joint states, but the BFS did not finish: inconclusive.
2. **Identities of the `L_PST` kind** (`shcount ≡ good counts + [joint state ∈ Q]`) are a special
   case of determination, so the results of 1 apply.
3. **Transfer variant: valid**, not applicable.  Proof: induct on a star-free expression for `L`;
   `σ` commutes with `∪` and `·`, and, `σ(B)` being a prefix code with disjoint `σ(b)`,
   `σ(B* ∖ L) = σ(B)* ∖ σ(L)`; each step keeps height ≤ 1 (`transfer_height_one` is the block-count
   case).  With the `A`-fibre code `{b, c} ∪ a{b,c}*a` the target over the block alphabet is a pair
   count mod 2 of block classes (`|w|_c` odd, `|w|_b` odd), a group language, and those classes are
   not star-free.  No star-free `L` was found.

## 4. The exact gap

`theorem shear_height_one (p : ℕ) [Fact p.Prime] (q : ZMod p × ZMod p) {n k : ℕ} (hk : k < n) :
HasHeightAtMost {u : List (Fin 3) | shcount p q u % n = k} 1`, first `p = 2, n = 2` (equivalent to
`L(abac, k, 2)`).  By the covering method: height-one components whose joint loops miss the
central `z = (abc)⁴` of `G`.  Needed: a component on which `(abc)⁴` is never a loop (order
divisible by 8 on `abc`); no single good automaton on ≤ 7 points (with counts mod 8) or on 8
points with cycles of length 1, 2, 4, 8 does it.  If it closed: `L(abac, k, 2)`, `L(abca, k, 2)`
and renamings, hence (span, not Lean) the `(2,1,1)` direction at `p = 2`; length 4 mod 2 would
then miss `L(aabb, k, 2)` and the `(1,1,1,1)` sum of all 24 permutations.
