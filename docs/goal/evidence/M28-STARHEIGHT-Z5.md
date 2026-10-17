# M28-STARHEIGHT-Z5-CORE, M28-STARHEIGHT-INDEX-FIVE, M28-STARHEIGHT-INDEX-FOUR-LETTERS

All theorems below are proved in Lean with no `sorry`, no `native_decide`, no
`Lean.ofReduceBool` and no new axioms. Their `#print axioms` output is in
`docs/goal/evidence/M28-STARHEIGHT-Z5-axioms.txt`. They use only `propext`, `Classical.choice`
and `Quot.sound`.

## Terminal statements

```lean
-- Start/StarHeightZpCoreHeight.lean
def ZpCoreHeightOne (p : ℕ) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (δ : α → ZMod p) (x : α) (n k : ℕ),
    k < n → HasHeightAtMost {w : List α | vcount δ 0 x w % n = k} 1
theorem zpcore (p : ℕ) [Fact p.Prime] : ZpCoreHeightOne p
def Z5CoreHeightOne : Prop := ∀ (α : Type) [Fintype α] [DecidableEq α] (δ : α → ZMod 5) (x : α) (n k : ℕ),
  k < n → HasHeightAtMost {w : List α | vcount δ 0 x w % n = k} 1
theorem z5core : Z5CoreHeightOne

-- Start/StarHeightIndexPrime.lean
theorem height_one_of_abelian_prime_index [Finite Alphabet] {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) {p : ℕ}
    [hp : Fact p.Prime] (hidx : N.index = p)
    (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1
theorem height_one_of_abelian_index_five [Finite Alphabet] {G : Type} [Group G] [Fintype G] (N : Subgroup G)
    [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hidx : N.index = 5) (T : FreeMonoid Alphabet →* G)
    (F : Set G) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1
theorem height_one_G55 {Alphabet : Type u} [Finite Alphabet] (T : FreeMonoid Alphabet →* G55)
    (F : Set G55) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1

-- Start/StarHeightIndexFourLetters.lean
theorem height_one_of_abelian_cyclic_index_four_of_letters [Finite Alphabet]
    {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hidx : N.index = 4)
    (hcyc : IsCyclic (G ⧸ N)) (T : FreeMonoid Alphabet →* G)
    (hlet : (∀ a, orderOf (psi N T (FreeMonoid.of a)) ≠ 2) ∨
      (∀ a, orderOf (psi N T (FreeMonoid.of a)) ≠ 4)) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1
theorem height_one_F20_of_letters {Alphabet : Type u} [Finite Alphabet]
    (T : FreeMonoid Alphabet →* F20)
    (hlet : (∀ a, (T (FreeMonoid.of a)).a ≠ -1) ∨
      (∀ a, ((T (FreeMonoid.of a)).a : ZMod 5) ≠ 2 ∧ ((T (FreeMonoid.of a)).a : ZMod 5) ≠ 3))
    (F : Set F20) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1
```

`G55` is `Z₁₁ ⋊ Z₅`. It consists of the pairs `(b, e) ∈ ZMod 11 × ZMod 5` with
`(b, e)(b', e') = (b + 3^e·b', e + e')`. Its normal subgroup `{e = 0}` has index `5`, and the group
is not abelian (`G55.not_comm`). Since `zpcore` holds for every prime, Bourne's Question 5.8 is
answered for every prime `r`, not only `r = 5`.

## The identity (the case `δ x = 1`)

Notation:

- `σ : β → ZMod p` are the displacements, with `p` prime and `σ x = 1`;
- every other letter `c ≠ x` has `σ c ≠ 0`, after erasing neutral letters;
- `φ(t) = (-t).val ∈ {0, …, p-1}`;
- for a word `u`, `s` denotes the state between two adjacent letters (the sum of the
  displacements of the prefix up to and including the first letter);
- `N₀(u)` is the number of `x` read in state `0`.

**Identity** (`zp_identity_aux`, an exact identity in `ℕ` on all words):

    p·N₀(u) + Σ_{adjacent (a, x), a ≠ x} φ(s)  =  |u|ₓ + Σ_{adjacent (x, c), c ≠ x} φ(s)
                                                 + [u ends with x]·φ(σ(u))

It telescopes along the maximal runs of `x`:

- `φ` satisfies `p·[s = 0] + φ(s) = 1 + φ(s + 1)` (`zphi_step`);
- a run `xᴸ` entered in state `s` contributes `p·#{x in state 0} + φ(s) = L + φ(s + L)`;
- `φ(s)` is paid by the pair before the run (or is `φ(0) = 0` at the start of the word);
- `φ(s + L)` is paid by the pair after the run, or by the end term.

In Lean the identity is proved by induction on the word, with the potential
`[prev = some x]·φ(s)`. No automaton check is needed.

**From weighted pairs to block counts:**

1. The weighted sums are `Σ_{s₀, d} φ(s₀)·pcB(Q ∧ σ c = d, s₀)` (`pairW_eq_sum2`).
   - `pcB Q s₀` counts the adjacent pairs `(a, c)` with `Q a c` and state `s₀` before `c`.
   - `Q` is `QA` (`a ≠ x`, `c = x`) or `QB` (`a = x`, `c ≠ x`).
2. A pair `(a, c)` with `σ c = d` and state `s₀` before `c` is a pair after which the state is
   `s₀ + d`. Prepend a fresh letter `none` of displacement `-(s₀ + d)`. In the shifted word the
   state after `c` is `0`, so `c` ends a first-return block.
   - Since `σ c ≠ 0`, the letter `a` lies in the same block.
3. Hence `pcB = bcount (pcls σ' (liftQ Q))` on the first-return factorization of
   `none :: u.map some` (`pcB_eq_bcount`).
   - `pcls σ P = zpX σ ⊓ PairEnd P` is the class of first returns whose last two letters form a
     `P`-pair.
4. Modulo `M = p·n`:

       (p·N₀ : ZMod M) = |u|ₓ + Σ φ(s₀)·Σ_d pcB_QB − Σ φ(s₀)·Σ_d pcB_QA + [last = x]·φ(Σ_b |u|_b·σ b)

   (`zp_identity_cast`).
   - The right side is determined by the residues modulo `M` of the letter counts, the `2p²`
     pair counts, and the indicator of "ends with `x`".
   - Each residue class has height at most one (`height_one_of_residues`). Since `p ∣ M`, the
     letter residues determine `σ(u)` modulo `p`.
   - Finally, `N₀ % n = k ↔ (p·N₀ : ZMod (p·n)) = p·k` (`zmod_mul_iff`).

## The classes and why their stars are star-free

These are proofs, not automaton certificates: they hold for every prime `p` and every alphabet.

- **`zpX σ`** (first returns to `0`) and **`zpNR σ`** (no return) are star-free for `p` prime
  (`zpX_starFree`, `zpNR_starFree`).
  - The walk automaton `zpWalk` satisfies `w^(p+2) ≡ w^(p+1)` (`zpWalk_pow_stable`).
  - If `σ(w) ≠ 0`, some `wᵏ` with `1 ≤ k ≤ p` brings every live state to `0`, because `σ(w)`
    generates `ZMod p`. The next copy kills the run.
  - If `σ(w) = 0`, `w` fixes the live states.
  - `starFree_of_pow_stable` turns this into star-freeness through `Aperiodic.starFree_of_aperiodic`.
- **`PairEnd P = ⊤ · ⋃_{P a c} {a c}`** is star-free, so `pcls σ P` is star-free.
- **`(pcls σ P)∗`** is star-free when `P a c → a = y ∧ c ≠ y` for all `a, c`, or
  `P a c → a ≠ y ∧ c = y` for all `a, c` (`pcls_kstar_starFree`). Both `QA` and `QB` satisfy this,
  with `y = x`.
  - The star is recognized by `pkStep`, with states: boundary, `(state, last letter)`, dead
    (`pcls_kstar_eq`).
  - `pkStep` satisfies `w^(p+2) ≡ w^(p+1)`.
  - If `σ(w) = 0`, then `w³ ≡ w²` (`pk_rot0`).
  - If `σ(w) ≠ 0`, the condition on `P` gives a cyclic pair `(ℓ, c)` of `w` that is not a
    `P`-pair: `(last w, head w)` or `(w₀, w₁)`. Rotate `w` to start with `c`
    (`wpow_rotate`). Within `p` copies the state just before some copy of `c` is `-σ c`, and that
    copy lands on `0` through the non-pair, which kills the run (`pk_wpow_kill`).
- Since `pcls ≤ zpX`, the Transfer Lemma applies to `L₀ = pcls`, `L₁ = zpX ∖ pcls`
  (`bcount_split_height`), and the tail `zpNR` is star-free.

**Case `δ x = 0`** (`zpcore_fixed`):

- `x` is read in state `0` exactly when `[x]` is a block of the first-return factorization
  (`vcount_fixed_eq`).
- `{[x]}∗` is star-free (`kstar_singleton_starFree`), and the Transfer Lemma applies to
  `L₀ = {[x]}`.

**Reductions** (`zpcore`):

- multiply the displacements by the unit `(δ x)⁻¹` (`vcountFrom_hom`);
- erase the letters `≠ x` of displacement `0` through the inverse alphabetic morphism onto the
  subtype `{a // a = x ∨ δ' a ≠ 0}` (`vcountFrom_filterMap_erase`).

Every state `q` (needed by the group theorems) is reached by a fresh first letter of displacement
`-q` (`vcount_zp_height`).

## The search that found the identity (not Lean-verified)

The scripts were scratch work and are not part of the delivery, except the identity checker
`docs/goal/evidence/M28-STARHEIGHT-Z5-identity-check.py`. The checker verifies the identity
exhaustively for `p = 5` with rotations `(1,1,2,3,4)` up to length 7, `p = 3` with `(1,2,0)` up to
8, `p = 7` with `(1,3,0,6)` up to 7, and `p = 5` with `(1,0)` up to 10.

- **Calibration.** The star-freeness checker for block classes reproduces the PM1 situation
  (`Z₄`, rotations `(1,1,3)`): the two PM1 classes `C+`, `C-` have aperiodic stars (monoids of 68
  and 69 elements), and the class of blocks beginning with the counted letter does not.
- **First family.** Block classes of the first-return code (determined by head, penultimate and
  last letters), letter counts and pure counters.
  - On the alphabet `{x (+1), b (+4)}` an identity was found from short words only.
  - On the full alphabet `{x (+1), b₁, b₂, b₃, b₄}`, `k = 2` classes with backtracking found an
    identity whose classes have transition monoids of up to 3288 elements. This was judged too
    large for kernel certificates.
- **Landing-count family.** For each factor `f` of length ≤ 2 and state `j`, count the
  occurrences of `f` whose last letter lands on `j`; add letter counts and boundary
  indicators. On 6000 random words in state `0`, the feature matrix has rank 150 out of 165
  features.
  - The kernel contains the identity above, with coefficients `φ(j)` on the pairs `(a ≠ x, x)` and
    `(x, c ≠ x)` landing on `j`.
  - Landing counts on `j` are block counts of the first-return code of the shifted word, which
    led to the proof above.

## Memory table

Max RSS of `lake env lean <file>`, with all dependencies built. It was measured as
`ru_maxrss` of the child processes, from a Python wrapper, one fresh wrapper per file. The baseline
is a file containing only `import Mathlib`.

| module | max RSS (KiB) | above baseline (MiB) | wall time (s) |
| --- | ---: | ---: | ---: |
| `import Mathlib` (baseline) | 8065180 | 0 | 7.5 |
| `Start/StarHeightStarFreeAperiodic.lean` | 8144368 | 77 | 7.6 |
| `Start/StarHeightRot2Obstruction.lean` | 8168460 | 101 | 7.6 |
| `Start/StarHeightZpWalk.lean` | 8179148 | 111 | 8.8 |
| `Start/StarHeightZpPairs.lean` | 8169308 | 102 | 7.7 |
| `Start/StarHeightZpCore.lean` | 8214140 | 145 | 8.3 |
| `Start/StarHeightZpCoreHeight.lean` | 8183380 | 115 | 8.1 |
| `Start/StarHeightIndexPrime.lean` | 8170412 | 103 | 8.3 |
| `Start/StarHeightIndexFourLetters.lean` | 8183608 | 115 | 7.9 |

No new module uses an automaton certificate checked by kernel `decide`. Star-freeness is proved
uniformly in `p` through `starFree_of_pow_stable`. The only `decide` calls are on small finite
facts:

- `tw_add` on `ZMod 5 × ZMod 5`;
- orders in `ZMod 4` and `(ZMod 5)ˣ`;
- `G55.not_comm`.
