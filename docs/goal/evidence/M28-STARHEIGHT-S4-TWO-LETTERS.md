# S4 over two letters has generalized star height at most one

Terminal theorem (`Start/StarHeightS4TwoLetters.lean`):

```
theorem height_one_S4_two_letters (T : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4))
    (F : Set (Equiv.Perm (Fin 4))) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1
```

with `height_one_S4_two_values` (any finite alphabet whose letters take at most two values under
`T`) and `height_one_S4_card_two` (any alphabet of cardinality two) as corollaries, through
`HasHeightAtMost.comap` (`Start/StarHeightRenaming.lean`: reading the letters through any map of a
finite alphabet preserves height).

No earlier proof found.

## The assembly theorem

`Start/StarHeightCosetFamily.lean`. For a finite monoid `M`, a morphism `T : FreeMonoid α →* M`
and observers `ob i : M → X` that jointly separate `M`,

```
theorem height_one_of_separating_family (T : FreeMonoid Alphabet →* M) {ι} [Fintype ι]
    (ob : ι → M → X) (hsep : ∀ u v : M, (∀ i, ob i u = ob i v) → u = v)
    (hgood : ∀ i x, HasHeightAtMost {w | ob i (T (FreeMonoid.ofList w)) = x} 1)
    (F : Set M) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1
```

because `{w | T w ∈ F}` is the union over `g ∈ F` of the intersection over `i` of the observed
languages, both finite.  `height_one_of_three_observers` is the three-observer form.  The coset
form, for a finite group `G` and subgroups `H i` with `⨅ i, H i = ⊥`, is
`height_one_of_coset_family`: the observers are the right cosets `H i * {g}`, and `g ↦ (H i g)ᵢ`
is injective exactly because the subgroups meet in `{1}`.  The bridge from an automaton is
`obs_runQ` (`ob (g * T x) = δ (ob g) x` implies `ob (T w) = runQ δ (ob 1) w`) and, for a point
stabilizer of any action, `stab_coset_eq_runQ`: the coset of `T w` modulo `stabilizer G p` is
determined by `(T w)⁻¹ • p`, the state of `δ q x = (T x)⁻¹ • q` started at `p`.

## The five classes

`classify_pairs` (`Start/StarHeightS4Classes.lean`, one `decide` on `Fin`-valued data) says that
every pair `(A, B)` of permutations of four points

* has a common fixed point, or centralizes one of the three double transpositions, or consists of
  two even permutations — then both letters lie in a proper subgroup of `S₄`, of order at most
  `12`, and `height_one_of_card_lt_twenty` applies after restricting `T` (`height_one_of_mem_proper`);
* or is conjugate, possibly after swapping the two letters, to one of

| class | `a` | `b` | family used | other good subgroups |
| ----- | --- | --- | ----------- | -------------------- |
| 1 | `(2 3)` | `(0 1 2)` | `Stab(2)`, `D₄ = ⟨(1 3), (0 1)(2 3)⟩`, sign | the `D₄` of the pairing `{03\|12}` |
| 2 | `(2 3)` | `(0 1 2 3)` | `Stab(3)`, `Stab(2)`, sign | one `D₄` |
| 3 | `(1 2 3)` | `(0 1 2 3)` | `Stab(3)`, `Stab(2)`, sign | `Stab(1)`, two `D₄` |
| 4 | `(1 2 3)` | `(0 1 3 2)` | `Stab(2)`, `Stab(1)`, sign | two `D₄` |
| 5 | `(0 1 2 3)` | `(0 1 3 2)` | `Stab(3)`, `Stab(2)`, sign | `Stab(0)`, `Stab(1)`, one `D₄`, one cyclic `Z₄` |

In class 1 the base point `2` is the only good point: the four-point automaton of the pair has an
aperiodic avoid-the-base monoid only for `p = 2` (monoid of size 23, `f⁵ = f⁴`); for `p = 0, 1, 3`
the monoid contains a nontrivial group.

Swapping the two letters renames the alphabet, which preserves height
(`HasHeightAtMost.comap_equiv`, `height_one_of_swap`); conjugating `T` by `c` and replacing `F` by
`{g | c⁻¹ g c ∈ F}` leaves the language unchanged (`conj_language`).

## Why each family meets trivially

* `Stab(p) ∩ Stab(q) = ⟨(r s)⟩` for `{p, q, r, s} = {0, 1, 2, 3}`, and `(r s)` is odd, so
  `Stab(p) ∩ Stab(q) ∩ A₄ = 1`.  In Lean this is `two_points_sign`, the finite check that a
  permutation of four points fixing two points with sign `1` is the identity, and `sep_two_points`,
  which applies it to `v * u⁻¹`.
* Class 1: an element of `D₄` (the stabilizer of the pairing `{02|13}`) that fixes `2` also fixes
  its partner `0`, so `Stab(2) ∩ D₄ ∩ A₄ = 1` (`sep_class0`, a finite check on the 576 pairs).

## The height-one observers

* A good base point `p`: `{w | (T w)⁻¹ p = r} = {w | runQ δ p w = r}` with `δ q x = (T x)⁻¹ q`, and
  `height_one_of_starFree_returns` applies because the first-return code to `p` and every
  `avoidTo` language are star-free.  Both are languages of the single automaton `retAut δ p`, so
  one aperiodicity certificate per (class, base point) suffices: `Aperiodic.certOK` on the six
  closed states `st4 p` (four unvisited points, the returned base, the dead state), checked by
  `decide +kernel` (`good_base4`, `cert0_2` … `cert4_3`), with exponent `N = 4` (class 1) or
  `N = 5` (classes 2–5).
* Class 1 also uses the three-point automaton of the action on the pairings (`good_base3`,
  `cert0_P`; five closed states `st3 p`, `N = 4`), through the observer
  `obP u = pidx (u⁻¹ 0) (u⁻¹ 2)` and the finite check `pact_spec`.
* The sign: `{w | sign (T w) = s}` is recognized by the commutative group `ℤˣ`, so
  `height_one_of_comm` applies (`sign_height`).

## How the data was found

`docs/goal/evidence/M28-STARHEIGHT-S4-SEARCH.py classes`: for each of the five normal forms, all
30 subgroups of `S₄` are enumerated; the coset automaton of `H` (right cosets `H x`, base `H`,
letter `x` acting by `H y ↦ H y T(x)`) is good when the transformation monoid of the automaton
that dies after the first return to the base is aperiodic — computed by exact closure — or when
`H` is normal with abelian quotient.  The script also re-checks the classification itself: of the
576 pairs, 216 generate `S₄`, and every one of them is conjugate, up to a swap, to one of the five
normal forms.  In each class the good subgroups meet in `{1}`.  The Lean proof repeats the parts
it needs as kernel-checked certificates; the script is evidence only.
