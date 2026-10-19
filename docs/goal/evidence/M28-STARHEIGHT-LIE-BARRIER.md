# M28-STARHEIGHT-LIE-BARRIER: `L(abac, 1, 2)` is beyond metabelian 2-subgroups

Lean: `Start/StarHeightLieBarrier.lean`, no `sorry`, no `native_decide`; axioms in
`M28-STARHEIGHT-LIE-BARRIER-axioms.txt` (`propext`, `Classical.choice`, `Quot.sound`).

## The theorem

`TwoSubgroupsMetabelian Γ := ∀ P : Subgroup Γ, IsPGroup 2 P → ⁅⁅P, P⁆, ⁅P, P⁆⁆ = ⊥`.

    theorem not_recognizes_abac {Γ : Type} [Group Γ] [Finite Γ] (hΓ : TwoSubgroupsMetabelian Γ)
        (T : FreeMonoid (Fin 3) →* Γ) (F : Set Γ) :
        {u : List (Fin 3) | scount [0, 1, 0, 2] u % 2 = 1} ≠ {u | T (FreeMonoid.ofList u) ∈ F}

This is a statement about recognizers, not about star height: it says that no proof of
`L(abac, k, 2)` by covering/lifting into groups of this kind can exist.  It does not say that
`L(abac, k, 2)` has height > 1.

## Proof (all steps in Lean)

- `UT5`: the upper unitriangular `5 × 5` matrices over `F₂` as a structure of 10 entries, with the
  matrix product and a row-by-row inverse; group axioms by `ext; ring`; `card = 2¹⁰`, so
  `UT5.isPGroup`.  `abacHom = FreeMonoid.lift ![Ma, Mb, Mc]`, `Ma = I + E₀₁ + E₂₃`, `Mb = I + E₁₂`,
  `Mc = I + E₃₄`; `abacHom_row`: row 0 of `abacHom u` is `(|u|_a, ab, aba, abac)` mod 2.
- (i) `abac_separate`: if `(X·m·Y)₀₄ = (X·m'·Y)₀₄` for `X ∈ abacHom {ε, a, ab, aba}`,
  `Y ∈ abacHom {ε, c, ac, bac}`, then `m = m'` (ten exact integer `linear_combination`s; the rows of
  the `X` and the columns of the `Y` are triangular bases of `F₂⁵`).  `abacHom_eq_of_T_eq`: if
  `T u = T v` then `abacHom u = abacHom v`.
- (ii) `rangeSubgroup T` (the range is a subgroup since `Γ` is finite) and `abacPhi : range T →* UT5`.
- (iii) For `S : Sylow 2 (range T)`, the index of `φ(S)` in `φ(range T)` divides `[range T : S]`
  (odd, `Sylow.not_dvd_index`) and `|φ(range T)| = 2ⁿ`; so it is 1 and `Ma, Mb, Mc ∈ φ(S)`.
- (iv) `S` (as a 2-subgroup of `Γ`) is metabelian, so `⁅⁅sa, sb⁆, ⁅sa, sc⁆⁆ = 1`, but its image
  `⁅⁅Ma, Mb⁆, ⁅Ma, Mc⁆⁆ ≠ 1` (`UT5.double_commutator_ne_one`, `decide`).

Closure: `TwoSubgroupsMetabelian.pi`, `.prod` (via the projections; a 2-subgroup maps into
2-subgroups, `Subgroup.map_commutator`), `.of_metabelian`, `.of_card_dvd_eight` (a group of order
dividing 8 has nontrivial centre, the quotient has order ≤ 4 and is abelian, so `P' ≤ Z(P)`),
`twoSubgroupsMetabelian_perm_four` (`|P|` divides 24 and is a power of 2).
`not_recognizes_abac_pi`: no Boolean combination of languages recognized by finitely many such
groups is `L(abac, 1, 2)`; `not_recognizes_abac_perm_four` for copies of `S₄`.

## Which good classes satisfy the hypothesis (argument, not Lean unless stated)

A subgroup of a metabelian group is metabelian, so a metabelian `G` qualifies.
- PST's `A ⋊ (Z₂)ⁿ`, `A` abelian: `G' ≤ A`, metabelian.
- nilpotent of class ≤ 3: `[G', G'] ≤ γ₄ = 1`.
- Frattini-abelian (`commPowSubgroup G p` abelian): `G' ≤ commPowSubgroup`, metabelian.
- the index-four theorems (abelian normal `N` of index 4): `G/N` abelian, `G' ≤ N`.
- `Z₂ ≀ Z₄`: abelian base, cyclic top.  `A₄ = V₄ ⋊ Z₃`: metabelian.
- `S₄`: not metabelian, but its 2-subgroups have order ≤ 8 (Lean).
- the groups of order < 24: 2-subgroups of order ≤ 16; a non-abelian 2-group `P` has
  `|P : P'| ≥ 4`, so `|P'| ≤ 4` and `P'` is abelian.
- every permutation automaton on ≤ 7 points: its 2-subgroups lie in a Sylow 2-subgroup of `S₇`,
  `D₄ × Z₂` (order 16), metabelian.
- the counters used in the searches (letter counts, `scount` of length ≤ 3 mod 2, counts mod 8)
  are recognized by 2-subgroups of `UT₄(F₂)` (class 3) or cyclic groups.

So every covering or lift proof of `abac` modulo 2 needs a good group with a 2-subgroup of derived
length ≥ 3, as in `S₈` (Sylow 2-subgroup `Z₂ ≀ Z₂ ≀ Z₂`, order 128, derived length 3).  This explains
why all the searches on ≤ 7 points (with counters, with counts mod 8) failed for the shear/abac
count.  It does not explain the 8-point failures, where such 2-subgroups exist.

## The other length-4 classes (computer, not Lean)

`M28-STARHEIGHT-CORE-MOD-TWO-search/derived_table.py` (output `derived_table_output.txt`) gives,
for all 15 classes, `|G(w)|, |G'|, |G''|, |Z|`, whether the row orbit of `e₀` and the column
orbit of `e₄` span `F₂⁵` (step (i)), and the central involutions flipping the count.  Steps
(ii)–(iv) only need (i), `G(w) ≤ UT₅(F₂)` and `G(w)'' ≠ 1`; so the same argument applies to
`abbc` (512), `abcb` (128), `abcd` (1024) and also to `abca` (512, centre of order 4; the central
flip is not used by the argument).  `aabb` is not blocked: `G(aabb)` (order 256, `|G'| = 16`) is
metabelian, consistent with its reduction to the `Z₄ × Z₂` core (M28-STARHEIGHT-CORE-MOD-TWO).
Every class with `G'' = 1` is not blocked by this argument.  The blocked classes are exactly those
with a nonzero coefficient in `[[x,y],[z,t]]`.
