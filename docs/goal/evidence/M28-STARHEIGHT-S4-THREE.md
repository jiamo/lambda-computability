# S4 over three letters without double transpositions

Terminal theorems (`Start/StarHeightS4ThreeLetters.lean`, namespace
`GeneralizedStarHeight.S4Three`):

```
theorem height_one_S4_three_letters (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : ∀ x, T (FreeMonoid.of x) ∉ dbl) (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1

theorem height_one_S4_three_letters_or_proper (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))
    (hT : (∀ x, T (FreeMonoid.of x) ∉ dbl) ∨
      Subgroup.closure (Set.range fun x => T (FreeMonoid.of x)) ≠ ⊤)
    (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1
```

with `def dbl : Set (Equiv.Perm (Fin 4)) := {σ | σ * σ = 1 ∧ ∀ i, σ i ≠ i}`.  Axioms:
`propext, Classical.choice, Quot.sound` (`M28-STARHEIGHT-S4-THREE-axioms.txt`).  No earlier
proof found.

## Reduction to 56 representatives (no search in the kernel)

1. Conjugate the first letter to one of five cycle-type representatives (witnesses `w1L`).
2. Conjugate the second letter by the centralizer of the first (witnesses `w2L`).  This
   leaves the 43 pairs of `P3`.
3. For each of the 43 × 24 completions, an explicit witness (`w3L`, checked by `fin3`) says one
   of the following:
   - a letter is a double transposition (excluded by `hT`);
   - two letters are equal (`height_one_S4_two_values`);
   - the letters lie in one of the eight maximal subgroups (`height_one_of_mem_proper`);
   - the triple is conjugate, after a permutation of the letters, to a representative in `repL`.

Conjugation invariance is `allHeightOne_of_conj`, and letter renaming uses
`HasHeightAtMost.comap`.  The `_or_proper` version adds the proper-subgroup case directly.
Each stage is one `decide +kernel` over at most 43 × 24 small table checks.

## The 56 representatives and their method

Tables list the images of `0 1 2 3` (Lean's convention).  The board's right-action tuples are
the inverse permutations: for example, Lean's `3012` is the board's `1230`.

**`D = 1`, 45 classes** (`Start/StarHeightS4ThreeCertsA`–`E`, 9 per file).
- Each class has two or three coset automata of S4 on at most 4 states, with one
  `decide +kernel` aperiodicity certificate (`Aperiodic.certOK`) per automaton.
- One table check `tableOK` per class lists the 24 joint states with the value of `T`.
- These are combined by `height_one_of_tableOK` (`Start/StarHeightS4ThreeTable.lean`), an instance of
  `height_one_of_determined`.

Automaton shapes:
- point (4) + pairing (3) + sign (2): 42 classes;
- two points (4, 4) + sign (2): `K28`, `K29`, `K45`.

`K01`–`K05` have an identity letter.

| file | classes |
|---|---|
| CertsA | K01 `0123 0132 1203`, K02 `0123 0132 1230`, K03 `0123 0231 1230`, K04 `0123 0231 1302`, K05 `0123 1230 1302`, K06 `0132 0213 1203`, K07 `0132 0213 1302`, K08 `0132 0213 2013`, K09 `0132 0213 2031` |
| CertsB | K10 `0132 0231 1203`, K11 `0132 0231 1230`, K12 `0132 0231 1302`, K13 `0132 0231 1320`, K14 `0132 0231 2013`, K15 `0132 0231 2031`, K16 `0132 0231 2130`, K17 `0132 0231 2310`, K18 `0132 0231 3012` |
| CertsC | K19 `0132 0231 3021`, K20 `0132 0231 3102`, K21 `0132 0231 3201`, K22 `0132 1203 1230`, K23 `0132 1203 1302`, K24 `0132 1203 2013`, K25 `0132 1203 2031`, K26 `0132 1203 3012`, K27 `0132 1203 3201` |
| CertsD | K28 `0132 1230 1302`, K29 `0132 1230 2031`, K30 `0132 1230 2310`, K31 `0132 1230 3012`, K32 `0132 1230 3201`, K33 `0231 0312 1230`, K34 `0231 1203 1230`, K35 `0231 1203 1302`, K36 `0231 1230 1302` |
| CertsE | K37 `0231 1230 1320`, K38 `0231 1230 2013`, K39 `0231 1230 2031`, K40 `0231 1230 2310`, K41 `0231 1230 3012`, K42 `0231 1230 3102`, K43 `0231 1302 2013`, K44 `1230 1302 2031`, K45 `1230 1302 2310` |

**Lift classes, 11** (from the previous run: `StarHeightS4ThreeHitsA/B`, `S4Cox`).  The
representative in Lean's tables, then the theorem:
- `0132 0213 3012` → `C0132_0213_1230.height_one`
- `0132 0213 3021` → `C0132_0213_1320.height_one`
- `0132 0213 2103` → `C0132_0213_2103.height_one`
- `0132 0312 1023` → `C0132_0231_1023.height_one`
- `0132 1023 3012` → `C0132_1023_1230.height_one`
- `0132 2013 3021` → `C0132_1203_1320.height_one`
- `0132 2013 3201` → `C0132_1203_2310.height_one`
- `0132 2013 1320` → `C0132_1203_3021.height_one`
- `0312 2013 3201` → `C0231_1203_2310.height_one`
- `0312 2031 3201` → `C0231_1302_2310.height_one`
- `1023 0213 0132` → `S4Cox.height_one_S4_coxeter`

That gives 45 + 11 = 56 representatives.  Of these, 51 have no identity letter: the 40 `D = 1`
classes `K06`–`K45` and the 11 lift classes, which matches the board's count of 51.

**Not covered by the hypothesis.** The 19 generating classes with a double-transposition letter
are excluded by `hT`; see `M28-STARHEIGHT-S4-DOUBLE-TRANSPOSITION.md`.

## Cost

Max RSS of `lake env lean` per module, in MiB (`import Mathlib` baseline: 7874):

| module | RSS |
|---|---|
| Table | 7966 |
| CertsA | 8242 |
| CertsB | 8328 |
| CertsC | 8323 |
| CertsD | 8361 |
| CertsE | 8742 |
| Letters | 8194 |

The worst is CertsE, at +868 MiB, caused by a return monoid with 93 elements.  The cert files
and `Letters` use `set_option Elab.async false`; without it, `Letters` peaks at 9095 MiB.

## Scripts

All under `M28-STARHEIGHT-S4-search/`:
- `s4three.py`: class enumeration;
- `gen.py`, `data.py`: the coset-automaton families and the stage witnesses;
- `emit_certs.py`, `emit_glue.py` + `glue_template.lean`: these regenerate the five cert files and
  `StarHeightS4ThreeLetters.lean` byte for byte;
- `rss.py`: memory measurement.
