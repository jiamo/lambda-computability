# M28-STARHEIGHT-SHEAR search scripts (computational evidence, not Lean-verified)

Python 3 (standard library only) and C (`gcc -O2`).  Summary: `../M28-STARHEIGHT-SHEAR.md`.

| script | output | what |
|---|---|---|
| `common.py` | | permutations, subgroups, star-free first returns, target automata |
| `group_facts.py 2` | `group_facts_output.txt` | `G`, element orders, `N = ⟨[x,y], x²⟩`, 576 subgroups, coset test |
| `obstruction.py` | `obstruction_output.txt` | centre `{1, z}`, `z = (abc)⁴`, counters see `G` up to `z`; `p = 3` group |
| `minimal_counters.py` | `minimal_counters_output.txt` | order-8 words, minimal counters (`acc, bac, ccc` mod 2) |
| `counters.py L` | `counters_output.txt` | counters only (levels 0, 1): witness pairs |
| `schreier.py`, `schreier_counters.py` | | exact determination test by Schreier generators |
| `central_bit.py 5` | `central_bit_output.txt` | good automata on ≤ 5 points: `z ∈ Im` always |
| `automata_search.py`, `greedy.py` | | witness filtering; greedy families (inconclusive, BFS cap) |
| `filter8.c`, `imtest8.c` | `search8_output.txt` | 8 points, cycles of length 1, 2, 4, 8: no hit |
| `gen_automata.py`, `imtest_gen.c` | `imtest_gen_output.txt` | ≤ 7 points with counts mod 8: no hit |
| `identity_mod2.py` | `identity_mod2_output.txt` | random check of `shcount_two_cast` (proved in Lean) |
