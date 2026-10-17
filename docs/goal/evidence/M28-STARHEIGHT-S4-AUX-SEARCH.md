# M28 star height: auxiliary automata beyond the coset families (R3)

Computational evidence only; nothing in this note is Lean-verified.  Script:
`docs/goal/evidence/M28-STARHEIGHT-S4-SEARCH.py` (modes `quot` and `aux`).

## The question

For a group language `{w | T w ∈ F}` the coset method (`height_one_of_coset_family`) needs good
subgroups `H_i ≤ G` with `⋂ H_i = 1`.  Let `D` be the intersection of all good subgroups of `G`
(good = the coset automaton has star-free first returns, i.e. the avoid-the-base transformation
monoid is aperiodic, or `H` is normal with `G/H` abelian).  When `D ≠ 1` no Boolean combination of
good coset automata of `G` determines the element, and an auxiliary automaton is needed.

## Targets and their `D` (mode `quot`, exact closure)

| target | letters | `|G|` | good indices | `|D|` |
|---|---|---|---|---|
| (a) F20 | `x ↦ 2x`, `x ↦ 1 − x` | 20 | 1, 2, 4 | 5 |
| (b) S4 Coxeter | `(0 1)`, `(1 2)`, `(2 3)` | 24 | 1, 2, 3 | 4 |
| (c) K3 | the K3 pair (target: the count mod 3) | 162 | 1, 2, 3, 6 | 9 |

## What was searched (mode `aux`)

Candidates are one auxiliary automaton with base state 0:

* every complete DFA on 2..m states (all letter maps `Fin k → Fin k`);
* every permutation automaton on m+1..M points (all letter permutations).

Duplicates are removed.  A candidate is kept only if its own first returns to state 0 are
star-free (the avoid-the-base monoid is aperiodic, exact closure).  This is what makes each
of its state languages height ≤ 1 through `height_one_of_starFree_returns`.

The test is whether the candidate, together with all good coset automata of `G`, determines
the target.  Build the product automaton on pairs `(g, q)`, reachable from `(1, 0)`.  The
combination determines the target iff no two reachable pairs with the same auxiliary state
`q` and the same coset `D g` have different target values.

| target | DFA states | perm points | candidates | star-free returns | determining | time |
|---|---|---|---|---|---|---|
| (a) F20 | 2..4 | 5..6 | 599,081 | 143,209 | 0 | 179 s |
| (b) S4 Coxeter (3 letters) | 2..3 | 4..5 | 1,761,571 | 179,399 | 0 | 613 s |
| (c) K3 | 2..4 | 5..6 | 599,081 | 143,209 | 0 | 389 s |

Cost discipline.  Each run was timed first on a sample of about 20,000 candidates and
extrapolated.  The projections were about 60 s for (a), 299 s for (b) and 308 s for (c).  All
were under the 20-minute limit, so every run was carried out in full.  The actual times above
are larger than the projections because later candidates (6-point permutations) cost more.
For (b), 3 letters make 4-state DFAs (`256³ ≈ 1.7·10⁷`) and 6-point permutations (`720³`) too
expensive, so the limits were lowered to 3 states and 5 points.

## Exclusions established

Within these limits, **no single auxiliary automaton** helps in any of (a), (b), (c):

* (a) F20, two letters: complete DFAs on ≤ 4 states and permutation automata on ≤ 6 points;
* (b) S4 Coxeter, three letters: complete DFAs on ≤ 3 states and permutation automata on ≤ 5 points;
* (c) K3, two letters: complete DFAs on ≤ 4 states and permutation automata on ≤ 6 points.

In each case no candidate both has star-free first returns and, combined with the good coset
automata of `G`, determines the target.

## Not covered

* Pairs or larger families of auxiliary automata.  Two auxiliary automata can determine where
  each alone does not; this was not searched.
* Good subgroups of the joint group `J = ⟨(T x, aux x)⟩` other than products of a good `G`-coset
  automaton and the auxiliary automaton itself.  The test uses the auxiliary state as one
  observation, not every good coset automaton of `J`.  So "0 determining" excludes the simplest
  use of each candidate, not every use.
* Auxiliary automata with a base state other than 0.  For permutation automata this is only a
  relabelling.  For DFAs, base 0 ranges over all automata up to relabelling, but only states
  reachable from 0 matter.
* Non-group observers beyond 4 states, and three-letter DFAs on 4 states.

## Height 2?

No invariant was found that separates these languages from height-one languages.  So there is
no evidence-backed conjecture that (a)–(c) have height 2.  The searches above only show that the
cheapest certificates of height one do not exist.  The question stays open both ways.

## Literature

No earlier proof found.
