#!/usr/bin/env python3
"""Approach 1, greedy refinement (not Lean-verified).  Start from the counters of
counters.family(LEVEL); repeatedly collect witness pairs (equal components, different shcount q
mod 2), add the good automaton on <= NMAX points (with its fixed-letter base counts) that
separates the most pairs, and repeat.  Stops when shcount q mod 2 is determined, when no good
automaton separates any remaining pair, or after ROUNDS rounds.
Usage: python3 greedy.py NMAX LEVEL ROUNDS
"""
import sys
from common import starfree_returns
import counters
from automata_search import automata, signature

L3 = (0, 1, 2)


def as_component(lets):
    def step(s, x):
        st, k = s
        if st == 0 and lets[x][0] == 0:
            k = tuple(k[i] ^ (i == x) for i in range(3))
        return (lets[x][st], k)
    return ((0, (0, 0, 0)), step, f"aut{lets}")


if __name__ == '__main__':
    nmax, level, rounds = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    q = (0, 0)
    comps = counters.family(level)
    good = []
    for n, lets in automata(nmax):
        delta = [[lets[x][s] for x in L3] for s in range(n)]
        if starfree_returns(delta, 0, 3) is True:
            good.append(lets)
    print(f"{len(good)} good automata on <= {nmax} points")
    chosen = []
    for r in range(rounds):
        W = counters.witnesses(comps, q, maxw=300, cap=1_500_000)
        if not W:
            ok, wit, size = counters.determined(comps, q, cap=1_500_000)
            print(f"round {r}: no witness found; determined = {ok} ({size} joint states)")
            break
        best = max(good, key=lambda l: sum(signature(l, u) != signature(l, v) for u, v in W))
        ns = sum(signature(best, u) != signature(best, v) for u, v in W)
        print(f"round {r}: {len(W)} witnesses, e.g. {W[0]}; best automaton separates {ns}: {best}")
        sys.stdout.flush()
        if ns == 0:
            break
        chosen.append(best)
        comps = comps + [as_component(best)]
    print("chosen:", chosen)
