#!/usr/bin/env python3
"""Approach 1: good permutation automata added to the counters (not Lean-verified).

A good automaton: transitive on n points, each of a, b, c is the identity or a single cycle
through the base point 0, and the automaton that dies after the first return to 0 is aperiodic
(star-free first returns; height_one_of_starFree_returns).  Besides its state, such an automaton
also gives the count of each letter x with 0.x = 0 read in state 0, modulo 2 (a fixed-letter count
at a star-free base point: the blocks equal to [x] of the first-return factorization).

The pairs (u, v) on which all counters of counters.family(LEVEL) agree but shcount q differs mod 2
are collected.  An automaton is useful only if it separates some pair.  Usage:
    python3 automata_search.py NMAX LEVEL
"""
import itertools, sys
from common import starfree_returns
import counters

L3 = (0, 1, 2)


def cycles_through_0(n):
    res = [tuple(range(n))]  # identity
    for L in range(2, n + 1):
        for rest in itertools.permutations(range(1, n), L - 1):
            cyc = (0,) + rest
            img = list(range(n))
            for i in range(L):
                img[cyc[i]] = cyc[(i + 1) % L]
            res.append(tuple(img))
    return res


def transitive(lets, n):
    seen, todo = {0}, [0]
    while todo:
        s = todo.pop()
        for l in lets:
            if l[s] not in seen:
                seen.add(l[s]); todo.append(l[s])
    return len(seen) == n


def signature(lets, w):
    s, k = 0, [0, 0, 0]
    for ch in w:
        x = 'abc'.index(ch)
        if s == 0 and lets[x][0] == 0:
            k[x] ^= 1
        s = lets[x][s]
    return (s, tuple(k))


def automata(nmax):
    for n in range(2, nmax + 1):
        cyc = cycles_through_0(n)
        acanon = [tuple(range(n))] + [tuple(list(range(1, L)) + [0] + list(range(L, n)))
                                       for L in range(2, n + 1)]
        for a in acanon:
            for b in cyc:
                for c in cyc:
                    lets = (a, b, c)
                    if transitive(lets, n):
                        yield n, lets


if __name__ == '__main__':
    nmax, level = int(sys.argv[1]), int(sys.argv[2])
    comps = counters.family(level)
    W = counters.witnesses(comps, (0, 0))
    print(f"{len(W)} witness pairs for q = (0, 0) at counter level {level}; first {W[:3]}")
    total = good = sep = 0
    hits = []
    for n, lets in automata(nmax):
        total += 1
        nsep = sum(signature(lets, u) != signature(lets, v) for u, v in W)
        if nsep == 0:
            continue
        delta = [[lets[x][s] for x in L3] for s in range(n)]
        if starfree_returns(delta, 0, 3) is not True:
            continue
        sep += 1
        hits.append((nsep, n, lets))
    hits.sort(reverse=True)
    print(f"automata enumerated {total}; good and separating some pair {sep}")
    for h in hits[:10]:
        print("  separates", h[0], "of", len(W), "n =", h[1], "letters", h[2])
