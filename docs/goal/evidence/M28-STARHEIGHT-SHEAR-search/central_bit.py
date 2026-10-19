#!/usr/bin/env python3
"""The central bit (not Lean-verified).

(1) The counters (letter counts mod 2, every scount of length <= 3 mod 2) see all of G except a
    subgroup Im_C = {1, z} of order 2, and z changes shcount q mod 2.  So shcount q mod 2 is
    determined by the counters and one more good component Y iff z is not in Im_C ∩ Im_Y' where
    Im_Y' is the image in G of the loops of Y at its start, i.e. it suffices that z ∉ Im_Y.
    (Every coset automaton G/K with K ⊇ Im_Y is a quotient of Y, so its state languages are
    unions of state languages of Y.)
(2) Search: good automata Y on n <= NMAX points (letters identity or one cycle through 0,
    star-free first returns), with and without the parities of the letters fixing 0 read at 0.
    Reports the smallest |Im_Y| and whether z ∈ Im_Y always.
Usage: python3 central_bit.py NMAX
"""
import itertools, sys
import counters
from schreier import image, determined, target_group, perm_component
from automata_search import automata
from common import starfree_returns, closure

L3 = (0, 1, 2)
tl, t0, val, e = target_group()


def central_z():
    W2 = list(itertools.product(L3, repeat=2))
    W3 = list(itertools.product(L3, repeat=3))
    comps = [counters.cnt(x, 2) for x in L3] + [counters.sc(list(w), 2) for w in W2 + W3]
    Im, n = image([(c[0], c[1]) for c in comps], tl, e)
    assert len(Im) == 2
    z = next(g for g in Im if g != e)
    G = closure(tl, e)
    central = all(tuple(g[i] for i in z) == tuple(z[i] for i in g) for g in G)
    return z, central


if __name__ == '__main__':
    nmax = int(sys.argv[1])
    z, central = central_z()
    print("z =", z, "central:", central, flush=True)
    stats = {}
    found = []
    for n, lets in automata(nmax):
        for bc in (False, True):
            Im, _ = image([perm_component(lets, bc)], tl, e)
            key = (n, bc)
            st = stats.setdefault(key, [0, 0, 999])
            if z in Im:
                st[0] += 1
                continue
            delta = [[lets[x][s] for x in L3] for s in range(n)]
            if starfree_returns(delta, 0, 3) is not True:
                continue
            st[1] += 1
            st[2] = min(st[2], len(Im))
            found.append((n, bc, lets, len(Im)))
    for k in sorted(stats):
        print(f"n = {k[0]}, base counts {k[1]}: z in Im_Y for {stats[k][0]} automata; "
              f"good with z not in Im_Y: {stats[k][1]}")
    for f in found[:10]:
        print("  FOUND", f)
