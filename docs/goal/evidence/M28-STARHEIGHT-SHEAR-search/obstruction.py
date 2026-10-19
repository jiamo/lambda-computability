#!/usr/bin/env python3
"""The central bit and the order obstruction, for p = 2 and p = 3 (not Lean-verified).

For p in {2, 3} and q = (0, 0): G = transition group of the automaton of shcount q mod p.
Prints |G|, the centre, the element orders, and Im_C = the image in G of the words that return
the counters (letter counts mod p, scount w mod p for |w| <= 3) to their start.  For p = 2 also
checks that z = (abc)^4 is the central element of Im_C and that (abc)^4 has odd shcount q for
every q: so any family of components on which (abc)^4 acts trivially (every permutation automaton
on fewer than 8 points composed with ... see NOTES) cannot determine shcount q mod 2.
Usage: python3 obstruction.py
"""
import itertools
from common import mul, inv, closure, order, shear_target
import counters
from schreier import image

L3 = (0, 1, 2)


def shcount(p, q, u):
    A = S = k = 0
    for x in u:
        if x == 'b' and (A % p, S % p) == q:
            k += 1
        if x == 'a':
            A += 1
        elif x == 'c':
            S += A
    return k


def sc_mod(w, N):
    return counters.sc(list(w), N)


for p in (2, 3):  # counters only for p = 2 (the p = 3 joint orbit is too large here)
    q = (0, 0)
    pts, tl, t0, val = shear_target(p, q, p)
    e = tuple(range(len(pts)))
    G = closure(tl, e)
    Z = [g for g in G if all(mul(g, h) == mul(h, g) for h in tl)]
    ords = {}
    for g in G:
        o = order(g)
        ords[o] = ords.get(o, 0) + 1
    print(f"p = {p}: |G| = {len(G)}, |Z(G)| = {len(Z)}, element orders {dict(sorted(ords.items()))}",
          flush=True)
    if p == 2:
        W2 = list(itertools.product(L3, repeat=2))
        W3 = list(itertools.product(L3, repeat=3))
        comps = [counters.cnt(x, p) for x in L3] + [sc_mod(w, p) for w in W2 + W3]
        Im, n = image([(c[0], c[1]) for c in comps], tl, e)
        print(f"  counters: joint orbit {n}, |Im_C| = {len(Im)}, Im_C central: {set(Im) <= set(Z)}")
        w = (tl[0], tl[1], tl[2])
        abc = mul(mul(tl[0], tl[1]), tl[2])
        z4 = mul(mul(abc, abc), mul(abc, abc))
        print("  (abc)^4 in Im_C:", z4 in Im, "; (abc)^4 central:", z4 in Z,
              "; shcount q((abc)^4) mod 2 for q in (Z/2)^2:",
              [shcount(2, qq, 'abc' * 4) % 2 for qq in itertools.product(range(2), repeat=2)])
