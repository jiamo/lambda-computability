#!/usr/bin/env python3
"""|Im| for counter families (see schreier.py).  Usage: python3 schreier_counters.py"""
import itertools, time
import counters
from schreier import image, determined, target_group, counter
from common import closure

L3 = (0, 1, 2)
tl, t0, val, e = target_group()


def run(name, comps):
    t = time.time()
    Im, n = image([(c[0], c[1]) for c in comps], tl, e)
    print(f"{name}: orbit {n}, |Im| = {len(Im)}, determined {determined(Im, tl, t0, val, e)}"
          f" ({time.time() - t:.0f}s)", flush=True)
    return Im


if __name__ == '__main__':
    W2 = list(itertools.product(L3, repeat=2))
    W3 = list(itertools.product(L3, repeat=3))
    run("counts mod 2", [counters.cnt(x, 2) for x in L3])
    run("counts mod 2, scount |w|=2 mod 2", [counters.cnt(x, 2) for x in L3] +
        [counters.sc(list(w), 2) for w in W2])
    run("counts mod 2, scount |w|=2 mod 4", [counters.cnt(x, 2) for x in L3] +
        [counters.sc(list(w), 4) for w in W2])
    run("counts mod 2, scount |w|<=3 mod 2", [counters.cnt(x, 2) for x in L3] +
        [counters.sc(list(w), 2) for w in W2 + W3])
    run("+ translation automata (Z/2)^2, all letter-in-state counts mod 2",
        [counters.cnt(x, 2) for x in L3] + [counters.sc(list(w), 2) for w in W2 + W3] +
        [counters.tr(d, 2, 2) for d in itertools.product(itertools.product(range(2), repeat=2), repeat=3)])
