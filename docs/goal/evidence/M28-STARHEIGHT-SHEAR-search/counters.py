#!/usr/bin/env python3
"""Approach 1/2, counters only: is shcount q mod 2 a function of the residues of already-proved
good counts?  (Computational evidence, not Lean-verified.)

Every component is a deterministic automaton (start, step).  The joint automaton of the
components and the target is explored by BFS from the start; the target is determined iff no two
reachable joint states agree on the components and differ on the target value.  When it is not
determined, the script prints a witness pair of words.

Counter components (each is a Lean-proved good count, every modulus):
  cnt(x, N)        |u|_x mod N                                     (goodCount_count)
  sc(w, N)         scount w mod N, |w| <= 3                        (goodCount_scount_le_three)
  pst(i, x, y, j, N) scount (x^i y x^j) mod N                      (goodCount_scount_pst)
  tr(delta, N)     all letter-in-state counts mod N of the translation automaton
                   delta : letters -> (Z/2)^r                      (goodCount_vcount_prime)
and their pullbacks along letter maps (GoodCount.comp_map).
Usage: python3 counters.py
"""
import itertools, sys
from collections import deque
from common import shear_step

L3 = (0, 1, 2)


def cnt(x, N):
    return (0, lambda s, y: (s + (y == x)) % N, f"cnt({x},{N})")


def sc(w, N):
    m = len(w)
    def step(t, x):
        t2 = list(t)
        for j in range(m - 1, -1, -1):
            if w[j] == x:
                t2[j] = (t2[j] + (t[j - 1] if j > 0 else 1)) % N
        return tuple(t2)
    return ((0,) * m, step, f"sc({''.join('abc'[x] for x in w)},{N})")


def tr(delta, r, N):
    """state (pos, counts[(pos, letter)])"""
    keys = [(q, y) for q in itertools.product(range(2), repeat=r) for y in L3]
    kix = {k: i for i, k in enumerate(keys)}
    def step(s, x):
        pos, cs = s
        cs = list(cs)
        cs[kix[(pos, x)]] = (cs[kix[(pos, x)]] + 1) % N
        pos2 = tuple((pos[i] + delta[x][i]) % 2 for i in range(r))
        return (pos2, tuple(cs))
    return (((0,) * r, (0,) * len(keys)), step, f"tr({delta},{N})")


def pull(comp, psi):
    s0, step, name = comp
    return (s0, lambda s, x: step(s, psi[x]), f"{name}o{psi}")


def target(q):
    def step(s, x):
        A, l, k = s
        A2, l2 = shear_step(2, (A, l), x)
        return (A2, l2, (k + (x == 1 and (A, l) == q)) % 2)
    return ((0, 0, 0), step)


def determined(comps, q, cap=3_000_000):
    t0, tstep = target(q)
    st0 = (t0, tuple(c[0] for c in comps))
    seen = {st0: ''}
    todo = deque([st0])
    fib = {}
    while todo:
        st = todo.popleft()
        key = st[1]
        v = st[0][2]
        if key in fib and fib[key][0] != v:
            return False, (fib[key][1], seen[st]), len(seen)
        fib.setdefault(key, (v, seen[st]))
        for x in L3:
            ns = (tstep(st[0], x), tuple(c[1](s, x) for c, s in zip(comps, st[1])))
            if ns not in seen:
                seen[ns] = seen[st] + 'abc'[x]
                todo.append(ns)
                if len(seen) > cap:
                    return None, None, len(seen)
    return True, None, len(seen)


def family(level):
    comps = [cnt(x, 8) for x in L3]
    words2 = [w for w in itertools.product(L3, repeat=2)]
    words3 = [w for w in itertools.product(L3, repeat=3)]
    comps += [sc(list(w), 8 if level >= 1 else 4) for w in words2]
    comps += [sc(list(w), 4 if level >= 1 else 2) for w in words3]
    if level >= 2:
        deltas = set()
        for v in itertools.product(itertools.product(range(2), repeat=2), repeat=3):
            deltas.add(v)
        comps += [tr(d, 2, 2) for d in sorted(deltas)]
    if level >= 3:
        # PST shapes of length 4 and 5 modulo 4
        for x, y in itertools.permutations(L3, 2):
            for i, j in [(i, 4 - 1 - i) for i in range(4)] + [(i, 5 - 1 - i) for i in range(5)]:
                comps.append(sc([x] * i + [y] + [x] * j, 4))
    return comps


if __name__ == '__main__':
    level = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    comps = family(level)
    for q in [(0, 0), (0, 1), (1, 0), (1, 1)]:
        ok, wit, size = determined(comps, q)
        print(f"level {level}, {len(comps)} counters, q = {q}: determined = {ok}, "
              f"joint states explored {size}, witness {wit}")
        sys.stdout.flush()


def witnesses(comps, q, maxw=200, cap=2_000_000):
    """up to maxw pairs of words agreeing on all components with different target value"""
    t0, tstep = target(q)
    st0 = (t0, tuple(c[0] for c in comps))
    seen = {st0: ''}
    todo = deque([st0])
    fib, out = {}, []
    while todo and len(out) < maxw and len(seen) < cap:
        st = todo.popleft()
        key, v = st[1], st[0][2]
        if key in fib and fib[key][0] != v:
            out.append((fib[key][1], seen[st]))
        fib.setdefault(key, (v, seen[st]))
        for x in L3:
            ns = (tstep(st[0], x), tuple(c[1](s, x) for c, s in zip(comps, st[1])))
            if ns not in seen:
                seen[ns] = seen[st] + 'abc'[x]
                todo.append(ns)
    return out
