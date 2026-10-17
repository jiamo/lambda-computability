#!/usr/bin/env python3
"""R3 searches for M28-STARHEIGHT-PST-HEIGHT-ONE (computational evidence, not Lean-verified).

Usage: python3 docs/goal/evidence/M28-STARHEIGHT-PST-HEIGHT-ONE-search.py quot k2|k3|z4
       python3 docs/goal/evidence/M28-STARHEIGHT-PST-HEIGHT-ONE-search.py combo N K [small]

quot:  G = transition group of the target automaton (K mod 2, K mod 3, Z4Rot2Abc n = 2).  For every
       subgroup H of G, the coset automaton G/H (base point H) is "good" if its first returns are
       star-free (aperiodic transformation monoid of the automaton that dies after the first
       return) or G/H is abelian.  Every Boolean combination of good automata of G determines the
       target iff the intersection D of all good subgroups fixes the target value.
combo: all transitive 2-letter permutation automata on 2..5 points with star-free first returns
       (149 up to relabelling), combined K at a time with stateOf 0, |w|_a mod 2 and |w|_b mod 6
       (mod 4 for N = 4); reports combinations determining b0count mod N.  With 'small', K = 3
       and two of the automata have at most 4 points.
"""
import itertools, sys
from functools import reduce

M3 = ((1, 0, 2), (2, 1, 0))  # letters a, b on the S3 automaton
CAP = 200000  # monoids larger than this are reported as undecided


def mul(p, q):
    return tuple(q[i] for i in p)


def inv(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)


def closure(gens, e):
    seen, todo = {e}, [e]
    while todo:
        g = todo.pop()
        for h in gens:
            x = mul(g, h)
            if x not in seen:
                seen.add(x); todo.append(x)
    return frozenset(seen)


def subgroups(G, e):
    subs, front = {frozenset([e])}, [frozenset([e])]
    while front:
        new = []
        for H in front:
            for g in G:
                if g not in H:
                    K = closure(list(H) + [g], e)
                    if K not in subs:
                        subs.add(K); new.append(K)
        front = new
    return subs


def starfree_returns(delta, q0):
    nl = len(delta[0])
    def step(s, x):
        if s[0] == 'r':
            t = delta[s[1]][x]
            return ('h',) if t == q0 else ('r', t)
        return ('d',)
    states, i = [('r', q0)], 0
    while i < len(states):
        for x in range(nl):
            t = step(states[i], x)
            if t not in states:
                states.append(t)
        i += 1
    ix = {s: k for k, s in enumerate(states)}
    lets = [tuple(ix[step(s, x)] for s in states) for x in range(nl)]
    n, e = len(states), tuple(range(len(states)))
    seen, todo = {e}, [e]
    while todo:
        f = todo.pop()
        p = f
        for _ in range(n):
            p = mul(p, f)
        if mul(p, f) != p:
            return False
        for l in lets:
            g = mul(f, l)
            if g not in seen:
                seen.add(g); todo.append(g)
                if len(seen) > CAP:
                    return None
    return True


def quot(pts, letters, start):
    e = tuple(range(len(pts)))
    G = closure(letters, e)
    f = {g: pts[g[start]][1] for g in G}
    S = frozenset(h for h in G if all(f[mul(g, h)] == f[g] for g in G))
    comm = closure([mul(mul(mul(x, y), inv(x)), inv(y)) for x in G for y in G], e)
    subs, good, undecided = subgroups(G, e), [], []
    for H in subs:
        lab, reps = {}, []
        for g in G:
            if g not in lab:
                for h in H:
                    lab[mul(h, g)] = len(reps)
                reps.append(g)
        delta = [[lab[mul(r, l)] for l in letters] for r in reps]
        sf, ab = starfree_returns(delta, lab[e]), comm <= H
        if sf is None:
            undecided.append(len(G) // len(H))
        if sf or ab:
            good.append((H, len(G) // len(H), sf, ab))
    D = reduce(lambda x, y: x & y, [H for H, *_ in good], G)
    print("|G|", len(G), "subgroups", len(subs), "good (index, sf, abelian):",
          sorted({t[1:] for t in good}), "|D|", len(D), "determines:", D <= S,
          "undecided indices:", sorted(undecided))


def target(which):
    if which in ('k2', 'k3'):
        n = int(which[1])
        pts = [(s, c) for s in range(3) for c in range(n)]
        ix = {p: i for i, p in enumerate(pts)}
        A = tuple(ix[(M3[0][s], c)] for s, c in pts)
        B = tuple(ix[(M3[1][s], (c + (s == 0)) % n)] for s, c in pts)
        return pts, [A, B], ix[(0, 0)]
    pts = [(z, c) for z in range(4) for c in range(2)]
    ix = {p: i for i, p in enumerate(pts)}
    L = [tuple(ix[((z + d) % 4, (c + (d == 0 and z == 0)) % 2)] for z, c in pts) for d in range(3)]
    return pts, L, ix[(0, 0)]


def automata():
    res = set()
    for m in range(2, 6):
        for sa in itertools.permutations(range(m)):
            for sb in itertools.permutations(range(m)):
                lab, order, i = {0: 0}, [0], 0
                while i < len(order):
                    for s in (sa, sb):
                        if s[order[i]] not in lab:
                            lab[s[order[i]]] = len(order); order.append(s[order[i]])
                    i += 1
                if len(order) < m:
                    continue
                c = tuple(tuple(lab[s[order[j]]] for j in range(m)) for s in (sa, sb))
                if c not in res and starfree_returns([[c[0][q], c[1][q]] for q in range(m)], 0) is True:
                    res.add(c)
    return sorted(res)


def determines(n, chosen, cbm):
    st0 = (0, 0, 0, 0) + (0,) * len(chosen)
    seen, todo, fib = {st0}, [st0], {}
    while todo:
        st = todo.pop()
        if fib.setdefault((st[0],) + st[2:], st[1]) != st[1]:
            return False
        for x in (0, 1):
            ns = (M3[x][st[0]], (st[1] + (x == 1 and st[0] == 0)) % n, (st[2] + (x == 0)) % 2,
                  (st[3] + (x == 1)) % cbm) + tuple(A[x][q] for A, q in zip(chosen, st[4:]))
            if ns not in seen:
                seen.add(ns); todo.append(ns)
    return True


if __name__ == '__main__':
    if sys.argv[1] == 'quot':
        quot(*target(sys.argv[2]))
    else:
        n, k = int(sys.argv[2]), int(sys.argv[3])
        au = automata()
        print(len(au), "automata")
        cbm = {2: 2, 3: 6, 4: 4}[n]
        if len(sys.argv) > 4:
            sm = [i for i, a in enumerate(au) if len(a[0]) <= 4]
            combs = ((i, j, l) for i, j in itertools.combinations(sm, 2)
                     for l in range(len(au)) if not (l <= j and l in sm))
        else:
            combs = itertools.combinations(range(len(au)), k)
        cnt = hits = 0
        for c in combs:
            cnt += 1
            if determines(n, [au[i] for i in c], cbm):
                hits += 1
                if hits <= 3:
                    print("hit", [au[i] for i in c])
        print("N", n, "combinations", cnt, "hits", hits)
