#!/usr/bin/env python3
"""Computational evidence for M28-STARHEIGHT-Z4-PM1 and M28-STARHEIGHT-Z4-ROT2 (not Lean-verified).

Usage:  python3 docs/goal/evidence/M28-STARHEIGHT-Z4-search.py [pm1|rot2|all]

pm1:  letters a (+1, counted), b (+1), d (-1) on ZMod 4, read from state 0.  Checks the identity
      2*N(u) = Z2(u) + #C+(u) - #C-(u) - #{blocks of bb.u equal to ad}
      on every returning word of length <= 12 and on random returning words, and checks that the
      minimal automata of X, C+, C-, C+*, C-* are aperiodic (hence star-free, Schutzenberger).
rot2: letters a (0, counted), b (+1), c (+2).  Tests whether N lies in the rational span of the
      family R (letter counts; letter-in-state counts of every ZMod 4 counter whose displacements
      take one nonzero value; block classes, by first letter and last three letters, of the
      first-return code to the even states read from the prefixes '' and 'b') on the returning
      words of length <= 8, by elimination modulo the prime 2^31 - 1.
"""
import itertools, random, sys

P = 2147483647

def minimize(start, delta, acc, letters):
    seen, st = {start}, [start]
    while st:
        q = st.pop()
        for l in letters:
            r = delta(q, l)
            if r not in seen:
                seen.add(r); st.append(r)
    Q = list(seen); idx = {q: i for i, q in enumerate(Q)}
    T = [[idx[delta(q, l)] for l in letters] for q in Q]
    part = [1 if acc(q) else 0 for q in Q]
    while True:
        sig, new = {}, []
        for i in range(len(Q)):
            key = (part[i],) + tuple(part[T[i][j]] for j in range(len(letters)))
            new.append(sig.setdefault(key, len(sig)))
        if len(set(new)) == len(set(part)):
            break
        part = new
    n = len(set(new)); M = [None] * n
    for i in range(len(Q)):
        M[new[i]] = tuple(new[T[i][j]] for j in range(len(letters)))
    return n, M

def aperiodic(n, M, nl):
    gens = [tuple(M[q][j] for q in range(n)) for j in range(nl)]
    seen, st = set(gens), list(gens)
    while st:
        f = st.pop()
        for g in gens:
            h = tuple(g[f[q]] for q in range(n))
            if h not in seen:
                seen.add(h); st.append(h)
    for f in seen:
        p = f
        for _ in range(n):
            p = tuple(f[p[q]] for q in range(n))
        if p != tuple(f[p[q]] for q in range(n)):
            return False
    return True

def inspan(rows, y):
    piv = {}
    for r, yy in zip(rows, y):
        v = {k: x % P for k, x in r.items() if x % P}
        if yy % P:
            v['y'] = yy % P
        for k in [k for k in list(v) if k in piv]:
            if k in v:
                c = v[k]
                for kk, xx in piv[k].items():
                    nv = (v.get(kk, 0) - c * xx) % P
                    if nv: v[kk] = nv
                    else: v.pop(kk, None)
        ks = [k for k in v if k != 'y']
        if not ks:
            if 'y' in v:
                return False
            continue
        k = min(ks); inv = pow(v[k], P - 2, P)
        v = {kk: xx * inv % P for kk, xx in v.items()}
        for pr in piv.values():
            if k in pr:
                c = pr[k]
                for k2, x2 in v.items():
                    nv = (pr.get(k2, 0) - c * x2) % P
                    if nv: pr[k2] = nv
                    else: pr.pop(k2, None)
        piv[k] = v
    return True

def returning(L, D, maxlen):
    for n in range(maxlen + 1):
        for t in itertools.product(L, repeat=n):
            if sum(D[c] for c in t) % 4 == 0:
                yield ''.join(t)

def count_at_zero(w, D):
    s = c = 0
    for ch in w:
        c += ch == 'a' and s == 0
        s = (s + D[ch]) % 4
    return c

def pm1():
    L, D = 'abd', {'a': 1, 'b': 1, 'd': -1}
    up = lambda ch: D[ch] == 1
    def blocks(w):
        s, out, st = 0, [], 0
        for i, ch in enumerate(w):
            s = (s + D[ch]) % 4
            if s == 0:
                out.append(w[st:i + 1]); st = i + 1
        return out
    cplus = lambda e: e[0] == 'a' and not (len(e) >= 2 and e[-2] == 'a' and up(e[-1]))
    cminus = lambda e: e[0] != 'a' and len(e) >= 2 and e[-2] == 'a' and up(e[-1])
    def rhs(u):
        bl = blocks(u)
        return (sum(1 for i, ch in enumerate(u) if ch == 'a' and i % 2 == 0)
                + sum(map(cplus, bl)) - sum(map(cminus, bl))
                - sum(1 for e in blocks('bb' + u) if e == 'ad'))
    bad = cnt = 0
    for u in returning(L, D, 12):
        cnt += 1; bad += 2 * count_at_zero(u, D) != rhs(u)
    print('pm1: returning words of length <= 12:', cnt, 'failures:', bad)
    random.seed(7); bad = cnt = 0
    for _ in range(40000):
        u = ''.join(random.choice(L) for _ in range(random.randrange(400)))
        if sum(D[c] for c in u) % 4 == 0:
            cnt += 1; bad += 2 * count_at_zero(u, D) != rhs(u)
    print('pm1: random returning words (length < 400):', cnt, 'failures:', bad)
    classes = [('X', lambda f, l: True),
               ('C+', lambda f, l: f == 'a' and not (len(l) == 2 and l[0] == 'a' and up(l[1]))),
               ('C-', lambda f, l: f != 'a' and len(l) == 2 and l[0] == 'a' and up(l[1]))]
    for star in (False, True):
        for name, pred in classes:
            if star and name == 'X':
                continue
            def delta(q, l, pred=pred, star=star):
                if q in ('dead', 'acc'):
                    return 'dead'
                pos, first, last = q
                if pos == 0: pos2, first, last = D[l], l, l
                else: pos2, last = pos + D[l], (last + l)[-2:]
                if pos2 in (0, 4, -4):
                    if not pred(first, last): return 'dead'
                    return (0, '', '') if star else 'acc'
                return (pos2, first, last)
            acc = (lambda q: q != 'dead' and q != 'acc' and q[0] == 0) if star else (lambda q: q == 'acc')
            n, M = minimize((0, '', ''), delta, acc, L)
            print('pm1: %s%s aperiodic:' % (name, '*' if star else ''), aperiodic(n, M, 3))

def rot2():
    L, D, K = 'abc', {'a': 0, 'b': 1, 'c': 2}, 3
    counters = [c for c in itertools.product(range(4), repeat=3) if len({v for v in c if v}) == 1]
    def blocks2(w):
        p, out, st = 0, [], 0
        for i, ch in enumerate(w):
            p ^= ch == 'b'
            if p == 0:
                out.append(w[st:i + 1]); st = i + 1
        return out
    rows, y = [], []
    for w in returning(L, D, 8):
        r = {}
        for c in L:
            r['#' + c] = w.count(c)
        for cnt in counters:
            dd, s = dict(zip(L, cnt)), 0
            for ch in w:
                k = 'ctr%s:%s@%d' % (cnt, ch, s); r[k] = r.get(k, 0) + 1
                s = (s + dd[ch]) % 4
        for p in ('', 'b'):
            for e in blocks2(p + w):
                k = 'X2%s:%s|%s' % (p, e[0], e[-K:]); r[k] = r.get(k, 0) + 1
        rows.append(r); y.append(count_at_zero(w, D))
    print('rot2: returning words of length <= 8:', len(rows), ' N in span of R:', inspan(rows, y))

if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if what in ('pm1', 'all'): pm1()
    if what in ('rot2', 'all'): rot2()
