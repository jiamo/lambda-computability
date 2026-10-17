#!/usr/bin/env python3
"""Lift searches for M28-STARHEIGHT-S4-COXETER / -LIFT (computational evidence, not Lean-verified).

The lift test.  Letters T[x] of a target group G (permutations, right action: p*q = p then q) and
letters L[x] of an auxiliary permutation group K.  E = <(T x, L x)> <= G x K, pi = projection to G
(every choice of L gives a lift).  A subgroup H of E of index <= MAXK is *good* if its coset
automaton (cosets H y, letter x: H y -> H y (T x, L x), base H) has star-free first returns
(aperiodic transformation monoid of the automaton that dies after the first return to the base),
or if E/H is abelian (H normal; commutative counts).  D = intersection of the good subgroups.
The test *hits* iff D <= ker pi; then the good coset automata of E determine T w (height_one_of_lift).

Subgroups of E: all subgroups, as joins of cyclic subgroups of prime-power order (exact; used for
|E| <= MAXE only, larger E are skipped and counted).

Usage:
  liftsearch.py coxeter             the Coxeter lift of R1 (|E| = 192)
  liftsearch.py classes             the 84 / 70 / 30 classes of generating triples of S4
  liftsearch.py s4three FAMILY      run FAMILY on the 30 classes with D != 1 (8 processes)
      FAMILY in: signed1 (one sign per cycle, fixed points included, closing edge),
                 signedall (all sign vectors, up to conjugation by diagonal sign matrices),
                 z4 (one Z4 label per cycle, fixed points included), gl23, bo (binary
                 octahedral 2.S4), s3 (K = S3, all letter triples), s4 (K = S4, all triples up to
                 conjugation in K, with a time cap)
  liftsearch.py target f20|k3 FAMILY [BUDGET]
      F20 = <x->2x, x->1-x> (value = the element) or K3 (value = b-count in state 0 mod 3);
      FAMILY as above, plus z5 and cyc (K cyclic of order 2..6)
  liftsearch.py s4univ coxword|randE192|randsign [COUNT [BUDGET]]
      the universal S4 alphabet (24 letters) with lifts into Z2 wr S4: the Coxeter-word rule,
      or COUNT random preimages in the order-192 group E, or COUNT random sign vectors
Here liftsearch.py is this file.  Each run prints what it covered (lifts, tried, skipped).
"""
import itertools, sys, time, json
from multiprocessing import Pool

MAXK = 12
MAXE = 800


def mul(p, q):
    return tuple(q[i] for i in p)


def inv(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)


def closure_set(gens):
    e = tuple(range(len(gens[0])))
    seen, todo = {e}, [e]
    while todo:
        g = todo.pop()
        for h in gens:
            x = mul(g, h)
            if x not in seen:
                seen.add(x); todo.append(x)
    return seen


def pair_group(T, L, cap=None):
    e = (tuple(range(len(T[0]))), tuple(range(len(L[0]))))
    elems, idx, tab, i = [e], {e: 0}, [], 0
    while i < len(elems):
        g = elems[i]
        row = []
        for x in range(len(T)):
            h = (mul(g[0], T[x]), mul(g[1], L[x]))
            j = idx.get(h)
            if j is None:
                j = len(elems); idx[h] = j; elems.append(h)
                if cap and len(elems) > cap:
                    return None
            row.append(j)
        tab.append(row)
        i += 1
    return elems, tab


def full_table(tab):
    n = len(tab)
    par, order = [None] * n, [0]
    par[0] = (-1, -1)
    for g in order:
        for s, h in enumerate(tab[g]):
            if par[h] is None:
                par[h] = (g, s); order.append(h)
    cols = [None] * n
    cols[0] = list(range(n))
    for g in order[1:]:
        p, s = par[g]
        cols[g] = [tab[x][s] for x in cols[p]]
    return [[cols[b][a] for b in range(n)] for a in range(n)]


def closure(M, gens):
    seen, lst = 1, [0]
    for x in lst:
        row = M[x]
        for g in gens:
            y = row[g]
            if not (seen >> y) & 1:
                seen |= 1 << y; lst.append(y)
    return seen


def all_subgroups(M):
    n = len(M)
    cyc = {}
    for g in range(1, n):
        k, x = 1, g
        while x != 0:
            x = M[x][g]; k += 1
        p = next(q for q in range(2, k + 1) if k % q == 0)
        while k % p == 0:
            k //= p
        if k != 1:
            continue
        m = closure(M, [g])
        cyc.setdefault(m, g)
    subs, front = {1: []}, [1]
    while front:
        new = []
        for H in front:
            gens = subs[H]
            for m, g in cyc.items():
                if m & ~H:
                    K = closure(M, gens + [g])
                    if K not in subs:
                        subs[K] = gens + [g]; new.append(K)
        front = new
    return list(subs)


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
    return True


def coset_table(M, tab, H):
    n = len(M)
    lab, reps = [-1] * n, []
    hs = [h for h in range(n) if (H >> h) & 1]
    for g in range(n):
        if lab[g] < 0:
            c = len(reps); reps.append(g)
            for h in hs:
                lab[M[h][g]] = c
    return [[lab[tab[r][s]] for s in range(len(tab[0]))] for r in reps]


AMB = {}


def ambient(name, gens, key):
    """All subgroups of an ambient group W (by generators), cached per process."""
    if name not in AMB:
        e = tuple(range(len(gens[0])))
        els, idx, tab, i = [e], {e: 0}, [], 0
        while i < len(els):
            row = []
            for g in gens:
                h = mul(els[i], g)
                if h not in idx:
                    idx[h] = len(els); els.append(h)
                row.append(idx[h])
            tab.append(row)
            i += 1
        M = full_table(tab)
        AMB[name] = (idx, all_subgroups(M), key)
    return AMB[name]


def subgroups_of_E(elems, M, amb):
    if amb is None:
        return all_subgroups(M)
    idx, subs, key = amb
    wpos = [idx[key(g)] for g in elems]
    emask = 0
    for p in wpos:
        emask |= 1 << p
    back = {p: j for j, p in enumerate(wpos)}
    n = len(elems)
    out = []
    for S in subs:
        if S & ~emask:
            continue
        c = bin(S).count('1')
        if n // c > MAXK:
            continue
        H, x = 0, S
        while x:
            b = x & -x
            H |= 1 << back[b.bit_length() - 1]
            x ^= b
        out.append(H)
    return out


def lift_test(T, L, value=None, maxk=MAXK, maxe=MAXE, amb=None):
    """Returns None if |E| > maxe, else a dict.  value: function of the G-component (default:
    the element itself); hit iff value is constant on D-cosets.  amb: an ambient group whose
    subgroup list is restricted to E (exact, faster)."""
    pg = pair_group(T, L, cap=maxe)
    if pg is None:
        return None
    elems, tab = pg
    n = len(elems)
    M = full_table(tab)
    good = []
    for H in subgroups_of_E(elems, M, amb):
        k = n // bin(H).count('1')
        if k == 1 or k > maxk:
            continue
        table = coset_table(M, tab, H)
        sf = starfree_returns(table, 0)
        gens = [tuple(table[c][s] for c in range(k)) for s in range(len(tab[0]))]
        ab = all(mul(a, b) == mul(b, a) for a in gens for b in gens)
        if sf or ab:
            good.append((H, k, sf, ab, table))
    full = (1 << n) - 1
    if value is None:
        value = lambda g: g
    # hit test: D-cosets constant in value.  Equivalent for value = id: D <= ker pi.
    def hits(masks):
        D = full
        for m in masks:
            D &= m
        dl = [j for j in range(n) if (D >> j) & 1]
        for g in range(n):
            v = value(elems[g][0])
            for d in dl:
                if value(elems[M[d][g]][0]) != v:
                    return False, D
        return True, D
    hit, D = hits([g[0] for g in good])
    fam = None
    if hit:
        for r in range(1, 6):
            for combo in itertools.combinations(range(len(good)), r):
                if hits([good[i][0] for i in combo])[0]:
                    fam = [(good[i][1], good[i][4]) for i in combo]
                    break
            if fam:
                break
    ker = sum(1 for g in elems if g[0] == elems[0][0])
    return dict(E=n, ker=ker, ngood=len(good), D=bin(D).count('1'), hit=hit, family=fam)


# ------------------------------------------------------------------ lift families

def cycles(p):
    seen, cs = set(), []
    for i in range(len(p)):
        if i not in seen:
            c, j = [], i
            while j not in seen:
                seen.add(j); c.append(j); j = p[j]
            cs.append(c)
    return cs


def monomial(p, labels, m):
    """p with Z_m labels: point i + n*b -> p(i) + n*((b + labels[i]) % m)."""
    n = len(p)
    return tuple(p[i] + n * ((b + labels[i]) % m) for b in range(m) for i in range(n))


def per_cycle_lifts(p, m):
    """One Z_m label per cycle (fixed points included), on the closing edge of the cycle."""
    cs = cycles(p)
    out = []
    for labs in itertools.product(range(m), repeat=len(cs)):
        lab = [0] * len(p)
        for c, l in zip(cs, labs):
            lab[c[-1]] = l
        out.append(monomial(p, lab, m))
    return out


def signed_all_up_to_diag(T):
    """All sign vectors for all letters, up to conjugation by a diagonal sign matrix."""
    n = len(T[0])
    seen, out = set(), []
    for labs in itertools.product(itertools.product(range(2), repeat=n), repeat=len(T)):
        if labs in seen:
            continue
        for d in itertools.product(range(2), repeat=n):
            seen.add(tuple(tuple((lab[i] + d[i] + d[T[x][i]]) % 2 for i in range(n))
                           for x, lab in enumerate(labs)))
        out.append([monomial(T[x], labs[x], 2) for x in range(len(T))])
    return out


def gl23():
    """GL(2,3) on the 8 nonzero vectors, with the induced permutation of the 4 lines."""
    vecs = [(a, b) for a in range(3) for b in range(3) if (a, b) != (0, 0)]
    lines = [(1, 0), (0, 1), (1, 1), (1, 2)]

    def line(v):
        a, b = v
        if a == 0:
            return 1
        b = (b * a) % 3  # a^{-1} = a in F3
        return [0, 2, 3][b]
    out = []
    for a, b, c, d in itertools.product(range(3), repeat=4):
        if (a * d - b * c) % 3 == 0:
            continue
        img = lambda v: ((a * v[0] + b * v[1]) % 3, (c * v[0] + d * v[1]) % 3)
        perm = tuple(vecs.index(img(v)) for v in vecs)
        lp = tuple(line(img(l)) for l in lines)
        out.append((perm, lp))
    return out


def binary_octahedral():
    import math
    r = 1 / math.sqrt(2)

    def qm(p, q):
        a1, b1, c1, d1 = p; a2, b2, c2, d2 = q
        return (a1*a2 - b1*b2 - c1*c2 - d1*d2, a1*b2 + b1*a2 + c1*d2 - d1*c2,
                a1*c2 - b1*d2 + c1*a2 + d1*b2, a1*d2 + b1*c2 - c1*b2 + d1*a2)
    key = lambda q: tuple(round(x, 6) + 0.0 for x in q)
    gens = [(r, r, 0, 0), (0.5, 0.5, 0.5, 0.5)]
    els, seen = [(1.0, 0, 0, 0)], {key((1.0, 0, 0, 0))}
    i = 0
    while i < len(els):
        for g in gens:
            h = qm(els[i], g)
            if key(h) not in seen:
                seen.add(key(h)); els.append(h)
        i += 1
    assert len(els) == 48
    ix = {key(q): j for j, q in enumerate(els)}
    diags = [(1, 1, 1), (1, 1, -1), (1, -1, 1), (-1, 1, 1)]
    out = []
    for q in els:
        perm = tuple(ix[key(qm(q, p))] for p in els)  # left multiplication (function p -> q p)
        qi = (q[0], -q[1], -q[2], -q[3])
        lp = []
        for dv in diags:
            v = qm(qm(q, (0,) + dv), qi)[1:]
            w = tuple(round(x) for x in v)
            nw = tuple(-x for x in w)
            lp.append(diags.index(w) if w in diags else diags.index(nw))
        out.append((perm, tuple(lp)))
    return out


def lifts_from_cover(T, cover):
    """cover: list of (perm, induced S4 perm); for each letter, all preimages."""
    # the induced perm is a function-level homomorphism; our letters are function tuples too
    pre = [[k for k, ind in cover if ind == t] for t in T]
    return [list(c) for c in itertools.product(*pre)]


def family_lifts(T, fam):
    n = len(T[0])
    if fam == 'signed1':
        return [list(c) for c in itertools.product(*[per_cycle_lifts(t, 2) for t in T])]
    if fam == 'z4':
        return [list(c) for c in itertools.product(*[per_cycle_lifts(t, 4) for t in T])]
    if fam == 'z5':
        return [list(c) for c in itertools.product(*[per_cycle_lifts(t, 5) for t in T])]
    if fam == 'signedall':
        return signed_all_up_to_diag(T)
    if fam == 'gl23':
        return lifts_from_cover(T, gl23())
    if fam == 'bo':
        return lifts_from_cover(T, binary_octahedral())
    if fam in ('s3', 's4', 'cyc'):
        if fam == 'cyc':
            K = [tuple((i + k) % m for i in range(m)) for m in (2, 3, 4, 5, 6) for k in range(m)]
            out = []
            for m in (2, 3, 4, 5, 6):
                Km = [tuple((i + k) % m for i in range(m)) for k in range(m)]
                out += [list(c) for c in itertools.product(Km, repeat=len(T))]
            return out
        m = 3 if fam == 's3' else 4
        Km = list(itertools.permutations(range(m)))
        seen, out = set(), []
        for c in itertools.product(Km, repeat=len(T)):
            if c in seen:
                continue
            for g in Km:
                seen.add(tuple(mul(mul(inv(g), x), g) for x in c))
            out.append(list(c))
        return out
    raise SystemExit('unknown family ' + fam)


# ------------------------------------------------------------------ targets

def s4_classes():
    P = list(itertools.permutations(range(4)))
    e = tuple(range(4))
    reps, seen = [], set()
    for t in itertools.product(P, repeat=3):
        if t in seen or len(closure_set(list(t))) != 24:
            continue
        orb = {tuple(mul(mul(inv(c), x), c) for x in pt) for c in P for pt in itertools.permutations(t)}
        seen |= orb
        reps.append(min(orb))
    return reps


def d_of(T):
    r = lift_test(T, [tuple(range(1))] * len(T), maxk=24)
    return r['D']


def family_ambient(T, fam):
    n = len(T[0])
    idn = tuple(range(n))
    Sn = [tuple((i + 1) % n for i in range(n)), tuple([1, 0] + list(range(2, n)))]
    G = Sn if len(closure_set(list(T))) == len(closure_set(Sn)) else list(T)
    gname = 'S%d' % n if G is Sn else 'G' + '.'.join(fmt(t) for t in T)
    if fam in ('signed1', 'signedall'):
        flip = tuple(i + n if i == 0 else i - n if i == n else i for i in range(2 * n))
        gens = [monomial(p, [0] * n, 2) for p in G] + [flip]
        return ambient('signed' + gname, gens, lambda g: g[1])
    if fam == 'gl23':
        return ambient('gl23', [k for k, _ in gl23()], lambda g: g[1])
    if fam == 'bo':
        return ambient('bo', [k for k, _ in binary_octahedral()], lambda g: g[1])
    if fam in ('s3', 's4'):
        m = 3 if fam == 's3' else 4
        Sm = [tuple((i + 1) % m for i in range(m)), tuple([1, 0] + list(range(2, m)))]
        gens = [p + tuple(n + i for i in range(m)) for p in G] + \
            [idn + tuple(n + q[i] for i in range(m)) for q in Sm]
        return ambient(fam + gname, gens, lambda g: g[0] + tuple(n + x for x in g[1]))
    return None


def run_one(args):
    T, fam, budget, value = args
    t0 = time.time()
    amb = family_ambient(T, fam)
    lifts = family_lifts(T, fam)
    tried, skipped, hits = 0, 0, []
    for L in lifts:
        if time.time() - t0 > budget:
            break
        r = lift_test(T, L, value=value, amb=amb)
        tried += 1
        if r is None:
            skipped += 1
            continue
        if r['hit']:
            hits.append((L, r))
            break
    return dict(T=T, fam=fam, total=len(lifts), tried=tried, skipped=skipped,
                secs=round(time.time() - t0, 1), hit=hits[0] if hits else None)


def fmt(p):
    return ''.join(map(str, p))


def target(which):
    """(letters, value function or None)."""
    if which == 'f20':
        return [tuple((2 * x) % 5 for x in range(5)), tuple((1 - x) % 5 for x in range(5))], None
    if which == 'k3':
        M3 = ((1, 0, 2), (2, 1, 0))
        pts = [(q, c) for q in range(3) for c in range(3)]
        ix = {pt: i for i, pt in enumerate(pts)}
        A = tuple(ix[(M3[0][q], c)] for q, c in pts)
        B = tuple(ix[(M3[1][q], (c + (q == 0)) % 3)] for q, c in pts)
        start = ix[(0, 0)]
        return [A, B], (lambda g: pts[g[start]][1])
    raise SystemExit('unknown target ' + which)


def univ_lifts(rule, count, seed=1):
    """Lifts of the universal S4 alphabet (all 24 elements, sorted) into Z2 wr S4."""
    import random
    rnd = random.Random(seed)
    P = sorted(itertools.permutations(range(4)))
    sw = lambda i, j: tuple(j if k == i else i if k == j else k for k in range(4))

    def sl(i, j):
        q = list(range(8)); q[i] = j; q[i + 4] = j + 4; q[j] = i + 4; q[j + 4] = i
        return tuple(q)
    cox = [(sw(i, i + 1), sl(i, i + 1)) for i in range(3)]
    # one fixed reduced word per element (BFS in the Coxeter generators)
    word, todo = {tuple(range(4)): []}, [tuple(range(4))]
    for g in todo:
        for k, (t, _) in enumerate(cox):
            h = mul(g, t)
            if h not in word:
                word[h] = word[g] + [k]; todo.append(h)
    e8 = tuple(range(8))
    E192 = {}
    for g in closure_set([c[1] for c in cox]):
        E192.setdefault(tuple(g[i] % 4 for i in range(4)), []).append(g)
    out = []
    if rule == 'coxword':
        L = []
        for g in P:
            x = e8
            for k in word[g]:
                x = mul(x, cox[k][1])
            L.append(x)
        out.append(L)
    elif rule == 'randE192':
        for _ in range(count):
            out.append([rnd.choice(E192[g]) for g in P])
    elif rule == 'randsign':
        for _ in range(count):
            out.append([monomial(g, [rnd.randrange(2) for _ in range(4)], 2) for g in P])
    return P, out


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'coxeter':
        sw = lambda i, j: tuple(j if k == i else i if k == j else k for k in range(4))

        def sl(i, j):
            p = list(range(8)); p[i] = j; p[i + 4] = j + 4; p[j] = i + 4; p[j + 4] = i
            return tuple(p)
        T = [sw(0, 1), sw(1, 2), sw(2, 3)]
        r = lift_test(T, [sl(0, 1), sl(1, 2), sl(2, 3)])
        print(json.dumps(r))
    elif cmd == 'classes':
        reps = s4_classes()
        res = [(T, d_of(list(T))) for T in reps]
        triv = [T for T, d in res if any(x == tuple(range(4)) for x in T) or len(set(T)) < 3]
        print('classes up to conjugation and letter order:', len(res),
              ' with an identity or repeated letter:', len(triv),
              ' D = 1:', sum(1 for T, d in res if d == 1),
              ' D != 1:', sum(1 for T, d in res if d != 1))
        for T, d in res:
            if d != 1:
                print(' '.join(fmt(x) for x in T), '|D| =', d)
    elif cmd == 's4three':
        fam = sys.argv[2]
        budget = float(sys.argv[3]) if len(sys.argv) > 3 else 600
        only = sys.argv[4].split(',') if len(sys.argv) > 4 else None
        reps = [list(T) for T in s4_classes() if d_of(list(T)) != 1]
        if only:
            reps = [T for T in reps if ' '.join(fmt(x) for x in T) in only]
        with Pool(8) as pool:
            for r in pool.imap_unordered(run_one, [(T, fam, budget, None) for T in reps]):
                h = r['hit']
                print(' '.join(fmt(x) for x in r['T']), fam, 'lifts %d tried %d skipped(|E|>%d) %d %.0fs'
                      % (r['total'], r['tried'], MAXE, r['skipped'], r['secs']),
                      ('HIT |E|=%d ker=%d good=%d |D|=%d family-indices=%s L=%s' %
                       (h[1]['E'], h[1]['ker'], h[1]['ngood'], h[1]['D'],
                        [f[0] for f in h[1]['family']], [fmt(x) for x in h[0]])) if h else 'no hit',
                      flush=True)
    elif cmd == 'target':
        which, fam = sys.argv[2], sys.argv[3]
        budget = float(sys.argv[4]) if len(sys.argv) > 4 else 600
        T, value = target(which)
        r = run_one((T, fam, budget, value))
        h = r['hit']
        print(which, fam, 'lifts %d tried %d skipped(|E|>%d) %d %.0fs'
              % (r['total'], r['tried'], MAXE, r['skipped'], r['secs']),
              ('HIT |E|=%d |D|=%d L=%s' % (h[1]['E'], h[1]['D'], [fmt(x) for x in h[0]]))
              if h else 'no hit', flush=True)
    elif cmd == 's4univ':
        rule, count = sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 1
        budget = float(sys.argv[4]) if len(sys.argv) > 4 else 600
        T, lifts = univ_lifts(rule, count)
        amb = family_ambient(T, 'signed1')
        t0, best = time.time(), None
        for k, L in enumerate(lifts):
            if time.time() - t0 > budget:
                break
            r = lift_test(T, L, amb=amb)
            if best is None or r['D'] < best[0]:
                best = (r['D'], r['E'], r['ngood'])
            if r['hit']:
                print('HIT', rule, k, r); break
        print('s4univ', rule, 'tried %d of %d in %.0fs; smallest |D| (with |E|, number of good subgroups): %s'
              % (k + 1, len(lifts), time.time() - t0, best))
