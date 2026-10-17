#!/usr/bin/env python3
"""R1/R3 searches for M28-STARHEIGHT-S4-TWO-LETTERS (computational evidence, not Lean-verified).

Usage:
  python3 docs/goal/evidence/M28-STARHEIGHT-S4-SEARCH.py classes
      The five generating pairs of S4 over two letters, up to conjugation and a swap of the two
      letters, with every good subgroup of S4 for each pair and the intersection D of the good
      subgroups.  "Good" = the coset automaton of H (right cosets H x, base H, letter x acting by
      H y -> H y T(x)) has star-free first returns, i.e. the transformation monoid of the
      automaton that dies after the first return to the base is aperiodic; or H is normal with
      G/H abelian (commutative counts).
  python3 docs/goal/evidence/M28-STARHEIGHT-S4-SEARCH.py quot f20|s4|s4coxeter|k3
      The same computation for one target: all good subgroups and D.
  python3 docs/goal/evidence/M28-STARHEIGHT-S4-SEARCH.py aux f20|s4coxeter|k3 [sample [maxdfa [maxperm]]]
      R3: auxiliary automata.  Every complete DFA on 2..4 states and every permutation automaton
      on 2..6 points (one per letter), base state 0, with star-free first returns, is combined
      with the good coset automata of G: the combination determines the target iff no two states
      (g, q), (g', q) of the product automaton that are reachable from (1, 0) have the same
      auxiliary state q, the same coset D g = D g', and different target values.  With 'time',
      only a sample is run and the total is extrapolated.
"""
import itertools, sys, time
from functools import reduce

CAP = 200000  # monoids larger than this are reported as undecided


def mul(p, q):
    """p then q (right action): (p*q)[i] = q[p[i]]."""
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
    """Are the first returns to q0 (and the avoiding paths) star-free?  delta[q][x]."""
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


def good_subgroups(letters, e):
    """All good subgroups of G = <letters>, and their intersection D."""
    G = closure(letters, e)
    comm = closure([mul(mul(mul(x, y), inv(x)), inv(y)) for x in G for y in G], e)
    good = []
    for H in subgroups(G, e):
        lab, reps = {}, []
        for g in G:
            if g not in lab:
                for h in H:
                    lab[mul(h, g)] = len(reps)
                reps.append(g)
        delta = [[lab[mul(r, l)] for l in letters] for r in reps]
        sf, ab = starfree_returns(delta, lab[e]), comm <= H
        if sf or ab:
            good.append((H, len(G) // len(H), bool(sf), ab))
    D = reduce(lambda x, y: x & y, [H for H, *_ in good], G)
    return G, good, D


# ---------------------------------------------------------------- the targets

def cyc(n, *c):
    p = list(range(n))
    for i in range(len(c)):
        p[c[i]] = c[(i + 1) % len(c)]
    return tuple(p)


def target(which):
    """(letters, e, value function on G, name)."""
    if which == 'f20':                       # AGL(1,5): x -> 2x and x -> 1 - x
        a = tuple((2 * x) % 5 for x in range(5))
        b = tuple((1 - x) % 5 for x in range(5))
        return [a, b], tuple(range(5)), (lambda g: g), 'F20, x -> 2x, x -> 1 - x'
    if which == 's4':                        # the PST pair
        return [cyc(4, 2, 3), cyc(4, 0, 1, 2, 3)], tuple(range(4)), (lambda g: g), 'S4, (2 3), (0 1 2 3)'
    if which == 's4coxeter':                 # the three Coxeter transpositions
        return ([cyc(4, 0, 1), cyc(4, 1, 2), cyc(4, 2, 3)], tuple(range(4)), (lambda g: g),
                'S4, (0 1), (1 2), (2 3)')
    if which == 'k3':                        # the K3 automaton: b counted in state 0, mod 3
        M3 = ((1, 0, 2), (2, 1, 0))
        pts = [(s, c) for s in range(3) for c in range(3)]
        ix = {p: i for i, p in enumerate(pts)}
        A = tuple(ix[(M3[0][s], c)] for s, c in pts)
        B = tuple(ix[(M3[1][s], (c + (s == 0)) % 3)] for s, c in pts)
        start = ix[(0, 0)]
        return [A, B], tuple(range(9)), (lambda g: pts[g[start]][1]), 'K3, b0count mod 3'
    raise SystemExit('unknown target ' + which)


def s4_classes():
    """The five normal forms of a generating pair of S4 over two letters."""
    return [(cyc(4, 2, 3), cyc(4, 0, 1, 2)), (cyc(4, 2, 3), cyc(4, 0, 1, 2, 3)),
            (cyc(4, 1, 2, 3), cyc(4, 0, 1, 2, 3)), (cyc(4, 1, 2, 3), cyc(4, 0, 1, 3, 2)),
            (cyc(4, 0, 1, 2, 3), cyc(4, 0, 1, 3, 2))]


def fixed_points(H, n):
    return [p for p in range(n) if all(h[p] == p for h in H)]


def classes():
    e = tuple(range(4))
    P = list(itertools.permutations(range(4)))
    reps = s4_classes()
    # the classification itself
    bad = 0
    for A in P:
        for B in P:
            if len(closure([A, B], e)) == 24:
                if not any((mul(mul(inv(c), A), c), mul(mul(inv(c), B), c)) in
                           ((a, b), (b, a)) for a, b in reps for c in P):
                    bad += 1
    print('generating pairs not conjugate (up to a swap) to a normal form:', bad)
    for k, (A, B) in enumerate(reps):
        G, good, D = good_subgroups([A, B], e)
        descr = []
        for H, idx, sf, ab in good:
            if len(H) == 24:
                continue
            fp = fixed_points(H, 4)
            name = ('Stab(%d)' % fp[0]) if (len(H) == 6 and fp) else (
                'A4' if len(H) == 12 else ('D4' if len(H) == 8 else '|H|=%d' % len(H)))
            descr.append('%s[index %d%s%s]' % (name, idx, ', star-free returns' if sf else '',
                                               ', abelian quotient' if ab else ''))
        print('class %d: a=%s b=%s  good: %s  |D| = %d' %
              (k + 1, A, B, ', '.join(sorted(descr)), len(D)))


# --------------------------------------------------------- R3: auxiliary automata

def aux_candidates(maxdfa=4, maxperm=6, nl=2):
    """Complete DFAs on 2..maxdfa states and permutation automata on 2..maxperm points."""
    seen = set()
    for m in range(2, maxdfa + 1):
        for letters in itertools.product(itertools.product(range(m), repeat=m), repeat=nl):
            if letters not in seen:
                seen.add(letters)
                yield letters
    for m in range(maxdfa + 1, maxperm + 1):
        for letters in itertools.product(itertools.permutations(range(m)), repeat=nl):
            if letters not in seen:
                seen.add(letters)
                yield letters


def determines(letters, e, value, D, aux, cos):
    """Do the good coset automata of G and the auxiliary automaton determine the value?

    cos[g] is a name of the coset D g; two words have the same observations iff their elements
    lie in the same coset D g and the auxiliary automaton is in the same state."""
    nl = len(letters)
    start = (e, 0)
    seen, todo = {start}, [start]
    while todo:
        g, q = todo.pop()
        for x in range(nl):
            s = (mul(g, letters[x]), aux[x][q])
            if s not in seen:
                seen.add(s); todo.append(s)
    val = {}
    for g, q in seen:
        k = (q, cos[g])
        v = value(g)
        if val.setdefault(k, v) != v:
            return False
    return True


def aux_search(which, sample=None, maxdfa=4, maxperm=6):
    letters, e, value, name = target(which)
    G, good, D = good_subgroups(letters, e)
    print('target:', name, '|G| =', len(G), '|D| =', len(D),
          'good subgroup indices:', sorted({t[1] for t in good}))
    nl = len(letters)
    cos = {}
    for g in G:
        cos[g] = min(mul(d, g) for d in D)
    t0, n, ngood, hits = time.time(), 0, 0, []
    for aux in aux_candidates(maxdfa=maxdfa, maxperm=maxperm, nl=nl):
        n += 1
        if sample and n > sample:
            break
        delta = [[aux[x][q] for x in range(nl)] for q in range(len(aux[0]))]
        if starfree_returns(delta, 0) is not True:
            continue
        ngood += 1
        if determines(letters, e, value, D, aux, cos):
            hits.append(aux)
    dt = time.time() - t0
    print('candidates: %d, with star-free first returns: %d, determining: %d, %.1f s'
          % (n, ngood, len(hits), dt))
    for h in hits[:5]:
        print('  hit', h)
    if sample:
        tot = sum(1 for _ in aux_candidates(maxdfa=maxdfa, maxperm=maxperm, nl=nl))
        print('sample %d of %d; projected %.1f s' % (sample, tot, dt * tot / max(n, 1)))


if __name__ == '__main__':
    if sys.argv[1] == 'classes':
        classes()
    elif sys.argv[1] == 'quot':
        letters, e, value, name = target(sys.argv[2])
        G, good, D = good_subgroups(letters, e)
        print(name, '|G|', len(G), 'good subgroups:',
              sorted([(len(H), idx, sf, ab) for H, idx, sf, ab in good]), '|D|', len(D),
              'determines:', all(value(mul(d, g)) == value(g) for d in D for g in G))
    else:
        sample = int(sys.argv[3]) if len(sys.argv) > 3 else None
        maxdfa = int(sys.argv[4]) if len(sys.argv) > 4 else 4
        maxperm = int(sys.argv[5]) if len(sys.argv) > 5 else 6
        print('limits: complete DFAs on 2..%d states, permutation automata on %d..%d points'
              % (maxdfa, maxdfa + 1, maxperm))
        aux_search(sys.argv[2], sample, maxdfa, maxperm)
