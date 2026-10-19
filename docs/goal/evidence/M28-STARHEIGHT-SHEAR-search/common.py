"""Shared helpers for the shear searches (computational evidence, not Lean-verified).

Letters: a = 0, b = 1, c = 2.  The shear automaton Sh_p on (Z/p)^2: a sends (A, l) to (A + 1, l),
c sends it to (A, l + A), b fixes it.  The target automaton for shcount q mod n has states
(A, l, k) and b adds 1 to k when (A, l) = q.
"""
import itertools
from functools import reduce

CAP = 400000


def mul(p, q):
    """first p, then q (right action)"""
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
                seen.add(x)
                todo.append(x)
    return frozenset(seen)


def order(g):
    e = tuple(range(len(g)))
    k, x = 1, g
    while x != e:
        x = mul(x, g)
        k += 1
    return k


def shear_step(p, s, x):
    A, l = s
    if x == 0:
        return ((A + 1) % p, l)
    if x == 2:
        return (A, (l + A) % p)
    return s


def shear_target(p, q, n):
    """points, letter permutations, start index, value function (k)"""
    pts = [(A, l, k) for A in range(p) for l in range(p) for k in range(n)]
    ix = {t: i for i, t in enumerate(pts)}
    lets = []
    for x in range(3):
        img = []
        for (A, l, k) in pts:
            A2, l2 = shear_step(p, (A, l), x)
            k2 = (k + (1 if (x == 1 and (A, l) == q) else 0)) % n
            img.append(ix[(A2, l2, k2)])
        lets.append(tuple(img))
    return pts, lets, ix[(0, 0, 0)], (lambda i: pts[i][2])


def scount_target(w, n, nl=3):
    """prefix-count automaton for scount w mod n: state = counts of the prefixes w[:1..len]"""
    m = len(w)
    pts = list(itertools.product(range(n), repeat=m))
    ix = {t: i for i, t in enumerate(pts)}
    lets = []
    for x in range(nl):
        img = []
        for t in pts:
            t2 = list(t)
            for j in range(m - 1, -1, -1):
                if w[j] == x:
                    t2[j] = (t2[j] + (t[j - 1] if j > 0 else 1)) % n
            img.append(ix[tuple(t2)])
        lets.append(tuple(img))
    return pts, lets, ix[(0,) * m], (lambda i: pts[i][m - 1])


def starfree_returns(delta, q0, nl):
    """aperiodicity of the automaton that dies after the first return to q0"""
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
        pw = f
        for _ in range(n):
            pw = mul(pw, f)
        if mul(pw, f) != pw:
            return False
        for l in lets:
            g = mul(f, l)
            if g not in seen:
                seen.add(g)
                todo.append(g)
                if len(seen) > CAP:
                    return None
    return True


def subgroups(G, e):
    """all subgroups, by joining cyclic subgroups"""
    cyc = {closure([g], e) for g in G}
    subs, front = set(cyc) | {frozenset([e])}, list(cyc)
    while front:
        new = []
        for H in front:
            for C in cyc:
                if not C <= H:
                    K = closure(list(H) + list(C), e)
                    if K not in subs:
                        subs.add(K)
                        new.append(K)
        front = new
    return subs


def coset_automaton(G, H, letters, e):
    lab, reps = {}, []
    for g in G:
        if g not in lab:
            for h in H:
                lab[mul(h, g)] = len(reps)
            reps.append(g)
    return [[lab[mul(r, l)] for l in letters] for r in reps], lab[e]
