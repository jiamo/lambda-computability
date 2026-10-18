#!/usr/bin/env python3
"""Classes of letter triples of S4 (Lean convention) and good coset automata."""
import itertools, sys, json

E = (0, 1, 2, 3)
S4 = list(itertools.permutations(range(4)))
IDX = {p: i for i, p in enumerate(S4)}


def mul(s, t):  # Lean: (s*t)(i) = s(t(i))
    return tuple(s[t[i]] for i in range(4))


def inv(s):
    r = [0] * 4
    for i, j in enumerate(s):
        r[j] = i
    return tuple(r)


def conj(c, s):
    return mul(mul(c, s), inv(c))


def gen(gens):
    seen = {E}
    todo = [E]
    while todo:
        g = todo.pop()
        for h in gens:
            x = mul(g, h)
            if x not in seen:
                seen.add(x)
                todo.append(x)
    return frozenset(seen)


def is_dbl(s):
    return mul(s, s) == E and all(s[i] != i for i in range(4))


# all subgroups
subs = set()
for a in S4:
    for b in S4:
        subs.add(gen([a, b]))
subs = sorted(subs, key=lambda H: (len(H), sorted(H)))
FULL = frozenset(S4)


def coset_aut(H, letters):
    """states: left cosets gH; base H; delta q x = T(x)^-1 q."""
    cos = []
    rep = {}
    # BFS from base under the letters (T generating => all cosets)
    def cid(g):
        key = frozenset(mul(g, h) for h in H)
        if key not in rep:
            rep[key] = len(cos)
            cos.append(key)
        return rep[key]
    reps = [E]
    cid(E)
    i = 0
    delta = []
    while i < len(reps):
        g = reps[i]
        row = []
        for t in letters:
            g2 = mul(inv(t), g)
            n0 = len(cos)
            j = cid(g2)
            if j == n0:
                reps.append(g2)
            row.append(j)
        delta.append(row)
        i += 1
    return delta


def ret_monoid(delta, p):
    n = len(delta)
    nl = len(delta[0])
    # states: 0..n-1 = (q,false), n = (p,true), n+1 = none
    def step(s, x):
        if s >= n:
            return n + 1
        r = delta[s][x]
        return n if r == p else r
    idt = tuple(range(n + 2))
    seen = {idt}
    order = [idt]
    i = 0
    while i < len(order):
        f = order[i]
        for x in range(nl):
            g = tuple(step(f[q], x) for q in range(n + 2))
            if g not in seen:
                seen.add(g)
                order.append(g)
        i += 1
        if len(order) > CAP:
            return None
    return order


CAP = 3000


def aper_index(mon):
    """least N with f^(N+1)=f^N for all f, or None."""
    best = 0
    for f in mon:
        pw = [tuple(range(len(f)))]
        cur = pw[0]
        found = None
        for k in range(1, 40):
            cur = tuple(f[c] for c in cur)
            pw.append(cur)
            if pw[k] == pw[k - 1]:
                found = k - 1
                break
        if found is None:
            return None
        # check periodic: f^(N+1)=f^N
        best = max(best, found)
    return best


def good(delta, p=0):
    mon = ret_monoid(delta, p)
    if mon is None:
        return None, None
    N = aper_index(mon)
    return N, len(mon)


def triple_classes(allow_identity):
    seen = set()
    classes = []
    for t in itertools.product(S4, repeat=3):
        if t in seen:
            continue
        a, b, c = t
        if len({a, b, c}) < 3:
            continue
        if any(is_dbl(x) for x in t):
            continue
        if (E in t) and not allow_identity:
            continue
        if gen(list(t)) != FULL:
            continue
        orb = set()
        for perm in itertools.permutations(range(3)):
            for g in S4:
                orb.add(tuple(conj(g, t[perm[i]]) for i in range(3)))
        seen |= orb
        classes.append(min(orb))
    return classes


def good_subgroups(t):
    res = []
    for H in subs:
        if H == FULL or len(H) < 2:
            continue
        d = coset_aut(H, t)
        N, m = good(d)
        if N is not None:
            res.append((H, d, N, m))
    return res


if __name__ == "__main__":
    cls = triple_classes(True)
    print(len(cls), "classes (with identity)")
    noid = [c for c in cls if E not in c]
    print(len(noid), "without identity")
    for t in cls:
        gs = good_subgroups(t)
        D = FULL
        for H, *_ in gs:
            D = D & H
        print(t, "D=", len(D), "good:", [(len(H), N, m) for H, d, N, m in gs][:6])


def best_family(t, sizes=(6, 8, 12)):
    gs = [g for g in good_subgroups(t) if len(g[0]) in sizes]
    best = None
    for r in range(1, 5):
        for fam in itertools.combinations(gs, r):
            D = FULL
            for H, *_ in fam:
                D = D & H
            if len(D) == 1:
                cost = sum(m for H, d, N, m in fam)
                if best is None or cost < best[0]:
                    best = (cost, fam)
        if best:
            return best
    return None
