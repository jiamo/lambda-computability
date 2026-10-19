#!/usr/bin/env python3
"""Span computation for scattered-subword counts of length 4 (R3 (a)).

Coordinates.  The counts `scount w` are linearly independent over every field (the matrix
`scount v u`, |v|, |u| <= 4, is unitriangular for the length order), so every function built from
them is a vector in the basis {scount w}.  Lengths <= 3 are handled, so we work modulo them: a
vector is its length-4 part, indexed by the 4^4 words over {a,b,c,d}.

Reachable span R (modulo p):
  * products of shorter counts: the length-4 part of scount v1 * scount v2 is the shuffle v1 ш v2;
  * handled shapes of length 4: x^4, the PST shapes x^i y x^j (i + j = 3), and, for odd p, the
    shapes x^i y z^j with i + j = 3, i, j < p (letters may coincide);
  * pullbacks along letter maps psi : A -> A (scount v (psi u) = sum of scount v' over the v' with
    psi(v') = v).  Mode "shapes" pulls back handled shapes only (the method of the brief);
    mode "closed" closes the whole span under pullbacks and reversal (both preserve height <= 1).
For each content (one multiset of letters, e.g. {a,a,b,c}) we report the number of missing directions supported
on that content, |V_c| - rank(projection of R to V_c), and a basis of the missing functionals.

Usage: python3 span_length4.py [p ...]      (default 2 3 5 7)
"""
import itertools
import sys

A = 4
WORDS = list(itertools.product(range(A), repeat=4))
IDX = {w: i for i, w in enumerate(WORDS)}
D = len(WORDS)


def content(w):
    return tuple(sorted((w.count(a) for a in set(w)), reverse=True))


class Span:
    """Row-reduced basis of a subspace of F_p^D (rows stored as dicts)."""

    def __init__(self, p):
        self.p = p
        self.rows = {}

    def reduce(self, v):
        p = self.p
        v = {k: c % p for k, c in v.items() if c % p}
        changed = True
        while changed:
            changed = False
            for k in sorted(v):
                if k in self.rows:
                    c = v[k]
                    for kk, cc in self.rows[k].items():
                        nv = (v.get(kk, 0) - c * cc) % p
                        if nv:
                            v[kk] = nv
                        else:
                            v.pop(kk, None)
                    changed = True
                    break
        return v

    def add(self, v):
        v = self.reduce(v)
        if not v:
            return False
        p = self.p
        piv = min(v)
        inv = pow(v[piv], p - 2, p)
        v = {k: (c * inv) % p for k, c in v.items()}
        for q in list(self.rows):
            r = self.rows[q]
            if piv in r:
                c = r[piv]
                nr = dict(r)
                for kk, cc in v.items():
                    nv = (nr.get(kk, 0) - c * cc) % p
                    if nv:
                        nr[kk] = nv
                    else:
                        nr.pop(kk, None)
                self.rows[q] = nr
        self.rows[piv] = v
        return True

    def rank(self):
        return len(self.rows)


def shuffle(u, w):
    if not u:
        return [w]
    if not w:
        return [u]
    return [(u[0],) + s for s in shuffle(u[1:], w)] + [(w[0],) + s for s in shuffle(u, w[1:])]


def shuffle_vec(u, w):
    v = {}
    for s in shuffle(u, w):
        v[IDX[s]] = v.get(IDX[s], 0) + 1
    return v


MAPS = list(itertools.product(range(A), repeat=A))
GENS = [(1, 0, 2, 3), (1, 2, 3, 0), (0, 1, 2, 0)]  # generate the monoid of all maps A -> A


def pullback(v, psi):
    out = {}
    for i, w in enumerate(WORDS):
        j = IDX[tuple(psi[a] for a in w)]
        if j in v:
            out[i] = v[j]
    return out


def reverse(v):
    return {IDX[tuple(reversed(WORDS[k]))]: c for k, c in v.items()}


def handled_shapes(p, use_r2):
    S = set()
    for x in range(A):
        S.add((x,) * 4)
        for y in range(A):
            if y != x:
                for i in range(4):
                    S.add((x,) * i + (y,) + (x,) * (3 - i))
    if use_r2:
        for x, y, z in itertools.product(range(A), repeat=3):
            for i in range(4):
                j = 3 - i
                if i < p and j < p:
                    S.add((x,) * i + (y,) + (z,) * j)
    return S


def frattini_words():
    """Length-4 words whose recognizing p-group has an abelian Frattini subgroup for p = 2
    (classes aaaa, abab, abba, see frattini_length4.py), with all renamings."""
    out = set()
    for w in WORDS:
        m = {}
        c = tuple(m.setdefault(a, len(m)) for a in w)
        if c in ((0, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 0)):
            out.add(w)
    return out


def build(p, use_r2, mode, extra_contents=(), extra_words=()):
    R = Span(p)
    short = [w for k in (1, 2, 3) for w in itertools.product(range(A), repeat=k)]
    for u in short:
        for w in short:
            if len(u) + len(w) == 4:
                R.add(shuffle_vec(u, w))
    shapes = handled_shapes(p, use_r2)
    for w in WORDS:
        if content(w) in extra_contents:
            shapes.add(w)
    shapes |= set(extra_words)
    pre = set()
    for s in shapes:
        for psi in MAPS:
            pre.add(frozenset(i for i, w in enumerate(WORDS) if tuple(psi[a] for a in w) == s))
    for S in pre:
        if S:
            R.add({i: 1 for i in S})
    if mode == "closed":
        changed = True
        while changed:
            changed = False
            for r in list(R.rows.values()):
                for psi in GENS:
                    changed |= R.add(pullback(r, psi))
                changed |= R.add(reverse(r))
    return R


def missing_by_content(R, p):
    reps = {}
    for w in WORDS:
        reps.setdefault(content(w), tuple(sorted(w)))
    res = {}
    for c, letters in sorted(reps.items()):
        cols = [i for i, w in enumerate(WORDS) if tuple(sorted(w)) == letters]
        P = Span(p)
        colset = set(cols)
        for r in R.rows.values():
            P.add({k: v for k, v in r.items() if k in colset})
        missing = len(cols) - P.rank()
        dual = []
        for f in cols:
            if f in P.rows:
                continue
            vec = {f: 1}
            for q, r in P.rows.items():
                if f in r:
                    vec[q] = (-r[f]) % p
            dual.append({''.join('abcd'[a] for a in WORDS[k]): (v if v <= p // 2 else v - p)
                         for k, v in vec.items()})
        res[c] = (len(cols), missing, dual)
    return res


if __name__ == "__main__":
    for p in [int(a) for a in sys.argv[1:]] or [2, 3, 5, 7]:
        for mode in ("shapes", "closed"):
            for extra in ((), ((2, 2), (2, 1, 1))):
                R = build(p, p != 2, mode, extra)
                m = missing_by_content(R, p)
                print(f"p={p} mode={mode} assumed={extra} rank={R.rank()} of {D}")
                for c, (n, k, dual) in m.items():
                    print(f"   content {c}: {n} words, missing {k}")
                    if k and k <= 4:
                        for d in dual:
                            print("      ", " ".join(f"{v:+d}{w}" for w, v in sorted(d.items())))
                sys.stdout.flush()
        if p == 2:
            R = build(p, False, "closed", (), frattini_words())
            m = missing_by_content(R, p)
            print(f"p=2 mode=closed with the abelian-Frattini words abab, abba (and renamings) rank={R.rank()}")
            for c, (n, k, dual) in m.items():
                print(f"   content {c}: {n} words, missing {k}")
                for d in dual:
                    print("      ", " ".join(f"{v:+d}{w}" for w, v in sorted(d.items())))
            sys.stdout.flush()
