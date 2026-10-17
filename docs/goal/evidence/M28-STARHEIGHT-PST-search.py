#!/usr/bin/env python3
"""Computational evidence for M28-STARHEIGHT-PST-CANDIDATE (not Lean-verified).

Usage:  python3 docs/goal/evidence/M28-STARHEIGHT-PST-search.py [collide|span|all] [maxlen]

Automaton: states {0,1,2}; a = (0 1), b = (0 2).  N(w) = number of b read in state 0.
On returning words (0.w = 0), w is in L_PST iff N(w) is even.

collide: for each family of integer-valued features, looks for two returning words with EQUAL
         feature vectors and different parity of N.  Such a pair rules out every Boolean
         combination of conditions "feature = r (mod m)", for every modulus m.
span:    tests whether N lies in the rational span of a family on the returning words of length
         <= maxlen (elimination modulo the prime 2^31 - 1), and reports ranks.
"""
import itertools, sys

P = 2147483647
MOVE = {'a': (1, 0, 2), 'b': (2, 1, 0)}

def run(w, s=0):
    n = 0
    for x in w:
        if x == 'b' and s == 0:
            n += 1
        s = MOVE[x][s]
    return s, n

def s3_elem(w):
    """Right action of w on (0,1,2): the S3 element of the walk (as the image tuple)."""
    return tuple(run(w, s)[0] for s in range(3))

def vcounts(w, p):
    """Letter-in-state counts of every translation automaton on ZMod p over {a,b}."""
    out = []
    for da in range(p):
        for db in range(p):
            if da == 0 and db == 0:
                continue
            d = {'a': da, 'b': db}
            cnt = {}
            s = 0
            for x in w:
                cnt[(s, x)] = cnt.get((s, x), 0) + 1
                s = (s + d[x]) % p
            out += [cnt.get((q, x), 0) for q in range(p) for x in 'ab']
    return out

def factors(w, k):
    out = []
    for L in range(1, k + 1):
        for u in itertools.product('ab', repeat=L):
            u = ''.join(u)
            out.append(sum(1 for i in range(len(w) - L + 1) if w[i:i + L] == u))
    return out

def blocks(w):
    """First-return blocks of a returning word: counts of ab+a, ba+b (Transfer-admissible
    classes: their stars are star-free) and of all blocks."""
    s, cur, nX0p, nX1p, tot = 0, '', 0, 0, 0
    for x in w:
        cur += x
        s = MOVE[x][s]
        if s == 0:
            tot += 1
            if len(cur) > 2:
                if cur[0] == 'a':
                    nX0p += 1
                else:
                    nX1p += 1
            cur = ''
    return [nX0p, nX1p, tot]

def runs_mod(w, m):
    """Number of maximal b-runs (and a-runs) of each length class mod m: a local recoding."""
    out = [0] * (2 * m)
    i = 0
    while i < len(w):
        j = i
        while j < len(w) and w[j] == w[i]:
            j += 1
        out[(0 if w[i] == 'a' else m) + (j - i) % m] += 1
        i = j
    return out

FAMILIES = {
    'letters+S3':      lambda w, k: [w.count('a'), w.count('b')] + list(s3_elem(w)),
    'factors<=k':      lambda w, k: factors(w, k),
    'Z2,Z3 counters':  lambda w, k: vcounts(w, 2) + vcounts(w, 3),
    'blocks':          lambda w, k: blocks(w),
    'runs mod 4':      lambda w, k: runs_mod(w, 4),
}

def feats(w, names, k):
    v = []
    for nm in names:
        v += FAMILIES[nm](w, k)
    return tuple(v)

def returning(maxlen):
    for n in range(maxlen + 1):
        for t in itertools.product('ab', repeat=n):
            w = ''.join(t)
            s, N = run(w)
            if s == 0:
                yield w, N

def collide(maxlen, k):
    names = list(FAMILIES)
    seen = {}
    for w, N in returning(maxlen):
        f = feats(w, names, k)
        if f in seen and seen[f][1] % 2 != N % 2:
            return seen[f][0], w
        seen.setdefault(f, (w, N))
    return None

def rank_mod(rows):
    rows = [list(r) for r in rows]
    rk, col = 0, 0
    ncol = len(rows[0]) if rows else 0
    for col in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][col] % P), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][col], P - 2, P)
        rows[rk] = [x * inv % P for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][col] % P:
                c = rows[i][col]
                rows[i] = [(x - c * y) % P for x, y in zip(rows[i], rows[rk])]
        rk += 1
    return rk

def span(maxlen, k):
    names = list(FAMILIES)
    A, B = [], []
    for w, N in returning(maxlen):
        f = [1] + list(feats(w, names, k))
        A.append(f)
        B.append(f + [N])
    r1, r2 = rank_mod(list(map(list, zip(*A)))), rank_mod(list(map(list, zip(*B))))
    return r1, r2

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'all'
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 14
    if mode in ('collide', 'all'):
        for k in range(1, 6):
            print('collide k =', k, ':', collide(maxlen, k))
    if mode in ('span', 'all'):
        for k in (2, 3):
            r1, r2 = span(min(maxlen, 10), k)
            print('span k =', k, ': rank(family) =', r1, ' rank(family + N) =', r2,
                  '-> N in span' if r1 == r2 else '-> N NOT in span')
