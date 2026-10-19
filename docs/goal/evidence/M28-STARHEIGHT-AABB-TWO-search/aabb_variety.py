# L(aabb, k, 2) through the variety of Z2 wr Z4.  Pure Python 3, no imports beyond itertools.
# (1) W-test: G(aabb) <= UT5(F2) lies in A2A4, so every hom of F2 into it factors through
#     W = F2 / R'R^2 with R = ker(F2 -> Z4 x Z4); M = R/R'R^2 = F_2^17 (Schreier basis).
#     G is in var(Delta) iff G's map on M vanishes on the common kernel of all homs F2 -> Delta.
# (2) Six homs into Z2 wr Z4 suffice: BFS of the joint group.
# (3) The identity (I) for H = #{b : A_i mod 4 in {2,3}, B_i odd}: 64 step cases + all words of length <= 14.
# (4) Single letter-in-state counts on Z4 x Z2 (a=(1,0), b=(0,1)): syntactic group vs var(Z2 wr Z4).
import itertools
def mmul(A, B):
    R = []
    for i in range(len(A)):
        r = 0
        for k in range(len(A)):
            if A[i] >> k & 1: r ^= B[k]
        R.append(r)
    return tuple(R)
I5 = tuple(1 << i for i in range(5))
def E(pairs):
    M = list(I5)
    for i, j in pairs: M[i] |= 1 << j
    return tuple(M)
def minv(A):
    N = tuple(A[i] ^ (1 << i) for i in range(5)); P = I5; R = list(I5)
    for _ in range(5):
        P = mmul(P, N); R = [r ^ p for r, p in zip(R, P)]
    return tuple(R)
class UT5:
    one = I5; mul = staticmethod(mmul); inv = staticmethod(minv)
def mk_wr(top, add):
    idx = {s: i for i, s in enumerate(top)}
    def act(s, f):
        g = 0
        for t in top:
            if f >> idx[t] & 1: g |= 1 << idx[add(t, s)]
        return g
    neg = {s: next(t for t in top if add(s, t) == top[0]) for s in top}
    class T:
        one = (0, top[0])
        @staticmethod
        def mul(x, y): return (x[0] ^ act(x[1], y[0]), add(x[1], y[1]))
        @staticmethod
        def inv(x): return (act(neg[x[1]], x[0]), neg[x[1]])
    return T, idx
Wr, _ = mk_wr([0, 1, 2, 3], lambda s, t: (s + t) % 4)
WR = [(f, k) for f in range(16) for k in range(4)]
def power(Gp, x, n):
    r = Gp.one
    for _ in range(n): r = Gp.mul(r, x)
    return r
def schreier_vals(Gp, X, Y):
    vals = []
    for i in range(4):
        for j in range(4):
            for z, Z in (("x", X), ("y", Y)):
                if (z == "y" and j < 3) or (z == "x" and j == 0 and i < 3): continue
                ni, nj = ((i + 1) % 4, j) if z == "x" else (i, (j + 1) % 4)
                rep = Gp.mul(power(Gp, X, i), power(Gp, Y, j))
                nrep = Gp.mul(power(Gp, X, ni), power(Gp, Y, nj))
                vals.append(Gp.mul(Gp.mul(rep, Z), Gp.inv(nrep)))
    assert len(vals) == 17
    return vals
def coords(Gp, vals):
    span = {Gp.one: 0}; d = 0; rows = []
    for v in vals:
        if v not in span:
            new = {Gp.mul(e, v): m | (1 << d) for e, m in span.items()}
            assert not (set(new) & set(span)); span.update(new); d += 1
        rows.append(span[v])
    for a in span:
        assert Gp.mul(a, a) == Gp.one
        for b in span: assert Gp.mul(a, b) == Gp.mul(b, a)
    return [sum(((rows[i] >> c) & 1) << i for i in range(17)) for c in range(d)]
def reduce(basis, v):
    for b in basis: v = min(v, v ^ b)
    return v
def add_all(basis, vs):
    basis = list(basis)
    for v in vs:
        v = reduce(basis, v)
        if v: basis.append(v)
    return basis
BD = []
for X in WR:
    for Y in WR: BD = add_all(BD, coords(Wr, schreier_vals(Wr, X, Y)))
Ma, Mb = E([(0, 1), (1, 2)]), E([(2, 3), (3, 4)])
gc = coords(UT5, schreier_vals(UT5, Ma, Mb))
print("(1) rank of all homs F2 -> Z2wrZ4 on M:", len(BD), "of 17; rank of G(aabb):", len(gc),
      "; G(aabb) in var(Z2wrZ4):", all(reduce(BD, c) == 0 for c in gc))
chosen, basis = [], []
for X, Y in [((0, 1), (0, 0)), ((0, 0), (0, 1))] + [(X, Y) for X in WR for Y in WR]:
    if len(chosen) >= 2 and all(reduce(basis, c) == 0 for c in gc): break
    cs = coords(Wr, schreier_vals(Wr, X, Y)); nb = add_all(basis, cs)
    if len(nb) > len(basis) or len(chosen) < 2: chosen.append((X, Y)); basis = nb
def step(s, c):
    g, ds = s; M, k = (Ma, 0) if c == "a" else (Mb, 1)
    return (mmul(g, M), tuple(Wr.mul(d, p[k]) for d, p in zip(ds, chosen)))
start = (I5, tuple(Wr.one for _ in chosen)); seen = {start}; fr = [start]
while fr:
    fr = [t for s in fr for c in "ab" for t in [step(s, c)] if t not in seen and not seen.add(t)]
f = {}
det = all(f.setdefault(ds, g) == g for g, ds in seen)
print("(2) homs (a, b) -> Z2wrZ4, elements (f, k):", chosen)
print("    joint group", len(seen), "; Z2wrZ4^6 part", len(set(ds for _, ds in seen)), "; determines G(aabb):", det)
c = lambda A, B: ((B + 2) // 4 + A * (B % 4 == 3)) % 2
bad = 0
for A in range(4):
    for B in range(8):
        bad += ((B % 4 == 3) + c(A + 1, B) - c(A, B)) % 2 != 0
        bad += ((A in (2, 3)) * (B % 2) - (A == 1) - ((A + B) % 4 == 1) - c(A, B + 1) + c(A, B)) % 2 != 0
words = mism = 0
for n in range(15):
    for u in itertools.product("ab", repeat=n):
        A = B = H = m1 = p1 = r3 = 0
        for ch in u:
            if ch == "a": r3 ^= B % 4 == 3; A += 1
            else:
                H ^= A % 4 in (2, 3) and B % 2 == 1; m1 ^= A % 4 == 1; p1 ^= (A + B) % 4 == 1; B += 1
        words += 1; mism += H != (m1 ^ p1 ^ r3 ^ c(A, B))
print("(3) identity (I): step cases failing", bad, "of 64; words of length <= 14:", words, "mismatches", mism)
top = [(i, j) for i in range(4) for j in range(2)]
T, idx = mk_wr(top, lambda s, t: ((s[0] + t[0]) % 4, (s[1] + t[1]) % 2))
def closure(gens):
    seen = {T.one}; fr = [T.one]
    while fr: fr = [y for x in fr for g in gens for y in [T.mul(x, g)] if y not in seen and not seen.add(y)]
    return seen
for x in "ab":
    X = (1 if x == "a" else 0, (1, 0)); Y = (1 if x == "b" else 0, (0, 1))
    G = closure([X, Y]); out = []
    for g in top:
        F = {t for t in G if t[0] >> idx[g] & 1}
        stab = {n for n in G if all(T.mul(e, n) in F for e in F)}
        N = [n for n in stab if all(T.mul(T.mul(T.inv(p), n), p) in stab for p in G)]
        rep = {}
        for t in G:
            if t not in rep:
                cos = [T.mul(t, n) for n in N]; m = min(cos)
                for e in cos: rep[e] = m
        class Q:
            one = rep[T.one]
            mul = staticmethod(lambda a, b: rep[T.mul(a, b)])
            inv = staticmethod(lambda a: rep[T.inv(a)])
        qc = coords(Q, schreier_vals(Q, rep[X], rep[Y]))
        out.append((g, len(G) // len(N), all(reduce(BD, v) == 0 for v in qc)))
    print("(4) count of", x, "at state g: (g, |syntactic group|, in var(Z2wrZ4)):", out)
