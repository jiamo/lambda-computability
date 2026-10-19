# R3 (b)(iii): the W-test for the three-letter word aabc modulo 2 (its syntactic group, order 512, is
# in A2A4 by words_a2a4.py).  F3 -> Z4^3, R its kernel, M = R/R'R^2 (rank 129); the Schreier values
# rep * x_k * rep'^-1 over all 64 * 3 (rep, k) are used (the trivial ones give zero coordinates).
# Families: WR = Z2 wr Z4 and UT = UT4(F2) (random samples of homs; a positive answer is sound,
# a negative one would only be evidence), FA = abelian Frattini subgroup (exact, Magnus embedding).
import os, random
_d = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(_d, "c0_variety.py")).read()
_print = print
print = lambda *a, **k: None
exec(_src[:_src.index("for x, g in")])
print = _print
random.seed(1)
NG = 3
REPS = [(i, j, k) for i in range(4) for j in range(4) for k in range(4)]
def rep_el(Gp, gens, r):
    e = Gp.one
    for g, n in zip(gens, r): e = Gp.mul(e, power(Gp, g, n))
    return e
def schreier3(Gp, gens):
    reps = {r: rep_el(Gp, gens, r) for r in REPS}
    vals = []
    for r in REPS:
        for k in range(NG):
            nr = tuple((r[t] + (t == k)) % 4 for t in range(NG))
            vals.append(Gp.mul(Gp.mul(reps[r], gens[k]), Gp.inv(reps[nr])))
    return vals
def coords3(Gp, vals):
    span = {Gp.one: 0}; d = 0; rows = []
    for v in vals:
        if v not in span:
            new = {Gp.mul(e, v): m | (1 << d) for e, m in span.items()}
            assert not (set(new) & set(span)); span.update(new); d += 1
        rows.append(span[v])
    return [sum(((rows[i] >> c) & 1) << i for i in range(len(vals))) for c in range(d)]
def sample(Gp, elems, n):
    B = []; hist = []
    for t in range(n):
        gens = [random.choice(elems) for _ in range(NG)]
        B = add_all(B, coords3(Gp, schreier3(Gp, gens)))
        if (t + 1) % 500 == 0: hist.append(len(B))
    return B, hist
B_WR, h1 = sample(Wr, WR, 3000)
B_UT, h2 = sample(UT4, UTE, 1500)
print("WR rank after each 500 samples:", h1, "; UT:", h2)
# Magnus embedding of W3: (f, q), f in F2[Z4^3]^3 (192 bits: 64*c + 16*i + 4*j + k), q in Z4^3
def qs(q, f):
    g = 0
    while f:
        b = f & -f; n = b.bit_length() - 1; f ^= b
        c, r = divmod(n, 64); i, rest = divmod(r, 16); j, k = divmod(rest, 4)
        g |= 1 << (64 * c + 16 * ((i + q[0]) % 4) + 4 * ((j + q[1]) % 4) + (k + q[2]) % 4)
    return g
class Mag3:
    one = (0, (0, 0, 0))
    @staticmethod
    def mul(x, y): return (x[0] ^ qs(x[1], y[0]), tuple((a + b) % 4 for a, b in zip(x[1], y[1])))
    @staticmethod
    def inv(x):
        q = tuple((-a) % 4 for a in x[1]); return (qs(q, x[0]), q)
mg = [(1 << (64 * c), tuple(int(t == c) for t in range(3))) for c in range(3)]
sv = [v[0] for v in schreier3(Mag3, mg)]
piv = {}
for i, v in enumerate(sv):
    m = 1 << i
    while v:
        h = v.bit_length() - 1
        if h in piv: v ^= piv[h][0]; m ^= piv[h][1]
        else: piv[h] = (v, m); break
print("Magnus: rank of M:", len(piv))
def sc(v):
    m = 0
    while v:
        h = v.bit_length() - 1; v ^= piv[h][0]; m ^= piv[h][1]
    return m
sq = [Mag3.mul(g, g) for g in mg]
gensK = []
for k in range(3):
    sh = tuple(2 * (t == k) for t in range(3))
    gensK += [qs(sh, v) ^ v for v in sv]
for k in range(3):
    for l in range(k + 1, 3):
        cm = Mag3.mul(Mag3.mul(sq[k], sq[l]), Mag3.inv(Mag3.mul(sq[l], sq[k])))
        gensK += [qs(q, cm[0]) for q in REPS]
# coordinates relative to the 192 Schreier values: express in the sv basis, as a 192-bit vector
KFA = add_all([], [sc(v) for v in gensK])
NS = len(sv)
print("FA: dim of M cap Phi(W)' (in Schreier-value coordinates):", len(KFA))
def word_group(w):
    letters = sorted(set(w))
    def elem(pairs):
        M = list(I5)
        for i, j in pairs: M[i] |= 1 << j
        return tuple(M)
    gens = [elem([(i, i + 1) for i in range(4) if w[i] == x]) for x in letters]
    G = {I5}; fr = [I5]
    while fr: fr = [y for x in fr for g in gens for y in [mmul(x, g)] if y not in G and not G.add(y)]
    F = {t for t in G if t[0] >> 4 & 1}
    stab = {n for n in G if all(mmul(e, n) in F for e in F)}
    N = [n for n in stab if all(mmul(mmul(minv(p), n), p) in stab for p in G)]
    rep = {}
    for t in G:
        if t not in rep:
            cos = [mmul(t, n) for n in N]; m = min(cos)
            for e in cos: rep[e] = m
    class Q:
        one = rep[I5]
        mul = staticmethod(lambda a, b: rep[mmul(a, b)])
        inv = staticmethod(lambda a: rep[minv(a)])
    return Q, [rep[g] for g in gens], len(set(rep.values()))
# kernel test: work in the quotient of F2^192 by the relations of M is unnecessary, since every
# functional comes from a group and is evaluated on vectors written in Schreier-value coordinates.
def kernel_in(funcs, within):
    out = []; piv2 = {}
    for v in within:
        ev = sum((bin(f & v).count("1") & 1) << i for i, f in enumerate(funcs))
        while ev:
            h = ev.bit_length() - 1
            if h in piv2: ev ^= piv2[h][0]; v ^= piv2[h][1]
            else: piv2[h] = (ev, v); break
        if ev == 0 and v: out.append(v)
    return add_all([], out)
FULL = [1 << i for i in range(NS)]
for w in ["aabc", "abcc"]:
    Q, qg, order = word_group(w)
    gf = coords3(Q, schreier3(Q, qg))
    res = []
    for name, fl, K in [("WR", B_WR, FULL), ("WR+UT", B_WR + B_UT, FULL), ("FA", [], KFA),
                        ("WR+UT+FA", B_WR + B_UT, KFA)]:
        Kk = kernel_in(fl, K) if fl else K
        res.append((name, all(bin(g & k).count("1") % 2 == 0 for g in gf for k in Kk)))
    print(w, "|syntactic group|", order, "; rank of its functionals", len(add_all([], gf)),
          "; in variety (sampled homs for WR, UT):", res)
# sanity check of the three-generator test: aabb (in var(Z2 wr Z4) by aabb_variety.py) with a third
# letter acting trivially, and with the third letter equal to the second
for w, extra in [("aabb", "one"), ("aabb", "copy")]:
    Q, qg, order = word_group(w)
    qg = qg + [Q.one if extra == "one" else qg[1]]
    gf = coords3(Q, schreier3(Q, qg))
    Kk = kernel_in(B_WR, FULL)
    print("sanity:", w, "third letter", extra, "; in var(WR):",
          all(bin(g & k).count("1") % 2 == 0 for g in gf for k in Kk))
