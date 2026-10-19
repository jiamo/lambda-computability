# R3 (b)(i), explicit formulas.  For each count c(x,(s,t)) of the Z4 x Z2 core (a = (1,0),
# b = (0,1)), find an F2-combination  c(x,(s,t)) + c(x, base) = sum of Z4 counts + counter term
# (no products needed), base = (0,1) for x = b and (0,0) for x = a, on all words of length <= N,
# and check it on all words of length <= N + 2.
# Z4 count  z[ra,rb;g;x] = #{i : u_i = x, ra*A_i + rb*B_i = g mod 4};  counter term = a function
# of (A mod 4, B mod 8), printed as the set of (A mod 4, B mod 8) where it is 1.
import itertools, sys

N = int(sys.argv[1]) if len(sys.argv) > 1 else 12

def table(n):
    rows = []
    for L in range(n + 1):
        for u in itertools.product((0, 1), repeat=L):
            A = B = 0; z = [0] * 128; c = [0] * 16
            for x in u:
                for ra in range(4):
                    for rb in range(4):
                        z[((ra * 4 + rb) * 4 + (ra * A + rb * B) % 4) * 2 + x] ^= 1
                c[(x * 4 + A % 4) * 2 + B % 2] ^= 1
                A += x == 0; B += x == 1
            rows.append((A % 4, B % 8, z, c))
    return rows

def vecs(rows):
    def vec(f): return sum(1 << i for i, r in enumerate(rows) if f(r))
    gens = []
    # Z4 counts: one representative per (rho up to the choice, g, x); simple rho first
    order = sorted(((ra, rb) for ra in range(4) for rb in range(4)), key=lambda p: (p[0] % 4 != 0) + (p[1] % 4 != 0))
    for ra, rb in order:
        for g in range(4):
            for x in (0, 1):
                k = ((ra * 4 + rb) * 4 + g) * 2 + x
                gens.append((("z", ra, rb, g, "ab"[x]), vec(lambda r, k=k: r[2][k])))
    for s in range(4):
        for t in range(8):
            gens.append((("ctr", s, t), vec(lambda r, s=s, t=t: r[0] == s and r[1] == t)))
    return gens, vec

rows = table(N)
gens, vec = vecs(rows)
basis = {}
for j, (_, v) in enumerate(gens):
    m = 1 << j
    while v:
        h = v.bit_length() - 1
        if h in basis: v ^= basis[h][0]; m ^= basis[h][1]
        else: basis[h] = (v, m); break
def solve(v):
    m = 0
    while v:
        h = v.bit_length() - 1
        if h not in basis: return None
        v ^= basis[h][0]; m ^= basis[h][1]
    return m
names = [("ab"[x], (s, t)) for x in (0, 1) for s in range(4) for t in range(2)]
big = table(N + 2)
for i, nm in enumerate(names):
    base = names.index((nm[0], (0, 1) if nm[0] == "b" else (0, 0)))
    if i == base: continue
    m = solve(vec(lambda r: r[3][i] ^ r[3][base]))
    if m is None:
        print(nm, "+", names[base], ": not a combination of Z4 counts and counters"); continue
    used = [gens[j][0] for j in range(len(gens)) if m >> j & 1]
    zs = [u[1:] for u in used if u[0] == "z"]; cs = sorted(u[1:] for u in used if u[0] == "ctr")
    ok = all((r[3][i] ^ r[3][base]) == (sum(r[2][((ra * 4 + rb) * 4 + g) * 2 + "ab".index(x)]
             for ra, rb, g, x in zs) + ((r[0], r[1]) in cs)) % 2 for r in big)
    print(nm, "+", names[base], "= Z4 counts", zs, "+ counter on", cs, "; holds up to length", N + 2, ":", ok)
