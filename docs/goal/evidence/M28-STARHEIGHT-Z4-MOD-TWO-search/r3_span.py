#!/usr/bin/env python3
"""R3: is a letter-in-state count a linear combination of proved pieces? (not Lean-verified)

A count `u -> #{i : u_i = x, g(n(u.take i))}` (n = vector of letter counts of the prefix) is
determined by its weight g, and g -> count is injective (append x to a^n... to isolate one
position).  So, for a fixed counted letter x, a count is an F2- (or Z/4-) linear combination of
other counts of x on all words iff its weight is the same combination of their weights, as
functions on N^alpha.  All weights below are 2^K-periodic, so this is a finite computation on
the torus (Z/M)^alpha, M = 2^K.  (Pieces of odd period cannot help: summing over odd shifts
maps them to 2-power-periodic pieces of the same kind and fixes the 2-power-periodic ones.)

Proved pieces (the letter-in-state counts known to have height one modulo the given modulus):
  PAR  : (Z2)^r translation automata, every modulus   -> weights of n mod 2;
  PC   : pcount, counted letter fixed, every p, every modulus (PST 6.6) -> [n_S = h mod p], x not in S;
  PC4  : pcount moving, p = 4, every modulus -> [n_S = h mod 4], x in S;
  Z4N2 : Z4 walks without displacement 2, or with displacements in {0, 2}, every modulus;
  Z4   : (modulo 2 only) every Z4 walk, every state (R1, vcount_z4_mod_two_height).
Rank deficiency = dim span(pieces + targets) - dim span(pieces) (log2 of the index for Z/4).
"""
import sys
from itertools import product, combinations


def torus(nlet, M):
    return list(product(range(M), repeat=nlet))


def ind(pts, pred):
    return [1 if pred(n) else 0 for n in pts]


def pieces(nlet, x, M, allz4):
    """Weights of the proved pieces for counted letter x (letters 0..nlet-1)."""
    pts = torus(nlet, M)
    out = []
    for p in product(range(2), repeat=nlet):                      # PAR
        out.append(ind(pts, lambda n, p=p: all(n[i] % 2 == p[i] for i in range(nlet))))
    others = [i for i in range(nlet) if i != x]
    pk = 2
    while pk <= M:                                               # PC
        for r in range(1, len(others) + 1):
            for S in combinations(others, r):
                for h in range(pk):
                    out.append(ind(pts, lambda n, S=S, h=h, pk=pk: sum(n[i] for i in S) % pk == h))
        pk *= 2
    for r in range(0, nlet):                                     # PC4 (x moving)
        for S0 in combinations(others, r):
            S = S0 + (x,)
            for h in range(4):
                out.append(ind(pts, lambda n, S=S, h=h: sum(n[i] for i in S) % 4 == h))
    for d in product(range(4), repeat=nlet):                     # Z4 walks
        ok_n2 = all(v != 2 for v in d) or all(v in (0, 2) for v in d)
        if allz4 or ok_n2:
            for q in range(4):
                out.append(ind(pts, lambda n, d=d, q=q: sum(a * b for a, b in zip(d, n)) % 4 == q))
    return pts, out


# ---------- F2 rank with Python ints ----------
def f2_rank(vecs):
    basis = {}
    for v in vecs:
        b = int("".join(map(str, v)), 2) if isinstance(v, list) else v
        while b:
            h = b.bit_length() - 1
            if h in basis:
                b ^= basis[h]
            else:
                basis[h] = b
                break
    return len(basis)


# ---------- Z/4: Howell-form insertion, returns log2 of the module size ----------
def z4_logsize(vecs):
    basis = {}
    stack = [list(v) for v in vecs]
    while stack:
        v = [a % 4 for a in stack.pop()]
        while True:
            j = next((k for k, a in enumerate(v) if a), None)
            if j is None:
                break
            if v[j] % 2 == 1:
                u = v[j]
                v = [(a * u) % 4 for a in v]          # u * u = 1 mod 4
            if j not in basis:
                basis[j] = v
                if v[j] == 2:
                    stack.append([(2 * a) % 4 for a in v])
                break
            b = basis[j]
            if b[j] == 1:
                c = v[j]
                v = [(a - c * bb) % 4 for a, bb in zip(v, b)]
            elif v[j] == 2:
                v = [(a - bb) % 4 for a, bb in zip(v, b)]
            else:
                basis[j] = v
                stack.append(b)
                break
    return sum(2 if b[j] == 1 else 1 for j, b in basis.items())


def report(name, nlet, x, M, mod, target_fn, states, allz4=None):
    if allz4 is None:
        allz4 = (mod == 2)
    pts, P = pieces(nlet, x, M, allz4)
    T = [ind(pts, lambda n, q=q: target_fn(n, q)) for q in states]
    if mod == 2:
        r0 = f2_rank(P)
        r1 = f2_rank(P + T)
    else:
        r0 = z4_logsize(P)
        r1 = z4_logsize(P + T)
    print(f"{name}: mod {mod}, torus (Z/{M})^{nlet}, counted letter {x}: "
          f"pieces span {r0}, with targets {r1}, deficiency {r1 - r0}")
    return r1 - r0


if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    # sanity checks of the Z/4 routine
    assert z4_logsize([[2]]) == 1 and z4_logsize([[1, 1], [0, 2]]) == 3 and z4_logsize([[2, 1]]) == 2
    # R1 control: Z4 walk a:1, b:2, x:0 is covered mod 2 even without the Z4 pieces' R1 entry
    # positive control: Z4Rot2Abc modulo 2 is in the span of the pieces other than R1 (the R1
    # identity), so the deficiency must be 0 with allz4=False
    report("control: Z4 mod 2, a:1 b:2 x:0, R1 pieces removed", 3, 2, M, 2,
           lambda n, q: (n[0] + 2 * n[1]) % 4 == q, range(4), allz4=False)
    # (a) Z8 modulo 2
    report("(a) Z8, a:1 x:0", 2, 1, M, 2, lambda n, q: n[0] % 8 == q, range(8))
    report("(a) Z8, a:1 b:2 x:0", 3, 2, M, 2, lambda n, q: (n[0] + 2 * n[1]) % 8 == q, range(8))
    report("(a) Z8, a:1 c:4 x:0", 3, 2, M, 2, lambda n, q: (n[0] + 4 * n[1]) % 8 == q, range(8))
    report("(a) Z8, a:1 b:3 x:0", 3, 2, M, 2, lambda n, q: (n[0] + 3 * n[1]) % 8 == q, range(8))
    report("(a) Z8, a:1 x:1 (moving)", 2, 1, M, 2, lambda n, q: (n[0] + n[1]) % 8 == q, range(8))
    # (b) Z4 x Z2 modulo 2: a:(1,0), c:(0,1), x:(0,0)
    report("(b) Z4xZ2, a:(1,0) c:(0,1) x:(0,0), all 8 states", 3, 2, M, 2,
           lambda n, q: n[0] % 4 == q % 4 and n[1] % 2 == q // 4, range(8))
    for r in range(4):
        report(f"(b) Z4xZ2, state ({r},1) only", 3, 2, M, 2,
               lambda n, q, r=r: n[0] % 4 == r and n[1] % 2 == 1, [0])
    report("(b) Z4xZ2, a:(1,0) c:(0,1) x:(1,1) (moving), all states", 3, 2, M, 2,
           lambda n, q: (n[0] + n[2]) % 4 == q % 4 and (n[1] + n[2]) % 2 == q // 4, range(8))
    # (b) Z4 modulo 4 (Z4Rot2Abc), pieces proved for every modulus
    report("(b) Z4 mod 4, a:1 b:2 x:0 (Z4Rot2Abc), all 4 states", 3, 2, M, 4,
           lambda n, q: (n[0] + 2 * n[1]) % 4 == q, range(4))
    report("(b) Z4 mod 4, a:1 b:2 x:0, state 0 only", 3, 2, M, 4,
           lambda n, q: (n[0] + 2 * n[1]) % 4 == 0, [0])
