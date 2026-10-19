# Order-8 cores modulo 2: computational evidence for the reductions in M28-STARHEIGHT-CORE-MOD-TWO.md.
# (A) Central extensions of V4 = (Z/2)^2 by Z/2 from bilinear cocycles beta: (u,z)(v,z') =
#     (u+v, z+z'+beta(u,v)); identify the group by its element orders.
# (B) For letter lifts rho(y) = (delta(y), eps(y)), the prefix product is (s_i, z_i) with
#     z_i = sum_{k<j<i} beta(delta_k, delta_j) + sum_{k<i} eps(y_k), so z is additive in beta:
#     z_Q8 = z_D4 + z_{Z4xZ2} for beta_Q8 = beta_D4 + beta_{Z4xZ2}.  Hence, mod 2,
#     hcount_Q8(x,(q,c)) = (1+c) #{x at q} + hcount_D4(x,(q,1)) + hcount_{Z4xZ2}(x,(q,1)) + E,
#     where E corrects the lifts eps (a count of x at q weighted by letter counts: good mod 2).
#     Checked on random words.
# (C) The group Z2WrZ2 of Start/StarHeightOrderEightCores.lean (Mathlib's semidirect product
#     convention, (e.f)(i) = f(i - e)) is D4.
# (D) Z8: with s = R + 4C (R the walk with the rotation-4 letters set to 0, C the parity of the
#     rotation-4 letters read), [s = q] = [R = q mod 4] + [R = q + 4] + [R = q mod 4] C (mod 2),
#     where [R = q mod 4] is a Z4 walk and [R = q mod 4] C a Z4 x Z2 walk.  Checked on all states.
import random, itertools
random.seed(1)
V4 = [(a, b) for a in range(2) for b in range(2)]
def add(u, v): return ((u[0] + v[0]) % 2, (u[1] + v[1]) % 2)
betas = {
    "Z2^3":  lambda u, v: 0,
    "Z4xZ2": lambda u, v: (u[0] * v[0] + u[1] * v[1]) % 2,
    "D4":    lambda u, v: (u[0] * v[1]) % 2,
    "Q8":    lambda u, v: (u[0] * v[0] + u[0] * v[1] + u[1] * v[1]) % 2,
}
def gmul(beta, x, y): return (add(x[0], y[0]), (x[1] + y[1] + beta(x[0], y[0])) % 2)
def order(beta, x):
    e = ((0, 0), 0); y = x; n = 1
    while y != e: y = gmul(beta, y, x); n += 1
    return n
print("(A) element orders of the cocycle extensions of V4 by Z2")
for name, beta in betas.items():
    els = [(v, z) for v in V4 for z in range(2)]
    prof = sorted(order(beta, x) for x in els)
    ab = all(gmul(beta, x, y) == gmul(beta, y, x) for x in els for y in els)
    print("  %-6s orders %s abelian %s" % (name, prof, ab))
def hcount(beta, rho, w, x, g):
    st = ((0, 0), 0); n = 0
    for y in w:
        if y == x and st == g: n += 1
        st = gmul(beta, st, rho[y])
    return n
bad = 0; trials = 0
for t in range(3000):
    k = random.randint(1, 4)
    delta = [random.choice(V4) for _ in range(k)]
    eps = [random.randint(0, 1) for _ in range(k)]
    w = [random.randrange(k) for _ in range(random.randint(0, 30))]
    x = random.randrange(k); q = random.choice(V4); c = random.randint(0, 1)
    rho = [(delta[y], eps[y]) for y in range(k)]
    rho0 = [(delta[y], 0) for y in range(k)]
    lhs = hcount(betas["Q8"], rho, w, x, (q, c))
    # E: sum over x at q of sum_{k<i} eps(y_k)
    s = (0, 0); E = 0; nxq = 0
    for i, y in enumerate(w):
        if y == x and s == q:
            nxq += 1; E += sum(eps[w[j]] for j in range(i))
        s = add(s, delta[y])
    rhs = (1 + c) * nxq + hcount(betas["D4"], rho0, w, x, (q, 1)) + \
        hcount(betas["Z4xZ2"], rho0, w, x, (q, 1)) + E
    trials += 1; bad += (lhs - rhs) % 2
print("(B) Q8 = D4 + Z4xZ2 (mod 2): trials %d mismatches %d" % (trials, bad))
# (C) Z2WrZ2 = (Z2 -> Z2) x| Z2, <f,e><f',e'> = <f + shift_e f', e + e'>, (shift_e f')(i) = f'(i - e)
els = [((f0, f1), e) for f0 in range(2) for f1 in range(2) for e in range(2)]
def wmul(x, y):
    (f, e), (g, d) = x, y
    sg = tuple(g[(i - e) % 2] for i in range(2))
    return (tuple((f[i] + sg[i]) % 2 for i in range(2)), (e + d) % 2)
def word(x):
    e = ((0, 0), 0); y = x; n = 1
    while y != e: y = wmul(y, x); n += 1
    return n
prof = sorted(word(x) for x in els)
ab = all(wmul(x, y) == wmul(y, x) for x in els for y in els)
print("(C) Z2WrZ2 orders %s abelian %s (D4: [1,2,2,2,2,2,4,4], non-abelian)" % (prof, ab))
# (D) the Z8 identity, all (R, C, q)
bad = 0
for R, C, q in itertools.product(range(8), range(2), range(8)):
    s = (R + 4 * C) % 8
    lhs = int(s == q)
    rhs = (int(R % 4 == q % 4) + int(R == (q + 4) % 8) + int(R % 4 == q % 4) * C) % 2
    bad += lhs != rhs
print("(D) Z8 identity [s=q] = [R=q mod 4] + [R=q+4] + [R=q mod 4]C: 128 cases, mismatches %d" % bad)
