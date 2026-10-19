#!/usr/bin/env python3
"""Group facts about Z2 wr Z4 = (ZMod 4 -> ZMod 2) x| ZMod 4 (not Lean-verified).

Elements are pairs (f, e) with f a 4-tuple of bits and e in Z/4, multiplied as in the Lean
`Z2WrZ4` (Mathlib's SemidirectProduct):  (f1, e1) * (f2, e2) = (f1 + e1.f2, e1 + e2),
where (e.f)(i) = f(i - e).

Prints: the order, the lower central series (hence the nilpotency class), the Frattini subgroup
Phi = G^2 [G, G] and whether it is abelian, the subgroups of index 2 and whether any is abelian,
and the abelian normal subgroups N with G/N elementary abelian (there are none iff G does not
divide a semidirect product (abelian) x| (Z2)^n: see the note).
"""
from itertools import product

E = [(f, e) for f in product(range(2), repeat=4) for e in range(4)]
ONE = ((0, 0, 0, 0), 0)


def mul(x, y):
    f1, e1 = x
    f2, e2 = y
    return (tuple((f1[i] + f2[(i - e1) % 4]) % 2 for i in range(4)), (e1 + e2) % 4)


def inv(x):
    for y in E:
        if mul(x, y) == ONE:
            return y


def closure(gens):
    S = {ONE}
    frontier = [ONE]
    while frontier:
        new = []
        for s in frontier:
            for g in gens:
                t = mul(s, g)
                if t not in S:
                    S.add(t)
                    new.append(t)
        frontier = new
    return frozenset(S)


def comm(x, y):
    return mul(mul(mul(x, y), inv(x)), inv(y))


def commutator_subgroup(A, B):
    return closure([comm(a, b) for a in A for b in B])


def is_abelian(H):
    return all(mul(x, y) == mul(y, x) for x in H for y in H)


def is_normal(H, G):
    return all(mul(mul(g, h), inv(g)) in H for g in G for h in H)


G = frozenset(E)
assert len(G) == 64
print("order", len(G))

lcs = [G]
while len(lcs[-1]) > 1:
    lcs.append(commutator_subgroup(G, lcs[-1]))
print("lower central series sizes", [len(H) for H in lcs], "-> nilpotency class", len(lcs) - 1)

D = commutator_subgroup(G, G)
Phi = closure(list(D) + [mul(x, x) for x in G])
print("Frattini subgroup Phi = G^2 [G,G]: order", len(Phi), ", abelian:", is_abelian(Phi))

# subgroups of index 2 contain Phi; G/Phi is elementary abelian, enumerate its hyperplanes
reps = []
for g in G:
    if all(mul(inv(r), g) not in Phi for r in reps):
        reps.append(g)
print("|G/Phi| =", len(reps))
index2 = set()
for a in reps:
    for b in reps:
        H = closure(list(Phi) + [a, b])
        if len(H) == 32:
            index2.add(H)
print("subgroups of index 2:", len(index2), ", abelian ones:", sum(is_abelian(H) for H in index2))

# abelian normal N with G/N elementary abelian: G/N elementary abelian iff N contains Phi
print("abelian normal subgroups containing Phi:",
      "none (Phi itself is not abelian)" if not is_abelian(Phi) else "check")

ords = {}
for g in G:
    k, x = 1, g
    while x != ONE:
        x, k = mul(x, g), k + 1
    ords[k] = ords.get(k, 0) + 1
print("element orders", dict(sorted(ords.items())))
Z = frozenset(z for z in G if all(mul(z, g) == mul(g, z) for g in G))
print("centre order", len(Z))
