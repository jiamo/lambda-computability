import sys, itertools
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import s4three as S
import gen as G

E = S.E
IDX = S.IDX
P = S.S4

LIFTS = [  # (Lean name, letter tables in Lean convention)
    ("S4Three.C0132_0213_1230", [[0, 1, 3, 2], [0, 2, 1, 3], [3, 0, 1, 2]]),
    ("S4Three.C0132_0213_1320", [[0, 1, 3, 2], [0, 2, 1, 3], [3, 0, 2, 1]]),
    ("S4Three.C0132_0213_2103", [[0, 1, 3, 2], [0, 2, 1, 3], [2, 1, 0, 3]]),
    ("S4Three.C0132_0231_1023", [[0, 1, 3, 2], [0, 3, 1, 2], [1, 0, 2, 3]]),
    ("S4Three.C0132_1023_1230", [[0, 1, 3, 2], [1, 0, 2, 3], [3, 0, 1, 2]]),
    ("S4Three.C0132_1203_1320", [[0, 1, 3, 2], [2, 0, 1, 3], [3, 0, 2, 1]]),
    ("S4Three.C0132_1203_2310", [[0, 1, 3, 2], [2, 0, 1, 3], [3, 2, 0, 1]]),
    ("S4Three.C0132_1203_3021", [[0, 1, 3, 2], [2, 0, 1, 3], [1, 3, 2, 0]]),
    ("S4Three.C0231_1203_2310", [[0, 3, 1, 2], [2, 0, 1, 3], [3, 2, 0, 1]]),
    ("S4Three.C0231_1302_2310", [[0, 3, 1, 2], [2, 0, 3, 1], [3, 2, 0, 1]]),
    ("S4Cox", [[1, 0, 2, 3], [0, 2, 1, 3], [0, 1, 3, 2]]),
]

P3T = [[0, 1, 2], [1, 0, 2], [2, 1, 0], [0, 2, 1], [1, 2, 0], [2, 0, 1]]

def orbit_key(t):
    orb = set()
    for perm in itertools.permutations(range(3)):
        for g in P:
            orb.add(tuple(S.conj(g, t[perm[i]]) for i in range(3)))
    return min(orb)

classes = S.triple_classes(True)
lift_keys = {orbit_key(tuple(tuple(r) for r in L)): (n, L) for n, L in LIFTS}
assert len(lift_keys) == 11
KCLS = [t for t in classes if t not in lift_keys]
assert len(KCLS) == 45
REPS = [("K%02d" % (i + 1), [list(r) for r in t]) for i, t in enumerate(KCLS)] + LIFTS
for t in lift_keys:
    assert t in classes

def cj(c, i):
    return IDX[S.conj(P[c], P[i])]

R0 = [0, 1, 7, 3, 9]
w1 = []
for a in range(24):
    c = next(c for c in range(24) if cj(c, a) in R0)
    w1.append(c)
w2 = {}
P3 = []
for r in R0:
    cent = [c for c in range(24) if cj(c, r) == r]
    row = []
    for b in range(24):
        c = min(cent, key=lambda c: cj(c, b))
        row.append(c)
        if (r, cj(c, b)) not in P3:
            P3.append((r, cj(c, b)))
    w2[r] = row

def is_dbl(i):
    return S.is_dbl(P[i])

def in_max(m, i):
    p = P[i]
    if m < 4:
        return p[m] == m
    if m < 7:
        d = [(1, 0, 3, 2), (2, 3, 0, 1), (3, 2, 1, 0)][m - 4]
        return S.mul(p, d) == S.mul(d, p)
    ev = [True, False, False, True, True, False, False, True, True, False, False, True, True,
          False, False, True, True, False, False, True, True, False, False, True]
    return ev[i]

def witness(a, b, c):
    if is_dbl(a) or is_dbl(b) or is_dbl(c):
        return 0
    if a == b or a == c or b == c:
        return 1
    for m in range(8):
        if in_max(m, a) and in_max(m, b) and in_max(m, c):
            return 2 + 4 * m
    t = (P[a], P[b], P[c])
    for k, (name, L) in enumerate(REPS):
        for p in range(6):
            for cc in range(24):
                if all(S.conj(P[cc], t[P3T[p][x]]) == tuple(L[x]) for x in range(3)):
                    return 3 + 4 * (k + 56 * (p + 6 * cc))
    raise Exception("no witness %s" % ((a, b, c),))

W3 = [[witness(r, b, c) for c in range(24)] for (r, b) in P3]
CJ = [[cj(c, i) for i in range(24)] for c in range(24)]

if __name__ == "__main__":
    print(len(P3), "pairs in stage 3")
    from collections import Counter
    print(Counter(w % 4 for row in W3 for w in row))
