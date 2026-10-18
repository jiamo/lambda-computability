import r2obs as R, s4three as S, itertools
t = R.user_class("0132 0213 1032")
print("letters (Lean):", t)
# pairings: index of pairing containing {0,j}: j=1,2,3 -> P0={01|23}, P1={02|13}, P2={03|12}
def pidx(u, v):
    s = frozenset((u, v))
    for k, (x, y) in enumerate([(0, 1), (0, 2), (0, 3)]):
        if s == frozenset((x, y)) or s == frozenset(set(range(4)) - {x, y}):
            return k
pairs = [(0, 1), (0, 2), (0, 3)]
# pairing automaton: state = pairing index; letter acts by T(x)^-1 (left-to-right reading)
def act(p, k):
    x, y = pairs[k]
    return pidx(p[x], p[y])
delta = [[act(S.inv(t[x]), k) for x in range(3)] for k in range(3)]
print("pairing automaton", delta)
for base in range(3):
    mon = S.ret_monoid(delta, base)
    print("base", base, "aperiodic index", S.aper_index(mon))
# relabel: base P1 -> 0
perm = [1, 0, 2]  # new label of old state: old1->0, old0->1, old2->2
inv = {perm[o]: o for o in range(3)}
d2 = [[perm[delta[inv[q]][x]] for x in range(3)] for q in range(3)]
print("relabelled", d2, "aper", S.aper_index(S.ret_monoid(d2, 0)))
for r in range(3):
    for X in [(2,), (0,), (1,)]:
        print("start", r, "X", X, "amb", len(R.ambiguity2([R.offbase_counter(d2, r, X)], t)))
# all three counts of a in each pairing state (the full V4 part) - sanity: should determine
def full(st, x):
    q, c = st
    c = list(c)
    if x == 2: c[q] ^= 1
    return (delta[q][x], tuple(c))
o = R.Obs("full", (0, (0, 0, 0)), full)
print("full counts amb", len(R.ambiguity2([o], t)))
for r in range(3):
    for X in [(2,), (0,), (1,), (0, 1, 2)]:
        print("REV start", r, "X", X, "amb", len(R.ambiguity2([R.rev_counter(d2, r, X)], t)))
