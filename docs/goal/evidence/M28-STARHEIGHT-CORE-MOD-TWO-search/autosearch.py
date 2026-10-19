# Search 2-letter permutation automata (base 0, star-free first returns at 0) on n points that,
# together with all counters (words over {a,b} of length <= 4 except the target's, mod 2), determine
# the target L(w,k,2).  Joint BFS over (automaton state, counter+target state).
import sys, time, itertools
from itertools import product
TGT = sys.argv[1]; NMAX = int(sys.argv[2])
excl = {TGT, ''.join({'a': 'b', 'b': 'a'}[c] for c in TGT)}
words = [''.join(p) for L in range(1, 5) for p in product("ab", repeat=L) if ''.join(p) not in excl]
def act(w, v, x):
    v = list(v)
    for i in range(len(w) - 1, -1, -1):
        if w[i] == x: v[i + 1] ^= v[i]
    return tuple(v)
allw = words + [TGT]
s0 = tuple((1,) + (0,) * len(w) for w in allw)
idx = {s0: 0}; states = [s0]
for s in states:
    for x in "ab":
        t = tuple(act(w, v, x) for w, v in zip(allw, s))
        if t not in idx: idx[t] = len(states); states.append(t)
NH = len(states)
P = {x: [idx[tuple(act(w, v, x) for w, v in zip(allw, s))] for s in states] for x in "ab"}
byc = {}
for i, s in enumerate(states): byc.setdefault(s[:-1], []).append(i)
partner = [None] * NH
for c, l in byc.items():
    assert len(l) <= 2
    if len(l) == 2: partner[l[0]], partner[l[1]] = l[1], l[0]
print("target", TGT, "H-states", NH, "paired", sum(p is not None for p in partner), flush=True)
def aperiodic_avoid(n, letters):
    BOT = n
    gens = [tuple((BOT if (s == 0 or s == BOT or p[s] == 0) else p[s]) for s in range(n + 1)) for p in letters]
    ident = tuple(BOT if s == 0 else s for s in range(n + 1))
    seen = {ident}; fr = [ident]
    while fr:
        nf = []
        for m in fr:
            for g in gens:
                h = tuple(g[m[s]] for s in range(n + 1))
                if h not in seen: seen.add(h); nf.append(h)
        fr = nf
    for m in seen:
        x = m
        for _ in range(n + 3):
            y = tuple(m[x[s]] for s in range(n + 1))
            if y == x: break
            x = y
        else: return False
    return True
def transitive(n, L):
    seen = {0}; fr = [0]
    while fr:
        nf = [p[s] for s in fr for p in L if p[s] not in seen]
        for t in nf: seen.add(t)
        fr = [t for t in set(nf)]
    return len(seen) == n
def a_reps(n):
    # permutations of {0..n-1} up to relabeling of {1..n-1}: cycle type with 0's cycle first
    out = []
    def parts(m, mx):
        if m == 0: yield []; return
        for k in range(min(m, mx), 0, -1):
            for r in parts(m - k, k): yield [k] + r
    for L0 in range(1, n + 1):
        for rest in parts(n - L0, n):
            p = list(range(n)); pts = list(range(n)); pos = 0
            for L in [L0] + rest:
                cyc = pts[pos:pos + L]; pos += L
                for i in range(L): p[cyc[i]] = cyc[(i + 1) % L]
            out.append(tuple(p))
    return out
def determines(n, sa, sb):
    seen = set([(0, 0)]); fr = [(0, 0)]; byq = {}
    pa, pb = P['a'], P['b']
    while fr:
        nf = []
        for q, h in fr:
            for s, Px in ((sa, pa), (sb, pb)):
                t = (s[q], Px[h])
                if t not in seen:
                    pt = partner[t[1]]
                    if pt is not None and (t[0], pt) in seen: return False
                    seen.add(t); nf.append(t)
        fr = nf
    return True
t0 = time.time()
for n in range(2, NMAX + 1):
    tot = good = hits = 0
    for sa in a_reps(n):
        for sb in itertools.permutations(range(n)):
            tot += 1
            L = [sa, sb]
            if not transitive(n, L): continue
            if not aperiodic_avoid(n, L): continue
            good += 1
            if determines(n, sa, sb):
                hits += 1
                if hits <= 5: print("  HIT n", n, "a", sa, "b", sb, flush=True)
    print("n", n, "pairs", tot, "good", good, "hits", hits, flush=True)
