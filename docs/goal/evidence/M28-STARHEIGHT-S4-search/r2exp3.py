import r2obs as R, r2, itertools, sys
classes = [R.user_class(nm) for nm in R.FIVE]
G = R.good_automata(int(sys.argv[1]))
V4 = R.V4
res = {}
best = None
for gi, d in enumerate(G):
    n = len(d)
    for r in range(n):
        for X in [(0,), (1,), (2,), (0, 1), (0, 2), (1, 2), (0, 1, 2)]:
            for ci, t in enumerate(classes):
                a = R.ambiguity2([R.offbase_counter(d, r, X)], t)
                if a != V4:
                    res.setdefault(ci, []).append((d, r, X, len(a)))
for ci in range(5):
    print(R.FIVE[ci], "hits:", len(res.get(ci, [])), res.get(ci, [])[:3])
