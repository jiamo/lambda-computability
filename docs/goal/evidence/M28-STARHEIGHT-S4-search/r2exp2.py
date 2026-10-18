import r2obs as R, r2, sys, itertools, random
which = sys.argv[1]
classes = [R.user_class(nm) for nm in R.FIVE]
G = R.good_automata(int(sys.argv[2]))
Z = R.zlangs()
V4 = R.V4
tested = 0; hits = []
if which == "single":
    for d in G:
        for t in classes:
            a = R.ambiguity2([R.perm_obs(d)], t); tested += 1
            if a != V4: hits.append(("single", d, t, len(a)))
elif which == "transfer":
    for d in G:
        for zn, zd in Z:
            o = R.transfer_obs(d, zd, zn)
            for t in classes:
                a = R.ambiguity2([o], t); tested += 1
                if a != V4: hits.append(("transfer", d, zn, t, len(a)))
elif which == "marker":
    for d in G:
        for m in range(3):
            o = R.marker_obs(d, m)
            for t in classes:
                a = R.ambiguity2([o], t); tested += 1
                if a != V4: hits.append(("marker", d, m, t, len(a)))
elif which == "rev":
    # one forward and one reversed good automaton
    for d1 in G:
        for d2 in G:
            for t in classes:
                a = R.ambiguity2([R.perm_obs(d1), R.rev_perm_obs(d2)], t); tested += 1
                if a != V4: hits.append(("fwd+rev", d1, d2, t, len(a)))
elif which == "transfer2":
    random.seed(int(sys.argv[3]))
    for _ in range(int(sys.argv[4])):
        d1, d2 = random.choice(G), random.choice(G)
        (z1, zd1), (z2, zd2) = random.choice(Z), random.choice(Z)
        t = random.choice(classes)
        a = R.ambiguity2([R.transfer_obs(d1, zd1), R.transfer_obs(d2, zd2)], t); tested += 1
        if a != V4: hits.append(("transfer2", d1, z1, d2, z2, t, len(a)))
elif which == "markerpair":
    random.seed(int(sys.argv[3]))
    for _ in range(int(sys.argv[4])):
        d1, d2 = random.choice(G), random.choice(G)
        t = random.choice(classes)
        obs = [R.marker_obs(d1, random.randrange(3)), random.choice([R.perm_obs(d2), R.marker_obs(d2, random.randrange(3)), R.rev_perm_obs(d2)])]
        a = R.ambiguity2(obs, t); tested += 1
        if a != V4: hits.append(("markerpair", d1, d2, t, len(a)))
print(which, sys.argv[2:], "tested", tested, "hits", len(hits))
for h in hits[:10]: print(h)
