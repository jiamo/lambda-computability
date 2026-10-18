import itertools, sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import s4three as S
P=S.S4; IDX=S.IDX; E=S.E
V4=[p for p in P if p==E or S.is_dbl(p)]

def letter_cycles(n):
    """permutations of range(n) that are a single cycle through 0, or identity"""
    res=[tuple(range(n))]
    others=list(range(1,n))
    for k in range(1,n):
        for seq in itertools.permutations(others,k):
            cyc=(0,)+seq
            p=list(range(n))
            for i in range(len(cyc)):
                p[cyc[i]]=cyc[(i+1)%len(cyc)]
            res.append(tuple(p))
    return res

def W_of(auts, t):
    # auts: list of (letters as perms of range(n)) ; state update q -> perm[q] (any fixed convention)
    # t: Lean letters; s -> s * t[x]
    start=(tuple(0 for _ in auts), E)
    seen={start}; todo=[start]
    while todo:
        qs,s=todo.pop()
        for x in range(3):
            q2=tuple(a[x][q] for a,q in zip(auts,qs))
            s2=S.mul(s,t[x])
            st=(q2,s2)
            if st not in seen:
                seen.add(st); todo.append(st)
    z=tuple(0 for _ in auts)
    return frozenset(s for (qs,s) in seen if qs==z and s in V4)

def dt_classes():
    res=[]
    seen=set()
    for t in itertools.product(P,repeat=3):
        if len(set(t))<3 or E in t: continue
        if not any(S.is_dbl(x) for x in t): continue
        if S.gen(list(t))!=S.FULL: continue
        if t in seen: continue
        orb=set()
        for perm in itertools.permutations(range(3)):
            for g in P:
                orb.add(tuple(S.conj(g,t[perm[i]]) for i in range(3)))
        seen|=orb
        res.append(min(orb))
    return res
