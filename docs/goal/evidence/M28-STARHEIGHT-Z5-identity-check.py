#!/usr/bin/env python3
"""Exhaustive check of the Z_p identity of M28-STARHEIGHT-Z5-CORE (letter 0 is the counted letter x, rot[0] = 1)."""
import itertools, random
def check(p, rot, L):
    nl=len(rot); phi=lambda t: (-t)%p
    for n in range(0,L+1):
        for u in itertools.product(range(nl), repeat=n):
            st=[0]
            for a in u: st.append((st[-1]+rot[a])%p)
            N0=sum(1 for i,a in enumerate(u) if a==0 and st[i]==0)
            lhs = p*N0 + sum(phi(st[i+1]) for i in range(n-1) if u[i]!=0 and u[i+1]==0)
            rhs = u.count(0) + sum(phi(st[i+1]) for i in range(n-1) if u[i]==0 and u[i+1]!=0) + (phi(st[n]) if n and u[-1]==0 else 0)
            assert lhs==rhs, (u,lhs,rhs)
    print('ok',p,rot,L)
check(5,[1,1,2,3,4],7); check(3,[1,2,0],8); check(7,[1,3,0,6],7); check(5,[1,0],10)
