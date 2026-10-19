#!/usr/bin/env python3
"""p = 2, q = (0, 0) (not Lean-verified): the centre of G, short words for the 16 elements of
order 8 (all with fourth power z), and a minimal set of mod-2 counters whose loops still have
image {1, z} in G (used by imtest8.c).  Usage: python3 minimal_counters.py"""
import itertools
from collections import deque
import counters
from schreier import image, target_group
from common import closure, mul, order
L3=(0,1,2)
tl,t0,val,e=target_group()
G=closure(tl,e)
Z=[g for g in G if all(mul(g,h)==mul(h,g) for h in G)]
print("center size",len(Z))
# short words for order-8 elements
rep={e:''}; dq=deque([e])
while dq:
    g=dq.popleft()
    for x in L3:
        h=mul(g,tl[x])
        if h not in rep: rep[h]=rep[g]+'abc'[x]; dq.append(h)
o8=[(rep[g],g) for g in G if order(g)==8]
z=(1, 0, 3, 2, 5, 4, 7, 6)
print(sorted(len(w) for w,g in o8), [w for w,g in o8][:16])
print("w^4 = z for all:", all(mul(mul(g,g),mul(g,g))==z for w,g in o8))
# minimal counter set with Im = <z>
W2=list(itertools.product(L3,repeat=2)); W3=list(itertools.product(L3,repeat=3))
comps=[counters.cnt(x,2) for x in L3]+[counters.sc(list(w),2) for w in W2+W3]
names=[c[2] for c in comps]
cur=list(range(len(comps)))
for i in list(cur):
    trial=[j for j in cur if j!=i]
    Im,n=image([(comps[j][0],comps[j][1]) for j in trial],tl,e)
    if len(Im)==2: cur=trial
Im,n=image([(comps[j][0],comps[j][1]) for j in cur],tl,e)
print("minimal counters:",[names[j] for j in cur],"orbit",n,"|Im|",len(Im))
