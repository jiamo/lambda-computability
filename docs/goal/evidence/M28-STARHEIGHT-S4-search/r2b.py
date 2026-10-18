import r2, itertools, sys, random
cl=r2.dt_classes()
V4=frozenset(r2.V4)
L3=[trip for n in (2,3) for trip in itertools.product(r2.letter_cycles(n),repeat=3)]
L4=list(itertools.product(r2.letter_cycles(4),repeat=3))
found=0
cnt=0
for A in L3:
    for B in L3:
        cnt+=1
        for t in cl:
            W=r2.W_of([A,B],t)
            if W!=V4:
                found+=1
                if found<=5: print("pair",A,B,t,len(W),flush=True)
                break
print("pairs",cnt,"found",found)
