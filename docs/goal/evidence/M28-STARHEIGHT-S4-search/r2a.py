import r2, itertools, sys
cl=r2.dt_classes()
V4=frozenset(r2.V4)
for n in range(2,6):
    L=r2.letter_cycles(n)
    bad=0; tot=0
    for trip in itertools.product(L,repeat=3):
        tot+=1
        for t in cl:
            if r2.W_of([trip],t)!=V4:
                bad+=1; print("BAD",n,trip,t); break
    print(n,len(L),tot,"bad",bad, flush=True)
