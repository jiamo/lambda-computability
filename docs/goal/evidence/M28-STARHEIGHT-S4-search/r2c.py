import r2, itertools, sys, random
random.seed(int(sys.argv[1]))
cl=r2.dt_classes()
V4=frozenset(r2.V4)
LC={n:r2.letter_cycles(n) for n in range(2,8)}
def rand_aut(n):
    return tuple(random.choice(LC[n]) for _ in range(3))
cnt=0; found=0
import time
t0=time.time()
while time.time()-t0 < float(sys.argv[2]):
    m=random.choice([2,2,3])
    auts=[rand_aut(random.randint(2,7)) for _ in range(m)]
    t=random.choice(cl)
    W=r2.W_of(auts,t)
    cnt+=1
    if W!=V4:
        found+=1
        print("FOUND",auts,t,len(W),flush=True)
print("tested",cnt,"found",found,flush=True)
