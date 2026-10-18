import r2obs as R, r2, itertools, time, sys
cls = r2.dt_classes()
t0 = cls[0]
G = R.good_automata(4)
print("good automata n<=4:", len(G), flush=True)
from collections import Counter
print(Counter(len(d) for d in G))
