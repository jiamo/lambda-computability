# Check the regular expressions for the candidate language of the smallest
# double-transposition class: a = (23), b = (12), c = (01)(23) acting on {0,1,2,3}.
# State q goes to T(x)(q) on letter x; L_fix_q = {w | the run from q returns to q}.
import re, random
P = {'a': (0, 1, 3, 2), 'b': (0, 2, 1, 3), 'c': (1, 0, 3, 2)}
def run(q, w):
    for x in w:
        q = P[x][q]
    return q
RX = {
    0: r"(a|b|c(a|b((a|c)b*(a|c))*b)*c)*",
    1: r"(a|c(a|b)*c|b((a|c)b*(a|c))*b)*",
    2: r"((a|c)b*(a|c)|b(a|c(a|b)*c)*b)*",
}
random.seed(1)
bad = 0
for _ in range(200000):
    w = ''.join(random.choice('abc') for _ in range(random.randint(0, 14)))
    for q, rx in RX.items():
        if (re.fullmatch(rx, w) is not None) != (run(q, w) == q):
            bad += 1
    ident = all(run(q, w) == q for q in range(4))
    fix012 = all(re.fullmatch(RX[q], w) is not None for q in range(3))
    if ident != fix012:
        bad += 1
print("mismatches", bad)
