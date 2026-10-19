# R3 (b)(i): the two-letter Z4 x Z2 core (a = (1,0), b = (0,1)) modulo 2 and the good terms.
# Pure Python 3.  Functions on all words over {a,b} of length <= N are F2-vectors (Python ints).
# Good span (every term has height <= 1 modulo 2 in Lean):
#   Z4 counts   z(ra,rb,g,x) = #{i : u_i = x, ra*A_i + rb*B_i = g mod 4}   (128 functions);
#   counter bits [A mod 4 = s, B mod 8 = t] of the whole word                (32 functions);
#   products of a counter bit with a Z4 count                                (4096 functions).
# Targets: the 16 counts c(x, (s,t)) = #{i : u_i = x, A_i = s mod 4, B_i = t mod 2}.
import itertools, sys

def run(N):
    words = []
    def dfs(u, A, B, z4, c16):
        words.append((A, B, z4, c16))
        if len(u) == N: return
        for x in (0, 1):
            nz = list(z4); nc = list(c16)
            for ra in range(4):
                for rb in range(4):
                    g = (ra * A + rb * B) % 4
                    k = ((ra * 4 + rb) * 4 + g) * 2 + x
                    nz[k] ^= 1
            nc[(x * 4 + A % 4) * 2 + B % 2] ^= 1
            dfs(u + [x], A + (x == 0), B + (x == 1), nz, nc)
    dfs([], 0, 0, [0] * 128, [0] * 16)
    W = len(words)
    def vec(f):
        v = 0
        for i, w in enumerate(words):
            if f(w): v |= 1 << i
        return v
    z4v = [vec(lambda w, k=k: w[2][k]) for k in range(128)]
    ctr = [vec(lambda w, s=s, t=t: w[0] % 4 == s and w[1] % 8 == t) for s in range(4) for t in range(8)]
    good = z4v + ctr + [c & z for c in ctr for z in z4v]
    basis = {}
    def red(v):
        while v:
            h = v.bit_length() - 1
            if h in basis: v ^= basis[h]
            else: return v
        return 0
    for v in good:
        v = red(v)
        if v: basis[v.bit_length() - 1] = v
    names = [("ab"[x], (s, t)) for x in (0, 1) for s in range(4) for t in range(2)]
    tv = [vec(lambda w, k=k: w[3][k]) for k in range(16)]
    return W, len(basis), names, tv, red

def quotient_dim(tv, red):
    # rank of (good + counts) minus rank of good
    extra = {}
    def red2(v):
        while v:
            v = red(v)
            if not v: return 0
            h = v.bit_length() - 1
            if h in extra: v ^= extra[h]
            else: return v
        return 0
    for v in tv:
        v = red2(v)
        if v: extra[v.bit_length() - 1] = v
    return len(extra)

if __name__ == "__main__":
    for N in (int(a) for a in sys.argv[1:] or ["12", "14"]):
        W, rk, names, tv, red = run(N)
        res = [red(v) for v in tv]
        print("N =", N, "; words", W, "; rank of good span", rk)
        print("  counts that are good modulo 2:", [names[i] for i in range(16) if res[i] == 0])
        print("  dimension of (counts + good) / good:", quotient_dim(tv, red))
        # express every count over the basis {c(b,(0,1)), c(a,(0,0))} when possible
        sel = [names.index(("b", (0, 1))), names.index(("a", (0, 0)))]
        span = {0: frozenset()}
        for i in sel:
            span.update({k ^ res[i]: v ^ {i} for k, v in list(span.items())})
        for i in range(16):
            m = res[i]
            hit = [frozenset(v) for k, v in span.items() if red(k ^ m) == 0]
            print("  ", names[i], "= good +", sorted(names[j] for j in hit[0]) if hit else "NOT in span")
        for pair in [((2, 1), (3, 1)), ((0, 1), (1, 1)), ((0, 1), (2, 1))]:
            v = tv[names.index(("b", pair[0]))] ^ tv[names.index(("b", pair[1]))]
            print("  b-sum", pair, "good modulo 2:", red(v) == 0)
