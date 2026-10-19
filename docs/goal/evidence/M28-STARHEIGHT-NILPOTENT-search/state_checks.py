#!/usr/bin/env python3
"""R3 (b), (c): two state-level checks (exploration, not Lean-verified).

(b) Heisenberg form of scount abac.  With the state (A, C, S) = (|.|_a, |.|_c, scount [a,c]) of
the prefix before each position (the Heisenberg group H(Z/p): a adds (1,0,0), c adds (0,1,A)),
    scount [a,b,a,c] u = sum over the b's of A_t * (S - S_t - A_t * (C - C_t)),
with S, C the totals of u.  So modulo p, scount abac is a combination, with coefficients depending
on (C, S) mod p, of the counts of b read in each state of the H(Z/p) counter.  Checked on all
words of length <= 9 over {a,b,c} and on random long words.

(c) p = 2, content (2,2).  scount aabb mod 2 = sum over the b's of C(A_t, 2) * (#b after t), i.e.
the count of the moving letter b in the states (A mod 4, B mod 2) of Z/4 x Z/2.  Every
homomorphism Z/4 x Z/2 -> Z/4 is, up to sign, (A, B) -> A, (A, B) -> A + 2B, or lands in 2Z/4.
Let N(A, B) be the number of b's read in state (A, B).  The cyclic-quotient counts (the Z4 cores
for (A) and (A + 2B) -- the latter has a letter of displacement 1 and a counted letter of
displacement 2, the open Z4CoreRot2 configuration -- and the (Z/2)^2 counts) span a space of
rank 6 in F_2^8; the needed N(2, B) + N(3, B) is outside it (rank 7).
"""
import itertools
import random


def scount(w, u):
    dp = [1] + [0] * len(w)
    for ch in u:
        for i in range(len(w), 0, -1):
            if w[i - 1] == ch:
                dp[i] += dp[i - 1]
    return dp[len(w)]


def heis(u):
    A = C = S = 0
    states = []
    for ch in u:
        states.append((ch, A, C, S))
        if ch == 'a':
            A += 1
        elif ch == 'c':
            C += 1
            S += A
    return sum(At * (S - St - At * (C - Ct)) for ch, At, Ct, St in states if ch == 'b')


def check_b():
    for L in range(10):
        for t in itertools.product('abc', repeat=L):
            u = ''.join(t)
            assert heis(u) == scount('abac', u), u
    rnd = random.Random(1)
    for _ in range(300):
        u = ''.join(rnd.choice('abcd') for _ in range(rnd.randint(50, 300)))
        assert heis(u) == scount('abac', u)
    print("(b) Heisenberg form of scount abac: OK")


def rank2(rows, n):
    rows = [r[:] for r in rows]
    rk = 0
    for c in range(n):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c]), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(len(rows)):
            if i != rk and rows[i][c]:
                rows[i] = [x ^ y for x, y in zip(rows[i], rows[rk])]
        rk += 1
    return rk


def check_c():
    idx = {s: i for i, s in enumerate(itertools.product(range(4), range(2)))}

    def vec(pairs):
        v = [0] * 8
        for pr in pairs:
            v[idx[pr]] ^= 1
        return v
    rows = []
    for s in range(4):
        rows.append(vec([(s, 0), (s, 1)]))            # state A = s
        rows.append(vec([(s, 0), ((s + 2) % 4, 1)]))  # state A + 2B = s
    for r in range(2):
        for b in range(2):
            rows.append(vec([(r, b), (r + 2, b)]))    # state (A mod 2, B) = (r, b)
    print("(c) rank of the cyclic-quotient counts:", rank2(rows, 8))
    for b in range(2):
        print(f"    with N(2,{b}) + N(3,{b}):", rank2(rows + [vec([(2, b), (3, b)])], 8))
    # sanity: scount aabb mod 2 from N
    rnd = random.Random(2)
    for _ in range(200):
        u = ''.join(rnd.choice('ab') for _ in range(rnd.randint(0, 60)))
        A = B = 0
        tot = u.count('b')
        val = 0
        for ch in u:
            if ch == 'b':
                val += (A * (A - 1) // 2) * (tot - B - 1)
                B += 1
            else:
                A += 1
        assert val % 2 == scount('aabb', u) % 2
    print("    scount aabb mod 2 as a state count: OK")


if __name__ == "__main__":
    check_b()
    check_c()
