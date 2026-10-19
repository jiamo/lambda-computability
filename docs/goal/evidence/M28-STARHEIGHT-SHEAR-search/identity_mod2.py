#!/usr/bin/env python3
"""Check (random words, not a proof; the Lean file proves it): modulo 2, for q = (q1, q2),
   shcount q u = scount acab + (q2 + 1) scount ab + q1 scount acb + (q1 + 1)(q2 + 1) |u|_b.
So at p = 2 the shear count and scount acab (= abac with b and c swapped) are good together."""
import random


def scount(w, u):
    dp = [1] + [0] * len(w)
    for x in u:
        for j in range(len(w), 0, -1):
            if w[j - 1] == x:
                dp[j] += dp[j - 1]
    return dp[len(w)]


def shcount(q, u):
    A = S = 0
    k = 0
    for x in u:
        if x == 'b' and (A % 2, S % 2) == q:
            k += 1
        if x == 'a':
            A += 1
        elif x == 'c':
            S += A
    return k


random.seed(1)
bad = 0
for trial in range(20000):
    u = ''.join(random.choice('abc') for _ in range(random.randint(0, 16)))
    for q in [(0, 0), (0, 1), (1, 0), (1, 1)]:
        rhs = (scount('acab', u) + (q[1] + 1) * scount('ab', u) + q[0] * scount('acb', u)
               + (q[0] + 1) * (q[1] + 1) * u.count('b'))
        if (shcount(q, u) - rhs) % 2:
            bad += 1
print("words checked: 20000 x 4 states, failures:", bad)
