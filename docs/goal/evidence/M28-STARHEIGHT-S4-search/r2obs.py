"""Observer experiments for the double-transposition classes (R2 (b))."""
import itertools, sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import s4three as S
import r2

P = S.S4
E = S.E
V4 = frozenset(r2.V4)
KLEIN = {p: frozenset(S.mul(p, v) for v in V4) for p in P}  # coset p V4


def good_automata(nmax):
    """letter-cycle permutation automata on 2..nmax states with aperiodic return monoid
    (delta[q][x]), connected from 0."""
    res = []
    for n in range(2, nmax + 1):
        L = r2.letter_cycles(n)
        for trip in itertools.product(L, repeat=3):
            delta = [[trip[x][q] for x in range(3)] for q in range(n)]
            # connected
            seen = {0}; todo = [0]
            while todo:
                q = todo.pop()
                for x in range(3):
                    r = delta[q][x]
                    if r not in seen:
                        seen.add(r); todo.append(r)
            if len(seen) != n:
                continue
            mon = S.ret_monoid(delta, 0)
            if mon is None or S.aper_index(mon) is None:
                continue
            res.append(delta)
    return res


class Obs:
    """deterministic observer: start state, step(state, x) -> state (hashable)."""
    def __init__(self, name, start, step):
        self.name, self.start, self.step = name, start, step


def perm_obs(delta, name="A"):
    return Obs(name, 0, lambda q, x: delta[q][x])


def transfer_obs(delta, zdfa, name="Tr"):
    """Transfer counter: blocks = first returns of delta to 0; zdfa = (start, step, accept) a DFA
    on letters deciding membership of a block in Z; parity of completed blocks in Z."""
    zs, zstep, zacc = zdfa
    def step(st, x):
        q, z, par = st
        q2 = delta[q][x]
        z2 = zstep(z, x)
        if q2 == 0:
            return (0, zs, par ^ (1 if zacc(z2) else 0))
        return (q2, z2, par)
    return Obs(name, (0, zs, 0), step)


def marker_obs(delta, m, name="Mk"):
    """state of delta started after the first occurrence of the letter m."""
    def step(st, x):
        seen, q = st
        if not seen:
            return (1, 0) if x == m else (0, 0)
        return (1, delta[q][x])
    return Obs(name, (0, 0), step)


def ambiguity(obs, t, cap=2000000):
    """set of d in V4 with words u, v: same observations, same T mod V4, T(u) = d T(v);
    observers act on the left-to-right reading; T multiplies on the right."""
    start = (tuple(o.start for o in obs), E)
    seen = {start}; todo = [start]
    while todo:
        os_, s = todo.pop()
        for x in range(3):
            o2 = tuple(o.step(q, x) for o, q in zip(obs, os_))
            st = (o2, S.mul(s, t[x]))
            if st not in seen:
                seen.add(st); todo.append(st)
                if len(seen) > cap:
                    return None
    by = {}
    for os_, s in seen:
        by.setdefault(os_, set()).add(s)
    amb = set()
    for os_, ss in by.items():
        for s in ss:
            for s2 in ss:
                d = S.mul(s, S.inv(s2))
                if d in V4:
                    amb.add(d)
    return frozenset(amb)


def rev_perm_obs(delta, name="Rev"):
    """reads the word right to left; tracked left to right as the composed map, output = image of 0."""
    n = len(delta)
    beta = [tuple(delta[q][x] for q in range(n)) for x in range(3)]
    def step(M, x):
        # M_{wx} = M_w o beta_x
        return tuple(M[beta[x][q]] for q in range(n))
    o = Obs(name, tuple(range(n)), step)
    o.out = lambda M: M[0]
    return o


def ambiguity2(obs, t, cap=3000000):
    start = (tuple(o.start for o in obs), E)
    seen = {start}; todo = [start]
    while todo:
        os_, s = todo.pop()
        for x in range(3):
            o2 = tuple(o.step(q, x) for o, q in zip(obs, os_))
            st = (o2, S.mul(s, t[x]))
            if st not in seen:
                seen.add(st); todo.append(st)
                if len(seen) > cap:
                    return None
    by = {}
    for os_, s in seen:
        key = tuple(getattr(o, 'out', lambda q: q)(q) for o, q in zip(obs, os_))
        by.setdefault(key, set()).add(s)
    amb = set()
    for ss in by.values():
        for s in ss:
            for s2 in ss:
                d = S.mul(s, S.inv(s2))
                if d in V4:
                    amb.add(d)
    return frozenset(amb)


def user_class(names):
    """Lean-convention letters from the right-action image tuples of the notes."""
    return tuple(S.inv(tuple(int(c) for c in nm)) for nm in names.split())


FIVE = ["0132 0213 1032", "0132 0213 2301", "0132 0231 1032", "0132 0231 2301",
        "0132 0231 3210"]


def zlangs():
    """simple star-free block languages, as DFAs (start, step, accept)."""
    Ls = []
    for x in range(3):
        Ls.append((f"starts{x}", (0, lambda z, y, x=x: (1 if y == x else 2) if z == 0 else z,
                                  lambda z: z == 1)))
        Ls.append((f"ends{x}", (0, lambda z, y, x=x: 1 if y == x else 0, lambda z: z == 1)))
        Ls.append((f"contains{x}", (0, lambda z, y, x=x: 1 if (z == 1 or y == x) else 0,
                                    lambda z: z == 1)))
        Ls.append((f"avoids{x}", (0, lambda z, y, x=x: 1 if (z == 1 or y == x) else 0,
                                  lambda z: z == 0)))
    Ls.append(("len1", (0, lambda z, y: min(z + 1, 2), lambda z: z == 1)))
    Ls.append(("len2", (0, lambda z, y: min(z + 1, 3), lambda z: z == 2)))
    Ls.append(("len>=3", (0, lambda z, y: min(z + 1, 3), lambda z: z == 3)))
    for x in range(3):
        for y in range(3):
            # contains factor xy: states 0 none, 1 last letter x, 2 found
            Ls.append((f"factor{x}{y}", (0, lambda z, c, x=x, y=y: 2 if z == 2 else
                                         (2 if (z == 1 and c == y) else (1 if c == x else 0)),
                                         lambda z: z == 2)))
    return Ls


def offbase_counter(delta, r, X, name="Off"):
    """automaton delta (good at base 0) started at state r; parity of letters of X read while the
    automaton is at state 0."""
    def step(st, x):
        q, par = st
        return (delta[q][x], par ^ (1 if (q == 0 and x in X) else 0))
    return Obs(name, (r, 0), step)


def rev_counter(delta, r, X, name="RevOff"):
    """offbase_counter read from right to left: tracked as the composed map of the augmented
    automaton, output = image of the start (r, 0)."""
    n = len(delta)
    states = [(q, e) for q in range(n) for e in range(2)]
    idx = {s: i for i, s in enumerate(states)}
    def alpha(x, s):
        q, e = s
        return (delta[q][x], e ^ (1 if (q == 0 and x in X) else 0))
    A = [tuple(idx[alpha(x, s)] for s in states) for x in range(3)]
    def step(M, x):
        return tuple(M[A[x][i]] for i in range(len(states)))
    o = Obs(name, tuple(range(len(states))), step)
    st = idx[(r, 0)]
    o.out = lambda M: M[st]
    return o
