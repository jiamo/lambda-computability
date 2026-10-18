import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "..")
import data as D, gen as G

def tstr(L):
    return " ".join("".join(str(v) for v in r) for r in L)

HDR = '''import Start.StarHeightS4ThreeTable

/-!
# Certificates for classes of letter triples of `S₄` (part {part})

Classes of triples of letters of `S₄` (no double transposition, distinct letters, generating `S₄`)
for which the good coset automata of `S₄` separate `S₄` (`D = 1`).  Letters are written in Lean's
convention: the table `p0 p1 p2 p3` of a letter lists its images of `0, 1, 2, 3`.

For each class `Knn`: the letters `Knn.L`; two or three coset automata of `S₄` on at most four
states (embedded in `Fin 4`; unused states are fixed by every letter), with base state `0`; for
each, the certificate that its return automaton has an aperiodic transformation monoid
(`decide +kernel`); the list `Knn.R` of the `24` reachable joint states with the value of the
morphism; and `Knn.height_one`, an instance of `height_one_of_tableOK`.

{lst}
-/

-- The certificates below are checked one at a time, which keeps the peak memory low.
set_option Elab.async false

namespace GeneralizedStarHeight

namespace S4Three

open S4Two

'''
FTR = '''end S4Three

end GeneralizedStarHeight
'''
parts = {"A": range(0, 9), "B": range(9, 18), "C": range(18, 27), "D": range(27, 36), "E": range(36, 45)}
for part, rng in parts.items():
    lines = []
    body = []
    for i in rng:
        name, L = D.REPS[i]
        t = tuple(tuple(r) for r in L)
        auts, R = G.class_data(t)
        sizes = []
        for rows, N, m in auts:
            n = 4 - sum(1 for q in range(4) if rows[q] == [q, q, q] and q > 0)
            sizes.append(str(n))
        lines.append(f"* `{name}`: `{tstr(L)}` (automata on {', '.join(sizes)} states)")
        body.append(G.lean_block(name, t, auts, R, f"`{name}`: letters `{tstr(L)}`"))
    s = HDR.replace("{part}", part).replace("{lst}", "\n".join(lines)) + "\n".join(body) + FTR
    open(os.path.join(ROOT, "Start", f"StarHeightS4ThreeCerts{part}.lean"), "w").write(s)
print("ok")
