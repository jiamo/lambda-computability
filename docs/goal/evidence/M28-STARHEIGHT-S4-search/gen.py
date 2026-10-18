import sys, json, itertools
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import s4three as S

def embed(d):
    n = len(d)
    rows = [list(r) for r in d]
    for q in range(n, 4):
        rows.append([q, q, q])
    return rows

def ret_mon4(rows):
    return S.ret_monoid(rows, 0)

def class_data(t):
    cost, fam = S.best_family(t)
    auts = []
    for H, d, N, m in fam:
        rows = embed(d)
        mon = ret_mon4(rows)
        N4 = S.aper_index(mon)
        auts.append((rows, N4, len(mon)))
    # R by BFS
    start = (tuple(0 for _ in auts), (0, 1, 2, 3))
    R = [start]; seen = {start}; i = 0
    while i < len(R):
        o, p = R[i]
        for x in range(3):
            o2 = tuple(auts[k][0][o[k]][x] for k in range(len(auts)))
            p2 = tuple(p[t[x][j]] for j in range(4))
            e = (o2, p2)
            if e not in seen:
                seen.add(e); R.append(e)
        i += 1
    fst = [o for o, p in R]
    assert len(set(fst)) == len(fst), "not functional"
    assert len(R) == 24
    return auts, R

def lst(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"

def lean_block(name, t, auts, R, doc):
    out = []
    out.append(f"/-! ### {doc} -/\n")
    out.append(f"namespace {name}\n")
    out.append("/-- The letters (row `x`: the images of `0, 1, 2, 3` under the letter `x`). -/")
    out.append(f"def L : List (List ℕ) := {lst([lst(r) for r in t])}\n")
    for k, (rows, N, m) in enumerate(auts):
        out.append(f"/-- Automaton `a{k}` (transformation monoid of its return automaton: {m} elements). -/")
        out.append(f"def a{k} : List (List ℕ) := {lst([lst(r) for r in rows])}\n")
        out.append(f"lemma a{k}_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a{k}) 0)")
        out.append(f"    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut (autT a{k}) 0) 400) {N} = true := by")
        out.append("  decide +kernel\n")
    out.append("/-- The joint states with the tables of the value. -/")
    ents = [f"({lst(o)}, {lst(p)})" for o, p in R]
    lines = []
    cur = "def R : List (List (Fin 4) × List (Fin 4)) := ["
    for j, e in enumerate(ents):
        piece = e + (", " if j < len(ents) - 1 else "]")
        if len(cur) + len(piece) > 98:
            lines.append(cur.rstrip())
            cur = "    " + piece
        else:
            cur += piece
    lines.append(cur)
    out.append("\n".join(lines) + "\n")
    names = ", ".join(f"a{k}" for k in range(len(auts)))
    out.append("/-- **Every language recognized by a morphism with these letters has height at most one.** -/")
    out.append("theorem height_one (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4))")
    out.append("    (hT : ∀ x i, T (FreeMonoid.of x) i = letT L x i) (F : Set (Equiv.Perm (Fin 4))) :")
    out.append("    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by")
    out.append(f"  refine height_one_of_tableOK L [{names}] R (by decide +kernel) ?_ T hT F")
    out.append("  intro t ht q")
    out.append("  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht")
    out.append("  rcases ht with " + " | ".join("rfl" for _ in auts))
    for k in range(len(auts)):
        out.append(f"  · exact good_baseN _ 0 _ a{k}_cert q")
    out.append(f"\nend {name}\n")
    return "\n".join(out)

def tstr(p):
    return "".join(str(x) for x in p)
