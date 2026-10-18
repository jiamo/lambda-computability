import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "..")
import data as D

def lst(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"

def wrap(prefix, items, indent="    ", width=99):
    text = prefix + ", ".join(items) + "]"
    toks = text.split(", ")
    lines = []
    cur = ""
    for j, tk in enumerate(toks):
        piece = tk + ("," if j < len(toks) - 1 else "")
        cand = (cur + " " + piece) if cur else piece
        if len(cand) > width and cur:
            lines.append(cur)
            cur = indent + piece
        else:
            cur = cand
    lines.append(cur)
    return "\n".join(lines)

def tstr(L):
    return " ".join("".join(str(v) for v in r) for r in L)

repl_items = []
for name, L in D.REPS:
    if name.startswith("K"):
        repl_items.append(f"{name}.L")
    else:
        repl_items.append(lst([lst(r) for r in L]))
repL = wrap("def repL : List (List (List ℕ)) := [", repl_items)

cjL = wrap("def cjL : List (List ℕ) := [", [lst(r) for r in D.CJ])
w1L = wrap("def w1L : List ℕ := [", [str(x) for x in D.w1])
W2rows = [lst(D.w2[r]) if r in D.w2 else "[]" for r in range(24)]
W2 = wrap("def w2L : List (List ℕ) := [", W2rows)
CH = [D.P3[i:i + 5] for i in range(0, len(D.P3), 5)]
NCH = len(CH)
p3parts = []
for j, ch in enumerate(CH):
    p3parts.append(f"/-- Pairs of `P3`, part {j}. -/\n" + wrap(f"def P3_{j} : List (Fin 24 × Fin 24) := [", [f"({a}, {b})" for a, b in ch]))
p3parts.append("/-- The pairs of letters that remain after stage 2. -/\ndef P3 : List (Fin 24 × Fin 24) :=\n  " + " ++ ".join(f"P3_{j}" for j in range(NCH)))
P3 = "\n\n".join(p3parts)
chk = []
for j in range(NCH):
    chk.append(f"lemma stage3_check_{j} : ∀ pr ∈ P3_{j}, ∀ c : Fin 24, fin3 pr.1 pr.2 c (w3 pr c) = true := by\n  decide +kernel")
chk.append("lemma stage3_check : ∀ pr ∈ P3, ∀ c : Fin 24, fin3 pr.1 pr.2 c (w3 pr c) = true := by\n  intro pr hpr\n  simp only [P3, List.mem_append, or_assoc] at hpr\n  rcases hpr with " + " | ".join("h" + str(j) for j in range(NCH)) + "\n" + "\n".join(f"  · exact stage3_check_{j} pr h{j}" for j in range(NCH)))
STAGE3 = "\n\n".join(chk)
W3 = wrap("def w3L : List (List ℕ) := [", [lst(r) for r in D.W3])

cases = []
for k, (name, L) in enumerate(D.REPS):
    if name.startswith("K"):
        cases.append(f"  · exact fun T hT => {name}.height_one T hT")
    elif name == "S4Cox":
        cases.append("""  · intro T hT
    have hTc : T = S4Cox.coxT := FreeMonoid.hom_eq fun x => Equiv.ext fun i => by
      rw [hT, S4Cox.coxT, FreeMonoid.lift_eval_of]
      revert x i
      decide
    subst hTc
    exact S4Cox.height_one_S4_coxeter""")
    else:
        n = name.split(".")[1]
        cases.append(f"""  · intro T hT
    have hTc : T = {n}.T := FreeMonoid.hom_eq fun x => Equiv.ext fun i => by
      rw [hT, {n}.T_of]
      revert x i
      decide
    subst hTc
    exact {n}.height_one""")

cls_doc = []
for k, (name, L) in enumerate(D.REPS):
    nm = name if name.startswith("K") else name.replace("S4Three.", "")
    if name == "S4Cox":
        nm = "S4Cox.coxT"
    cls_doc.append(f"`{k}`: `{tstr(L)}` ({nm})")

tmpl = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'glue_template.lean')).read()
out = (tmpl.replace("@REPL@", repL).replace("@CJL@", cjL).replace("@W1L@", w1L)
       .replace("@W2L@", W2).replace("@P3@", P3).replace("@W3L@", W3)
       .replace("@STAGE3@", STAGE3).replace("@CASES@", "\n".join(cases)))
open(os.path.join(ROOT, 'Start', 'StarHeightS4ThreeLetters.lean'), 'w').write(out)
print("\n".join(cls_doc))
