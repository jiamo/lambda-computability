# M9-DINF-HNF

**Status:** DONE_STRONG

`Start/ScottDinfModel.lean` interprets the untyped calculus in Scott's inverse limit `D∞` and
proves the interpretation sound for βη.  Soundness leaves open which terms denote the least
element `⊥`.  This task settles one half of the question, the one that does not need a
computability relation on the tower: every head normalizable term is *somewhere* different from
`⊥`.

## Bottom and abstraction — `Start/DinfHnf.lean`

* `ScottDinf.Phi_botDinf` — `⊥` denotes the everywhere-`⊥` function.  It follows from the
  adjunction `ScottDinf.Phi_le_iff` of the isomorphism `Φ ⊣ Ψ`.
* `ScottDinf.exists_ne_botDinf` — `D∞` has an element other than `⊥` (the image of `true` from
  the base of the tower).
* `ScottDinf.dlamAny_ne_botDinf` — an abstraction is nonbottom as soon as its body is nonbottom
  at some argument.

## Head normal forms are nonbottom

* `ScottDinf.constEnv` — the constant environment, stable under `ScottDinf.dcons` of its own
  value, which is what lets one environment serve the whole abstraction prefix.
* **`ScottDinf.exists_const_env_ddenot_neutral`** — a neutral term `y M₁ … Mₘ` takes *any*
  prescribed value in a suitable constant environment: interpret its head as the element
  `λ_ … λ_. z` that discards `m` arguments.
* **`ScottDinf.exists_ddenot_ne_botDinf_of_isHnf`** — hence a head normal form is nonbottom in a
  suitable environment, the abstraction prefix being handled by `dlamAny_ne_botDinf`;
* **`ScottDinf.exists_ddenot_ne_botDinf_of_hasHnf`** — and so is a head normalizable term, by
  soundness (`ScottDinf.ddenot_reduces`).

## Contrapositives

* `ScottDinf.not_hasHnf_of_ddenot_eq_botDinf` — a term that denotes `⊥` in every environment has
  no head normal form;
* `ScottDinf.exists_ddenot_ne_botDinf_of_solvable`, `ScottDinf.not_solvable_of_ddenot_eq_botDinf`
  — the same for solvability, through `Lambda.hasHnf_of_solvable`.

## Boundary

This is the *converse* half of adequacy.  Adequacy proper for `D∞` — a nonbottom denotation
forces a head normal form — needs a computability relation on the finite stages of the tower and
remains open; it is tracked by `M9-DINF-ADEQUACY`.

## Gates

* `python3 scripts/goal_state.py validate`
* `lake build` — clean, no `sorry`, axioms `propext, Classical.choice, Quot.sound`.
