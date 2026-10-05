# M24-ABSTRACT-LOB — Löb's theorem and the second incompleteness theorem, abstractly

**Status:** DONE_STRONG

## Terminal statements (`Start/AbstractLob.lean`)

```lean
structure Lambda.Lob.ProvabilitySystem   -- sentences, →, ⊥, □, theorems; K, S, MP; D1–D3; diagonal lemma
theorem Lambda.Lob.ProvabilitySystem.lob {B} (h : T.Thm (T.imp (T.box B) B)) : T.Thm B
theorem Lambda.Lob.ProvabilitySystem.lob_internal (B) :
    T.Thm (T.imp (T.box (T.imp (T.box B) B)) (T.box B))
theorem Lambda.Lob.ProvabilitySystem.not_thm_con (hT : T.Consistent) : ¬ T.Thm T.con
theorem Lambda.Lob.ProvabilitySystem.not_thm_reflection {A} (hA : ¬ T.Thm A) :
    ¬ T.Thm (T.imp (T.box A) A)
theorem Lambda.Lob.ProvabilitySystem.trueBox_consistent : trueBox.Consistent
```

`T.con` is `□⊥ → ⊥`.  All results depend on no axioms beyond Lean's core.

## Hypotheses

* the theorems contain the Hilbert axioms `K` and `S` and are closed under modus ponens (this is
  all the propositional logic the argument needs);
* `D1` (`⊢ A ⟹ ⊢ □A`), `D2` (`⊢ □(A → B) → (□A → □B)`), `D3` (`⊢ □A → □□A`);
* the diagonal lemma for the formulas `□X → B`: for each `B` a sentence `L` with `⊢ L → (□L → B)`
  and `⊢ (□L → B) → L`.

`Lambda.Lob.ProvabilitySystem.trueBox` (sentences are propositions, `□A` is `True`) satisfies all
of them and is consistent, so the hypotheses are not contradictory and the results are not
vacuous.

## What this does not do

It exhibits no theory of arithmetic satisfying the hypotheses; that is `M24-GODEL2-ARITH`, which
needs `M24-ARITH-THEORY` first.

## Gates

```
lake build
python3 scripts/check_sorry.py
python3 scripts/check_closure.py
python3 scripts/goal_state.py validate
scripts/pack_gate.sh HEAD
```
