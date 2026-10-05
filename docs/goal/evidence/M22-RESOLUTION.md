# M22-RESOLUTION — resolution refutations: soundness and refutational completeness

**Status:** DONE_STRONG (the proof-system criterion moved to `M22-RESOLUTION-PROOF-SYSTEM`)

## Terminal statements (`Start/Resolution.lean`)

```lean
def Complexity.Sat.resolvent (k : ℕ) (C D : Clause) : Clause
inductive Complexity.Sat.Deriv (F : Cnf) : Clause → Type   -- leaves in F, resolution steps
def Complexity.Sat.Deriv.size : Deriv F C → ℕ
theorem Complexity.Sat.Deriv.sound (hσ : cnfVal σ F = true) : Deriv F C → clauseVal σ C = true
theorem Complexity.Sat.unsat_of_refutation (d : Refutation F) : ∀ σ, cnfVal σ F = false
theorem Complexity.Sat.refutation_of_unsat (hF : ∀ σ, cnfVal σ F = false) :
    Nonempty (Refutation F)
theorem Complexity.Sat.refutation_iff_unsat (F : Cnf) :
    Nonempty (Refutation F) ↔ ∀ σ, cnfVal σ F = false
```

The CNFs, clauses, literals and their values are those of `Start/Sat.lean`.  `#print axioms
Complexity.Sat.refutation_iff_unsat` gives `propext, Classical.choice, Quot.sound`.

## The completeness proof

Davis–Putnam: for every list `V` containing the variables of `F`, by induction on `V`.

* `Complexity.Sat.restrict F k b` drops the clauses containing the literal `(b, k)` and removes
  `(!b, k)` from the others; restrictions of unsatisfiable CNFs are unsatisfiable
  (`Complexity.Sat.restrict_unsat`, via the assignment update `Complexity.Sat.upd`), and they
  avoid the variable `k` (`Complexity.Sat.avoids_restrict`).
* `Complexity.Sat.Deriv.lift`: a derivation of `C` from `F|k:=b` gives a derivation from `F` of a
  clause whose literals are in `C` or equal to `(!b, k)`.
* Refuting both restrictions and lifting gives derivations from `F` of a clause inside `{¬k}` and of
  a clause inside `{k}`; either one is already empty, or one resolution step on `k` gives the empty
  clause.

## What moved

The third exit criterion (resolution as a proof system in the sense of `M22-COOK-RECKHOW`) needs
the notion of a proof system, defined in that later row, and a Cobham term checking encoded
refutations.  It is now the row `M22-RESOLUTION-PROOF-SYSTEM`, depending on both.

## Gates

```
lake build
python3 scripts/check_sorry.py
python3 scripts/check_closure.py
python3 scripts/goal_state.py validate
scripts/pack_gate.sh HEAD
```
