# M22-COOK-RECKHOW — NP = coNP iff some proof system is polynomially bounded

**Status:** DONE_STRONG

## Terminal statements (`Start/CookReckhow.lean`)

```lean
def Complexity.Sat.UNSAT : Language := fun u => ¬ Sat.SAT u
def Complexity.IsProofSystem (f : Cob) : Prop := ∀ x, Sat.UNSAT x ↔ ∃ π, f.eval [π] = x
def Complexity.PolyBounded (f : Cob) : Prop :=
  ∃ p, PolyBound p ∧ ∀ x, Sat.UNSAT x → ∃ π, π.length ≤ p x.length ∧ f.eval [π] = x

theorem Complexity.inCoNP_UNSAT : InCoNP Sat.UNSAT
theorem Complexity.NP_eq_coNP_iff_inNP_UNSAT : (∀ L, InNP L ↔ InCoNP L) ↔ InNP Sat.UNSAT
theorem Complexity.inNP_UNSAT_of_polyBounded : IsProofSystem f → PolyBounded f → InNP Sat.UNSAT
theorem Complexity.polyBounded_of_inNP_UNSAT : InNP Sat.UNSAT → ∃ f, IsProofSystem f ∧ PolyBounded f
theorem Complexity.cook_reckhow :
    (∀ L, InNP L ↔ InCoNP L) ↔ ∃ f : Cob, IsProofSystem f ∧ PolyBounded f
```

`InCoNP` is that of `Start/PolyHierarchy.lean` (`M22-CONP-PH`); the CNF code and `SAT` are those
of `Start/Sat.lean`.

## Proof

* `UNSAT` is `coNP`-complete: every `NP` reduction to `SAT` (`npHard_SAT`) is a reduction of the
  complement to `UNSAT`, so `UNSAT ∈ NP` gives `NP = coNP` (`NP_eq_coNP_iff_inNP_UNSAT`).
* From a polynomially bounded proof system `f` with bound `p ≤ a (n+1)^k`: the verifier checks
  `f π = x` (`Cob.eqW`) and `|π| ≤ a (|x|+1)^k` (`Cob.leU` against the term `padT a k`).
* From an `NP` verifier `v` for `UNSAT`: the proof system `proofSystemOf v` reads a proof as a pair
  `⟨x, w⟩` (`fstTerm`, `sndTerm`) and outputs `x` if `v` accepts `w` for `x`, and the fixed
  unsatisfiable code `000` (one empty clause) otherwise.  Proofs have length
  `2|x| + 2 + |w| ≤ 2|x| + 2 + p |x|`.

## Gates

```
lake build
python3 scripts/check_sorry.py
python3 scripts/check_closure.py
python3 scripts/goal_state.py validate
```
