# M22-CONP-PH — coNP and the polynomial hierarchy

**Status:** DONE_STRONG

## Terminal statements (`Start/PolyHierarchy.lean`)

```lean
def Complexity.InCoNP (L : Language) : Prop := InNP (fun x => ¬ L x)
def Complexity.ExistsP (C : Language → Prop) (L : Language) : Prop
def Complexity.InSigma : ℕ → Language → Prop      -- Σ₀ = P, Σₖ₊₁ = ∃ᵖ Πₖ
def Complexity.InPi (k : ℕ) (L : Language) : Prop := InSigma k (fun x => ¬ L x)

theorem Complexity.inSigma_one_iff (L) : InSigma 1 L ↔ InNP L
theorem Complexity.inPi_one_iff (L) : InPi 1 L ↔ InCoNP L
theorem Complexity.InNP.of_existsP : ExistsP InNP L → InNP L
theorem Complexity.inNP_of_inSigma_of_NP_eq_coNP (h : ∀ L, InNP L ↔ InCoNP L) :
    ∀ k L, InSigma k L → InNP L
theorem Complexity.inNP_of_inPi_of_NP_eq_coNP (h : ∀ L, InNP L ↔ InCoNP L) k L :
    InPi k L → InNP L
theorem Complexity.ph_collapse_of_NP_eq_coNP (h : ∀ L, InNP L ↔ InCoNP L) k L :
    (InSigma (k + 1) L ↔ InNP L) ∧ (InPi (k + 1) L ↔ InNP L)
theorem Complexity.NP_eq_coNP_of_peqNP (h : PeqNP) L : InNP L ↔ InCoNP L
theorem Complexity.inP_of_inSigma_of_peqNP (h : PeqNP) k L : InSigma k L → InP L
theorem Complexity.inP_of_inPi_of_peqNP (h : PeqNP) k L : InPi k L → InP L
```

## Design

* `ExistsP C L`: there are `L' ∈ C` and a monotone polynomial `p` with
  `L' ⟨x, w⟩ → |w| ≤ p |x|` and `L x ↔ ∃ w, L' ⟨x, w⟩`, where `⟨x, w⟩ = pairW x w` is the
  self-delimiting pairing of `Start/NPInter.lean`.  The witness bound is forced by membership, as
  in `Complexity.InNP`; `inSigma_one_iff` shows that the first level is exactly the library's `NP`.
* `pairT` is the Cobham term for `pairW` (bit doubling is a one-state transduction, then
  concatenation), needed to merge two existential quantifiers (`InNP.of_existsP`): the new witness
  is `pairW w u`, and its length is bounded by `length_le_of_proj`.
* The collapse is an induction on `k`: if `Πₖ ⊆ NP` then `Σₖ₊₁ = ∃ᵖ Πₖ ⊆ ∃ᵖ NP = NP`, and
  `NP = coNP` turns `Σₖ₊₁ ⊆ NP` into `Πₖ₊₁ ⊆ NP`.  `P = NP` gives `NP = coNP` since `P` is closed
  under complement.

`#print axioms` of the terminal theorems: `propext, Classical.choice, Quot.sound`.

## Gates

```
lake build
python3 scripts/check_sorry.py
python3 scripts/check_closure.py
python3 scripts/goal_state.py validate
```
