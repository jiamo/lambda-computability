/-
A step-counting complexity measure for the partial recursive codes, the Blum axioms, and a
diagonalization showing that no computable bound is enough for every computable function.

Mathlib's `Nat.Partrec.Code.evaln k c x` runs the code `c` on the input `x` with `k` units of
fuel.  The least amount of fuel that suffices is a *Blum complexity measure*:

* `Complexity.steps c x` — the least `k` with `evaln k c x` defined;
* `Complexity.steps_dom_iff` — **the first Blum axiom**: `steps c x` is defined exactly when
  `eval c x` is;
* `Complexity.primrec_stepsLe`, `Complexity.decidable_stepsLe` — **the second Blum axiom**: the
  predicate "`c` converges on `x` within `m` units of fuel" is primitive recursive, in
  particular decidable.

The measure is then used for the basic separation result of complexity theory that does not need
a machine model at all:

* `Complexity.exists_computable_not_withinFuel` — for every computable bound `t` there is a
  *total computable* function that no code computes within `t x` units of fuel.  So there is no
  computable time bound that captures all computable functions: complexity classes given by
  computable bounds form a proper hierarchy of subclasses of the computable functions.

## Boundary

This is a fuel-counting measure, not the number of steps of a concrete machine, and the
convention `evaln` uses (`x < k` is required for convergence) makes the fuel bound at least the
input.  Nothing here develops `P`, `NP`, or reductions: for that one needs a cost model over a
machine with a robust notion of composition, and mathlib's `Turing.TM2ComputableInPolyTime`
does not yet provide the closure properties that Cook–Levin-style arguments require.
-/

import Mathlib.Computability.Halting

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Nat.Partrec (Code)
open Encodable Denumerable

/-- The fuel-counting complexity measure: the least `k` for which `c` converges on `x` with `k`
units of fuel. -/
def steps (c : Code) (x : ℕ) : Part ℕ :=
  Nat.rfind fun k => ((Code.evaln k c x).isSome : Bool)

theorem isSome_evaln_of_mem_steps {c : Code} {x k : ℕ} (h : k ∈ steps c x) :
    (Code.evaln k c x).isSome := by
  have := (Nat.rfind_spec h)
  simpa using this

/-- **The first Blum axiom**: the measure is defined exactly on the domain of the function. -/
theorem steps_dom_iff (c : Code) (x : ℕ) : (steps c x).Dom ↔ (Code.eval c x).Dom := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ : ∃ k, k ∈ steps c x := ⟨_, Part.get_mem h⟩
    have hsome := isSome_evaln_of_mem_steps hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsome
    exact Part.dom_iff_mem.2 ⟨v, Code.evaln_sound (by simpa using hv)⟩
  · intro h
    obtain ⟨v, hv⟩ : ∃ v, v ∈ Code.eval c x := ⟨_, Part.get_mem h⟩
    obtain ⟨k, hk⟩ := Code.evaln_complete.1 hv
    refine Nat.rfind_dom.2 ⟨k, ?_, fun {m} _ => trivial⟩
    simpa using Option.isSome_iff_exists.2 ⟨v, by simpa using hk⟩

/-- "The code `c` converges on `x` with at most `m` units of fuel." -/
def StepsLe (c : Code) (x m : ℕ) : Prop := (Code.evaln m c x).isSome

/-- **The second Blum axiom**: the graph of the measure is decidable.  Here in the strong form
that the bounded-convergence predicate is primitive recursive. -/
theorem primrec_stepsLe :
    Primrec fun a : (Code × ℕ) × ℕ => (Code.evaln a.2 a.1.1 a.1.2).isSome := by
  have h : Primrec fun a : (Code × ℕ) × ℕ => Code.evaln a.2 a.1.1 a.1.2 :=
    Code.primrec_evaln.comp (((Primrec.snd).pair (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.fst))
  exact Primrec.option_isSome.comp h

instance decidable_stepsLe (c : Code) (x m : ℕ) : Decidable (StepsLe c x m) :=
  inferInstanceAs (Decidable ((Code.evaln m c x).isSome = true))

theorem stepsLe_mono {c : Code} {x m m' : ℕ} (h : m ≤ m') (hm : StepsLe c x m) :
    StepsLe c x m' := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hm
  exact Option.isSome_iff_exists.2 ⟨v, by simpa using Code.evaln_mono h (by simpa using hv)⟩

------------------------------------------------------------------------
-- No computable bound suffices for every computable function
------------------------------------------------------------------------

/-- The code `c` computes the total function `f` within the fuel bound `t`. -/
def WithinFuel (c : Code) (t : ℕ → ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ x, Code.evaln (t x) c x = some (f x)

/-- The diagonal function for the bound `t`: run the `x`-th code on the input `x` with `t x`
units of fuel, and return one more than its output (or `0` if it has not converged). -/
def diag (t : ℕ → ℕ) (x : ℕ) : ℕ :=
  ((Code.evaln (t x) (ofNat Code x) x).map fun v => v + 1).getD 0

theorem computable_diag {t : ℕ → ℕ} (ht : Computable t) : Computable (diag t) := by
  have hev : Computable fun x : ℕ => Code.evaln (t x) (ofNat Code x) x :=
    Code.primrec_evaln.to_comp.comp ((ht.pair (Computable.ofNat Code)).pair Computable.id)
  exact (Computable.option_getD (hev.option_map (Computable.succ.comp Computable.snd).to₂)
    (Computable.const 0))

/-- **No computable bound is enough.**  For every computable fuel bound `t` there is a total
computable function that no code computes within `t`. -/
theorem exists_computable_not_withinFuel {t : ℕ → ℕ} (ht : Computable t) :
    ∃ f : ℕ → ℕ, Computable f ∧ ∀ c : Code, ¬ WithinFuel c t f := by
  refine ⟨diag t, computable_diag ht, fun c hc => ?_⟩
  set x := Encodable.encode c with hx
  have hcx : ofNat Code x = c := by rw [hx, Denumerable.ofNat_encode]
  have hrun := hc x
  have hdiag : diag t x = ((Code.evaln (t x) c x).map fun v => v + 1).getD 0 := by
    rw [diag, hcx]
  rw [hrun] at hdiag
  simp at hdiag

/-- Restated with the complexity measure: for every computable bound `t`, some total computable
function needs more than `t x` units of fuel on some input, whichever code computes it. -/
theorem exists_computable_steps_gt {t : ℕ → ℕ} (ht : Computable t) :
    ∃ f : ℕ → ℕ, Computable f ∧
      ∀ c : Code, (∀ x, Code.eval c x = Part.some (f x)) → ∃ x, ¬ StepsLe c x (t x) := by
  obtain ⟨f, hf, hnot⟩ := exists_computable_not_withinFuel ht
  refine ⟨f, hf, fun c hc => ?_⟩
  by_contra hall
  push Not at hall
  refine hnot c fun x => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hall x)
  have hmem : v ∈ Code.eval c x := Code.evaln_sound (by simpa using hv)
  have : v = f x := by
    rw [hc x] at hmem
    simpa using hmem
  rw [hv, this]

end Complexity
