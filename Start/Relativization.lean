/-
**The relativization barrier.**

A proof technique *relativizes* when its conclusion survives the attachment of an arbitrary
oracle: an argument that proves `P = NP` and relativizes proves `P^A = NP^A` for every oracle `A`,
and an argument that proves `P ≠ NP` and relativizes proves `P^A ≠ NP^A` for every `A`.  This file
states that, and records what the library proves about it.

* `Complexity.Relativizes` — a statement about the oracle holds for every oracle;
* `Complexity.peqnp_does_not_relativize` — **`P = NP` does not relativize**, by the separating
  oracle of `Start/BakerGillSolovay.lean`;
* `Complexity.no_relativizing_resolution` — given a collapsing oracle, neither `P = NP` nor
  `P ≠ NP` relativizes, so no relativizing argument settles the question either way.

The hypothesis of the last statement is the half of Baker–Gill–Solovay that the library does not
yet have: an oracle `A` with `P^A = NP^A`, classically a `PSPACE`-complete one.  Here time is
measured on Cobham's class and space on the offline machine of `Start/SpaceMachine.lean`, so that
half needs a compiler from Cobham terms to space-bounded machines; see the boundary of
`M15-BGS-EQUAL` on the task board.
-/

import Mathlib
import Start.BakerGillSolovay

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-- A statement about an oracle *relativizes* when it holds for every oracle. -/
def Relativizes (S : Oracle → Prop) : Prop := ∀ A : Oracle, S A

/-- The statement `P^A ≠ NP^A`. -/
def PneNP_rel (A : Oracle) : Prop := ¬ PeqNP_rel A

/-- **`P = NP` does not relativize**: some oracle separates the two classes, so no argument whose
conclusion survives every oracle can prove `P = NP`. -/
theorem peqnp_does_not_relativize : ¬ Relativizes PeqNP_rel := by
  intro h
  obtain ⟨B, hB⟩ := bgs_different
  exact hB (h B)

/-- `P ≠ NP` does not relativize either, as soon as one oracle collapses the two classes. -/
theorem pnenp_does_not_relativize (h : ∃ A : Oracle, PeqNP_rel A) :
    ¬ Relativizes PneNP_rel := by
  intro hrel
  obtain ⟨A, hA⟩ := h
  exact hrel A hA

/-- **The relativization barrier.**  With a collapsing oracle at hand, neither `P = NP` nor
`P ≠ NP` relativizes: a proof technique whose conclusions hold with every oracle attached settles
neither side of the question. -/
theorem no_relativizing_resolution (h : ∃ A : Oracle, PeqNP_rel A) :
    ¬ Relativizes PeqNP_rel ∧ ¬ Relativizes PneNP_rel :=
  ⟨peqnp_does_not_relativize, pnenp_does_not_relativize h⟩

end Complexity
