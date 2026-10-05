/-
**The relativization barrier.**

A proof technique *relativizes* when its conclusion survives the attachment of an arbitrary
oracle: an argument that proves `P = NP` and relativizes proves `P^A = NP^A` for every oracle `A`,
and an argument that proves `P ≠ NP` and relativizes proves `P^A ≠ NP^A` for every `A`.  This file
states that, and records what the library proves about it.

* `Complexity.Relativizes` — a statement about the oracle holds for every oracle;
* `Complexity.peqnp_does_not_relativize` — **`P = NP` does not relativize**, by the separating
  oracle of `Start/BakerGillSolovay.lean`;
* `Complexity.pnenp_does_not_relativize` — **`P ≠ NP` does not relativize**, by the collapsing
  oracle of `Start/CollapsingOracle.lean` (`Complexity.bgs_equal`);
* `Complexity.no_relativizing_resolution` — **neither `P = NP` nor `P ≠ NP` relativizes**, so no
  relativizing argument settles the question either way.  This holds with no hypothesis.

The collapsing oracle is not the classical `PSPACE`-complete one: it is built directly by a
self-referential construction (the oracle answers whether a verifier, run with the oracle restricted
to shorter words, accepts some short witness), which needs no space-bounded machines.
-/

import Mathlib
import Start.BakerGillSolovay
import Start.CollapsingOracle

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

/-- `P ≠ NP` does not relativize as soon as one oracle collapses the two classes. -/
theorem pnenp_does_not_relativize_of (h : ∃ A : Oracle, PeqNP_rel A) :
    ¬ Relativizes PneNP_rel := by
  intro hrel
  obtain ⟨A, hA⟩ := h
  exact hrel A hA

/-- **`P ≠ NP` does not relativize**: some oracle collapses the two classes
(`Complexity.bgs_equal`), so no argument whose conclusion survives every oracle can prove
`P ≠ NP`. -/
theorem pnenp_does_not_relativize : ¬ Relativizes PneNP_rel :=
  pnenp_does_not_relativize_of bgs_equal

/-- **The relativization barrier.**  Neither `P = NP` nor `P ≠ NP` relativizes: a proof technique
whose conclusions hold with every oracle attached settles neither side of the question. -/
theorem no_relativizing_resolution :
    ¬ Relativizes PeqNP_rel ∧ ¬ Relativizes PneNP_rel :=
  ⟨peqnp_does_not_relativize, pnenp_does_not_relativize⟩

end Complexity
