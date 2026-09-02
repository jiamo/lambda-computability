/-
**A natural numbers object for the partial equivalence relations.**

`Start/ModestNNO.lean` proves that the assembly of natural numbers is modest over an algebra with
more than one element, so that the modest assemblies have a natural numbers object.  Under the
equivalence of `Start/ModestEquiv.lean` the modest assemblies are the partial equivalence
relations, and this module transports the natural numbers object across it.

The transport is an instance of a general fact, proved here for Lawvere's universal property as
stated in `Start/AssemblyNNO.lean`: an equivalence of categories carries a natural numbers object
to a natural numbers object.  The image of a terminal object is terminal, and definition by
iteration transfers because the functor is full, faithful and essentially surjective, so a
recursion datum in the target can be pulled back along the counit isomorphism, solved in the
source, and pushed forward again.

Main results:

* `CategoryTheory.Limits.IsNNO.ofEquivalence` — **an equivalence of categories preserves natural
  numbers objects**;
* `Realizability.PER.isNNO_natPER` — **the partial equivalence relations have a natural numbers
  object**, the image of the assembly of natural numbers.
-/

import Start.ModestNNO

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

namespace CategoryTheory.Limits

variable {C : Type w} [Category.{v} C] {D : Type u} [Category D]

/-- **An equivalence of categories preserves natural numbers objects.** -/
theorem IsNNO.ofEquivalence (e : C ≌ D) {T N : C} {zero : T ⟶ N} {succ : N ⟶ N}
    (h : IsNNO zero succ) : IsNNO (e.functor.map zero) (e.functor.map succ) := by
  refine ⟨h.isTerminal.map fun ht => ?_, fun X q f => ?_⟩
  · exact IsTerminal.ofIso (IsTerminal.isTerminalObj e.functor _ ht) (Iso.refl _)
  · have i : e.functor.obj (e.inverse.obj X) ≅ X := e.counitIso.app X
    obtain ⟨u, ⟨h₀, hs⟩, huniq⟩ :=
      h.existsUnique_rec (e.inverse.obj X) (e.functor.preimage (q ≫ i.inv))
        (e.functor.preimage (i.hom ≫ f ≫ i.inv))
    refine ⟨e.functor.map u ≫ i.hom, ⟨?_, ?_⟩, ?_⟩
    · rw [← Category.assoc, ← e.functor.map_comp, h₀, e.functor.map_preimage,
        Category.assoc, i.inv_hom_id, Category.comp_id]
    · rw [← Category.assoc, ← e.functor.map_comp, hs, e.functor.map_comp, Category.assoc,
        e.functor.map_preimage, Category.assoc, Category.assoc, i.inv_hom_id, Category.comp_id,
        Category.assoc]
    · intro m ⟨hm₀, hms⟩
      have hm : m = e.functor.map (e.functor.preimage (m ≫ i.inv)) ≫ i.hom := by
        rw [e.functor.map_preimage, Category.assoc, i.inv_hom_id, Category.comp_id]
      rw [hm, huniq (e.functor.preimage (m ≫ i.inv)) ⟨?_, ?_⟩]
      · apply e.functor.map_injective
        rw [e.functor.map_comp, e.functor.map_preimage, e.functor.map_preimage,
          ← Category.assoc, hm₀]
      · apply e.functor.map_injective
        rw [e.functor.map_comp, e.functor.map_comp, e.functor.map_preimage,
          e.functor.map_preimage, ← Category.assoc, hms]
        simp

end CategoryTheory.Limits

namespace Realizability

open CategoryTheory CategoryTheory.Limits Assembly

namespace PER

variable (A : Type u) [PCA A] [Nontrivial A]

/-- The natural numbers as a partial equivalence relation: the image of the modest assembly of
natural numbers under the equivalence of `Start/ModestEquiv.lean`. -/
noncomputable def natPER : PER A :=
  (perEquivModest A).inverse.obj (Modest.natModest A)

/-- The terminal partial equivalence relation, as the source of zero. -/
noncomputable def unitOfModest : PER A :=
  (perEquivModest A).inverse.obj (Modest.unitModest A)

/-- Zero, as a morphism of partial equivalence relations. -/
noncomputable def natZeroPER : unitOfModest A ⟶ natPER A :=
  (perEquivModest A).inverse.map (Modest.natZeroModest A)

/-- The successor, as a morphism of partial equivalence relations. -/
noncomputable def natSuccPER : natPER A ⟶ natPER A :=
  (perEquivModest A).inverse.map (Modest.natSuccModest A)

/-- **The partial equivalence relations have a natural numbers object** over an algebra with more
than one element: the image of the assembly of natural numbers. -/
theorem isNNO_natPER : IsNNO (natZeroPER A) (natSuccPER A) :=
  (Modest.isNNO_natModest A).ofEquivalence (perEquivModest A).symm

end PER

end Realizability
