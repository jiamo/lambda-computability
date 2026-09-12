/-
**Every object of the exact completion is the quotient of an assembly.**

`Start/AsmExReg.lean` shows that the canonical map `quot E` from the base of a pseudo-equivalence
relation, with equality, to the relation itself is an epimorphism.  This module identifies it as a
*coequalizer*: of the two endpoints of the assembly of proofs of the relation.

The assembly of proofs of `E` has the related pairs as its points and the proofs as their
realizers.  Its two endpoints are morphisms of assemblies, because the endpoints of a proof are
computable, and the two composites with `quot E` are homotopic — the proof at hand *is* the
homotopy.  Conversely a map out of the base of `E` which coequalizes the two endpoints is
precisely a map that transports proofs, i.e. a morphism out of `E`: the descent is the same
function, tracked by the homotopy.

Main results:

* `Realizability.ExReg.prfAsm` — the assembly of proofs of a pseudo-equivalence relation;
* `Realizability.ExReg.quotIsColimit` — **`quot E` is the coequalizer of the two endpoints**;
* `Realizability.ExReg.regularEpi_quot` — hence every object of the completion is a *regular*
  quotient of an assembly.
-/

import Start.AsmExRegEq
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace ExReg

variable {A : Type u} [PCA A]

/-! ### The assembly of proofs -/

/-- The **assembly of proofs** of a pseudo-equivalence relation: the related pairs of points,
realized by the proofs that they are related. -/
def prfAsm (E : ERel.{u, v} A) : Assembly.{u, v} A where
  carrier := {p : E.base.carrier × E.base.carrier // E.rel p.1 p.2}
  realizes w p := E.Prf w p.1.1 p.1.2
  exists_realizer p := p.2

/-- The first endpoint, as a pre-morphism between the assemblies with equality. -/
def relFstPre (E : ERel.{u, v} A) : Pre (eqERel (prfAsm E)) (eqERel E.base) where
  toFun p := p.1.1
  tracked := by
    obtain ⟨t, ht⟩ := E.exists_fstTracker
    refine ⟨t, fun a x y h => ?_⟩
    obtain ⟨hx, rfl⟩ := h
    obtain ⟨v, hv, hvx⟩ := ht a x.1.1 x.1.2 hx
    exact ⟨v, hv, hvx, rfl⟩

/-- The second endpoint, as a pre-morphism between the assemblies with equality. -/
def relSndPre (E : ERel.{u, v} A) : Pre (eqERel (prfAsm E)) (eqERel E.base) where
  toFun p := p.1.2
  tracked := by
    obtain ⟨t, ht⟩ := E.exists_sndTracker
    refine ⟨t, fun a x y h => ?_⟩
    obtain ⟨hx, rfl⟩ := h
    obtain ⟨v, hv, hvx⟩ := ht a x.1.1 x.1.2 hx
    exact ⟨v, hv, hvx, rfl⟩

/-- The first endpoint. -/
noncomputable def relFst (E : ERel.{u, v} A) : (emb A).obj (prfAsm E) ⟶ (emb A).obj E.base :=
  homOf (relFstPre E)

/-- The second endpoint. -/
noncomputable def relSnd (E : ERel.{u, v} A) : (emb A).obj (prfAsm E) ⟶ (emb A).obj E.base :=
  homOf (relSndPre E)

/-- The two endpoints become homotopic after the quotient map: a point of the assembly of proofs
is realized by a proof that its two endpoints are related. -/
theorem relFst_quot_homotopic (E : ERel.{u, v} A) :
    Homotopic ((relFstPre E).comp (quotPre E)) ((relSndPre E).comp (quotPre E)) :=
  ⟨PCA.i A, fun a x hx => ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, hx⟩⟩

theorem relFst_comp_quot (E : ERel.{u, v} A) :
    relFst E ≫ quot E = relSnd E ≫ quot E :=
  homOf_eq_iff.2 (relFst_quot_homotopic E)

/-! ### Descent -/

/-- A map out of the base of `E` which identifies the two endpoints of every proof descends to
a map out of `E`: the same function, tracked by the homotopy. -/
noncomputable def descendPre {E G : ERel.{u, v} A} (r : Pre (eqERel E.base) G)
    (h : Homotopic ((relFstPre E).comp r) ((relSndPre E).comp r)) : Pre E G where
  toFun := r.toFun
  tracked := by
    obtain ⟨t, ht⟩ := h
    refine ⟨t, fun a x y hxy => ?_⟩
    exact ht a ⟨(x, y), ⟨a, hxy⟩⟩ hxy

theorem quot_comp_descendPre {E G : ERel.{u, v} A} (r : Pre (eqERel E.base) G)
    (h : Homotopic ((relFstPre E).comp r) ((relSndPre E).comp r)) :
    (quotPre E).comp (descendPre r h) = r := Pre.ext rfl

/-! ### The coequalizer -/

/-- The cofork given by the quotient map. -/
noncomputable def quotCofork (E : ERel.{u, v} A) : Cofork (relFst E) (relSnd E) :=
  Cofork.ofπ (quot E) (relFst_comp_quot E)

@[simp] theorem quotCofork_π (E : ERel.{u, v} A) : Cofork.π (quotCofork E) = quot E := rfl

/-- The condition of a cofork, read on a representative of its leg. -/
theorem homotopic_of_cofork {E : ERel.{u, v} A} (s : Cofork (relFst E) (relSnd E)) :
    Homotopic ((relFstPre E).comp (repr (Cofork.π s)))
      ((relSndPre E).comp (repr (Cofork.π s))) := by
  have h : relFst E ≫ homOf (repr (Cofork.π s)) = relSnd E ≫ homOf (repr (Cofork.π s)) := by
    rw [homOf_repr]
    exact s.condition
  exact homOf_eq_iff.1 h

/-- **The quotient map is the coequalizer of the two endpoints of the assembly of proofs**:
every object of the completion is the quotient of an assembly by a relation on it. -/
noncomputable def quotIsColimit (E : ERel.{u, v} A) : IsColimit (quotCofork E) :=
  Cofork.IsColimit.mk _
    (fun s => homOf (descendPre (repr (Cofork.π s)) (homotopic_of_cofork s)))
    (fun s => by
      have h : homOf ((quotPre E).comp
          (descendPre (repr (Cofork.π s)) (homotopic_of_cofork s)))
          = homOf (repr (Cofork.π s)) :=
        congrArg homOf (quot_comp_descendPre _ _)
      rw [homOf_repr] at h
      exact h)
    (fun s m hm => by
      have hfac : Cofork.π (quotCofork E) ≫
          homOf (descendPre (repr (Cofork.π s)) (homotopic_of_cofork s)) = Cofork.π s := by
        have h : homOf ((quotPre E).comp
            (descendPre (repr (Cofork.π s)) (homotopic_of_cofork s)))
            = homOf (repr (Cofork.π s)) :=
          congrArg homOf (quot_comp_descendPre _ _)
        rw [homOf_repr] at h
        exact h
      exact (cancel_epi (quot E)).1 (hm.trans hfac.symm))

instance hasCoequalizer_rel (E : ERel.{u, v} A) : HasCoequalizer (relFst E) (relSnd E) :=
  ⟨⟨⟨quotCofork E, quotIsColimit E⟩⟩⟩

/-- **Every object of the completion is a regular quotient of an assembly.** -/
noncomputable def regularEpi_quot (E : ERel.{u, v} A) : RegularEpi (quot E) where
  W := (emb A).obj (prfAsm E)
  left := relFst E
  right := relSnd E
  w := relFst_comp_quot E
  isColimit := quotIsColimit E

end ExReg

end Realizability
