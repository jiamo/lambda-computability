import Start.GrpdSigmaPair

/-!
# The pairing functor `∫ B ⥤ ∫ (SigF A B)` (row M23-GROUPOID-SIGMA; series V, round 3, run 1, C2)

`Start/GrpdSigmaPair.lean` gives the object and morphism parts `pairObj`, `pairHom` of the pairing
and its identity law `pairHom_id`.  This module proves the composition law, so the pairing is a
functor:

* `eqToHom_fib_eq'` — the fibre component of an `eqToHom` in a Grothendieck construction;
* **`pairHom_comp`** — `pairHom A B (f ≫ g) = pairHom A B f ≫ pairHom A B g` (the base component
  closes by `eqToHom_base`; the fibre component by stripping `eqToHom`s and `heq_comp` along the
  factorization `ghom_factor A g.base`);
* `pairFunctor` — the pairing functor `GObj B ⥤ GObj (SigF A B)`.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory
namespace GrpdModel
variable {Γ : Type u} [Groupoid.{u} Γ] (A : Γ ⥤ Grpd.{u, u}) (B : GObj A ⥤ Grpd.{u, u})

theorem eqToHom_fib_eq' {C : Type u} [Category.{u} C] {F : C ⥤ Grpd.{u, u}} {p q : GObj F}
    (h : p = q) :
    (eqToHom h).fib = eqToHom (by subst h; exact map_id_obj _ _) := by
  subst h; rfl

/-- **The composition law of the pairing.** -/
theorem pairHom_comp {x y z : GObj B} (f : x ⟶ y) (g : y ⟶ z) :
    pairHom A B (f ≫ g) = pairHom A B f ≫ pairHom A B g := by
  refine GHom.hext rfl ?_
  refine heq_of_eq (GHom.hext ?_ ?_)
  · simp only [pairHom, comp_fib, comp_base]
    rw [comp_base, comp_base, eqToHom_base]
    rfl
  · show HEq (pairHomFib A B (f ≫ g)) _
    rw [comp_fib]
    simp only [pairHom, pairHomFib, comp_fib]
    rw [comp_fib, comp_fib]
    simp only [Functor.comp_map, eqToHom_trans_assoc]
    simp only [SigF, sigMapG, sigMap, Functor.map_comp, eqToHom_map, eqToHom_trans_assoc]
    rw [map_map (A := B)]
    refine (eqToHom_comp_heq _ _).trans ?_
    refine HEq.trans ?_ (eqToHom_comp_heq _ _).symm
    simp only [Category.assoc, eqToHom_trans_assoc]
    rw [eqToHom_fib_eq', eqToHom_map, eqToHom_trans_assoc]
    refine HEq.trans ?_ (eqToHom_comp_heq _ _).symm
    have e : B.map g.base = B.map ((sigTheta A g.base.base).app y.base.fib ≫
        (fibI A z.base.base).map g.base.fib) := congrArg B.map (ghom_factor A g.base)
    exact heq_comp (Functor.congr_obj e _) (Functor.congr_obj e _) rfl
      (Functor.hcongr_hom e f.fib) (eqToHom_comp_heq _ _).symm

/-- The pairing functor `∫ B ⥤ ∫ (SigF A B)`. -/
def pairFunctor : GObj B ⥤ GObj (SigF A B) where
  obj := pairObj A B
  map := pairHom A B
  map_id := pairHom_id A B
  map_comp := pairHom_comp A B

end GrpdModel
