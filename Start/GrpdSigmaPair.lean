/-
**Towards the pairing isomorphism of `Σ A B` in the groupoid model** — task
`M23-GROUPOID-SIGMA` (round 10, part D), continuing `Start/GrpdSigmaFun.lean`.

* `GrpdModel.ghom_factor` — **the factorization of a morphism of `∫ A`**: `(g, φ)` is the
  composite of the fibre-transformation component `sigTheta A g` at the source and the fibre
  inclusion of `φ`;
* `GrpdModel.pairObj`, `GrpdModel.unpairObj` — the object parts of the pairing isomorphism
  `∫ B ≅ ∫ (SigF A B)`, with their two round trips (`unpairObj_pairObj`, `pairObj_unpairObj`)
  and the compatibility with the display maps (`pairObj_base`);
* `GrpdModel.pairHomFib` — the fibre part of the morphism map of the pairing functor, built from
  `ghom_factor`.

Proved also: `pairHom_id`, the identity law of the pairing functor.

Open: the composition law (first missing lemma `pairHom_comp`), the
inverse functor and the round trips on morphisms, then `pair_disp`, `Sig_sub` and
`grpdSigmaStruct`; see `docs/goal/evidence/M23-GROUPOID-MODEL.md`, round 10.
-/

import Start.GrpdSigmaFun

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace GrpdModel

section Pair

variable {Γ : Type u} [Groupoid.{u} Γ] (A : Γ ⥤ Grpd.{u, u}) (B : GObj A ⥤ Grpd.{u, u})

/-- **The factorization of a morphism of `∫ A`** through the fibre transformation. -/
theorem ghom_factor {p q : GObj A} (f : p ⟶ q) :
    f = (sigTheta A f.base).app p.fib ≫ (fibI A q.base).map f.fib := by
  refine GHom.hext (Category.comp_id _).symm ?_
  simp only [comp_fib, fibI_map]
  simp only [sigTheta]
  have hX : (A.map (𝟙 q.base)).map (𝟙 ((A.map f.base).obj p.fib)) = 𝟙 _ :=
    (A.map (𝟙 q.base)).map_id _
  erw [hX, Category.id_comp, eqToHom_trans_assoc]
  exact (eqToHom_comp_heq f.fib _).symm

/-- The object part of the pairing functor `∫ B ⥤ ∫ (SigF A B)`. -/
def pairObj (x : GObj B) : GObj (SigF A B) := ⟨x.base.base, ⟨x.base.fib, x.fib⟩⟩

/-- The object part of the unpairing functor `∫ (SigF A B) ⥤ ∫ B`. -/
def unpairObj (y : GObj (SigF A B)) : GObj B := ⟨⟨y.base, y.fib.base⟩, y.fib.fib⟩

theorem unpairObj_pairObj (x : GObj B) : unpairObj A B (pairObj A B x) = x := rfl

theorem pairObj_unpairObj (y : GObj (SigF A B)) : pairObj A B (unpairObj A B y) = y := rfl

/-- The pairing is over `Γ` on objects. -/
theorem pairObj_base (x : GObj B) : (pairObj A B x).base = x.base.base := rfl

/-- The fibre part of the image of a morphism of `∫ B` under the pairing functor. -/
theorem pairHom_obj_eq {x y : GObj B} (f : x ⟶ y) :
    (B.map ((fibI A y.base.base).map f.base.fib)).obj
        ((B.map ((sigTheta A f.base.base).app x.base.fib)).obj x.fib) =
      (B.map f.base).obj x.fib := by
  exact (Functor.congr_obj (B.map_comp _ _) x.fib).symm.trans
    (Functor.congr_obj (congrArg B.map (ghom_factor A f.base)) x.fib).symm

/-- **The fibre part of the morphism map of the pairing functor.** -/
def pairHomFib {x y : GObj B} (f : x ⟶ y) :
    (B.map ((fibI A y.base.base).map f.base.fib)).obj
        ((B.map ((sigTheta A f.base.base).app x.base.fib)).obj x.fib) ⟶ y.fib :=
  eqToHom (pairHom_obj_eq A B f) ≫ f.fib

/-- **The morphism map of the pairing functor** `∫ B ⥤ ∫ (SigF A B)`. -/
def pairHom {x y : GObj B} (f : x ⟶ y) : pairObj A B x ⟶ pairObj A B y :=
  ⟨f.base.base, ⟨f.base.fib, pairHomFib A B f⟩⟩

/-- The pairing is over `Γ` on morphisms. -/
theorem pairHom_base {x y : GObj B} (f : x ⟶ y) : (pairHom A B f).base = f.base.base := rfl

theorem pairHom_id (x : GObj B) : pairHom A B (𝟙 x) = 𝟙 (pairObj A B x) := by
  refine GHom.hext rfl ?_
  refine heq_of_eq (GHom.hext ?_ ?_)
  · simp only [pairHom, id_fib]
    rw [eqToHom_base]
    rfl
  · simp only [pairHom, pairHomFib, id_fib]
    rw [eqToHom_trans]
    exact (eqToHom_heq_id_cod _ _ _).trans
      (eqToHom_fib_heq (fibI A x.base.base ⋙ B)
        (q := (⟨x.base.fib, x.fib⟩ : GObj (fibI A x.base.base ⋙ B))) _).symm

end Pair

end GrpdModel
