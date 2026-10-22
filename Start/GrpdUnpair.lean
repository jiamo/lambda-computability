import Start.GrpdPairComp
import Start.CwaGroupoid

/-!
# The unpairing functor and `∫ B ≌ ∫ (SigF A B)` (row M23-GROUPOID-SIGMA; series V, round 3,
run 2, part C)

* `unpairBase_id`, `unpairHom_id`, `unpairBase_comp`, **`unpairHom_comp`** — the unpairing
  `∫ (SigF A B) ⥤ ∫ B` is a functor (`unpairFunctor`); the base of an `eqToHom` is handled by
  `eqToHom_base`;
* `unpairHom_pairHom`, `pairHom_unpairHom` and the round trips
  **`pairFunctor_comp_unpairFunctor`**, **`unpairFunctor_comp_pairFunctor`**;
* `sigIso : GObj B ≌ GObj (SigF A B)`;
* `grpdSigPair` — the pairing isomorphism `ext (ext Γ A) B ≅ ext Γ (SigF A B)` in `Grpd`, and
  **`grpdSigPair_disp`** (the `pair_disp` field of `Cwa.SigmaStruct grpdCwa`);
* `fibI_comp_extend` — the fibre inclusions commute with reindexing (first step of `Sig_sub`).
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory
namespace GrpdModel
variable {Γ : Type u} [Groupoid.{u} Γ] (A : Γ ⥤ Grpd.{u, u}) (B : GObj A ⥤ Grpd.{u, u})

/-- The base morphism of `∫ A` underlying a morphism of `∫ (SigF A B)`. -/
def unpairBase {p q : GObj (SigF A B)} (f : p ⟶ q) :
    (unpairObj A B p).base ⟶ (unpairObj A B q).base := ⟨f.base, f.fib.base⟩

theorem unpairHom_obj_eq {p q : GObj (SigF A B)} (f : p ⟶ q) :
    (B.map (unpairBase A B f)).obj p.fib.fib =
      (B.map ((fibI A q.base).map f.fib.base)).obj
        ((B.map ((sigTheta A f.base).app p.fib.base)).obj p.fib.fib) :=
  (Functor.congr_obj (congrArg B.map (ghom_factor A (unpairBase A B f))) p.fib.fib).trans
    (Functor.congr_obj (B.map_comp _ _) p.fib.fib)

def unpairHom {p q : GObj (SigF A B)} (f : p ⟶ q) : unpairObj A B p ⟶ unpairObj A B q :=
  ⟨unpairBase A B f, eqToHom (unpairHom_obj_eq A B f) ≫ f.fib.fib⟩

theorem unpairBase_id (p : GObj (SigF A B)) : unpairBase A B (𝟙 p) = 𝟙 (unpairObj A B p).base := by
  refine GHom.hext rfl ?_
  simp only [unpairBase, id_fib, id_base]
  rw [eqToHom_base]

theorem unpairHom_id (p : GObj (SigF A B)) : unpairHom A B (𝟙 p) = 𝟙 (unpairObj A B p) := by
  refine GHom.hext (unpairBase_id A B p) ?_
  simp only [unpairHom, id_fib]
  rw [eqToHom_fib_eq', eqToHom_trans]
  exact eqToHom_heq_eqToHom _ _
    (Functor.congr_obj (congrArg B.map (unpairBase_id A B p)) _) rfl

theorem unpairBase_comp {p q r : GObj (SigF A B)} (f : p ⟶ q) (g : q ⟶ r) :
    unpairBase A B (f ≫ g) = unpairBase A B f ≫ unpairBase A B g := by
  refine GHom.hext rfl ?_
  simp only [unpairBase, comp_fib, comp_base]
  rw [comp_base, comp_base, eqToHom_base]
  rfl

theorem unpairHom_comp {p q r : GObj (SigF A B)} (f : p ⟶ q) (g : q ⟶ r) :
    unpairHom A B (f ≫ g) = unpairHom A B f ≫ unpairHom A B g := by
  refine GHom.hext (unpairBase_comp A B f g) ?_
  simp only [unpairHom, comp_fib]
  rw [comp_fib, comp_fib]
  simp only [SigF, sigMapG, sigMap, Functor.map_comp, eqToHom_map, Category.assoc]
  rw [eqToHom_fib_eq']
  simp only [eqToHom_trans_assoc]
  refine (eqToHom_comp_heq _ _).trans ?_
  refine HEq.trans ?_ (eqToHom_comp_heq _ _).symm
  rw [eqToHom_map, eqToHom_trans_assoc]
  refine (eqToHom_comp_heq _ _).trans ?_
  have e : B.map (unpairBase A B g) = B.map ((sigTheta A g.base).app q.fib.base ≫
      (fibI A r.base).map g.fib.base) := congrArg B.map (ghom_factor A (unpairBase A B g))
  have h1 : HEq (((fibI A r.base ⋙ B).map g.fib.base).map
      ((B.map ((sigTheta A g.base).app q.fib.base)).map f.fib.fib))
      ((B.map ((sigTheta A g.base).app q.fib.base ≫ (fibI A r.base).map g.fib.base)).map
        f.fib.fib) := by
    change HEq ((B.map ((fibI A r.base).map g.fib.base)).map
      ((B.map ((sigTheta A g.base).app q.fib.base)).map f.fib.fib)) _
    rw [map_map (A := B)]
    exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)
  exact heq_comp ((map_comp_obj (A := B) _ _ _).symm.trans (Functor.congr_obj e _).symm)
    ((map_comp_obj (A := B) _ _ _).symm.trans (Functor.congr_obj e _).symm) rfl
    (h1.trans (Functor.hcongr_hom e f.fib.fib).symm) (eqToHom_comp_heq _ _).symm

/-- The unpairing functor `∫ (SigF A B) ⥤ ∫ B`. -/
def unpairFunctor : GObj (SigF A B) ⥤ GObj B where
  obj := unpairObj A B
  map := unpairHom A B
  map_id := unpairHom_id A B
  map_comp := unpairHom_comp A B

theorem unpairHom_pairHom {x y : GObj B} (f : x ⟶ y) : unpairHom A B (pairHom A B f) = f := by
  refine GHom.hext rfl ?_
  simp only [unpairHom, pairHom, pairHomFib]
  exact (eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _)

theorem pairHom_unpairHom {p q : GObj (SigF A B)} (g : p ⟶ q) :
    pairHom A B (unpairHom A B g) = g := by
  refine GHom.hext rfl (heq_of_eq (GHom.hext rfl ?_))
  simp only [unpairHom, pairHom, pairHomFib]
  exact (eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _)

/-- **Round trip** `∫ B → ∫ (SigF A B) → ∫ B`. -/
theorem pairFunctor_comp_unpairFunctor : pairFunctor A B ⋙ unpairFunctor A B = 𝟭 (GObj B) :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f => by
    simp only [Functor.comp_map, Functor.id_map, eqToHom_refl, Category.id_comp,
      Category.comp_id]
    exact unpairHom_pairHom A B f)

/-- **Round trip** `∫ (SigF A B) → ∫ B → ∫ (SigF A B)`. -/
theorem unpairFunctor_comp_pairFunctor :
    unpairFunctor A B ⋙ pairFunctor A B = 𝟭 (GObj (SigF A B)) :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ g => by
    simp only [Functor.comp_map, Functor.id_map, eqToHom_refl, Category.id_comp,
      Category.comp_id]
    exact pairHom_unpairHom A B g)

/-- **The isomorphism** `∫ B ≅ ∫ (SigF A B)` of the Σ-type model. -/
def sigIso : GObj B ≌ GObj (SigF A B) :=
  CategoryTheory.Equivalence.mk (pairFunctor A B) (unpairFunctor A B)
    (eqToIso (pairFunctor_comp_unpairFunctor A B).symm)
    (eqToIso (unpairFunctor_comp_pairFunctor A B))

end GrpdModel

namespace GrpdModel

/-- **The pairing isomorphism of the groupoid model**, in `Grpd`. -/
def grpdSigPair (Γ : Grpd.{u, u}) (A : Γ ⥤ Grpd.{u, u}) (B : grpdExt Γ A ⥤ Grpd.{u, u}) :
    grpdExt (grpdExt Γ A) B ≅ grpdExt Γ (SigF A B) where
  hom := pairFunctor A B
  inv := unpairFunctor A B
  hom_inv_id := pairFunctor_comp_unpairFunctor A B
  inv_hom_id := unpairFunctor_comp_pairFunctor A B

/-- **`pair_disp`**: the pairing isomorphism lives over the base context. -/
theorem grpdSigPair_disp (Γ : Grpd.{u, u}) (A : Γ ⥤ Grpd.{u, u})
    (B : grpdExt Γ A ⥤ Grpd.{u, u}) :
    (grpdSigPair Γ A B).hom ≫ dispG (SigF A B) = dispG B ≫ dispG A := rfl

end GrpdModel

namespace GrpdModel

/-- **The fibre inclusions commute with reindexing**: `fibI (σ ⋙ A) δ ⋙ extend σ A = fibI A (σ δ)`
(the first step of the Beck–Chevalley law `Sig_sub`). -/
theorem fibI_comp_extend {Γ Δ : Type u} [Groupoid.{u} Γ] [Groupoid.{u} Δ] (σ : Δ ⥤ Γ)
    (A : Γ ⥤ Grpd.{u, u}) (δ : Δ) : fibI (σ ⋙ A) δ ⋙ extend σ A = fibI A (σ.obj δ) :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ φ => by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact GHom.hext (σ.map_id δ)
      ((eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _).symm))

end GrpdModel
