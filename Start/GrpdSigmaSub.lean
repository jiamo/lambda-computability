import Start.GrpdUnpair

/-!
# Beck–Chevalley for Σ in the groupoid model, and `grpdSigmaStruct`
(row M23-GROUPOID-SIGMA; series V, round 3, run 2, part C)

* `sigMap_comp_right`, `sigMap_congr` — the generic Grothendieck functoriality `sigMap` under
  precomposition of the family and under equal fibre functors;
* **`grpdSig_sub`** — `σ ⋙ SigF A B = SigF (σ ⋙ A) (extendG σ A ⋙ B)` (stability of Σ under
  substitution), from `fibI_comp_extend`;
* **`grpdSigmaStruct : Cwa.SigmaStruct grpdCwa`** — Σ-types in the groupoid model, with the pairing
  isomorphism `grpdSigPair` and `grpdSigPair_disp` of `Start/GrpdUnpair.lean`.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u
open CategoryTheory

namespace GrpdModel

theorem sigMap_comp_right {C D X Y : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} X]
    [Category.{u} Y] (K : C ⥤ D) (F : C ⥤ X) (G : D ⥤ X) (θ : F ⟶ K ⋙ G) (E : X ⥤ Y)
    (B : Y ⥤ Grpd.{u, u}) :
    sigMap K F G θ (E ⋙ B) =
      sigMap K (F ⋙ E) (G ⋙ E) (Functor.whiskerRight θ E : F ⋙ E ⟶ K ⋙ (G ⋙ E)) B := rfl

theorem sigMap_congr {C D X : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} X]
    (K : C ⥤ D) (B : X ⥤ Grpd.{u, u}) {F F' : C ⥤ X} {G G' : D ⥤ X} (hF : F = F') (hG : G = G')
    {θ : F ⟶ K ⋙ G} {θ' : F' ⟶ K ⋙ G'} (hθ : ∀ c, HEq (θ.app c) (θ'.app c)) :
    HEq (sigMap K F G θ B) (sigMap K F' G' θ' B) := by
  subst hF hG
  have : θ = θ' := NatTrans.ext (funext fun c => eq_of_heq (hθ c))
  subst this
  rfl

/-- **Σ is stable under substitution** in the groupoid model. -/
theorem grpdSig_sub {Γ Δ : Grpd.{u, u}} (σ : Δ ⟶ Γ) (A : Γ ⥤ Grpd.{u, u})
    (B : grpdExt Γ A ⥤ Grpd.{u, u}) :
    σ ⋙ SigF A B = SigF (σ ⋙ A) (extendG σ A ⋙ B) := by
  refine CategoryTheory.Functor.hext (fun δ => ?_) (fun δ δ' g => ?_)
  · show Grpd.of (GObj (fibI A (σ.obj δ) ⋙ B)) =
      Grpd.of (GObj ((fibI (σ ⋙ A) δ ⋙ extend σ A) ⋙ B))
    rw [fibI_comp_extend]
  · show HEq (sigMapG A B (σ.map g)) (sigMapG (σ ⋙ A) (extend σ A ⋙ B) g)
    unfold sigMapG
    exact (sigMap_congr (A.map (σ.map g)) B (fibI_comp_extend σ A δ).symm
      (fibI_comp_extend σ A δ').symm
      (θ' := (Functor.whiskerRight (sigTheta (σ ⋙ A) g) (extend σ A) :
        fibI (σ ⋙ A) δ ⋙ extend σ A ⟶ A.map (σ.map g) ⋙ (fibI (σ ⋙ A) δ' ⋙ extend σ A)))
      (fun _ => HEq.rfl)).trans (heq_of_eq (sigMap_comp_right _ _ _ _ _ _).symm)

/-- **Σ-types in the groupoid model.** -/
def grpdSigmaStruct : Cwa.SigmaStruct grpdCwa.{u} where
  Sig A B := SigF A B
  Sig_sub σ A B := grpdSig_sub σ A B
  pair A B := grpdSigPair _ A B
  pair_disp A B := grpdSigPair_disp _ A B

end GrpdModel
