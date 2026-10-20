/-
**The groupoid model of type theory (Hofmann–Streicher)** — task `M23-GROUPOID-MODEL`.

* `GrpdModel.grpdCwa : Cwa Grpd` — the category with attributes on Mathlib's category of
  groupoids: a type in context `Γ` is a functor `Γ ⥤ Grpd`, substitution is precomposition
  (strictly functorial, by `rfl`), context extension is the Grothendieck construction
  (`Start/GrpdGrothendieck.lean`), the display map is the projection, and the extension squares
  are pullbacks (`isPullbackG`, through an explicit limit cone).
-/

import Start.CwaId
import Start.GrpdGrothendieck

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace GrpdModel

/-- Context extension in the groupoid model: the Grothendieck construction. -/
def grpdExt (Γ : Grpd.{u, u}) (A : Γ ⥤ Grpd.{u, u}) : Grpd.{u, u} := Grpd.of (GObj A)

/-- The display map of the groupoid model, as a morphism of `Grpd`. -/
def dispG {Γ : Grpd.{u, u}} (A : Γ ⥤ Grpd.{u, u}) : grpdExt Γ A ⟶ Γ := disp A

/-- The action of a substitution on extended contexts, as a morphism of `Grpd`. -/
def extendG {Γ Δ : Grpd.{u, u}} (σ : Δ ⟶ Γ) (A : Γ ⥤ Grpd.{u, u}) :
    grpdExt Δ (σ ⋙ A) ⟶ grpdExt Γ A := extend σ A

/-- **The extension squares of the groupoid model are pullbacks.** -/
theorem isPullbackG {Γ Δ : Grpd.{u, u}} (σ : Δ ⟶ Γ) (A : Γ ⥤ Grpd.{u, u}) :
    IsPullback (extendG σ A) (dispG (σ ⋙ A)) (dispG A) σ := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (fst := extendG σ A)
    (snd := dispG (σ ⋙ A)) (f := dispG A) (g := σ) rfl
    (fun s => liftG σ A s.fst s.snd s.condition) (fun s => liftG_fst σ A _ _ _)
    (fun s => liftG_snd σ A _ _ _) (fun s m h₁ h₂ => liftG_uniq σ A _ _ _ m h₁ h₂))

/-- **The groupoid model as a category with attributes.** -/
def grpdCwa : Cwa.{u + 1, u, u + 1} Grpd.{u, u} where
  Ty Γ := Γ ⥤ Grpd.{u, u}
  tySub σ A := σ ⋙ A
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  ext Γ A := grpdExt Γ A
  disp A := dispG A
  extend σ A := extendG σ A
  isPullback σ A := isPullbackG σ A

end GrpdModel
