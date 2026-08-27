/-
**Subject reduction for System F**: β-reduction preserves typing.

In Curry style the two rules for `∀` do not change the term, so a derivation of
`Γ ⊢ λx. s : A → B` need not end with the abstraction rule: it may end with any number of
generalizations and instantiations.  The *generation lemma* — that an abstraction of a function
type is an abstraction whose body has the codomain type — therefore needs an induction that looks
through those quantifiers.  The device used here is:

* `SystemF.AllArrow` — the shape of the type of an abstraction: peeling the quantifiers of the
  type of a `λ` always reaches an arrow (`SystemF.allArrow_of_lam`);
* `SystemF.Peel σ T A B` — "instantiating the leading quantifiers of `T`, and then substituting
  `σ`, gives `A → B`", the invariant strong enough to be carried through the induction;
* `SystemF.Typing.gen_lam_peel`, and its corollary `SystemF.Typing.gen_lam` — **the generation
  lemma**;
* `SystemF.Typing.preservation` — **subject reduction**, and `SystemF.Typing.preservation_reduces`
  for many steps.
-/

import Start.SystemFSubst

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace SystemF

open Lambda

/-! ### The shape of the type of an abstraction -/

/-- A type whose leading quantifiers hide an arrow. -/
def AllArrow : FTy → Prop
  | FTy.var _ => False
  | FTy.arrow _ _ => True
  | FTy.all A => AllArrow A

theorem allArrow_tySubst {A : FTy} (h : AllArrow A) (s : ℕ → FTy) : AllArrow (tySubst s A) := by
  induction A generalizing s with
  | var i => exact absurd h (by simp [AllArrow])
  | arrow A B _ _ => trivial
  | all A ih => exact ih h (ups s)

/-- **The type of an abstraction is an arrow under its quantifiers.** -/
theorem allArrow_of_lam {Γ : List FTy} {t : Lambda} {T : FTy} (h : Typing Γ t T) :
    ∀ s : Lambda, t = Lambda.lam s → AllArrow T := by
  induction h with
  | var _ => intro s hs; exact absurd hs (by simp)
  | app _ _ _ _ => intro s hs; exact absurd hs (by simp)
  | lam _ _ => intro _ _; trivial
  | tlam _ ih => intro s hs; exact ih s hs
  | @tapp Γ t A B _ ih =>
      intro s hs
      have hA : AllArrow A := ih s hs
      exact allArrow_tySubst hA (tyScons B)

/-! ### Peeling the quantifiers of a type -/

/-- `Peel σ T A B` holds when instantiating the leading quantifiers of `T` and substituting `σ`
in the result yields the arrow type `A → B`. -/
inductive Peel : (ℕ → FTy) → FTy → FTy → FTy → Prop
  /-- No quantifier left: substitute. -/
  | arrow {s : ℕ → FTy} {A B : FTy} : Peel s (FTy.arrow A B) (tySubst s A) (tySubst s B)
  /-- Instantiate the outermost quantifier by `D`. -/
  | all {s : ℕ → FTy} {A₀ : FTy} (D : FTy) {A B : FTy} :
      Peel (tyCons D s) A₀ A B → Peel s (FTy.all A₀) A B

/-- Peeling a substituted type is peeling the type along the composite substitution. -/
theorem peel_tySubst (X : FTy) (hX : AllArrow X) :
    ∀ (s t : ℕ → FTy) (A B : FTy), Peel s (tySubst t X) A B →
      Peel (fun i => tySubst s (t i)) X A B := by
  induction X with
  | var i => exact absurd hX (by simp [AllArrow])
  | arrow X₁ X₂ _ _ =>
      intro s t A B h
      cases h with
      | arrow =>
          rw [tySubst_tySubst, tySubst_tySubst]
          exact Peel.arrow
  | all X₁ ih =>
      intro s t A B h
      cases h with
      | all D h₁ =>
          refine Peel.all D ?_
          have hcomp : (fun i => tySubst (tyCons D s) (ups t i))
              = tyCons D fun i => tySubst s (t i) := by
            funext i
            cases i with
            | zero => rfl
            | succ i => exact tySubst_tyCons_tyShift D s (t i)
          have := ih hX (tyCons D s) (ups t) A B h₁
          rwa [hcomp] at this

/-! ### The generation lemma -/

/-- **Generation for abstractions**, in the form that survives the quantifier rules. -/
theorem Typing.gen_lam_peel {Γ : List FTy} {t : Lambda} {T : FTy} (h : Typing Γ t T) :
    ∀ s : Lambda, t = Lambda.lam s → ∀ (σ : ℕ → FTy) (A B : FTy), Peel σ T A B →
      Typing (A :: Γ.map (tySubst σ)) s B := by
  induction h with
  | var _ => intro s hs; exact absurd hs (by simp)
  | app _ _ _ _ => intro s hs; exact absurd hs (by simp)
  | @lam Γ t A₀ B₀ hbody _ =>
      intro s hs σ A B hp
      have hst : t = s := by injection hs
      subst hst
      cases hp with
      | arrow => exact hbody.substTy σ
  | @tlam Γ t A₀ _ ih =>
      intro s hs σ A B hp
      cases hp with
      | all D hp₁ =>
          have hres := ih s hs (tyCons D σ) A B hp₁
          have hmap : (Γ.map tyShift).map (tySubst (tyCons D σ)) = Γ.map (tySubst σ) := by
            simp only [List.map_map, Function.comp_def]
            exact List.map_congr_left fun X _ => tySubst_tyCons_tyShift D σ X
          rwa [hmap] at hres
  | @tapp Γ t A₀ B₀ hall ih =>
      intro s hs σ A B hp
      have hshapeAll : AllArrow (FTy.all A₀) := allArrow_of_lam hall s hs
      have hshape : AllArrow A₀ := hshapeAll
      have hp' : Peel (fun i => tySubst σ (tyScons B₀ i)) A₀ A B :=
        peel_tySubst A₀ hshape σ (tyScons B₀) A B hp
      have hcomp : (fun i => tySubst σ (tyScons B₀ i)) = tyCons (tySubst σ B₀) σ := by
        funext i
        cases i with
        | zero => rfl
        | succ i => rfl
      rw [hcomp] at hp'
      exact ih s hs σ A B (Peel.all (tySubst σ B₀) hp')

/-- **The generation lemma**: an abstraction of a function type has a body of the codomain type in
the extended context. -/
theorem Typing.gen_lam {Γ : List FTy} {s : Lambda} {A B : FTy}
    (h : Typing Γ (Lambda.lam s) (FTy.arrow A B)) : Typing (A :: Γ) s B := by
  have hp : Peel FTy.var (FTy.arrow A B) A B := by
    have := Peel.arrow (s := FTy.var) (A := A) (B := B)
    rwa [tySubst_var_id, tySubst_var_id] at this
  have hres := h.gen_lam_peel s rfl FTy.var A B hp
  have hmap : Γ.map (tySubst FTy.var) = Γ := by
    refine (List.map_congr_left fun X _ => tySubst_var_id X).trans ?_
    exact List.map_id Γ
  rwa [hmap] at hres

/-! ### Subject reduction -/

/-- **Subject reduction**: β-reduction preserves typing. -/
theorem Typing.preservation {Γ : List FTy} {t : Lambda} {A : FTy} (h : Typing Γ t A) :
    ∀ t' : Lambda, Lambda.step t t' → Typing Γ t' A := by
  induction h with
  | var _ => intro t' hs; cases hs
  | @app Γ a b A₀ B ha hb iha ihb =>
      intro t' hs
      cases hs with
      | beta s u =>
          exact (ha.gen_lam).subst_zero hb
      | app_left _ a' _ hstep => exact Typing.app (iha a' hstep) hb
      | app_right _ _ b' hstep => exact Typing.app ha (ihb b' hstep)
  | @lam Γ t A₀ B _ ih =>
      intro t' hs
      cases hs with
      | lam _ s' hstep => exact Typing.lam (ih s' hstep)
  | tlam _ ih => intro t' hs; exact Typing.tlam (ih t' hs)
  | tapp B _ ih => intro t' hs; exact Typing.tapp B (ih t' hs)

/-- Subject reduction for many steps. -/
theorem Typing.preservation_reduces {Γ : List FTy} {t t' : Lambda} {A : FTy}
    (h : Typing Γ t A) (hr : Lambda.reduces t t') : Typing Γ t' A := by
  induction hr with
  | refl _ => exact h
  | step t₁ t₂ _ hstep _ ih => exact ih (h.preservation t₂ hstep)

end SystemF
