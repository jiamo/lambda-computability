/-
**The interpretation of `λΠ` is invariant under conversion.**

`Start/LambdaPiInterp.lean` interprets the *raw* expressions of the calculus, so β-reduction has to
be shown to preserve what an expression denotes.  Together with confluence
(`LambdaPi.Conv.church_rosser`) and functionality (`Start/LambdaPiInterpFun.lean`) this gives the
invariance of the interpretation under conversion, which is what the conversion rule of the typing
judgement needs.

* `LambdaPi.TmI.var_inv`, `LambdaPi.TmI.pi_inv`, `LambdaPi.TmI.lam_inv`, `LambdaPi.TmI.app_inv` —
  inversion of the interpretation of a term, with the type and the value left general;
* `LambdaPi.TmI.not_sort`, `LambdaPi.TyI.not_sort_box`, `LambdaPi.TyI.sort_star_inv` — the sorts:
  no sort denotes a *term*, `□` denotes nothing at all, and `∗` denotes the universe;
* `LambdaPi.Step.interp_preserves` — **β-reduction preserves the interpretation**.  The
  interesting case is the β-redex itself, where the β-law of the model (`SmallPi.app_lam`) and the
  substitution lemma of `Start/LambdaPiInterpSub.lean` (`TmI.inst`) match the two sides;
* `LambdaPi.Red.interp_preserves` — hence so does many-step reduction;
* `LambdaPi.TyI.conv_eq`, `LambdaPi.TmI.conv_eq` — **convertible expressions denote the same
  thing**: pass to a common reduct and use functionality.

The hypothesis `LambdaPi.Model.PiInj` is needed for exactly the reason it is needed in
`Start/LambdaPiInterpFun.lean`: a β-redex `(λx:A. b) g` does not record the domain of the type of
its function part, so the two interpretations of the redex must be matched through the product.
-/

import Start.LambdaPiInterpSub
import Start.LambdaPiInterpFun

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory

namespace LambdaPi

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

/-! ### Inversion of the interpretation -/

/-- No sort denotes a term: the sort `∗` denotes a *type*, and `□` denotes nothing. -/
theorem TmI.not_sort {Γ : C} {s : SemCtx M Γ} {k : Srt} {A : M.T.Ty Γ} {x : Cwa.Tm M.T Γ A} :
    ¬ TmI s (Tm.sort k) A x := by
  rintro ⟨⟩

/-- The top sort `□` denotes no type of the model. -/
theorem TyI.not_sort_box {Γ : C} {s : SemCtx M Γ} {A : M.T.Ty Γ} :
    ¬ TyI s (Tm.sort Srt.box) A := by
  intro h
  cases h with
  | el hc => exact TmI.not_sort hc

/-- The sort `∗` denotes the universe, and nothing else. -/
theorem TyI.sort_star_inv {Γ : C} {s : SemCtx M Γ} {A : M.T.Ty Γ}
    (h : TyI s (Tm.sort Srt.star) A) : A = M.Un.U Γ := by
  cases h with
  | star => rfl
  | el hc => exact absurd hc TmI.not_sort

/-- Inversion for a variable. -/
theorem TmI.var_inv {Γ : C} {s : SemCtx M Γ} {n : ℕ} {A : M.T.Ty Γ} {x : Cwa.Tm M.T Γ A}
    (h : TmI s (Tm.var n) A x) : s.varVal n = some ⟨A, x⟩ := by
  cases h with
  | var hv => exact hv

/-- Inversion for a product, as a term of the universe. -/
theorem TmI.pi_inv {Γ : C} {s : SemCtx M Γ} {A B : Tm} {P : M.T.Ty Γ} {y : Cwa.Tm M.T Γ P}
    (h : TmI s (Tm.pi A B) P y) :
    ∃ (a : Cwa.Tm M.T Γ (M.Un.U Γ))
      (b : Cwa.Tm M.T (M.T.ext Γ (M.Un.El a)) (M.Un.U (M.T.ext Γ (M.Un.El a)))),
      TmI s A (M.Un.U Γ) a ∧ TmI (s.cons (M.Un.El a)) B (M.Un.U _) b ∧
        (⟨P, y⟩ : TmVal M Γ) = ⟨M.Un.U Γ, M.PC.code a b⟩ := by
  cases h with
  | @pi _ _ _ _ a b ha hb => exact ⟨a, b, ha, hb, rfl⟩

/-- Inversion for an abstraction. -/
theorem TmI.lam_inv {Γ : C} {s : SemCtx M Γ} {A b : Tm} {P : M.T.Ty Γ} {y : Cwa.Tm M.T Γ P}
    (h : TmI s (Tm.lam A b) P y) :
    ∃ (a : Cwa.Tm M.T Γ (M.Un.U Γ)) (B' : M.T.Ty (M.T.ext Γ (M.Un.El a)))
      (x : Cwa.Tm M.T (M.T.ext Γ (M.Un.El a)) B'),
      TmI s A (M.Un.U Γ) a ∧ TmI (s.cons (M.Un.El a)) b B' x ∧
        (⟨P, y⟩ : TmVal M Γ) = ⟨M.SP.Pi a B', M.SP.lam x⟩ := by
  cases h with
  | @lam _ _ _ _ a B' x ha hb => exact ⟨a, B', x, ha, hb, rfl⟩

/-- Inversion for an application. -/
theorem TmI.app_inv {Γ : C} {s : SemCtx M Γ} {f g : Tm} {P : M.T.Ty Γ} {y : Cwa.Tm M.T Γ P}
    (h : TmI s (Tm.app f g) P y) :
    ∃ (a : Cwa.Tm M.T Γ (M.Un.U Γ)) (B' : M.T.Ty (M.T.ext Γ (M.Un.El a)))
      (f' : Cwa.Tm M.T Γ (M.SP.Pi a B')) (g' : Cwa.Tm M.T Γ (M.Un.El a)),
      TmI s f (M.SP.Pi a B') f' ∧ TmI s g (M.Un.El a) g' ∧
        (⟨P, y⟩ : TmVal M Γ) = ⟨M.T.tySub g'.1 B', M.T.tmSub g'.1 (M.SP.app f')⟩ := by
  cases h with
  | @app _ _ _ _ a B' f' g' hf hg => exact ⟨a, B', f', g', hf, hg, rfl⟩

/-! ### Reduction preserves the interpretation -/

/-- **A step of β-reduction preserves the interpretation**, both of a type and of a term.  The
β-redex is matched by the β-law of the model and the substitution lemma; every other case is a
congruence, and follows from the inductive hypothesis by rebuilding the same rule. -/
theorem Step.interp_preserves (hinj : M.PiInj) {t t' : Tm} (h : Step t t') :
    (∀ (Γ : C) (s : SemCtx M Γ) (A : M.T.Ty Γ), TyI s t A → TyI s t' A) ∧
    (∀ (Γ : C) (s : SemCtx M Γ) (A : M.T.Ty Γ) (x : Cwa.Tm M.T Γ A),
      TmI s t A x → TmI s t' A x) := by
  induction h with
  | beta A b g =>
      have htm : ∀ (Γ : C) (s : SemCtx M Γ) (A₀ : M.T.Ty Γ) (y : Cwa.Tm M.T Γ A₀),
          TmI s (Tm.app (Tm.lam A b) g) A₀ y → TmI s (b[g]) A₀ y := by
        intro Γ s A₀ y h
        obtain ⟨a, B', f', g', hf, hg, heq⟩ := h.app_inv
        obtain ⟨a₁, B₁, x, _, hb, heq2⟩ := hf.lam_inv
        rcases Sigma.mk.inj_iff.mp heq2 with ⟨hPi, hf2⟩
        rcases Sigma.mk.inj_iff.mp (hinj hPi) with ⟨haa, hBB⟩
        subst haa
        cases eq_of_heq hBB
        cases eq_of_heq hf2
        rw [M.SP.app_lam x] at heq
        exact TmI.cast_val (TmI.inst hb hg) heq.symm
      refine ⟨fun Γ s A₀ hTy => ?_, htm⟩
      cases hTy with
      | el hc => exact TyI.el (htm _ _ _ _ hc)
  | @appL f f' g _ ih =>
      have htm : ∀ (Γ : C) (s : SemCtx M Γ) (A₀ : M.T.Ty Γ) (y : Cwa.Tm M.T Γ A₀),
          TmI s (Tm.app f g) A₀ y → TmI s (Tm.app f' g) A₀ y := by
        intro Γ s A₀ y h
        obtain ⟨a, B', f', g', hf, hg, heq⟩ := h.app_inv
        exact TmI.cast_val (TmI.app (ih.2 _ _ _ _ hf) hg) heq.symm
      refine ⟨fun Γ s A₀ hTy => ?_, htm⟩
      cases hTy with
      | el hc => exact TyI.el (htm _ _ _ _ hc)
  | @appR f g g' _ ih =>
      have htm : ∀ (Γ : C) (s : SemCtx M Γ) (A₀ : M.T.Ty Γ) (y : Cwa.Tm M.T Γ A₀),
          TmI s (Tm.app f g) A₀ y → TmI s (Tm.app f g') A₀ y := by
        intro Γ s A₀ y h
        obtain ⟨a, B', f', g', hf, hg, heq⟩ := h.app_inv
        exact TmI.cast_val (TmI.app hf (ih.2 _ _ _ _ hg)) heq.symm
      refine ⟨fun Γ s A₀ hTy => ?_, htm⟩
      cases hTy with
      | el hc => exact TyI.el (htm _ _ _ _ hc)
  | @lamL A A' b _ ih =>
      have htm : ∀ (Γ : C) (s : SemCtx M Γ) (A₀ : M.T.Ty Γ) (y : Cwa.Tm M.T Γ A₀),
          TmI s (Tm.lam A b) A₀ y → TmI s (Tm.lam A' b) A₀ y := by
        intro Γ s A₀ y h
        obtain ⟨a, B', x, ha, hb, heq⟩ := h.lam_inv
        exact TmI.cast_val (TmI.lam (ih.2 _ _ _ _ ha) hb) heq.symm
      refine ⟨fun Γ s A₀ hTy => ?_, htm⟩
      cases hTy with
      | el hc => exact TyI.el (htm _ _ _ _ hc)
  | @lamR A b b' _ ih =>
      have htm : ∀ (Γ : C) (s : SemCtx M Γ) (A₀ : M.T.Ty Γ) (y : Cwa.Tm M.T Γ A₀),
          TmI s (Tm.lam A b) A₀ y → TmI s (Tm.lam A b') A₀ y := by
        intro Γ s A₀ y h
        obtain ⟨a, B', x, ha, hb, heq⟩ := h.lam_inv
        exact TmI.cast_val (TmI.lam ha (ih.2 _ _ _ _ hb)) heq.symm
      refine ⟨fun Γ s A₀ hTy => ?_, htm⟩
      cases hTy with
      | el hc => exact TyI.el (htm _ _ _ _ hc)
  | @piL A A' B _ ih =>
      have htm : ∀ (Γ : C) (s : SemCtx M Γ) (A₀ : M.T.Ty Γ) (y : Cwa.Tm M.T Γ A₀),
          TmI s (Tm.pi A B) A₀ y → TmI s (Tm.pi A' B) A₀ y := by
        intro Γ s A₀ y h
        obtain ⟨a, b, ha, hb, heq⟩ := h.pi_inv
        exact TmI.cast_val (TmI.pi (ih.2 _ _ _ _ ha) hb) heq.symm
      refine ⟨fun Γ s A₀ hTy => ?_, htm⟩
      cases hTy with
      | el hc => exact TyI.el (htm _ _ _ _ hc)
      | pi ha hB => exact TyI.pi (ih.2 _ _ _ _ ha) hB
  | @piR A B B' _ ih =>
      have htm : ∀ (Γ : C) (s : SemCtx M Γ) (A₀ : M.T.Ty Γ) (y : Cwa.Tm M.T Γ A₀),
          TmI s (Tm.pi A B) A₀ y → TmI s (Tm.pi A B') A₀ y := by
        intro Γ s A₀ y h
        obtain ⟨a, b, ha, hb, heq⟩ := h.pi_inv
        exact TmI.cast_val (TmI.pi ha (ih.2 _ _ _ _ hb)) heq.symm
      refine ⟨fun Γ s A₀ hTy => ?_, htm⟩
      cases hTy with
      | el hc => exact TyI.el (htm _ _ _ _ hc)
      | pi ha hB => exact TyI.pi ha (ih.1 _ _ _ hB)

/-- **Many-step β-reduction preserves the interpretation of a type.** -/
theorem Red.interp_preserves_ty (hinj : M.PiInj) {t t' : Tm} (h : Red t t') {Γ : C}
    {s : SemCtx M Γ} {A : M.T.Ty Γ} (hA : TyI s t A) : TyI s t' A := by
  induction h with
  | refl => exact hA
  | tail _ hs ih => exact (hs.interp_preserves hinj).1 _ _ _ ih

/-- **Many-step β-reduction preserves the interpretation of a term.** -/
theorem Red.interp_preserves_tm (hinj : M.PiInj) {t t' : Tm} (h : Red t t') {Γ : C}
    {s : SemCtx M Γ} {A : M.T.Ty Γ} {x : Cwa.Tm M.T Γ A} (hx : TmI s t A x) : TmI s t' A x := by
  induction h with
  | refl => exact hx
  | tail _ hs ih => exact (hs.interp_preserves hinj).2 _ _ _ _ ih

/-! ### Invariance under conversion -/

/-- **Convertible expressions denote the same type.** -/
theorem TyI.conv_eq (hinj : M.PiInj) {Γ : C} {s : SemCtx M Γ} {t u : Tm} {A A' : M.T.Ty Γ}
    (hc : Conv t u) (h : TyI s t A) (h' : TyI s u A') : A = A' := by
  obtain ⟨v, h1, h2⟩ := hc.church_rosser
  exact TyI.unique_of_piInj hinj (h1.interp_preserves_ty hinj h) (h2.interp_preserves_ty hinj h')

/-- **Convertible expressions denote the same term.** -/
theorem TmI.conv_eq (hinj : M.PiInj) {Γ : C} {s : SemCtx M Γ} {t u : Tm} {A A' : M.T.Ty Γ}
    {x : Cwa.Tm M.T Γ A} {x' : Cwa.Tm M.T Γ A'} (hc : Conv t u) (h : TmI s t A x)
    (h' : TmI s u A' x') : (⟨A, x⟩ : TmVal M Γ) = ⟨A', x'⟩ := by
  obtain ⟨v, h1, h2⟩ := hc.church_rosser
  exact TmI.unique_of_piInj hinj (h1.interp_preserves_tm hinj h) (h2.interp_preserves_tm hinj h')

end LambdaPi
