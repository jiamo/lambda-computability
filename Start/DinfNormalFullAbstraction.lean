/-
# Full abstraction of `D∞` on closed normal forms

Adequacy (`Start/DinfAdequacy.lean`) gives one half of full abstraction: terms with the same
denotation in `D∞` are observationally equivalent.  This file proves the converse half for
*closed β-normal forms*, which is the finite case of Wadsworth's theorem:

* `ScottDinf.not_obsEqHnf_of_separable` — separable terms are observationally distinguishable;
  the separating arguments are turned into the context `C[X] = X a₁ … aₖ Ω I`, which converges to
  `I` on one side and to `Ω` on the other;
* `ScottDinf.ddenot_eq_of_obsEqHnf_normal` — observationally equivalent closed normal forms have
  the same denotation.  Böhm's theorem in its η-general form
  (`Lambda.separable_toTerm_of_not_tagEq`) says that two closed normal forms that are not η-equal
  are separable, and `ScottDinf.ddenot_toTerm_eq_of_tagEq` says that η-equal ones are equal in
  `D∞`;
* `ScottDinf.obsEqHnf_iff_ddenot_eq_normal` — **full abstraction on closed normal forms**, and
  `ScottDinf.obsEqHnf_iff_ddenot_eq_of_normalizes` — the same for closed terms that *have* a
  β-normal form;
* `ScottDinf.ddenot_eq_of_obsEqHnf_of_not_hasHnf` — full abstraction at the other extreme, the
  head-divergent terms.

Full abstraction of `D∞` for arbitrary terms (Wadsworth's theorem) needs the separation theorem
for infinite Böhm trees, together with the infinite η-expansions that `D∞` identifies; it is not
proved here.
-/

import Start.DinfBohmEta
import Start.DinfApprox

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- Applying the term in the hole of a context to a list of arguments. -/
def Ctx.appListC : Ctx → List Lambda → Ctx
  | C, [] => C
  | C, a :: l => Ctx.appListC (C.appL a) l

theorem Ctx.fill_appListC : ∀ (l : List Lambda) (C : Ctx) (t : Lambda),
    (C.appListC l).fill t = appList (C.fill t) l := by
  intro l
  induction l with
  | nil => intro C t; rfl
  | cons a l ih => intro C t; rw [Ctx.appListC, ih, appList_cons]; rfl

/-- The context `X a₁ … aₖ Ω I` used to distinguish two separable terms. -/
def sepCtx (args : List Lambda) : Ctx :=
  Ctx.appL (Ctx.appL (Ctx.appListC Ctx.hole args) Lambda.omega) Lambda.I

theorem fill_sepCtx (args : List Lambda) (t : Lambda) :
    (sepCtx args).fill t
      = Lambda.app (Lambda.app (appList t args) Lambda.omega) Lambda.I := by
  rw [sepCtx]
  change Lambda.app (Lambda.app ((Ctx.appListC Ctx.hole args).fill t) Lambda.omega) Lambda.I = _
  rw [Ctx.fill_appListC]
  rfl

end Lambda

namespace ScottDinf

open Lambda

/-- On the `true` side the distinguishing context diverges. -/
theorem reduces_sepCtx_true {M : Lambda} {args : List Lambda}
    (h : Lambda.reduces (appList M args) Lambda.true) :
    Lambda.reduces ((sepCtx args).fill M) Lambda.omega := by
  rw [fill_sepCtx]
  exact Lambda.reduces_trans
    (Lambda.reduces_app_left (Lambda.reduces_app_left h)) (Lambda.true_works _ _)

/-- On the `false` side the distinguishing context converges to the identity. -/
theorem reduces_sepCtx_false {N : Lambda} {args : List Lambda}
    (h : Lambda.reduces (appList N args) Lambda.false) :
    Lambda.reduces ((sepCtx args).fill N) Lambda.I := by
  rw [fill_sepCtx]
  exact Lambda.reduces_trans
    (Lambda.reduces_app_left (Lambda.reduces_app_left h)) (Lambda.false_works _ _)

/-- **Separable terms are observationally distinguishable.**  The context `X a₁ … aₖ Ω I` sends
the first term to `Ω`, which has no head normal form, and the second to `I`, which is one. -/
theorem not_obsEqHnf_of_separable {M N : Lambda} (h : Separable M N) : ¬ ObsEqHnf M N := by
  obtain ⟨args, _, hM, hN⟩ := h
  intro hobs
  have hCN : HasHnf ((sepCtx args).fill N) :=
    HasHnf.of_reduces (reduces_sepCtx_false hN)
      (hasHnf_of_isHnf (IsHnf.lam (IsHnf.neutral (Neutral.var 0))))
  have hCM : ¬ HasHnf ((sepCtx args).fill M) := by
    refine not_hasHnf_of_ddenot_eq_botDinf fun ρ => ?_
    rw [ddenot_reduces (reduces_sepCtx_true hM) ρ, ddenot_omega]
  exact hCM ((hobs (sepCtx args)).2 hCN)

/-- **Observationally equivalent closed normal forms have the same denotation in `D∞`.**  This is
the finite case of Wadsworth's full abstraction theorem. -/
theorem ddenot_eq_of_obsEqHnf_normal {M N : Lambda} (hM : Lambda.is_normal M)
    (hN : Lambda.is_normal N) (hMc : Lambda.IsClosed M) (hNc : Lambda.IsClosed N)
    (hobs : Lambda.ObsEqHnf M N) (ρ₁ ρ₂ : DEnv) : ddenot M ρ₁ = ddenot N ρ₂ := by
  obtain ⟨x, rfl⟩ := Lambda.is_normal_iff_exists_bohmNF.1 hM
  obtain ⟨y, rfl⟩ := Lambda.is_normal_iff_exists_bohmNF.1 hN
  have hx := BohmNF.freeVarsBelow_zero_of_isClosed hMc
  have hy := BohmNF.freeVarsBelow_zero_of_isClosed hNc
  by_cases hteq : TagEq 0 (fun _ => 0) x (fun _ => 0) y
  · exact ddenot_toTerm_eq_of_tagEq hx hy hteq ρ₁ ρ₂
  · exact absurd hobs
      (not_obsEqHnf_of_separable (Lambda.separable_toTerm_of_not_tagEq hx hy hteq))

/-- **Full abstraction of `D∞` on closed normal forms**: two closed β-normal forms are
observationally equivalent exactly when they have the same denotation. -/
theorem obsEqHnf_iff_ddenot_eq_normal {M N : Lambda} (hM : Lambda.is_normal M)
    (hN : Lambda.is_normal N) (hMc : Lambda.IsClosed M) (hNc : Lambda.IsClosed N) :
    Lambda.ObsEqHnf M N ↔ ∀ ρ : DEnv, ddenot M ρ = ddenot N ρ :=
  ⟨fun hobs ρ => ddenot_eq_of_obsEqHnf_normal hM hN hMc hNc hobs ρ ρ, obsEqHnf_of_ddenot_eq⟩

/-- **Full abstraction of `D∞` on closed normalizing terms**: the same statement for closed terms
that merely *have* a β-normal form.  Soundness moves each term to its normal form, both
denotationally and — by adequacy — observationally. -/
theorem obsEqHnf_iff_ddenot_eq_of_normalizes {M N M₀ N₀ : Lambda} (hMc : Lambda.IsClosed M)
    (hNc : Lambda.IsClosed N) (hM : Lambda.reduces M M₀) (hN : Lambda.reduces N N₀)
    (hM₀ : Lambda.is_normal M₀) (hN₀ : Lambda.is_normal N₀) :
    Lambda.ObsEqHnf M N ↔ ∀ ρ : DEnv, ddenot M ρ = ddenot N ρ := by
  have hMd : ∀ ρ : DEnv, ddenot M ρ = ddenot M₀ ρ := fun ρ => ddenot_reduces hM ρ
  have hNd : ∀ ρ : DEnv, ddenot N ρ = ddenot N₀ ρ := fun ρ => ddenot_reduces hN ρ
  refine ⟨fun hobs ρ => ?_, obsEqHnf_of_ddenot_eq⟩
  rw [hMd, hNd]
  exact ddenot_eq_of_obsEqHnf_normal hM₀ hN₀ (hMc.reduces hM) (hNc.reduces hN)
    (((obsEqHnf_of_ddenot_eq hMd).symm.trans hobs).trans (obsEqHnf_of_ddenot_eq hNd)) ρ ρ

/-- **Full abstraction of `D∞` at the head-divergent terms**: a term observationally equivalent
to a term without head normal form has the same (least) denotation.  Here no hypothesis on the
second term is needed. -/
theorem ddenot_eq_of_obsEqHnf_of_not_hasHnf {M N : Lambda} (hM : ¬ Lambda.HasHnf M)
    (hobs : Lambda.ObsEqHnf M N) (ρ : DEnv) : ddenot M ρ = ddenot N ρ := by
  have hN : ¬ Lambda.HasHnf N := fun h => hM ((hobs Ctx.hole).2 h)
  rw [ddenot_eq_botDinf_of_not_hasHnf hM, ddenot_eq_botDinf_of_not_hasHnf hN]

end ScottDinf

end
