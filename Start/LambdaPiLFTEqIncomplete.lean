/-
**Completeness fails for `TEq`** — task `M23-LF-EQUIV-COMPLETE`.

The declarative equality `TEq` of `Start/LambdaPiLFEquiv.lean` has the β-rule

    TEq.beta : Typing (A :: Γ) b B → Typing Γ a A → TEq Γ (app (lam A b) a) (b[a]) (B[a])

with no condition on the domain `A`.  In `λΠ` an abstraction is typable only over a *type*
(`Rule s t := s = ∗`), but `TEq.beta` also accepts a *kind* as the domain, so it relates the
untypable type-level redex `(λx:∗. x) (Πy:X. X)` to its contractum `Πy:X. X`.  The two sides
have different skeletons (`base` and `base → base`), and the type-directed algorithm compares
the domains of two products only when their skeletons agree.  Put the redex in the domain of a
product, and `TEq` derives an equation the algorithm rejects:

    X : ∗  ⊢  Πz:((λx:∗. x) (Πy:X. X)). X  ≡  Πz:(Πy:X. X). X  :  ∗.

* `LambdaPi.ti_wf`, `LambdaPi.ti_teq` — the context `X : ∗` is well formed and the equation is
  derivable;
* `LambdaPi.ti_not_algEq` — the algorithm rejects it (`WhRed.pi_eq`: a product is weak head
  normal, and the side condition of `Eqv.basePi` fails);
* **`LambdaPi.teq_not_complete`** — completeness `TEq Γ M N A → AlgEq ⌊Γ⌋ M N ⌊A⌋` is false.

So the exit criterion of `M23-LF-EQUIV-COMPLETE` cannot be met for `TEq` as defined: the
declarative judgement itself must be corrected (the β-rule must ask for a typable abstraction),
which is done with the βη-typing of `Start/LambdaPiTypingE.lean`.
-/

import Start.LambdaPiLFEquiv

set_option autoImplicit false

namespace LambdaPi

open Tm

/-- A product is weak head normal. -/
theorem WhRed.pi_eq {A B u : Tm} (h : WhRed (pi A B) u) : u = pi A B := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; cases hs

/-- The context `X : ∗`. -/
def tiΓ : Ctx := [sort Srt.star]

/-- `Πy:X. X`, a type with an arrow skeleton. -/
def tiA : Tm := pi (var 0) (var 1)

/-- `(λx:∗. x) (Πy:X. X)`: an abstraction over the kind `∗`, which `λΠ` cannot type. -/
def tiR : Tm := app (lam (sort Srt.star) (var 0)) tiA

theorem ti_wf : Wf tiΓ := Wf.cons (s := Srt.box) Wf.nil (Typing.ax [])

theorem ti_typing_A : Typing tiΓ tiA (sort Srt.star) :=
  Typing.pi (s := Srt.star) (t := Srt.star) rfl (Typing.var (Lookup.zero _ _))
    (Typing.var (Lookup.succ _ (Lookup.zero _ _)))

/-- `TEq.beta` with the kind `∗` as the domain. -/
theorem ti_teq_redex : TEq tiΓ tiR tiA (sort Srt.star) :=
  TEq.beta (A := sort Srt.star) (b := var 0) (B := sort Srt.star)
    (Typing.var (Lookup.zero _ _)) ti_typing_A

/-- **The equation**: `Πz:((λx:∗. x) (Πy:X. X)). X ≡ Πz:(Πy:X. X). X : ∗`. -/
theorem ti_teq : TEq tiΓ (pi tiR (var 1)) (pi tiA (var 1)) (sort Srt.star) :=
  TEq.pi (s := Srt.star) (t := Srt.star) rfl ti_teq_redex
    (TEq.refl (Typing.var (Lookup.succ _ (Lookup.zero _ _))))

/-- The two domains have different skeletons. -/
theorem ti_skel_ne : skel (skelCtx tiΓ) tiR ≠ skel (skelCtx tiΓ) tiA := by
  simp [tiR, tiA, tiΓ, skel]

/-- **The algorithm rejects the equation.** -/
theorem ti_not_algEq :
    ¬ AlgEq (skelCtx tiΓ) (pi tiR (var 1)) (pi tiA (var 1)) (skel (skelCtx tiΓ) (sort Srt.star)) := by
  intro h
  rw [skel_sort] at h
  cases h with
  | basePath hM _ hp =>
      rw [WhRed.pi_eq hM] at hp
      cases hp
  | baseSort hM _ => exact Tm.noConfusion (WhRed.pi_eq hM)
  | basePi hM hN _ hsk _ =>
      have e₁ := WhRed.pi_eq hM
      have e₂ := WhRed.pi_eq hN
      simp only [pi.injEq] at e₁ e₂
      obtain ⟨rfl, rfl⟩ := e₁
      obtain ⟨rfl, rfl⟩ := e₂
      exact ti_skel_ne hsk

/-- **Completeness fails for `TEq`**: there are a well-formed context and a derivable equation
`Γ ⊢ M ≡ N : A` that the type-directed algorithm rejects at the skeleton of `A`. -/
theorem teq_not_complete :
    ∃ (Γ : Ctx) (M N A : Tm), Wf Γ ∧ TEq Γ M N A ∧
      ¬ AlgEq (skelCtx Γ) M N (skel (skelCtx Γ) A) :=
  ⟨tiΓ, _, _, _, ti_wf, ti_teq, ti_not_algEq⟩

/-- The left-hand side of the equation is not typable: `λx:∗. x` would need the rule `(□, □)`. -/
theorem ti_redex_untyped (T : Tm) : ¬ Typing tiΓ tiR T := by
  intro h
  obtain ⟨A, B, hf, -, -⟩ := h.app_inv
  obtain ⟨B₀, s₀, hP, -, -⟩ := hf.lam_inv
  obtain ⟨s, t, hr, hA, -, -⟩ := hP.pi_inv
  cases hr
  obtain ⟨-, hc⟩ := hA.sort_inv
  exact Srt.noConfusion (sort_conv_inj hc)

end LambdaPi
