/-
**The syntactic model of `λΠ` is coherent, so its substitution of terms is functorial.**

`Start/CwaSubFunctorial.lean` isolates the coherence law `Cwa.ExtCoherent` that a category with
attributes needs for the substitution of terms — which is defined by the universal property of
context extension, and is therefore only determined up to that property — to be functorial.  This
file checks the law for the syntactic model `LambdaPiFull.syntactic` of `Start/LambdaPiFull.lean`:
the action of a substitution on an extended context is the lifting `up` of the calculus, and `up`
takes the identity substitution to the identity and a composite to the composite.  Consequently
substituting the identity in a term of `λΠ` does nothing and substituting a composite is
substituting twice, *in the categorical sense* — the syntactic statements are of course already
available, the point being that the categorical operation agrees with them.

Main results:

* `LambdaPiFull.extendQ_id`, `LambdaPiFull.extendQ_comp` — the action of a substitution on extended
  contexts is functorial;
* `LambdaPiFull.extCoherent_syntactic` — **the syntactic model satisfies the coherence law**;
* `LambdaPiFull.tmSub_id_syntactic`, `LambdaPiFull.tmSub_comp_syntactic` — hence its substitution
  of terms is functorial.
-/

import Start.LambdaPiUniv
import Start.CwaSubFunctorial

set_option relaxedAutoImplicit false
set_option autoImplicit false

open CategoryTheory Limits

namespace LambdaPiFull

open LambdaPi LambdaPiCat LambdaPiUniv

/-- Two substitutions of the syntactic category are equal when their representatives are
convertible at every variable of the target context. -/
theorem hom_ext_out {Γ Δ : Ob} {f g : Δ ⟶ Γ}
    (h : ∀ n, n < Γ.ctx.length → Conv (f.out.sub n) (g.out.sub n)) : f = g := by
  conv_lhs => rw [← Quotient.out_eq f]
  conv_rhs => rw [← Quotient.out_eq g]
  exact mk_eq h

/-- The length of an extended context. -/
theorem extOb_length {Γ : Ob} (A : LambdaPiFull.TyQ Γ) :
    (extOb Γ A).ctx.length = Γ.ctx.length + 1 := rfl

/-- Lifting preserves conversion of substitutions. -/
theorem conv_up_congr {k : ℕ} {σ τ : ℕ → Tm} (h : ∀ m, m < k → Conv (σ m) (τ m)) :
    ∀ n, n < k + 1 → Conv (up σ n) (up τ n) := by
  intro n hn
  cases n with
  | zero => exact Conv.refl _
  | succ m =>
      simpa only [up_succ] using (h m (by omega)).rename Nat.succ

/-- The lifting of a substitution is bounded by the extended context. -/
theorem bnd_up {Γ Δ : Ob} (f : Δ ⟶ Γ) {n : ℕ} (hn : n < Γ.ctx.length + 1) :
    Bnd (Δ.ctx.length + 1) (up (Quotient.out f).sub n) := by
  cases n with
  | zero => simp
  | succ m =>
      have h := (Quotient.out f).bnd (n := m) (by omega)
      simpa only [up_succ, shift] using h.shift

/-- **The identity substitution acts on an extended context as the identity.** -/
theorem extendQ_id {Γ : Ob} (A : LambdaPiFull.TyQ Γ) :
    extendQ (𝟙 Γ) A = eqToHom (congrArg (extOb Γ) (tySubQ_id A)) := by
  refine hom_ext_out ?_
  intro n hn
  refine (extendQ_out_conv (𝟙 Γ) A hn).trans ?_
  refine Conv.trans ?_ (eqToHom_out_conv _ hn).symm
  have hup : ∀ m, m < Γ.ctx.length → Conv ((Quotient.out (𝟙 Γ : Γ ⟶ Γ)).sub m) (ids m) :=
    fun m hm => id_out_conv _ rfl hm
  have := conv_up_congr hup n (by simpa [extOb_length] using hn)
  simpa only [up_ids, ids_apply] using this

/-- **A composite substitution acts on an extended context as the composite.** -/
theorem extendQ_comp {Γ Δ Θ : Ob} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (A : LambdaPiFull.TyQ Γ) :
    extendQ (τ ≫ σ) A
      = eqToHom (congrArg (extOb Θ) (tySubQ_comp σ τ A)) ≫ extendQ τ (tySubQ σ A)
          ≫ extendQ σ A := by
  refine hom_ext_out ?_
  intro n hn
  refine (extendQ_out_conv (τ ≫ σ) A hn).trans ?_
  -- the right-hand side, read off its representatives
  have hbnd : Bnd (extOb Θ (tySubQ (τ ≫ σ) A)).ctx.length
      ((extendQ τ (tySubQ σ A) ≫ extendQ σ A).out.sub n) := by
    have := (extendQ τ (tySubQ σ A) ≫ extendQ σ A).out.bnd hn
    simpa only [extOb_length] using this
  have h₁ := comp_out_conv (eqToHom (congrArg (extOb Θ) (tySubQ_comp σ τ A)))
    (extendQ τ (tySubQ σ A) ≫ extendQ σ A) hn
  have h₂ : Conv (subst (eqToHom (congrArg (extOb Θ) (tySubQ_comp σ τ A))).out.sub
      ((extendQ τ (tySubQ σ A) ≫ extendQ σ A).out.sub n))
      ((extendQ τ (tySubQ σ A) ≫ extendQ σ A).out.sub n) :=
    subst_eqToHom_conv _ hbnd
  refine Conv.trans ?_ (h₁.trans h₂).symm
  -- the inner composite
  have h₃ := comp_out_conv (extendQ τ (tySubQ σ A)) (extendQ σ A) hn
  refine Conv.trans ?_ h₃.symm
  have h₄ : Conv (subst (extendQ τ (tySubQ σ A)).out.sub ((extendQ σ A).out.sub n))
      (subst (up τ.out.sub) (up σ.out.sub n)) := by
    refine Conv.trans ?_ (conv_subst_congr
      (k := (extOb Δ (tySubQ σ A)).ctx.length)
      (σ := (extendQ τ (tySubQ σ A)).out.sub) (τ := up τ.out.sub)
      (t := up σ.out.sub n) ?_ ?_)
    · exact ((extendQ_out_conv σ A hn).subst _)
    · simpa only [extOb_length] using bnd_up σ (by simpa [extOb_length] using hn)
    · intro m hm
      exact extendQ_out_conv τ (tySubQ σ A) (by simpa [extOb_length] using hm)
  refine Conv.trans ?_ h₄.symm
  rw [subst_up_subst]
  refine conv_up_congr (k := Γ.ctx.length) ?_ n (by simpa [extOb_length] using hn)
  intro m hm
  exact comp_out_conv τ σ hm

/-- **The syntactic model of `λΠ` satisfies the coherence law.** -/
theorem extCoherent_syntactic : Cwa.ExtCoherent syntactic where
  extend_id A := extendQ_id A
  extend_comp σ τ A := extendQ_comp σ τ A

/-- **In the syntactic model, substituting the identity in a term does nothing.** -/
theorem tmSub_id_syntactic {Γ : Ob} {A : LambdaPiFull.TyQ Γ} (a : Cwa.Tm syntactic Γ A) :
    Cwa.tmCast (syntactic.tySub_id A) (Cwa.tmSub (T := syntactic) (𝟙 Γ) a) = a :=
  extCoherent_syntactic.tmSub_id a

/-- **In the syntactic model, substituting a composite is substituting twice.** -/
theorem tmSub_comp_syntactic {Γ Δ Θ : Ob} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) {A : LambdaPiFull.TyQ Γ}
    (a : Cwa.Tm syntactic Γ A) :
    Cwa.tmCast (syntactic.tySub_comp σ τ A) (Cwa.tmSub (T := syntactic) (τ ≫ σ) a)
      = Cwa.tmSub (T := syntactic) τ (Cwa.tmSub (T := syntactic) σ a) :=
  extCoherent_syntactic.tmSub_comp σ τ a

end LambdaPiFull
