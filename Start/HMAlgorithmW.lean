/-
**Algorithm W** (Milner 1978, Damas–Milner 1982) for the Hindley–Milner system of
`Start/HindleyMilner.lean`, and its **soundness**.

`HM.W Γ e n` infers a type for `e` in the context `Γ`.  The natural number `n` is the supply of
fresh type variables: every variable `≥ n` is unused, and the result reports the new supply `m`.
On success it returns a substitution `s` (the refinement of the free type variables of `Γ` that
typing `e` forces) and a type `τ`; it fails when unification fails or a variable is unbound.

* variable: instantiate its scheme with fresh variables;
* abstraction: a fresh variable for the parameter;
* application: infer both sides, then unify the type of the function with
  `τ₂ → β` for a fresh `β` (`HM.mgu` of `Start/Unification.lean`);
* `let`: infer the bound term, generalize its type in the substituted context, and infer the
  body.

* `HM.W` — the algorithm, a total function by structural recursion on the term;
* `HM.W_sound` — **soundness**: if `W Γ e n = some (s, τ, m)` then `sΓ ⊢ e : τ`;
* `HM.W_sound_closed` — for closed terms, a returned type is a type of the term.
-/

import Start.HindleyMilner

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace HM

open Ty

/-- Composition of substitutions: first `s`, then `s'`. -/
def comp (s s' : ℕ → Ty) : ℕ → Ty := fun v => (s v).subst s'

theorem ctxSubst_comp (s s' : ℕ → Ty) (Γ : List Sch) :
    ctxSubst (comp s s') Γ = ctxSubst s' (ctxSubst s Γ) :=
  (ctxSubst_ctxSubst s s' Γ).symm

/-- **Algorithm W.**  `W Γ e n` returns a substitution, a type, and the new supply of fresh
type variables, or fails. -/
def W : List Sch → Expr → ℕ → Option ((ℕ → Ty) × Ty × ℕ)
  | Γ, Expr.var i, n =>
      match Γ[i]? with
      | none => none
      | some σ => some (Ty.var, σ.inst fun k => Ty.var (n + k), n + σ.bnd)
  | Γ, Expr.lam e, n =>
      match W (Sch.ofTy (Ty.var n) :: Γ) e (n + 1) with
      | none => none
      | some (s, τ, m) => some (s, Ty.arrow (s n) τ, m)
  | Γ, Expr.app e₁ e₂, n =>
      match W Γ e₁ n with
      | none => none
      | some (s₁, τ₁, m₁) =>
        match W (ctxSubst s₁ Γ) e₂ m₁ with
        | none => none
        | some (s₂, τ₂, m₂) =>
          match mgu (τ₁.subst s₂) (Ty.arrow τ₂ (Ty.var m₂)) with
          | none => none
          | some u => some (comp (comp s₁ s₂) u, u m₂, m₂ + 1)
  | Γ, Expr.let_ e₁ e₂, n =>
      match W Γ e₁ n with
      | none => none
      | some (s₁, τ₁, m₁) =>
        match W (gen (ctxSubst s₁ Γ) τ₁ :: ctxSubst s₁ Γ) e₂ m₁ with
        | none => none
        | some (s₂, τ₂, m₂) => some (comp s₁ s₂, τ₂, m₂)

/-- The `let` rule may be applied after a substitution of the context: if `Γ ⊢ a : A` and the
body is typed under the substituted generalization, the `let` is typed in the substituted
context. -/
theorem Typing.let_subst {Γ : List Sch} {a b : Expr} {A B : Ty} (s : ℕ → Ty)
    (ha : Typing Γ a A) (hb : Typing ((gen Γ A).subst s :: ctxSubst s Γ) b B) :
    Typing (ctxSubst s Γ) (Expr.let_ a b) B := by
  obtain ⟨s', hs', hmg⟩ := moreGen_gen_rename (ctxFvs Γ) (ctxFvs (ctxSubst s Γ)) s A
    (fun v hv w hw => mem_ctxFvs_subst.2 ⟨v, hv, hw⟩)
  have h1 := ha.subst s'
  rw [ctxSubst_congr hs'] at h1
  exact Typing.let_ h1
    (hb.mono (List.Forall₂.cons hmg (List.forall₂_same.2 fun σ _ => MoreGen.refl σ)))

/-- **Soundness of algorithm W**: the substituted context types the term with the returned
type. -/
theorem W_sound {e : Expr} :
    ∀ {Γ : List Sch} {n : ℕ} {s : ℕ → Ty} {τ : Ty} {m : ℕ},
      W Γ e n = some (s, τ, m) → Typing (ctxSubst s Γ) e τ := by
  induction e with
  | var i =>
    intro Γ n s τ m h
    simp only [W] at h
    cases hi : Γ[i]? with
    | none => simp [hi] at h
    | some σ =>
      simp only [hi, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [ctxSubst_var]
      exact Typing.var _ hi
  | lam e ih =>
    intro Γ n s τ m h
    simp only [W] at h
    cases hw : W (Sch.ofTy (Ty.var n) :: Γ) e (n + 1) with
    | none => simp [hw] at h
    | some r =>
      obtain ⟨s₁, τ₁, m₁⟩ := r
      simp only [hw, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have := ih hw
      simp only [ctxSubst_cons, Sch.ofTy_subst, Ty.subst_var'] at this
      exact Typing.lam this
  | app e₁ e₂ ih₁ ih₂ =>
    intro Γ n s τ m h
    simp only [W] at h
    cases hw₁ : W Γ e₁ n with
    | none => simp [hw₁] at h
    | some r₁ =>
      obtain ⟨s₁, τ₁, m₁⟩ := r₁
      simp only [hw₁] at h
      cases hw₂ : W (ctxSubst s₁ Γ) e₂ m₁ with
      | none => simp [hw₂] at h
      | some r₂ =>
        obtain ⟨s₂, τ₂, m₂⟩ := r₂
        simp only [hw₂] at h
        cases hu : mgu (τ₁.subst s₂) (Ty.arrow τ₂ (Ty.var m₂)) with
        | none => simp [hu] at h
        | some u =>
          simp only [hu, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have h₁ := ((ih₁ hw₁).subst s₂).subst u
          have h₂ := (ih₂ hw₂).subst u
          rw [Ty.subst_subst, ← Ty.subst_subst, mgu_sound hu] at h₁
          rw [ctxSubst_comp, ctxSubst_comp]
          exact Typing.app h₁ h₂
  | let_ e₁ e₂ ih₁ ih₂ =>
    intro Γ n s τ m h
    simp only [W] at h
    cases hw₁ : W Γ e₁ n with
    | none => simp [hw₁] at h
    | some r₁ =>
      obtain ⟨s₁, τ₁, m₁⟩ := r₁
      simp only [hw₁] at h
      cases hw₂ : W (gen (ctxSubst s₁ Γ) τ₁ :: ctxSubst s₁ Γ) e₂ m₁ with
      | none => simp [hw₂] at h
      | some r₂ =>
        obtain ⟨s₂, τ₂, m₂⟩ := r₂
        simp only [hw₂, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rw [ctxSubst_comp]
        exact Typing.let_subst s₂ (ih₁ hw₁) (ih₂ hw₂)

/-- For a closed term, a type returned by W is a type of the term. -/
theorem W_sound_closed {e : Expr} {n : ℕ} {s : ℕ → Ty} {τ : Ty} {m : ℕ}
    (h : W [] e n = some (s, τ, m)) : Typing [] e τ :=
  W_sound h

end HM
