/-
**The substitution calculus of λμ** (support for `M23-LAMBDA-MU-SN`).

The composition lemmas for the renaming and substitution operations of `Start/LambdaMu.lean`,
which the stability of `Step` under substitution needs:

* `LambdaMu.Tm.ren_ren`, `subst_ren`, `ren_subst`, `subst_subst` — the four composition laws;
* `LambdaMu.Tm.nameOf_ren` — the effect of renaming on the name carried by a μ-abstraction;
* `LambdaMu.Tm.ren_id`, `subst_var` — the unit laws;
* `LambdaMu.Tm.subst_single` — the β-commutation law;
* `LambdaMu.Tm.sstr_ren` — structural substitution commutes with an injective renaming.

Names and term variables share one index space, so a substitution acts on the name `β` of
`mu β t` through `nameOf`: these lemmas are exactly the bookkeeping that this mixing forces.
-/

import Start.LambdaMu

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaMu

namespace Tm

/-! ### Renaming -/

theorem up_id : up id = id := by
  funext i; cases i <;> rfl

theorem ren_id (t : Tm) : ren id t = t := by
  induction t with
  | var i => rfl
  | lam t ih => simp [ren, up_id, ih]
  | app t u iht ihu => simp [ren, iht, ihu]
  | mu β t ih => simp [ren, up_id, ih]

theorem up_comp (r s : ℕ → ℕ) (i : ℕ) : up r (up s i) = up (fun j => r (s j)) i := by
  cases i <;> rfl

theorem ren_ren (r s : ℕ → ℕ) (t : Tm) : ren r (ren s t) = ren (fun i => r (s i)) t := by
  induction t generalizing r s with
  | var i => rfl
  | lam t ih =>
      have h : (fun i => up r (up s i)) = up (fun i => r (s i)) := funext (up_comp r s)
      simp only [ren, ih, h]
  | app t u iht ihu => simp [ren, iht, ihu]
  | mu β t ih =>
      simp only [ren, ih, up_comp]

/-- The name carried by a renamed term. -/
theorem nameOf_ren (r : ℕ → ℕ) (t : Tm) :
    nameOf (ren r t) = match t with | var j => r j | _ => 0 := by
  cases t <;> rfl

/-! ### Substitution after renaming -/

theorem upS_up (σ : ℕ → Tm) (r : ℕ → ℕ) (i : ℕ) :
    upS σ (up r i) = upS (fun j => σ (r j)) i := by
  cases i <;> rfl

theorem subst_ren (σ : ℕ → Tm) (r : ℕ → ℕ) (t : Tm) :
    subst σ (ren r t) = subst (fun i => σ (r i)) t := by
  induction t generalizing σ r with
  | var i => rfl
  | lam t ih =>
      have h : (fun i => upS σ (up r i)) = upS (fun j => σ (r j)) := funext (upS_up σ r)
      simp only [ren, subst, ih, h]
  | app t u iht ihu => simp [ren, subst, iht, ihu]
  | mu β t ih =>
      simp only [ren, subst, ih, upS_up]

/-! ### Renaming after substitution -/

theorem ren_upS (r : ℕ → ℕ) (σ : ℕ → Tm) (i : ℕ) :
    ren (up r) (upS σ i) = upS (fun j => ren r (σ j)) i := by
  cases i with
  | zero => rfl
  | succ i =>
      simp only [upS, ren_ren]
      rfl

theorem ren_subst (r : ℕ → ℕ) (σ : ℕ → Tm) (t : Tm) :
    ren r (subst σ t) = subst (fun i => ren r (σ i)) t := by
  induction t generalizing r σ with
  | var i => rfl
  | lam t ih =>
      have h : (fun i => ren (up r) (upS σ i)) = upS (fun j => ren r (σ j)) :=
        funext (ren_upS r σ)
      simp only [subst, ren, ih, h]
  | app t u iht ihu => simp [subst, ren, iht, ihu]
  | mu β t ih =>
      have hup : (fun i => ren (up r) (upS σ i)) = upS (fun j => ren r (σ j)) := by
        funext i; exact ren_upS r σ i
      simp only [subst, ren, ih, hup]
      congr 1
      cases β with
      | zero => rfl
      | succ i =>
          have := ren_upS r σ (i + 1)
          cases hσ : σ i with
          | var j => simp [upS, ren, hσ, nameOf, up]
          | lam s => simp [upS, ren, hσ, nameOf, up]
          | app s s' => simp [upS, ren, hσ, nameOf, up]
          | mu b s => simp [upS, ren, hσ, nameOf, up]

/-! ### Substitution after substitution -/

theorem upS_comp (σ τ : ℕ → Tm) (i : ℕ) :
    subst (upS σ) (upS τ i) = upS (fun j => subst σ (τ j)) i := by
  cases i with
  | zero => rfl
  | succ i =>
      simp only [upS, subst_ren, ren_subst]

theorem subst_subst (σ τ : ℕ → Tm) (t : Tm) :
    subst σ (subst τ t) = subst (fun i => subst σ (τ i)) t := by
  induction t generalizing σ τ with
  | var i => rfl
  | lam t ih =>
      have h : (fun i => subst (upS σ) (upS τ i)) = upS (fun j => subst σ (τ j)) :=
        funext (upS_comp σ τ)
      simp only [subst, ih, h]
  | app t u iht ihu => simp [subst, iht, ihu]
  | mu β t ih =>
      have hup : (fun i => subst (upS σ) (upS τ i)) = upS (fun j => subst σ (τ j)) := by
        funext i; exact upS_comp σ τ i
      simp only [subst, ih, hup]
      congr 1
      cases β with
      | zero => rfl
      | succ i =>
          cases hτ : τ i with
          | var j =>
              cases hσ : σ j with
              | var k => simp [upS, hτ, hσ, nameOf, ren, subst]
              | lam s => simp [upS, hτ, hσ, nameOf, ren, subst]
              | app s s' => simp [upS, hτ, hσ, nameOf, ren, subst]
              | mu b s => simp [upS, hτ, hσ, nameOf, ren, subst]
          | lam s => simp [upS, hτ, nameOf, ren, subst]
          | app s s' => simp [upS, hτ, nameOf, ren, subst]
          | mu b s => simp [upS, hτ, nameOf, ren, subst]

theorem subst_var (t : Tm) : subst var t = t := by
  induction t with
  | var i => rfl
  | lam t ih =>
      have h : upS var = var := by funext i; cases i <;> rfl
      simp [subst, h, ih]
  | app t u iht ihu => simp [subst, iht, ihu]
  | mu β t ih =>
      have h : upS var = var := by funext i; cases i <;> rfl
      simp [subst, h, ih, nameOf]

/-- The β-commutation law: a substitution commutes with the substitution of an argument. -/
theorem subst_single (σ : ℕ → Tm) (u t : Tm) :
    subst σ (subst (single u) t) = subst (single (subst σ u)) (subst (upS σ) t) := by
  rw [subst_subst, subst_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => simp [single, upS, subst_ren, subst_var, subst]

/-! ### Structural substitution -/

/-- Structural substitution commutes with an injective renaming. -/
theorem sstr_ren (r : ℕ → ℕ) (hr : Function.Injective r) (a : ℕ) (v t : Tm) :
    ren r (sstr a v t) = sstr (r a) (ren r v) (ren r t) := by
  induction t generalizing r a v with
  | var i => rfl
  | lam t ih =>
      have hup : Function.Injective (up r) := by
        intro i j h
        cases i <;> cases j <;> simp [up] at h ⊢
        exact hr h
      have hv : ren (up r) (ren Nat.succ v) = ren Nat.succ (ren r v) := by
        rw [ren_ren, ren_ren]; rfl
      simp only [sstr, ren, ih (up r) hup, hv]
      rfl
  | app t u iht ihu => simp [sstr, ren, iht r hr, ihu r hr]
  | mu β t ih =>
      have hup : Function.Injective (up r) := by
        intro i j h
        cases i <;> cases j <;> simp [up] at h ⊢
        exact hr h
      have hv : ren (up r) (ren Nat.succ v) = ren Nat.succ (ren r v) := by
        rw [ren_ren, ren_ren]; rfl
      have hcond : (β = a + 1) ↔ (up r β = r a + 1) := by
        cases β with
        | zero => simp [up]
        | succ i =>
            constructor
            · rintro h
              simp only [Nat.succ_inj] at h
              simp [up, h]
            · intro h
              simp only [up, Nat.succ_inj] at h
              simp [hr h]
      by_cases h : β = a + 1
      · have h' : up r β = r a + 1 := hcond.1 h
        simp only [sstr, ren, if_pos h, if_pos h', ih (up r) hup, hv]
        rfl
      · have h' : ¬ up r β = r a + 1 := fun hc => h (hcond.2 hc)
        simp only [sstr, ren, if_neg h, if_neg h', ih (up r) hup, hv]
        rfl

end Tm

end LambdaMu
