/-
**Stability of λμ reduction under renaming and substitution** (support for `M23-LAMBDA-MU-SN`).

The first links of the chain to `LambdaMu.sn_of_typ` named in
`docs/goal/evidence/M23-LAMBDA-MU-SN.md`:

* `LambdaMu.Tm.NameFree a t` — the index `a` is not used as a free name in `t`;
  `sstr_nameFree`: structural substitution for such an `a` is the identity;
* `LambdaMu.Tm.subst_sstr` — **the commutation `subst ∘ sstr`**: for a substitution `τ` that fixes
  the name `a`, sends the names of `t` to variables (`NamesVar`), sends no other name to `a`, and
  introduces no free occurrence of the name `a`,
  `subst τ (sstr a v t) = sstr a (subst τ v) (subst τ t)`;
* `LambdaMu.Step.ren` (`Tm.step_ren`) — **reduction is stable under injective renaming**;
* `LambdaMu.Step.subst` (`Tm.step_subst`) — **reduction is stable under name-respecting substitution**:
  `Step t t' → NamesVar σ t → Step (subst σ t) (subst σ t')`.

Names and term variables share one index space, so a substitution that sent a name to a
non-variable would send it to the junk index `0`; `NamesVar σ t` (from `Start/LambdaMuCPS.lean`)
is exactly the hypothesis that rules this out.
-/

import Start.LambdaMuCPS
import Start.LambdaMuSubstLemmas

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaMu

namespace Tm

/-! ### Free names -/

/-- `a` is not used as a free name in `t`. -/
def NameFree : ℕ → Tm → Prop
  | _, var _ => True
  | a, lam t => NameFree (a + 1) t
  | a, app t u => NameFree a t ∧ NameFree a u
  | a, mu β t => β ≠ a + 1 ∧ NameFree (a + 1) t

/-- Structural substitution for a name that does not occur is the identity. -/
theorem sstr_nameFree : ∀ (t : Tm) (a : ℕ) (v : Tm), NameFree a t → sstr a v t = t
  | var _, _, _, _ => rfl
  | lam t, a, v, h => by simp only [sstr, sstr_nameFree t (a + 1) _ h]
  | app t u, a, v, h => by simp only [sstr, sstr_nameFree t a v h.1, sstr_nameFree u a v h.2]
  | mu β t, a, v, h => by simp only [sstr, ite_eq_right h.1, sstr_nameFree t (a + 1) _ h.2]

theorem nameFree_ren : ∀ (t : Tm) (r : ℕ → ℕ) (a b : ℕ), (∀ i, r i = b → i = a) →
    NameFree a t → NameFree b (ren r t)
  | var _, _, _, _, _, _ => trivial
  | lam t, r, a, b, hr, h => by
      refine nameFree_ren t (up r) (a + 1) (b + 1) ?_ h
      intro i hi
      cases i with
      | zero => simp [up] at hi
      | succ i => simp only [up, Nat.succ_inj] at hi; rw [hr i hi]
  | app t u, r, a, b, hr, h => ⟨nameFree_ren t r a b hr h.1, nameFree_ren u r a b hr h.2⟩
  | mu β t, r, a, b, hr, h => by
      have hup : ∀ i, up r i = b + 1 → i = a + 1 := by
        intro i hi
        cases i with
        | zero => simp [up] at hi
        | succ i => simp only [up, Nat.succ_inj] at hi; rw [hr i hi]
      exact ⟨fun hc => h.1 (hup β hc), nameFree_ren t (up r) (a + 1) (b + 1) hup h.2⟩

/-- A name outside the image of a renaming is free in every renamed term. -/
theorem nameFree_ren_of_ne : ∀ (t : Tm) (r : ℕ → ℕ) (b : ℕ), (∀ i, r i ≠ b) →
    NameFree b (ren r t)
  | var _, _, _, _ => trivial
  | lam t, r, b, hr => by
      refine nameFree_ren_of_ne t (up r) (b + 1) ?_
      intro i hi
      cases i with
      | zero => simp [up] at hi
      | succ i => simp only [up, Nat.succ_inj] at hi; exact hr i hi
  | app t u, r, b, hr => ⟨nameFree_ren_of_ne t r b hr, nameFree_ren_of_ne u r b hr⟩
  | mu β t, r, b, hr => by
      have hup : ∀ i, up r i ≠ b + 1 := by
        intro i hi
        cases i with
        | zero => simp [up] at hi
        | succ i => simp only [up, Nat.succ_inj] at hi; exact hr i hi
      exact ⟨hup β, nameFree_ren_of_ne t (up r) (b + 1) hup⟩

theorem nameFree_ren_succ {t : Tm} {a : ℕ} (h : NameFree a t) : NameFree (a + 1) (ren Nat.succ t) :=
  nameFree_ren t Nat.succ a (a + 1) (fun _ hi => Nat.succ_inj.1 hi) h

/-! ### Renaming and substitution of single variables -/

theorem ren_succ_upS (σ : ℕ → Tm) (v : Tm) :
    subst (upS σ) (ren Nat.succ v) = ren Nat.succ (subst σ v) := by
  rw [subst_ren, ren_subst]; rfl

theorem ren_single (r : ℕ → ℕ) (u t : Tm) :
    ren r (subst (single u) t) = subst (single (ren r u)) (ren (up r) t) := by
  rw [ren_subst, subst_ren]
  congr 1
  funext i
  cases i <;> rfl

/-! ### `subst ∘ sstr` -/

/-- **The commutation `subst ∘ sstr`.** -/
theorem subst_sstr : ∀ (t : Tm) (τ : ℕ → Tm) (a : ℕ) (v : Tm), NamesVar τ t → τ a = var a →
    (∀ i j, τ i = var j → j = a → i = a) → (∀ i, NameFree a (τ i)) →
    subst τ (sstr a v t) = sstr a (subst τ v) (subst τ t)
  | var i, τ, a, v, _, _, _, hfree => by
      simp only [sstr, subst]
      rw [sstr_nameFree _ a _ (hfree i)]
  | lam t, τ, a, v, hnv, hfix, hinj, hfree => by
      simp only [sstr, subst]
      congr 1
      rw [subst_sstr t (upS τ) (a + 1) (ren Nat.succ v) hnv (by simp [upS, hfix, ren]) ?_ ?_,
        ren_succ_upS]
      · intro i j hi hj
        cases i with
        | zero => simp [upS] at hi; omega
        | succ i =>
            simp only [upS] at hi
            cases hτ : τ i with
            | var k =>
                rw [hτ] at hi; simp only [ren, var.injEq] at hi
                rw [hinj i k hτ (by omega)]
            | lam _ => rw [hτ] at hi; simp [ren] at hi
            | app _ _ => rw [hτ] at hi; simp [ren] at hi
            | mu _ _ => rw [hτ] at hi; simp [ren] at hi
      · intro i
        cases i with
        | zero => trivial
        | succ i => exact nameFree_ren_succ (hfree i)
  | app t u, τ, a, v, hnv, hfix, hinj, hfree => by
      simp only [sstr, subst]
      rw [subst_sstr t τ a v hnv.1 hfix hinj hfree, subst_sstr u τ a v hnv.2 hfix hinj hfree]
  | mu β t, τ, a, v, hnv, hfix, hinj, hfree => by
      obtain ⟨⟨j, hj⟩, hnv'⟩ := hnv
      have hfix' : upS τ (a + 1) = var (a + 1) := by simp [upS, hfix, ren]
      have hinj' : ∀ i j, upS τ i = var j → j = a + 1 → i = a + 1 := by
        intro i j hi hj
        cases i with
        | zero => simp [upS] at hi; omega
        | succ i =>
            simp only [upS] at hi
            cases hτ : τ i with
            | var k =>
                rw [hτ] at hi; simp only [ren, var.injEq] at hi
                rw [hinj i k hτ (by omega)]
            | lam _ => rw [hτ] at hi; simp [ren] at hi
            | app _ _ => rw [hτ] at hi; simp [ren] at hi
            | mu _ _ => rw [hτ] at hi; simp [ren] at hi
      have hfree' : ∀ i, NameFree (a + 1) (upS τ i) := by
        intro i
        cases i with
        | zero => trivial
        | succ i => exact nameFree_ren_succ (hfree i)
      have ih := subst_sstr t (upS τ) (a + 1) (ren Nat.succ v) hnv' hfix' hinj' hfree'
      rw [ren_succ_upS] at ih
      have hcond : (β = a + 1) ↔ (nameOf (upS τ β) = a + 1) := by
        rw [hj]
        simp only [nameOf]
        constructor
        · rintro rfl; rw [hfix'] at hj; cases hj; rfl
        · intro h; exact hinj' β j hj h
      simp only [sstr, subst, hj, nameOf]
      rw [hj] at hcond
      simp only [nameOf] at hcond
      by_cases hβ : β = a + 1
      · rw [ite_eq_left hβ, ite_eq_left (hcond.1 hβ)]
        simp only [subst, ih, ren_succ_upS]
      · rw [ite_eq_right hβ, ite_eq_right (fun h => hβ (hcond.2 h))]
        rw [ih]

/-! ### Stability of reduction -/

/-- **Reduction is stable under injective renaming.** -/
theorem step_ren {t t' : Tm} (hs : Step t t') :
    ∀ (r : ℕ → ℕ), Function.Injective r → Step (ren r t) (ren r t') := by
  induction hs with
  | beta t u =>
      intro r _
      rw [ren_single]
      exact Step.beta _ _
  | struct β t u =>
      intro r hr
      have hup : Function.Injective (up r) := by
        intro i j h
        cases i <;> cases j <;> simp [up] at h ⊢
        exact hr h
      have hv : ren (up r) (ren Nat.succ u) = ren Nat.succ (ren r u) := by
        rw [ren_ren, ren_ren]; rfl
      have hs := sstr_ren (up r) hup 0 (ren Nat.succ u) t
      rw [hv] at hs
      have h0 : up r 0 = 0 := rfl
      rw [h0] at hs
      have hβ : (up r β = 0) ↔ (β = 0) := by
        cases β with
        | zero => simp [up]
        | succ i => simp [up]
      have := Step.struct (up r β) (ren (up r) t) (ren r u)
      simp only [ren]
      by_cases h : β = 0
      · rw [ite_eq_left h]
        rw [ite_eq_left (hβ.2 h)] at this
        simp only [ren, hs, hv]
        exact this
      · rw [ite_eq_right h]
        rw [ite_eq_right (fun h' => h (hβ.1 h'))] at this
        simp only [hs]
        exact this
  | rename β γ t =>
      intro r _
      simp only [ren]
      have hbody : ren (up r) (subst (single (var β)) t) =
          subst (single (var (up r β))) (ren (up (up r)) t) := by
        rw [ren_subst, subst_ren]
        congr 1
        funext i
        cases i <;> rfl
      have hname : up r (nameOf (single (var β) γ)) =
          nameOf (single (var (up r β)) (up (up r) γ)) := by
        cases γ <;> rfl
      rw [hbody, hname]
      exact Step.rename _ _ _
  | lam _ ih =>
      intro r hr
      have hup : Function.Injective (up r) := by
        intro i j h
        cases i <;> cases j <;> simp [up] at h ⊢
        exact hr h
      exact Step.lam (ih _ hup)
  | appL u _ ih => intro r hr; exact Step.appL _ (ih r hr)
  | appR t _ ih => intro r hr; exact Step.appR _ (ih r hr)
  | mu β _ ih =>
      intro r hr
      have hup : Function.Injective (up r) := by
        intro i j h
        cases i <;> cases j <;> simp [up] at h ⊢
        exact hr h
      exact Step.mu _ (ih _ hup)

theorem namesVar_upS_zero (σ : ℕ → Tm) : ∃ j, upS σ 0 = var j := ⟨0, rfl⟩

/-- **Reduction is stable under name-respecting substitution.** -/
theorem step_subst {t t' : Tm} (hs : Step t t') :
    ∀ (σ : ℕ → Tm), NamesVar σ t → Step (subst σ t) (subst σ t') := by
  induction hs with
  | beta t u =>
      intro σ _
      rw [subst_single]
      exact Step.beta _ _
  | struct β t u =>
      intro σ hnv
      obtain ⟨⟨j, hj⟩, hnvt⟩ := hnv.1
      have hfix : upS σ 0 = var 0 := rfl
      have hinj : ∀ i k, upS σ i = var k → k = 0 → i = 0 := by
        intro i k hi hk
        cases i with
        | zero => rfl
        | succ i =>
            simp only [upS] at hi
            cases hσ : σ i with
            | var m => rw [hσ] at hi; simp only [ren, var.injEq] at hi; omega
            | lam _ => rw [hσ] at hi; simp [ren] at hi
            | app _ _ => rw [hσ] at hi; simp [ren] at hi
            | mu _ _ => rw [hσ] at hi; simp [ren] at hi
      have hfree : ∀ i, NameFree 0 (upS σ i) := by
        intro i
        cases i with
        | zero => trivial
        | succ i => exact nameFree_ren_of_ne _ _ _ (fun i => Nat.succ_ne_zero i)
      have hc := subst_sstr t (upS σ) 0 (ren Nat.succ u) hnvt hfix hinj hfree
      rw [ren_succ_upS] at hc
      have hβ : (β = 0) ↔ (j = 0) := by
        constructor
        · rintro rfl; simp [upS] at hj; omega
        · intro h
          exact hinj β j hj h
      have := Step.struct j (subst (upS σ) t) (subst σ u)
      simp only [subst, hj, nameOf]
      by_cases h : β = 0
      · rw [ite_eq_left h]
        rw [ite_eq_left (hβ.1 h)] at this
        simp only [subst, hc, ren_succ_upS]
        exact this
      · rw [ite_eq_right h]
        rw [ite_eq_right (fun h' => h (hβ.2 h'))] at this
        rw [hc]
        exact this
  | rename β γ t =>
      intro σ hnv
      obtain ⟨⟨j, hj⟩, ⟨k, hk⟩, hnvt⟩ := hnv
      show Step (mu (nameOf (upS σ β)) (mu (nameOf (upS (upS σ) γ)) (subst (upS (upS σ)) t)))
        (mu (nameOf (upS σ (nameOf (single (var β) γ)))) (subst (upS σ) (subst (single (var β)) t)))
      have hbody : subst (upS σ) (subst (single (var β)) t) =
          subst (single (var j)) (subst (upS (upS σ)) t) := by
        rw [subst_subst, subst_subst]
        congr 1
        funext i
        cases i with
        | zero =>
            show upS σ β = subst (single (var j)) (var 0)
            rw [hj]; rfl
        | succ i => simp [single, subst, upS, subst_ren, subst_var]
      have hname : nameOf (upS σ (nameOf (single (var β) γ))) =
          nameOf (single (var j) (nameOf (upS (upS σ) γ))) := by
        cases γ with
        | zero =>
            show nameOf (upS σ β) = j
            rw [hj]; rfl
        | succ i =>
            have hk' : ren Nat.succ (upS σ i) = var k := hk
            show nameOf (upS σ i) = nameOf (single (var j) (nameOf (ren Nat.succ (upS σ i))))
            cases hσ : upS σ i with
            | var m => rfl
            | lam _ => rw [hσ] at hk'; simp [ren] at hk'
            | app _ _ => rw [hσ] at hk'; simp [ren] at hk'
            | mu _ _ => rw [hσ] at hk'; simp [ren] at hk'
      rw [hbody, hname, hj]
      exact Step.rename j _ _
  | lam _ ih => intro σ hnv; exact Step.lam (ih _ hnv)
  | appL u _ ih => intro σ hnv; exact Step.appL _ (ih σ hnv.1)
  | appR t _ ih => intro σ hnv; exact Step.appR _ (ih σ hnv.2)
  | mu β _ ih => intro σ hnv; exact Step.mu _ (ih _ hnv.2)

end Tm

/-- **Reduction is stable under injective renaming.** -/
theorem Step.ren {t t' : Tm} (hs : Step t t') (r : ℕ → ℕ) (hr : Function.Injective r) :
    Step (Tm.ren r t) (Tm.ren r t') :=
  Tm.step_ren hs r hr

/-- **Reduction is stable under name-respecting substitution.** -/
theorem Step.subst {t t' : Tm} (hs : Step t t') (σ : ℕ → Tm) (hσ : NamesVar σ t) :
    Step (Tm.subst σ t) (Tm.subst σ t') :=
  Tm.step_subst hs σ hσ

end LambdaMu
