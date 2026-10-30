/-
**Reduction is stable under structural substitution** (support for `M23-LAMBDA-MU-SN`, round 5).

The first missing lemma of round 4, `Step.sstr`, and the commutations it needs.

* `LambdaMu.Tm.TmFree a t` — the index `a` is not used as a *term* variable in `t` (names only
  occur in `μ`-positions, so this holds for every name of a well-typed term, `Typ.tmFree`);
* `LambdaMu.Tm.sstr_sstr` — **`sstr ∘ sstr`**: two structural substitutions at different names
  commute, `sstr c w (sstr b x t) = sstr b (sstr c w x) (sstr c w t)` when `b ≠ c` and `b` is not a
  free name of `w`;
* `LambdaMu.Tm.sstr_subst` — **`sstr ∘ subst`**: a structural substitution at `a` after a
  substitution `σ` that sends exactly the name `a'` to `a` is a structural substitution at `a'`
  before it;
* `LambdaMu.Tm.sstr_subst2` — the same when `σ` *merges* two names `b₁ ≠ b₂` into `a` (the shape
  of the renaming rule `[β]μγ.c → c[β/γ]` when `β` is the substituted name);
* `LambdaMu.Step.sstr` — **reduction is stable under structural substitution**:
  `Step t t' → TmFree a t → TransGen Step (sstr a v t) (sstr a v t')`.  One step becomes one step,
  except for a renaming redex `[a]μγ.c`, which becomes `[a]((μγ.c') v)` and needs a structural
  step before the renaming step (two steps).
-/

import Start.LambdaMuStep

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaMu

namespace Tm

/-! ### Auxiliary facts -/

theorem subst_single_ren (w x : Tm) : subst (single w) (ren Nat.succ x) = x := by
  rw [subst_ren]
  exact subst_var x

theorem nameFree_zero_ren_succ (v : Tm) : NameFree 0 (ren Nat.succ v) :=
  nameFree_ren_of_ne _ _ _ (fun i => Nat.succ_ne_zero i)

theorem sstr_ren_succ (a : ℕ) (v t : Tm) :
    ren Nat.succ (sstr a v t) = sstr (a + 1) (ren Nat.succ v) (ren Nat.succ t) :=
  sstr_ren Nat.succ (fun _ _ h => Nat.succ_inj.1 h) a v t

theorem sstr_var (a : ℕ) (v : Tm) (i : ℕ) : sstr a v (var i) = var i := rfl

/-- `a` is not used as a term variable in `t`. -/
def TmFree : ℕ → Tm → Prop
  | a, var i => i ≠ a
  | a, lam t => TmFree (a + 1) t
  | a, app t u => TmFree a t ∧ TmFree a u
  | a, mu _ t => TmFree (a + 1) t

/-- `upS` commutes with post-composing a structural substitution. -/
theorem sstr_upS (σ : ℕ → Tm) (a : ℕ) (v : Tm) (i : ℕ) :
    sstr (a + 1) (ren Nat.succ v) (upS σ i) = upS (fun j => sstr a v (σ j)) i := by
  cases i with
  | zero => rfl
  | succ i => exact (sstr_ren_succ a v (σ i)).symm

theorem nameOf_sstr (a : ℕ) (v t : Tm) : nameOf (sstr a v t) = nameOf t := by
  cases t <;> rfl

theorem nameOf_upS_sstr (σ : ℕ → Tm) (a : ℕ) (v : Tm) (i : ℕ) :
    nameOf (upS (fun j => sstr a v (σ j)) i) = nameOf (upS σ i) := by
  cases i with
  | zero => rfl
  | succ i =>
      show nameOf (ren Nat.succ (sstr a v (σ i))) = nameOf (ren Nat.succ (σ i))
      cases h : σ i <;> rfl

/-- The injectivity hypothesis is preserved under a binder. -/
theorem upS_hit {σ : ℕ → Tm} {a : ℕ} {P : ℕ → Prop}
    (h : ∀ i j, σ i = var j → j = a → P i) :
    ∀ i j, upS σ i = var j → j = a + 1 → ∃ i', i = i' + 1 ∧ P i' := by
  intro i j hi hj
  cases i with
  | zero => simp [upS] at hi; omega
  | succ i =>
      refine ⟨i, rfl, ?_⟩
      simp only [upS] at hi
      cases hσ : σ i with
      | var k =>
          rw [hσ] at hi; simp only [ren, var.injEq] at hi
          exact h i k hσ (by omega)
      | lam _ => rw [hσ] at hi; simp [ren] at hi
      | app _ _ => rw [hσ] at hi; simp [ren] at hi
      | mu _ _ => rw [hσ] at hi; simp [ren] at hi

theorem nameOf_eq_succ {t : Tm} {k : ℕ} (h : nameOf t = k + 1) : t = var (k + 1) := by
  cases t with
  | var j => simp only [nameOf] at h; rw [h]
  | lam _ => simp [nameOf] at h
  | app _ _ => simp [nameOf] at h
  | mu _ _ => simp [nameOf] at h

/-! ### `sstr ∘ sstr` -/

/-- **Two structural substitutions at different names commute.** -/
theorem sstr_sstr : ∀ (t : Tm) (b c : ℕ) (x w : Tm), b ≠ c → NameFree b w →
    sstr c w (sstr b x t) = sstr b (sstr c w x) (sstr c w t)
  | var _, _, _, _, _, _, _ => rfl
  | lam t, b, c, x, w, hbc, hw => by
      simp only [sstr]
      rw [sstr_sstr t (b + 1) (c + 1) (ren Nat.succ x) (ren Nat.succ w) (by omega)
        (nameFree_ren_succ hw), sstr_ren_succ]
  | app t u, b, c, x, w, hbc, hw => by
      simp only [sstr]
      rw [sstr_sstr t b c x w hbc hw, sstr_sstr u b c x w hbc hw]
  | mu β t, b, c, x, w, hbc, hw => by
      have ih := sstr_sstr t (b + 1) (c + 1) (ren Nat.succ x) (ren Nat.succ w) (by omega)
        (nameFree_ren_succ hw)
      have hx : sstr (c + 1) (ren Nat.succ w) (ren Nat.succ x) = ren Nat.succ (sstr c w x) :=
        (sstr_ren_succ c w x).symm
      have hw' : sstr (b + 1) (ren Nat.succ (sstr c w x)) (ren Nat.succ w) = ren Nat.succ w :=
        sstr_nameFree _ _ _ (nameFree_ren_succ hw)
      by_cases h1 : β = b + 1
      · have h2 : ¬ β = c + 1 := by omega
        simp only [sstr, ite_eq_left h1, ite_eq_right h2, ih, hx]
      · by_cases h2 : β = c + 1
        · simp only [sstr, ite_eq_left h2, ite_eq_right h1, ih, hx, hw']
        · simp only [sstr, ite_eq_right h1, ite_eq_right h2, ih, hx]

/-! ### `sstr ∘ subst` -/

/-- **Structural substitution after a substitution that sends exactly the name `a'` to `a`.** -/
theorem sstr_subst : ∀ (t : Tm) (σ : ℕ → Tm) (a a' : ℕ) (v v' : Tm),
    σ a' = var a → (∀ i j, σ i = var j → j = a → i = a') →
    subst (fun i => sstr a v (σ i)) v' = v →
    sstr a v (subst σ t) = subst (fun i => sstr a v (σ i)) (sstr a' v' t)
  | var _, _, _, _, _, _, _, _, _ => rfl
  | lam t, σ, a, a', v, v', hfix, hinj, hv => by
      have hfix' : upS σ (a' + 1) = var (a + 1) := by simp [upS, hfix, ren]
      have hinj' : ∀ i j, upS σ i = var j → j = a + 1 → i = a' + 1 := by
        intro i j hi hj
        obtain ⟨i', rfl, h⟩ := upS_hit hinj i j hi hj
        rw [h]
      have hfun : (fun i => sstr (a + 1) (ren Nat.succ v) (upS σ i)) =
          upS (fun j => sstr a v (σ j)) := funext (sstr_upS σ a v)
      have hv' : subst (fun i => sstr (a + 1) (ren Nat.succ v) (upS σ i)) (ren Nat.succ v') =
          ren Nat.succ v := by
        rw [hfun, ren_succ_upS, hv]
      have ih := sstr_subst t (upS σ) (a + 1) (a' + 1) (ren Nat.succ v) (ren Nat.succ v')
        hfix' hinj' hv'
      rw [hfun] at ih
      simp only [sstr, subst, ih]
  | app t u, σ, a, a', v, v', hfix, hinj, hv => by
      simp only [sstr, subst]
      rw [sstr_subst t σ a a' v v' hfix hinj hv, sstr_subst u σ a a' v v' hfix hinj hv]
  | mu β t, σ, a, a', v, v', hfix, hinj, hv => by
      have hfix' : upS σ (a' + 1) = var (a + 1) := by simp [upS, hfix, ren]
      have hinj' : ∀ i j, upS σ i = var j → j = a + 1 → i = a' + 1 := by
        intro i j hi hj
        obtain ⟨i', rfl, h⟩ := upS_hit hinj i j hi hj
        rw [h]
      have hfun : (fun i => sstr (a + 1) (ren Nat.succ v) (upS σ i)) =
          upS (fun j => sstr a v (σ j)) := funext (sstr_upS σ a v)
      have hv' : subst (fun i => sstr (a + 1) (ren Nat.succ v) (upS σ i)) (ren Nat.succ v') =
          ren Nat.succ v := by
        rw [hfun, ren_succ_upS, hv]
      have ih := sstr_subst t (upS σ) (a + 1) (a' + 1) (ren Nat.succ v) (ren Nat.succ v')
        hfix' hinj' hv'
      rw [hfun] at ih
      have hv1 : subst (upS (fun j => sstr a v (σ j))) (ren Nat.succ v') = ren Nat.succ v := by
        rw [ren_succ_upS, hv]
      have hname := nameOf_upS_sstr σ a v β
      have hcond : (β = a' + 1) ↔ (nameOf (upS σ β) = a + 1) := by
        constructor
        · rintro rfl; rw [hfix']; rfl
        · intro h; exact hinj' β _ (nameOf_eq_succ h) rfl
      by_cases hβ : β = a' + 1
      · simp only [sstr, subst, ite_eq_left hβ, ite_eq_left (hcond.1 hβ), hname, ih, hv1]
      · simp only [sstr, subst, ite_eq_right hβ, ite_eq_right (fun h => hβ (hcond.2 h)), hname, ih]

/-- **Structural substitution after a substitution that merges two names `b₁ ≠ b₂` into `a`.** -/
theorem sstr_subst2 : ∀ (t : Tm) (σ : ℕ → Tm) (a b₁ b₂ : ℕ) (v w : Tm), b₁ ≠ b₂ →
    σ b₁ = var a → σ b₂ = var a → (∀ i j, σ i = var j → j = a → i = b₁ ∨ i = b₂) →
    NameFree b₁ w → subst (fun i => sstr a v (σ i)) w = v →
    sstr a v (subst σ t) = subst (fun i => sstr a v (σ i)) (sstr b₁ w (sstr b₂ w t))
  | var _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | lam t, σ, a, b₁, b₂, v, w, hb, h₁, h₂, hinj, hw, hv => by
      have h₁' : upS σ (b₁ + 1) = var (a + 1) := by simp [upS, h₁, ren]
      have h₂' : upS σ (b₂ + 1) = var (a + 1) := by simp [upS, h₂, ren]
      have hinj' : ∀ i j, upS σ i = var j → j = a + 1 → i = b₁ + 1 ∨ i = b₂ + 1 := by
        intro i j hi hj
        obtain ⟨i', rfl, h⟩ := upS_hit hinj i j hi hj
        rcases h with h | h <;> simp [h]
      have hfun : (fun i => sstr (a + 1) (ren Nat.succ v) (upS σ i)) =
          upS (fun j => sstr a v (σ j)) := funext (sstr_upS σ a v)
      have hv' : subst (fun i => sstr (a + 1) (ren Nat.succ v) (upS σ i)) (ren Nat.succ w) =
          ren Nat.succ v := by
        rw [hfun, ren_succ_upS, hv]
      have ih := sstr_subst2 t (upS σ) (a + 1) (b₁ + 1) (b₂ + 1) (ren Nat.succ v) (ren Nat.succ w)
        (by omega) h₁' h₂' hinj' (nameFree_ren_succ hw) hv'
      rw [hfun] at ih
      simp only [sstr, subst, ih]
  | app t u, σ, a, b₁, b₂, v, w, hb, h₁, h₂, hinj, hw, hv => by
      simp only [sstr, subst]
      rw [sstr_subst2 t σ a b₁ b₂ v w hb h₁ h₂ hinj hw hv,
        sstr_subst2 u σ a b₁ b₂ v w hb h₁ h₂ hinj hw hv]
  | mu β t, σ, a, b₁, b₂, v, w, hb, h₁, h₂, hinj, hw, hv => by
      have h₁' : upS σ (b₁ + 1) = var (a + 1) := by simp [upS, h₁, ren]
      have h₂' : upS σ (b₂ + 1) = var (a + 1) := by simp [upS, h₂, ren]
      have hinj' : ∀ i j, upS σ i = var j → j = a + 1 → i = b₁ + 1 ∨ i = b₂ + 1 := by
        intro i j hi hj
        obtain ⟨i', rfl, h⟩ := upS_hit hinj i j hi hj
        rcases h with h | h <;> simp [h]
      have hfun : (fun i => sstr (a + 1) (ren Nat.succ v) (upS σ i)) =
          upS (fun j => sstr a v (σ j)) := funext (sstr_upS σ a v)
      have hv' : subst (fun i => sstr (a + 1) (ren Nat.succ v) (upS σ i)) (ren Nat.succ w) =
          ren Nat.succ v := by
        rw [hfun, ren_succ_upS, hv]
      have ih := sstr_subst2 t (upS σ) (a + 1) (b₁ + 1) (b₂ + 1) (ren Nat.succ v) (ren Nat.succ w)
        (by omega) h₁' h₂' hinj' (nameFree_ren_succ hw) hv'
      rw [hfun] at ih
      have hv1 : subst (upS (fun j => sstr a v (σ j))) (ren Nat.succ w) = ren Nat.succ v := by
        rw [ren_succ_upS, hv]
      have hww : sstr (b₁ + 1) (ren Nat.succ w) (ren Nat.succ w) = ren Nat.succ w :=
        sstr_nameFree _ _ _ (nameFree_ren_succ hw)
      have hname := nameOf_upS_sstr σ a v β
      have hcond : (β = b₁ + 1 ∨ β = b₂ + 1) ↔ (nameOf (upS σ β) = a + 1) := by
        constructor
        · rintro (rfl | rfl)
          · rw [h₁']; rfl
          · rw [h₂']; rfl
        · intro h; exact hinj' β _ (nameOf_eq_succ h) rfl
      by_cases hβ₁ : β = b₁ + 1
      · have hβ₂ : ¬ β = b₂ + 1 := by omega
        simp only [sstr, subst, ite_eq_left hβ₁, ite_eq_right hβ₂, ite_eq_left (hcond.1 (.inl hβ₁)), hname, ih,
          hv1]
      · by_cases hβ₂ : β = b₂ + 1
        · simp only [sstr, subst, ite_eq_left hβ₂, ite_eq_right hβ₁, ite_eq_left (hcond.1 (.inr hβ₂)), hname, ih,
            hv1, hww]
        · have hn : ¬ nameOf (upS σ β) = a + 1 := fun h => (hcond.2 h).elim hβ₁ hβ₂
          simp only [sstr, subst, ite_eq_right hβ₁, ite_eq_right hβ₂, ite_eq_right hn, hname, ih]

/-! ### Stability of reduction under structural substitution -/

theorem transGen_mu (β : ℕ) {t t' : Tm} (h : Relation.TransGen Step t t') :
    Relation.TransGen Step (mu β t) (mu β t') :=
  Relation.TransGen.lift (mu β) (fun _ _ hs => Step.mu β hs) _ _ h

theorem transGen_lam {t t' : Tm} (h : Relation.TransGen Step t t') :
    Relation.TransGen Step (lam t) (lam t') :=
  Relation.TransGen.lift lam (fun _ _ hs => Step.lam hs) _ _ h

theorem transGen_appL (u : Tm) {t t' : Tm} (h : Relation.TransGen Step t t') :
    Relation.TransGen Step (app t u) (app t' u) :=
  Relation.TransGen.lift (fun t => app t u) (fun _ _ hs => Step.appL u hs) _ _ h

theorem transGen_appR (t : Tm) {u u' : Tm} (h : Relation.TransGen Step u u') :
    Relation.TransGen Step (app t u) (app t u') :=
  Relation.TransGen.lift (fun u => app t u) (fun _ _ hs => Step.appR t hs) _ _ h

/-- **Reduction is stable under structural substitution** at a name `a` that is not used as a
term variable. -/
theorem step_sstr {t t' : Tm} (hs : Step t t') :
    ∀ (a : ℕ) (v : Tm), TmFree a t → Relation.TransGen Step (sstr a v t) (sstr a v t') := by
  induction hs with
  | beta t u =>
      intro a v hfree
      have hu : u ≠ var a := by
        intro h; subst h; exact hfree.2 rfl
      have hτ : (fun i => sstr a v (single u i)) = single (sstr a v u) := by
        funext i; cases i <;> rfl
      have hinj : ∀ i j, single u i = var j → j = a → i = a + 1 := by
        intro i j hi hj
        cases i with
        | zero => subst hj; exact absurd hi hu
        | succ i => simp only [single, var.injEq] at hi; omega
      have hv : subst (fun i => sstr a v (single u i)) (ren Nat.succ v) = v := by
        rw [hτ]; exact subst_single_ren _ _
      have key := sstr_subst t (single u) a (a + 1) v (ren Nat.succ v) rfl hinj hv
      rw [hτ] at key
      show Relation.TransGen Step (app (lam (sstr (a + 1) (ren Nat.succ v) t)) (sstr a v u))
        (sstr a v (subst (single u) t))
      rw [key]
      exact .single (Step.beta _ _)
  | struct β t u =>
      intro a v _
      have hcomm := sstr_sstr t 0 (a + 1) (ren Nat.succ u) (ren Nat.succ v) (by omega)
        (nameFree_zero_ren_succ v)
      have hu : sstr (a + 1) (ren Nat.succ v) (ren Nat.succ u) = ren Nat.succ (sstr a v u) :=
        (sstr_ren_succ a v u).symm
      rw [hu] at hcomm
      have hv0 : sstr 0 (ren Nat.succ (sstr a v u)) (ren Nat.succ v) = ren Nat.succ v :=
        sstr_nameFree _ _ _ (nameFree_zero_ren_succ v)
      have hst := Step.struct β
        (if β = a + 1 then app (sstr (a + 1) (ren Nat.succ v) t) (ren Nat.succ v)
          else sstr (a + 1) (ren Nat.succ v) t) (sstr a v u)
      by_cases h0 : β = 0
      · subst h0
        have hne : ¬ (0 : ℕ) = a + 1 := by omega
        simp only [ite_eq_right hne, ↓reduceIte] at hst
        simp only [sstr, ite_eq_right hne, ↓reduceIte, hu, hcomm]
        exact .single hst
      · by_cases ha : β = a + 1
        · simp only [ite_eq_left ha, ite_eq_right h0, sstr, hv0] at hst
          simp only [sstr, ite_eq_right h0, ite_eq_left ha, hcomm]
          exact .single hst
        · simp only [ite_eq_right ha, ite_eq_right h0] at hst
          simp only [sstr, ite_eq_right h0, ite_eq_right ha, hcomm]
          exact .single hst
  | rename β γ t =>
      intro a v _
      have hV : ∀ w, subst (single w) (ren Nat.succ (ren Nat.succ v)) = ren Nat.succ v :=
        fun w => subst_single_ren _ _
      have hSfun : ∀ b, (fun i => sstr (a + 1) (ren Nat.succ v) (single (var b) i)) =
          single (var b) := by
        intro b; funext i; cases i <;> rfl
      have hne0 : ¬ (0 = a + 1 + 1) := by omega
      by_cases hβ : β = a + 1
      · -- the renaming redex sits at the substituted name: one structural step, then renaming
        subst hβ
        have hinj : ∀ i j, single (var (a + 1)) i = var j → j = a + 1 → i = 0 ∨ i = a + 1 + 1 := by
          intro i j hi hj
          cases i with
          | zero => left; rfl
          | succ i => simp only [single, var.injEq] at hi; right; omega
        have hv : subst (fun i => sstr (a + 1) (ren Nat.succ v) (single (var (a + 1)) i))
            (ren Nat.succ (ren Nat.succ v)) = ren Nat.succ v := by rw [hSfun]; exact hV _
        have key := sstr_subst2 t (single (var (a + 1))) (a + 1) 0 (a + 1 + 1) (ren Nat.succ v)
          (ren Nat.succ (ren Nat.succ v)) (by omega) rfl rfl hinj
          (nameFree_zero_ren_succ _) hv
        rw [hSfun] at key
        have hVV : sstr 0 (ren Nat.succ (ren Nat.succ v)) (ren Nat.succ (ren Nat.succ v)) =
            ren Nat.succ (ren Nat.succ v) := sstr_nameFree _ _ _ (nameFree_zero_ren_succ _)
        have h1 := Step.struct γ (if γ = a + 1 + 1 then
            app (sstr (a + 1 + 1) (ren Nat.succ (ren Nat.succ v)) t) (ren Nat.succ (ren Nat.succ v))
          else sstr (a + 1 + 1) (ren Nat.succ (ren Nat.succ v)) t) (ren Nat.succ v)
        have h2 := Step.rename (a + 1) γ (if γ = 0 then
            app (sstr 0 (ren Nat.succ (ren Nat.succ v)) (if γ = a + 1 + 1 then
              app (sstr (a + 1 + 1) (ren Nat.succ (ren Nat.succ v)) t)
                (ren Nat.succ (ren Nat.succ v))
            else sstr (a + 1 + 1) (ren Nat.succ (ren Nat.succ v)) t))
              (ren Nat.succ (ren Nat.succ v))
          else sstr 0 (ren Nat.succ (ren Nat.succ v)) (if γ = a + 1 + 1 then
              app (sstr (a + 1 + 1) (ren Nat.succ (ren Nat.succ v)) t)
                (ren Nat.succ (ren Nat.succ v))
            else sstr (a + 1 + 1) (ren Nat.succ (ren Nat.succ v)) t))
        have hL : sstr a v (mu (a + 1) (mu γ t)) = mu (a + 1) (app (mu γ (if γ = a + 1 + 1 then
            app (sstr (a + 1 + 1) (ren Nat.succ (ren Nat.succ v)) t) (ren Nat.succ (ren Nat.succ v))
          else sstr (a + 1 + 1) (ren Nat.succ (ren Nat.succ v)) t)) (ren Nat.succ v)) := by
          simp only [sstr, ↓reduceIte]
        rw [hL]
        refine Relation.TransGen.head (Step.mu _ h1) (.single ?_)
        refine (congrArg (Step _) ?_).mp h2
        cases γ with
        | zero =>
            show mu (a + 1) (subst (single (var (a + 1))) _) =
              sstr a v (mu (a + 1) (subst (single (var (a + 1))) t))
            simp only [sstr, ↓reduceIte, hne0, subst, hV, key]
        | succ g =>
            have hg0 : ¬ (g + 1 = 0) := by omega
            by_cases hg : g = a + 1
            · subst hg
              show mu (a + 1) (subst (single (var (a + 1))) _) =
                sstr a v (mu (a + 1) (subst (single (var (a + 1))) t))
              simp only [sstr, ↓reduceIte, hg0, subst, hV, key, hVV]
            · have hg' : ¬ (g + 1 = a + 1 + 1) := by omega
              show mu g (subst (single (var (a + 1))) _) =
                sstr a v (mu g (subst (single (var (a + 1))) t))
              simp only [sstr, hg, hg', hg0, ↓reduceIte, key]
      · -- the renaming redex is not at the substituted name: one renaming step
        have hinj : ∀ i j, single (var β) i = var j → j = a + 1 → i = a + 1 + 1 := by
          intro i j hi hj
          cases i with
          | zero => simp only [single, var.injEq] at hi; omega
          | succ i => simp only [single, var.injEq] at hi; omega
        have hv : subst (fun i => sstr (a + 1) (ren Nat.succ v) (single (var β) i))
            (ren Nat.succ (ren Nat.succ v)) = ren Nat.succ v := by rw [hSfun]; exact hV _
        have key := sstr_subst t (single (var β)) (a + 1) (a + 1 + 1) (ren Nat.succ v)
          (ren Nat.succ (ren Nat.succ v)) rfl hinj hv
        rw [hSfun] at key
        have h2 := Step.rename β γ (if γ = a + 1 + 1 then
            app (sstr (a + 1 + 1) (ren Nat.succ (ren Nat.succ v)) t) (ren Nat.succ (ren Nat.succ v))
          else sstr (a + 1 + 1) (ren Nat.succ (ren Nat.succ v)) t)
        have hL : sstr a v (mu β (mu γ t)) = mu β (mu γ (if γ = a + 1 + 1 then
            app (sstr (a + 1 + 1) (ren Nat.succ (ren Nat.succ v)) t) (ren Nat.succ (ren Nat.succ v))
          else sstr (a + 1 + 1) (ren Nat.succ (ren Nat.succ v)) t)) := by
          simp only [sstr, hβ, ↓reduceIte]
        rw [hL]
        refine .single ((congrArg (Step _) ?_).mp h2)
        cases γ with
        | zero =>
            show mu β (subst (single (var β)) _) = sstr a v (mu β (subst (single (var β)) t))
            simp only [sstr, hβ, hne0, ↓reduceIte, key]
        | succ g =>
            by_cases hg : g = a + 1
            · subst hg
              show mu (a + 1) (subst (single (var β)) _) =
                sstr a v (mu (a + 1) (subst (single (var β)) t))
              simp only [sstr, ↓reduceIte, subst, hV, key]
            · have hg' : ¬ (g + 1 = a + 1 + 1) := by omega
              show mu g (subst (single (var β)) _) = sstr a v (mu g (subst (single (var β)) t))
              simp only [sstr, hg, hg', ↓reduceIte, key]
  | lam _ ih =>
      intro a v hfree
      exact transGen_lam (ih (a + 1) _ hfree)
  | appL u _ ih =>
      intro a v hfree
      exact transGen_appL _ (ih a v hfree.1)
  | appR t _ ih =>
      intro a v hfree
      exact transGen_appR _ (ih a v hfree.2)
  | mu β _ ih =>
      intro a v hfree
      by_cases hβ : β = a + 1
      · simp only [sstr, ite_eq_left hβ]
        exact transGen_mu _ (transGen_appL _ (ih (a + 1) _ hfree))
      · simp only [sstr, ite_eq_right hβ]
        exact transGen_mu _ (ih (a + 1) _ hfree)

end Tm

/-- **Reduction is stable under structural substitution** (the first missing lemma of round 4):
for a name `a` that is not used as a term variable, a step of `t` gives at least one step of
`t[[a](w v)/[a]w]`. -/
theorem Step.sstr {t t' : Tm} (hs : Step t t') (a : ℕ) (v : Tm) (ha : Tm.TmFree a t) :
    Relation.TransGen Step (Tm.sstr a v t) (Tm.sstr a v t') :=
  Tm.step_sstr hs a v ha

/-- In a well-typed term, a name of the context is never used as a term variable. -/
theorem Typ.tmFree {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) :
    ∀ (a : ℕ) (B : Ty), Γ[a]? = some (.nm B) → Tm.TmFree a t := by
  induction h with
  | @var Γ i A hi =>
      intro a B ha hia
      subst hia
      rw [ha] at hi
      cases hi
  | lam _ ih => intro a B ha; exact ih (a + 1) B (by simpa using ha)
  | app _ _ iht ihu => intro a B ha; exact ⟨iht a B ha, ihu a B ha⟩
  | mu _ _ ih => intro a B ha; exact ih (a + 1) B (by simpa using ha)

/-- **Typed form of `Step.sstr`**: structural substitution at a name of the context. -/
theorem Step.sstr_of_typ {Γ : List Entry} {t t' : Tm} {A B : Ty} (h : Typ Γ t A)
    (hs : Step t t') {a : ℕ} (ha : Γ[a]? = some (.nm B)) (v : Tm) :
    Relation.TransGen Step (Tm.sstr a v t) (Tm.sstr a v t') :=
  Step.sstr hs a v (h.tmFree a B ha)

end LambdaMu
