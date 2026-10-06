/-
**Principal types**: algorithm W is complete, every typable term has a principal type which W
computes, and Hindley–Milner typability is decidable.

`Start/HMAlgorithmW.lean` proved that W is sound.  This module proves the converse
(Damas–Milner 1982): every typing of a term in any substitution instance of the context is an
instance of the one W computes.

* `HM.W_inv` — the bookkeeping invariant of the supply of fresh variables: the returned type,
  and the returned substitution on the old variables, only mention variables below the new
  supply;
* `HM.W_complete` — **completeness of W**: if `s'Γ ⊢ e : τ'` then W succeeds on `Γ, e`, with
  `(s, τ)`, and there is `r` with `τ' = rτ` and `s' = r ∘ s` on the variables of `Γ`;
* `HM.principal` — **principal typings**: a term typable in some instance of `Γ` has a typing
  `(s, τ)` of which every other is an instance, and W computes it;
* `HM.principal_closed` — for closed terms: a typable term has a principal type `τ`, computed by
  W, and its types are exactly the substitution instances of `τ`;
* `HM.W_none_iff`, `HM.W_closed_none_iff` — **W fails exactly on the untypable terms**;
* `HM.typable_iff` and the instance `HM.decTypable` — **typability in a given context is
  decidable**: run W, then check that the substitution it returns is an injective renaming on the
  free type variables of the context.  System F, by contrast, has undecidable typability.
-/

import Start.HMAlgorithmW

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace HM

open Ty

/-! ### Variables below a bound -/

/-- Every variable of `t` is below `k`. -/
def Below (k : ℕ) (t : Ty) : Prop := ∀ w ∈ t.vars, w < k

theorem Below.mono {k k' : ℕ} (h : k ≤ k') {t : Ty} (ht : Below k t) : Below k' t :=
  fun w hw => lt_of_lt_of_le (ht w hw) h

theorem Below.subst {k k' : ℕ} {t : Ty} {s : ℕ → Ty} (ht : Below k t)
    (hs : ∀ v < k, Below k' (s v)) : Below k' (t.subst s) := fun w hw => by
  obtain ⟨v, hv, hw⟩ := mem_vars_subst.1 hw
  exact hs v (ht v hv) w hw

theorem subst_eq_of_below {k : ℕ} {t : Ty} {s s' : ℕ → Ty} (ht : Below k t)
    (h : ∀ v < k, s v = s' v) : t.subst s = t.subst s' :=
  Ty.subst_congr fun v hv => h v (ht v hv)

theorem vars_inst {σ : Sch} {ts : ℕ → Ty} {w : ℕ} (hw : w ∈ (σ.inst ts).vars) :
    w ∈ σ.fvs ∨ ∃ k < σ.bnd, w ∈ (ts k).vars := by
  induction σ with
  | fv v => left; simpa [Sch.inst, Sch.inst2, Sch.fvs] using hw
  | bv k => exact Or.inr ⟨k, by simp [Sch.bnd], by simpa [Sch.inst, Sch.inst2] using hw⟩
  | con c => simp [Sch.inst, Sch.inst2] at hw
  | arrow a b iha ihb =>
    simp only [Sch.inst, Sch.inst2, vars_arrow, Finset.mem_union] at hw
    rcases hw with hw | hw
    · rcases iha hw with h | ⟨k, hk, h⟩
      · exact Or.inl (by simp [Sch.fvs, h])
      · exact Or.inr ⟨k, lt_of_lt_of_le hk (by simp [Sch.bnd]), h⟩
    · rcases ihb hw with h | ⟨k, hk, h⟩
      · exact Or.inl (by simp [Sch.fvs, h])
      · exact Or.inr ⟨k, lt_of_lt_of_le hk (by simp [Sch.bnd]), h⟩

/-! ### The invariant of the supply of fresh variables -/

/-- **The fresh-variable invariant of W.**  If the free variables of `Γ` are below `n` and
`W Γ e n = some (s, τ, m)`, then `n ≤ m`, the type `τ` is below `m`, and `s` maps every variable
below `n` to a type below `m`. -/
theorem W_inv {e : Expr} :
    ∀ {Γ : List Sch} {n : ℕ} {s : ℕ → Ty} {τ : Ty} {m : ℕ},
      W Γ e n = some (s, τ, m) → (∀ v ∈ ctxFvs Γ, v < n) →
      n ≤ m ∧ Below m τ ∧ ∀ v < n, Below m (s v) := by
  induction e with
  | var i =>
    intro Γ n s τ m h hfv
    simp only [W] at h
    cases hi : Γ[i]? with
    | none => simp [hi] at h
    | some σ =>
      simp only [hi, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨Nat.le_add_right _ _, fun w hw => ?_, fun v hv w hw => ?_⟩
      · rcases vars_inst hw with h | ⟨k, hk, h⟩
        · have := hfv w (fvs_subset_ctxFvs hi h); omega
        · simp at h; omega
      · simp at hw; omega
  | lam e ih =>
    intro Γ n s τ m h hfv
    simp only [W] at h
    cases hw : W (Sch.ofTy (Ty.var n) :: Γ) e (n + 1) with
    | none => simp [hw] at h
    | some r =>
      obtain ⟨s₁, τ₁, m₁⟩ := r
      simp only [hw, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hfv' : ∀ v ∈ ctxFvs (Sch.ofTy (Ty.var n) :: Γ), v < n + 1 := by
        intro v hv
        simp only [ctxFvs_cons, Sch.fvs_ofTy, vars_var, Finset.mem_union,
          Finset.mem_singleton] at hv
        rcases hv with rfl | hv
        · omega
        · have := hfv v hv; omega
      obtain ⟨h1, h2, h3⟩ := ih hw hfv'
      refine ⟨by omega, fun w hw => ?_, fun v hv => h3 v (by omega)⟩
      simp only [vars_arrow, Finset.mem_union] at hw
      rcases hw with hw | hw
      · exact h3 n (by omega) w hw
      · exact h2 w hw
  | app e₁ e₂ ih₁ ih₂ =>
    intro Γ n s τ m h hfv
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
          obtain ⟨a1, a2, a3⟩ := ih₁ hw₁ hfv
          have hfv₁ : ∀ v ∈ ctxFvs (ctxSubst s₁ Γ), v < m₁ := by
            intro w hw
            obtain ⟨v, hv, hw⟩ := mem_ctxFvs_subst.1 hw
            exact a3 v (hfv v hv) w hw
          obtain ⟨b1, b2, b3⟩ := ih₂ hw₂ hfv₁
          -- the unifier keeps everything below `m₂ + 1`
          have hl : Below (m₂ + 1) (τ₁.subst s₂) := (a2.subst b3).mono (by omega)
          have hr : Below (m₂ + 1) (Ty.arrow τ₂ (Ty.var m₂)) := fun w hw => by
            simp only [vars_arrow, vars_var, Finset.mem_union, Finset.mem_singleton] at hw
            rcases hw with hw | rfl
            · have := b2 w hw; omega
            · omega
          have hu' : ∀ v < m₂ + 1, Below (m₂ + 1) (u v) := fun v hv w hw => by
            have := mgu_vars hu v hw
            simp only [Finset.mem_insert, Finset.mem_union] at this
            rcases this with rfl | h | h
            · exact hv
            · exact hl w h
            · exact hr w h
          refine ⟨by omega, hu' m₂ (by omega), fun v hv => ?_⟩
          change Below (m₂ + 1) (((s₁ v).subst s₂).subst u)
          exact ((((a3 v hv).subst b3).mono (by omega)).subst hu')
  | let_ e₁ e₂ ih₁ ih₂ =>
    intro Γ n s τ m h hfv
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
        obtain ⟨a1, a2, a3⟩ := ih₁ hw₁ hfv
        have hfv₁ : ∀ v ∈ ctxFvs (ctxSubst s₁ Γ), v < m₁ := by
          intro w hw
          obtain ⟨v, hv, hw⟩ := mem_ctxFvs_subst.1 hw
          exact a3 v (hfv v hv) w hw
        have hfv₂ : ∀ v ∈ ctxFvs (gen (ctxSubst s₁ Γ) τ₁ :: ctxSubst s₁ Γ), v < m₁ := by
          intro v hv
          simp only [ctxFvs_cons, Finset.mem_union] at hv
          rcases hv with hv | hv
          · exact hfv₁ v (fvs_gen'_subset _ _ hv)
          · exact hfv₁ v hv
        obtain ⟨b1, b2, b3⟩ := ih₂ hw₂ hfv₂
        exact ⟨by omega, b2, fun v hv => (a3 v hv).subst b3⟩

/-! ### Completeness -/

/-- **Completeness of algorithm W.**  If some substitution instance `s'Γ` of the context types
`e` with `τ'`, then W succeeds, and its answer `(s, τ)` is more general: `τ' = rτ` and `s'`
agrees with `r ∘ s` on every variable below the supply `n`. -/
theorem W_complete {e : Expr} :
    ∀ {Γ : List Sch} {n : ℕ} {s' : ℕ → Ty} {τ' : Ty}, (∀ v ∈ ctxFvs Γ, v < n) →
      Typing (ctxSubst s' Γ) e τ' →
      ∃ s τ m, W Γ e n = some (s, τ, m) ∧
        ∃ r : ℕ → Ty, τ' = τ.subst r ∧ ∀ v < n, s' v = (s v).subst r := by
  induction e with
  | var i =>
    intro Γ n s' τ' hfv h
    cases h with
    | @var _ _ σ' ts hi' =>
      cases hi : Γ[i]? with
      | none => simp [ctxSubst, hi] at hi'
      | some σ =>
        rw [getElem?_ctxSubst hi, Option.some.injEq] at hi'
        subst hi'
        refine ⟨Ty.var, σ.inst fun k => Ty.var (n + k), n + σ.bnd, by simp [W, hi],
          fun v => if v < n then s' v else ts (v - n), ?_, fun v hv => by simp [hv]⟩
        rw [Sch.subst_inst]
        have hk : (fun k => (Ty.var (n + k)).subst
            fun v => if v < n then s' v else ts (v - n)) = ts := by
          funext k; simp
        rw [hk]
        congr 1
        exact Sch.subst_congr fun v hv => by
          simp [hfv v (fvs_subset_ctxFvs hi hv)]
  | lam e ih =>
    intro Γ n s' τ' hfv h
    cases h with
    | @lam _ _ A B ht =>
      set s'' : ℕ → Ty := fun v => if v = n then A else s' v
      have hctx : ctxSubst s'' (Sch.ofTy (Ty.var n) :: Γ) = Sch.ofTy A :: ctxSubst s' Γ := by
        simp only [ctxSubst_cons, Sch.ofTy_subst, subst_var', s'', if_true, List.cons.injEq,
          true_and]
        exact ctxSubst_congr fun v hv => by
          have := hfv v hv
          simp [show v ≠ n by omega]
      have hfv' : ∀ v ∈ ctxFvs (Sch.ofTy (Ty.var n) :: Γ), v < n + 1 := by
        intro v hv
        simp only [ctxFvs_cons, Sch.fvs_ofTy, vars_var, Finset.mem_union,
          Finset.mem_singleton] at hv
        rcases hv with rfl | hv
        · omega
        · have := hfv v hv; omega
      obtain ⟨s, τ, m, hw, r, hτ, hs⟩ := ih hfv' (hctx ▸ ht)
      refine ⟨s, Ty.arrow (s n) τ, m, by simp [W, hw], r, ?_, fun v hv => ?_⟩
      · rw [subst_arrow, ← hτ, ← hs n (by omega)]
        simp [s'']
      · rw [← hs v (by omega)]
        simp [s'', show v ≠ n by omega]
  | app e₁ e₂ ih₁ ih₂ =>
    intro Γ n s' τ' hfv h
    cases h with
    | @app _ _ _ A _ ha hb =>
      obtain ⟨s₁, τ₁, m₁, hw₁, r₁, hτ₁, hs₁⟩ := ih₁ hfv ha
      obtain ⟨a1, a2, a3⟩ := W_inv hw₁ hfv
      have hctx₁ : ctxSubst s' Γ = ctxSubst r₁ (ctxSubst s₁ Γ) := by
        rw [← ctxSubst_comp]
        exact ctxSubst_congr fun v hv => hs₁ v (hfv v hv)
      have hfv₁ : ∀ v ∈ ctxFvs (ctxSubst s₁ Γ), v < m₁ := by
        intro w hw
        obtain ⟨v, hv, hw⟩ := mem_ctxFvs_subst.1 hw
        exact a3 v (hfv v hv) w hw
      obtain ⟨s₂, τ₂, m₂, hw₂, r₂, hτ₂, hs₂⟩ := ih₂ hfv₁ (hctx₁ ▸ hb)
      obtain ⟨b1, b2, b3⟩ := W_inv hw₂ hfv₁
      set r₃ : ℕ → Ty := fun v => if v = m₂ then τ' else r₂ v
      have hr₃ : ∀ t, Below m₂ t → t.subst r₃ = t.subst r₂ := fun t ht =>
        subst_eq_of_below ht fun v hv => by simp [r₃, show v ≠ m₂ by omega]
      have hkey : ∀ t, Below m₁ t → (t.subst s₂).subst r₃ = t.subst r₁ := by
        intro t ht
        rw [Ty.subst_subst]
        exact subst_eq_of_below ht fun v hv => by
          rw [hr₃ _ (b3 v hv), ← hs₂ v hv]
      have hunif : (τ₁.subst s₂).subst r₃ = (Ty.arrow τ₂ (Ty.var m₂)).subst r₃ := by
        rw [hkey τ₁ a2, ← hτ₁, subst_arrow, hr₃ τ₂ b2, ← hτ₂]
        simp [r₃]
      cases hu : mgu (τ₁.subst s₂) (Ty.arrow τ₂ (Ty.var m₂)) with
      | none => exact absurd hunif (mgu_none hu r₃)
      | some u =>
        have hmg := mgu_most_general hu hunif
        have hfac : ∀ t : Ty, (t.subst u).subst r₃ = t.subst r₃ := fun t => by
          rw [Ty.subst_subst]; exact congrArg (Ty.subst · t) (funext hmg)
        refine ⟨comp (comp s₁ s₂) u, u m₂, m₂ + 1, by simp [W, hw₁, hw₂, hu], r₃, ?_,
          fun v hv => ?_⟩
        · rw [hmg]; simp [r₃]
        · change s' v = (((s₁ v).subst s₂).subst u).subst r₃
          rw [hfac, hkey _ (a3 v hv), hs₁ v hv]
  | let_ e₁ e₂ ih₁ ih₂ =>
    intro Γ n s' τ' hfv h
    cases h with
    | @let_ _ _ _ A _ ha hb =>
      obtain ⟨s₁, τ₁, m₁, hw₁, r₁, hτ₁, hs₁⟩ := ih₁ hfv ha
      obtain ⟨a1, a2, a3⟩ := W_inv hw₁ hfv
      have hctx₁ : ctxSubst s' Γ = ctxSubst r₁ (ctxSubst s₁ Γ) := by
        rw [← ctxSubst_comp]
        exact ctxSubst_congr fun v hv => hs₁ v (hfv v hv)
      have hfv₁ : ∀ v ∈ ctxFvs (ctxSubst s₁ Γ), v < m₁ := by
        intro w hw
        obtain ⟨v, hv, hw⟩ := mem_ctxFvs_subst.1 hw
        exact a3 v (hfv v hv) w hw
      have hfv₂ : ∀ v ∈ ctxFvs (gen (ctxSubst s₁ Γ) τ₁ :: ctxSubst s₁ Γ), v < m₁ := by
        intro v hv
        simp only [ctxFvs_cons, Finset.mem_union] at hv
        rcases hv with hv | hv
        · exact hfv₁ v (fvs_gen'_subset _ _ hv)
        · exact hfv₁ v hv
      have hb' : Typing (ctxSubst r₁ (gen (ctxSubst s₁ Γ) τ₁ :: ctxSubst s₁ Γ)) e₂ τ' := by
        rw [hctx₁, hτ₁] at hb
        rw [ctxSubst_cons]
        refine hb.mono (List.Forall₂.cons ?_ (List.forall₂_same.2 fun σ _ => MoreGen.refl σ))
        exact moreGen_subst_gen _ _ r₁ τ₁ fun v hv w hw => mem_ctxFvs_subst.2 ⟨v, hv, hw⟩
      obtain ⟨s₂, τ₂, m₂, hw₂, r₂, hτ₂, hs₂⟩ := ih₂ hfv₂ hb'
      refine ⟨comp s₁ s₂, τ₂, m₂, by simp [W, hw₁, hw₂], r₂, hτ₂, fun v hv => ?_⟩
      change s' v = ((s₁ v).subst s₂).subst r₂
      rw [hs₁ v hv, Ty.subst_subst]
      exact subst_eq_of_below (a3 v hv) fun w hw => hs₂ w hw

/-! ### Principal types -/

/-- A supply of fresh variables for a context: one more than its largest free variable. -/
def ctxBound (Γ : List Sch) : ℕ := (ctxFvs Γ).sup id + 1

theorem lt_ctxBound {Γ : List Sch} {v : ℕ} (hv : v ∈ ctxFvs Γ) : v < ctxBound Γ :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) hv)

/-- **Principal typings.**  If `e` is typable in some substitution instance of `Γ`, then W
computes a typing `(s, τ)` of `e` such that every typing `(s', τ')` of `e` is an instance of it:
`τ' = rτ` and `s' = r ∘ s` on the free variables of `Γ`. -/
theorem principal {Γ : List Sch} {e : Expr} (h : ∃ s' τ', Typing (ctxSubst s' Γ) e τ') :
    ∃ s τ m, W Γ e (ctxBound Γ) = some (s, τ, m) ∧ Typing (ctxSubst s Γ) e τ ∧
      ∀ s' τ', Typing (ctxSubst s' Γ) e τ' →
        ∃ r : ℕ → Ty, τ' = τ.subst r ∧ ∀ v ∈ ctxFvs Γ, s' v = (s v).subst r := by
  obtain ⟨s₀, τ₀, h₀⟩ := h
  obtain ⟨s, τ, m, hw, -⟩ := W_complete (fun v hv => lt_ctxBound hv) h₀
  refine ⟨s, τ, m, hw, W_sound hw, fun s' τ' h' => ?_⟩
  obtain ⟨s₁, τ₁, m₁, hw₁, r, hτ, hs⟩ := W_complete (fun v hv => lt_ctxBound hv) h'
  rw [hw] at hw₁
  simp only [Option.some.injEq, Prod.mk.injEq] at hw₁
  obtain ⟨rfl, rfl, rfl⟩ := hw₁
  exact ⟨r, hτ, fun v hv => hs v (lt_ctxBound hv)⟩

/-- **Every typable closed term has a principal type, and W computes it**: the types of `e` are
exactly the substitution instances of the type `τ` returned by W. -/
theorem principal_closed {e : Expr} (h : ∃ τ, Typing [] e τ) :
    ∃ s τ m, W [] e 0 = some (s, τ, m) ∧ ∀ τ', Typing [] e τ' ↔ ∃ r : ℕ → Ty, τ' = τ.subst r := by
  obtain ⟨τ₀, h₀⟩ := h
  obtain ⟨s, τ, m, hw, -⟩ := W_complete (Γ := []) (n := 0) (s' := Ty.var) (by simp) h₀
  refine ⟨s, τ, m, hw, fun τ' => ⟨fun h' => ?_, ?_⟩⟩
  · obtain ⟨s₁, τ₁, m₁, hw₁, r, hτ, -⟩ :=
      W_complete (Γ := []) (n := 0) (s' := Ty.var) (by simp) h'
    rw [hw] at hw₁
    simp only [Option.some.injEq, Prod.mk.injEq] at hw₁
    obtain ⟨rfl, rfl, rfl⟩ := hw₁
    exact ⟨r, hτ⟩
  · rintro ⟨r, rfl⟩
    exact (W_sound_closed hw).subst r

/-- **W fails exactly on the untypable terms** (relative to the substitution instances of the
context). -/
theorem W_none_iff {Γ : List Sch} {e : Expr} {n : ℕ} (hfv : ∀ v ∈ ctxFvs Γ, v < n) :
    W Γ e n = none ↔ ¬ ∃ s' τ', Typing (ctxSubst s' Γ) e τ' := by
  constructor
  · rintro hw ⟨s', τ', h⟩
    obtain ⟨s, τ, m, hw', -⟩ := W_complete hfv h
    rw [hw] at hw'; cases hw'
  · intro h
    cases hw : W Γ e n with
    | none => rfl
    | some r =>
      obtain ⟨s, τ, m⟩ := r
      exact absurd ⟨s, τ, W_sound hw⟩ h

/-- For closed terms: W fails exactly when the term has no type. -/
theorem W_closed_none_iff {e : Expr} : W [] e 0 = none ↔ ¬ ∃ τ, Typing [] e τ := by
  rw [W_none_iff (by simp)]
  simp only [ctxSubst, List.map_nil, not_exists]
  exact ⟨fun h x => h (fun _ => Ty.var 0) x, fun h _ x => h x⟩

/-- **Typability of closed terms is decidable**, by running W. -/
instance decTypableClosed (e : Expr) : Decidable (∃ τ, Typing [] e τ) :=
  decidable_of_iff ((W [] e 0).isSome) <| by
    rw [← not_iff_not, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
      W_closed_none_iff]

/-! ### Typability in a given context -/

/-- Whether a type is a variable. -/
def Ty.isVar : Ty → Bool
  | Ty.var _ => true
  | _ => false

/-- `s` is an injective renaming on the finite set `A`. -/
def RenamingOn (s : ℕ → Ty) (A : Finset ℕ) : Prop :=
  (∀ v ∈ A, (s v).isVar = true) ∧ ∀ v ∈ A, ∀ v' ∈ A, s v = s v' → v = v'

instance (s : ℕ → Ty) (A : Finset ℕ) : Decidable (RenamingOn s A) := by
  unfold RenamingOn; infer_instance

/-- A substitution can be undone on `A` exactly when it is an injective renaming there. -/
theorem exists_inverse_iff (s : ℕ → Ty) (A : Finset ℕ) :
    (∃ r : ℕ → Ty, ∀ v ∈ A, (s v).subst r = Ty.var v) ↔ RenamingOn s A := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨fun v hv => ?_, fun v hv v' hv' hvv' => ?_⟩
    · have := hr v hv
      cases hs : s v with
      | var w => rfl
      | con c => rw [hs] at this; simp at this
      | arrow a b => rw [hs] at this; simp at this
    · have h1 := hr v hv
      have h2 := hr v' hv'
      rw [hvv', h2] at h1
      exact (Ty.var.inj h1).symm
  · rintro ⟨hvar, hinj⟩
    classical
    refine ⟨fun w => if h : ∃ v ∈ A, s v = Ty.var w then Ty.var h.choose else Ty.var w,
      fun v hv => ?_⟩
    cases hs : s v with
    | var w =>
      have hex : ∃ v ∈ A, s v = Ty.var w := ⟨v, hv, hs⟩
      simp only [subst_var', hex, dif_pos]
      obtain ⟨hA, hc⟩ := hex.choose_spec
      rw [hinj _ hA v hv (hc.trans hs.symm)]
    | con c => have := hvar v hv; rw [hs] at this; simp [Ty.isVar] at this
    | arrow a b => have := hvar v hv; rw [hs] at this; simp [Ty.isVar] at this

/-- **Typability in a context, through W**: `e` is typable in `Γ` iff W succeeds and the
substitution it returns is an injective renaming on the free type variables of `Γ`. -/
theorem typable_iff (Γ : List Sch) (e : Expr) :
    (∃ τ, Typing Γ e τ) ↔
      ∃ s τ m, W Γ e (ctxBound Γ) = some (s, τ, m) ∧ RenamingOn s (ctxFvs Γ) := by
  constructor
  · rintro ⟨τ', h⟩
    have h' : Typing (ctxSubst Ty.var Γ) e τ' := by rwa [ctxSubst_var]
    obtain ⟨s, τ, m, hw, r, -, hs⟩ := W_complete (fun v hv => lt_ctxBound hv) h'
    exact ⟨s, τ, m, hw, (exists_inverse_iff s _).1
      ⟨r, fun v hv => (hs v (lt_ctxBound hv)).symm⟩⟩
  · rintro ⟨s, τ, m, hw, hren⟩
    obtain ⟨r, hr⟩ := (exists_inverse_iff s _).2 hren
    have := (W_sound hw).subst r
    rw [← ctxSubst_comp, ctxSubst_congr (s := comp s r) (s' := Ty.var) (fun v hv => hr v hv),
      ctxSubst_var] at this
    exact ⟨_, this⟩

/-- **Hindley–Milner typability is decidable** in every context. -/
instance decTypable (Γ : List Sch) (e : Expr) : Decidable (∃ τ, Typing Γ e τ) :=
  decidable_of_iff
    ((match W Γ e (ctxBound Γ) with
      | none => false
      | some (s, _, _) => decide (RenamingOn s (ctxFvs Γ))) = true) <| by
    rw [typable_iff]
    cases W Γ e (ctxBound Γ) with
    | none => simp
    | some r =>
      obtain ⟨s, τ, m⟩ := r
      simp

/-! ### Sanity check -/

theorem Typing.var_inv {Γ : List Sch} {i : ℕ} {τ : Ty} (h : Typing Γ (Expr.var i) τ) :
    ∃ σ ts, Γ[i]? = some σ ∧ τ = σ.inst ts := by
  cases h with
  | var ts hi => exact ⟨_, ts, hi, rfl⟩

theorem Typing.app_inv {Γ : List Sch} {a b : Expr} {τ : Ty} (h : Typing Γ (Expr.app a b) τ) :
    ∃ A, Typing Γ a (Ty.arrow A τ) ∧ Typing Γ b A := by
  cases h with
  | app ha hb => exact ⟨_, ha, hb⟩

/-- The self-application `λx. x x` has no Hindley–Milner type (the occurs check), so by
`HM.W_closed_none_iff` algorithm W fails on it. -/
theorem not_typable_selfApp :
    ¬ ∃ τ, Typing [] (Expr.lam (Expr.app (Expr.var 0) (Expr.var 0))) τ := by
  rintro ⟨τ, h⟩
  cases h with
  | @lam _ _ A B h =>
    obtain ⟨C, h₁, h₂⟩ := h.app_inv
    obtain ⟨σ₁, ts₁, hi₁, e₁⟩ := h₁.var_inv
    obtain ⟨σ₂, ts₂, hi₂, e₂⟩ := h₂.var_inv
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi₁ hi₂
    subst hi₁ hi₂
    simp only [Sch.inst_ofTy] at e₁ e₂
    subst e₂
    have := congrArg Ty.size e₁
    simp only [Ty.size] at this
    omega

theorem W_selfApp : W [] (Expr.lam (Expr.app (Expr.var 0) (Expr.var 0))) 0 = none :=
  W_closed_none_iff.2 not_typable_selfApp

end HM
