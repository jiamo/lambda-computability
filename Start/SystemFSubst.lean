/-
The substitution calculus of the types of **System F**, and the two substitution lemmas for its
typing judgement.

`Start/SystemF.lean` needed only the raw definitions `SystemF.tyRename`, `SystemF.tySubst` and
`SystemF.tyInst`: the semantic argument for strong normalization interprets a substituted type by
reinterpreting the valuation, and never has to compute with composites of substitutions.  Subject
reduction does: it needs the syntactic laws of the calculus, and the two lemmas saying that a
typing derivation may be substituted, in its *type* variables and in its *term* variables.

* `SystemF.tyRename_tyRename`, `SystemF.tySubst_tyRename`, `SystemF.tyRename_tySubst`,
  `SystemF.tySubst_tySubst` — the composition laws, and `SystemF.tySubst_var_id`,
  `SystemF.tyInst_tyShift`, `SystemF.tySubst_tyCons_tyShift` — the cancellation laws;
* `SystemF.Typing.substTy` — **a derivation may be substituted in its type variables**:
  `Γ ⊢ t : A` implies `σ Γ ⊢ t : σ A`; `SystemF.Typing.shiftTy` is the special case of weakening
  by a fresh type variable;
* `SystemF.Typing.substEnv` — **a derivation may be substituted in its term variables**, in the
  parallel form: if every variable of `Γ` is replaced by a term of its type in `Δ`, a term of type
  `A` over `Γ` becomes a term of type `A` over `Δ`;
* `SystemF.Typing.subst_zero` — the single-variable form used by the β-rule.
-/

import Start.SystemF

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace SystemF

open Lambda

/-! ### Composition laws for type renaming and substitution -/

/-- Extending a substitution of type variables by a type at index `0`. -/
def tyCons (D : FTy) (s : ℕ → FTy) : ℕ → FTy
  | 0 => D
  | n + 1 => s n

@[simp] theorem tyCons_zero (D : FTy) (s : ℕ → FTy) : tyCons D s 0 = D := rfl

@[simp] theorem tyCons_succ (D : FTy) (s : ℕ → FTy) (n : ℕ) : tyCons D s (n + 1) = s n := rfl

theorem tyScons_eq (B : FTy) : tyScons B = tyCons B FTy.var := by
  funext i
  cases i with
  | zero => rfl
  | succ i => rfl

theorem tyRename_tyRename (r r' : ℕ → ℕ) (A : FTy) :
    tyRename r (tyRename r' A) = tyRename (fun i => r (r' i)) A := by
  induction A generalizing r r' with
  | var i => rfl
  | arrow A B ihA ihB => simp only [tyRename, ihA, ihB]
  | all A ih =>
      simp only [tyRename, ih]
      have h : (fun i => upr r (upr r' i)) = upr (fun i => r (r' i)) := by
        funext i
        cases i with
        | zero => rfl
        | succ i => rfl
      rw [h]

theorem tySubst_tyRename (s : ℕ → FTy) (r : ℕ → ℕ) (A : FTy) :
    tySubst s (tyRename r A) = tySubst (fun i => s (r i)) A := by
  induction A generalizing s r with
  | var i => rfl
  | arrow A B ihA ihB => simp only [tyRename, tySubst, ihA, ihB]
  | all A ih =>
      simp only [tyRename, tySubst, ih]
      have h : (fun i => ups s (upr r i)) = ups (fun i => s (r i)) := by
        funext i
        cases i with
        | zero => rfl
        | succ i => rfl
      rw [h]

theorem tyRename_tySubst (r : ℕ → ℕ) (s : ℕ → FTy) (A : FTy) :
    tyRename r (tySubst s A) = tySubst (fun i => tyRename r (s i)) A := by
  induction A generalizing r s with
  | var i => rfl
  | arrow A B ihA ihB => simp only [tyRename, tySubst, ihA, ihB]
  | all A ih =>
      simp only [tyRename, tySubst, ih]
      have h : (fun i => tyRename (upr r) (ups s i)) = ups (fun i => tyRename r (s i)) := by
        funext i
        cases i with
        | zero => rfl
        | succ i =>
            simp only [ups, tyShift, tyRename_tyRename]
            rfl
      rw [h]

theorem tySubst_tyShift (s : ℕ → FTy) (A : FTy) :
    tySubst (ups s) (tyShift A) = tyShift (tySubst s A) := by
  rw [tyShift, tySubst_tyRename, tyShift, tyRename_tySubst]
  rfl

theorem tySubst_tySubst (s s' : ℕ → FTy) (A : FTy) :
    tySubst s (tySubst s' A) = tySubst (fun i => tySubst s (s' i)) A := by
  induction A generalizing s s' with
  | var i => rfl
  | arrow A B ihA ihB => simp only [tySubst, ihA, ihB]
  | all A ih =>
      simp only [tySubst, ih]
      have h : (fun i => tySubst (ups s) (ups s' i)) = ups (fun i => tySubst s (s' i)) := by
        funext i
        cases i with
        | zero => rfl
        | succ i => exact tySubst_tyShift s (s' i)
      rw [h]

theorem tySubst_var_id (A : FTy) : tySubst FTy.var A = A := by
  induction A with
  | var i => rfl
  | arrow A B ihA ihB => simp only [tySubst, ihA, ihB]
  | all A ih =>
      have h : ups FTy.var = FTy.var := by
        funext i
        cases i with
        | zero => rfl
        | succ i => rfl
      simp only [tySubst, h, ih]

/-- Substituting a weakened type cancels the extension of the substitution. -/
theorem tySubst_tyCons_tyShift (D : FTy) (s : ℕ → FTy) (A : FTy) :
    tySubst (tyCons D s) (tyShift A) = tySubst s A := by
  rw [tyShift, tySubst_tyRename]
  rfl

/-- Instantiating a weakened type gives the type back. -/
theorem tyInst_tyShift (B A : FTy) : tyInst B (tyShift A) = A := by
  rw [tyInst, tyScons_eq, tySubst_tyCons_tyShift, tySubst_var_id]

/-- A renaming is the substitution by the renamed variables. -/
theorem tyRename_eq_tySubst (r : ℕ → ℕ) (A : FTy) :
    tyRename r A = tySubst (fun i => FTy.var (r i)) A := by
  induction A generalizing r with
  | var i => rfl
  | arrow A B ihA ihB => simp only [tyRename, tySubst, ihA, ihB]
  | all A ih =>
      have h : ups (fun i => FTy.var (r i)) = fun i => FTy.var (upr r i) := by
        funext i
        cases i with
        | zero => rfl
        | succ i => rfl
      simp only [tyRename, tySubst, ih, h]

/-- A weakening is the substitution by the variables shifted by one. -/
theorem tyShift_eq_tySubst (A : FTy) : tyShift A = tySubst (fun i => FTy.var (i + 1)) A :=
  tyRename_eq_tySubst Nat.succ A

/-- Substituting an instantiated type. -/
theorem tySubst_tyInst (s : ℕ → FTy) (B A : FTy) :
    tySubst s (tyInst B A) = tyInst (tySubst s B) (tySubst (ups s) A) := by
  rw [tyInst, tyInst, tySubst_tySubst, tySubst_tySubst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      change tySubst s (FTy.var i) = tySubst (tyScons (tySubst s B)) (tyShift (s i))
      rw [tyScons_eq, tySubst_tyCons_tyShift, tySubst_var_id]
      rfl

/-! ### Substitution of the type variables of a derivation -/

/-- **A typing derivation may be substituted in its type variables.** -/
theorem Typing.substTy {Γ : List FTy} {t : Lambda} {A : FTy} (h : Typing Γ t A) :
    ∀ s : ℕ → FTy, Typing (Γ.map (SystemF.tySubst s)) t (SystemF.tySubst s A) := by
  induction h with
  | @var Γ i A hi =>
      intro s
      refine Typing.var ?_
      rw [List.getElem?_map, hi]
      rfl
  | app _ _ iha ihb => intro s; exact Typing.app (iha s) (ihb s)
  | lam _ ih => intro s; exact Typing.lam (ih s)
  | @tlam Γ t A _ ih =>
      intro s
      refine Typing.tlam ?_
      have hmap : (Γ.map SystemF.tyShift).map (SystemF.tySubst (ups s))
          = (Γ.map (SystemF.tySubst s)).map SystemF.tyShift := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_congr_left fun X _ => tySubst_tyShift s X
      have := ih (ups s)
      rwa [hmap] at this
  | @tapp Γ t A B _ ih =>
      intro s
      rw [tySubst_tyInst]
      exact Typing.tapp _ (ih s)

/-- **Weakening a derivation by a fresh type variable.** -/
theorem Typing.shiftTy {Γ : List FTy} {t : Lambda} {A : FTy} (h : Typing Γ t A) :
    Typing (Γ.map SystemF.tyShift) t (SystemF.tyShift A) := by
  have := h.substTy (fun i => FTy.var (i + 1))
  have hA : SystemF.tySubst (fun i => FTy.var (i + 1)) A = SystemF.tyShift A :=
    (tyShift_eq_tySubst A).symm
  have hΓ : Γ.map (SystemF.tySubst (fun i => FTy.var (i + 1))) = Γ.map SystemF.tyShift :=
    List.map_congr_left fun X _ => (tyShift_eq_tySubst X).symm
  rwa [hA, hΓ] at this

/-! ### Weakening in the term variables -/

/-- **Weakening**, in the general form needed to go under an abstraction: a derivation survives any
reindexing of its context that inserts one variable at level `k`. -/
theorem Typing.lift_gen {Γ : List FTy} {t : Lambda} {A : FTy} (h : Typing Γ t A) :
    ∀ (k : ℕ) (Δ : List FTy),
      (∀ i A', Γ[i]? = some A' → Δ[if i < k then i else i + 1]? = some A') →
      Typing Δ (Lambda.lift 1 k t) A := by
  induction h with
  | @var Γ i A hi =>
      intro k Δ hk
      have hb := hk i A hi
      by_cases hik : i < k
      · rw [if_pos hik] at hb
        have hl : Lambda.lift 1 k (Lambda.var i) = Lambda.var i := by
          simp [Lambda.lift, hik]
        rw [hl]
        exact Typing.var hb
      · rw [if_neg hik] at hb
        have hl : Lambda.lift 1 k (Lambda.var i) = Lambda.var (i + 1) := by
          simp [Lambda.lift, hik]
        rw [hl]
        exact Typing.var hb
  | app _ _ iha ihb =>
      intro k Δ hk
      exact Typing.app (iha k Δ hk) (ihb k Δ hk)
  | @lam Γ t A B _ ih =>
      intro k Δ hk
      refine Typing.lam ?_
      refine ih (k + 1) (A :: Δ) ?_
      intro i A' hi
      cases i with
      | zero =>
          have hA : A = A' := by simpa using hi
          subst hA
          simp
      | succ j =>
          have hj : Γ[j]? = some A' := by simpa using hi
          have hb := hk j A' hj
          by_cases hjk : j < k
          · rw [if_pos hjk] at hb
            have hlt : j + 1 < k + 1 := by omega
            rw [if_pos hlt]
            simpa using hb
          · rw [if_neg hjk] at hb
            have hlt : ¬ (j + 1 < k + 1) := by omega
            rw [if_neg hlt]
            simpa using hb
  | @tlam Γ t A _ ih =>
      intro k Δ hk
      refine Typing.tlam ?_
      refine ih k (Δ.map SystemF.tyShift) ?_
      intro i A' hi
      rw [List.getElem?_map] at hi ⊢
      match hΓ : Γ[i]? with
      | none => rw [hΓ] at hi; exact absurd hi (by simp)
      | some A₀ =>
          rw [hΓ] at hi
          have hA' : SystemF.tyShift A₀ = A' := by simpa using hi
          subst hA'
          rw [hk i A₀ hΓ]
          rfl
  | tapp B _ ih =>
      intro k Δ hk
      exact Typing.tapp B (ih k Δ hk)

/-- Weakening by one variable in front of the context. -/
theorem Typing.lift_one {Δ : List FTy} {v : Lambda} {A : FTy} (h : Typing Δ v A) (B : FTy) :
    Typing (B :: Δ) (Lambda.lift 1 0 v) A := by
  refine h.lift_gen 0 (B :: Δ) ?_
  intro i A' hi
  simpa using hi

/-! ### Substitution of the term variables of a derivation -/

/-- **A typing derivation may be substituted in its term variables**, in parallel form. -/
theorem Typing.substEnv {Γ : List FTy} {t : Lambda} {A : FTy} (h : Typing Γ t A) :
    ∀ (Δ : List FTy) (u : ℕ → Lambda),
      (∀ i A', Γ[i]? = some A' → Typing Δ (u i) A') →
      Typing Δ (Lambda.substEnv u t) A := by
  induction h with
  | var hi => intro Δ u hu; exact hu _ _ hi
  | app _ _ iha ihb =>
      intro Δ u hu
      exact Typing.app (iha Δ u hu) (ihb Δ u hu)
  | @lam Γ t A B _ ih =>
      intro Δ u hu
      refine Typing.lam ?_
      refine ih (A :: Δ) (Lambda.envCons u) ?_
      intro i A' hi
      cases i with
      | zero =>
          have hA : A = A' := by simpa using hi
          subst hA
          exact Typing.var (by simp)
      | succ i =>
          have hi' : Γ[i]? = some A' := by simpa using hi
          have hshift : Lambda.envCons u (i + 1) = Lambda.lift 1 0 (u i) := rfl
          rw [hshift]
          exact (hu i A' hi').lift_one A
  | @tlam Γ t A _ ih =>
      intro Δ u hu
      refine Typing.tlam ?_
      refine ih (Δ.map SystemF.tyShift) u ?_
      intro i A' hi
      rw [List.getElem?_map] at hi
      match hΓ : Γ[i]? with
      | none => rw [hΓ] at hi; exact absurd hi (by simp)
      | some A₀ =>
          rw [hΓ] at hi
          have hA' : SystemF.tyShift A₀ = A' := by simpa using hi
          subst hA'
          exact (hu i A₀ hΓ).shiftTy
  | tapp B _ ih =>
      intro Δ u hu
      exact Typing.tapp B (ih Δ u hu)

/-- **Substituting a single term variable**, the form used by the β-rule. -/
theorem Typing.subst_zero {Γ : List FTy} {t v : Lambda} {A B : FTy}
    (ht : Typing (B :: Γ) t A) (hv : Typing Γ v B) : Typing Γ (Lambda.subst v 0 t) A := by
  have hid : Lambda.envCons (fun k => Lambda.var k) = fun k => Lambda.var k := by
    funext k
    cases k with
    | zero => rfl
    | succ k => rfl
  have hsub : Lambda.subst v 0 t
      = Lambda.substEnv (Lambda.envScons v (fun k => Lambda.var k)) t := by
    have h := Lambda.subst_zero_substEnv v t (fun k => Lambda.var k)
    rwa [hid, Lambda.substEnv_var_id] at h
  rw [hsub]
  refine ht.substEnv Γ (Lambda.envScons v (fun k => Lambda.var k)) ?_
  intro i A' hi
  cases i with
  | zero =>
      have hB : B = A' := by simpa using hi
      subst hB
      exact hv
  | succ i => exact Typing.var (by simpa using hi)

end SystemF
