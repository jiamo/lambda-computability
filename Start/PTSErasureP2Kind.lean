import Start.PTSRouteIITwoLevel
import Start.PTSErasureP2

/-!
# The erasure of λP2 types into the two-level skeletons `SkP`

Task `M29-EP-IMPREDICATIVE`, round 10, part A1.  The erasure of round 8 (`ErasureP2.er`, into
λ2 skeletons) with the quantifier `(□,∗)` recording the **kind skeleton** of the bound
constructor variable, as the two-level relation of round 9 (`RouteII.GoodP`) needs:

* `ErasureP2.erP Δ ρ T : SkP` — like `er`, except that `Π α:K. B` (rule `(□,∗)`) goes to
  `.all (erK Δ ρ K) (erP … B)`;
* `ErasureP2.erK Δ ρ K : KSkP` — `erK (Π x:A. K') = .pi (erP A) (erK K')`, `erK ∗ = .star`.

Proved, with no typing hypothesis:

* `erP_rename` / `erK_rename`, `erP_skRename` / `erK_skRename`, `erP_skSubst` / `erK_skSubst`;
* `erP_subst` / `erK_subst` — **commutation with substitution** respecting the classification;
* `erP_instantiate_obj` / `erK_instantiate_obj` — **invariance under object substitution**;
* `erP_instantiate` / `erK_instantiate` — **commutation with constructor substitution**, with
  `SkP.subst` and `KSkP.subst`.

Proved for well-typed λP2 terms:

* `erP_beta`, `erP_reduces`, `erP_conv` and `erK_beta`, `erK_reduces`, `erK_conv` — **invariance
  under β-reduction and β-conversion**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PureTypeSystem

namespace ErasureP2

open LambdaPi (Srt)
open RouteII (SkP KSkP upSP singleP upR)
open CoC (Cls cl ncons ncons_zero ncons_succ bindC appCls lamCls piCls ctxCl)

/-! ### Renaming and substitution of `SkP` skeletons -/

namespace SkPL

mutual
theorem rename_comp : ∀ (t : SkP) (r s : ℕ → ℕ),
    (t.rename s).rename r = t.rename (fun i => r (s i))
  | .base _, _, _ => rfl
  | .arr a b, r, s => by simp only [SkP.rename, rename_comp a, rename_comp b]
  | .all κ b, r, s => by
      simp only [SkP.rename, krename_comp κ, rename_comp b, Sk2.upR_comp]

theorem krename_comp : ∀ (κ : KSkP) (r s : ℕ → ℕ),
    (κ.rename s).rename r = κ.rename (fun i => r (s i))
  | .star, _, _ => rfl
  | .pi a κ, r, s => by simp only [KSkP.rename, rename_comp a, krename_comp κ]
end

theorem upSP_rename (σ : ℕ → SkP) (r : ℕ → ℕ) :
    (fun i => (upSP σ i).rename (upR r)) = upSP (fun i => (σ i).rename r) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp only [upSP, rename_comp]; rfl

mutual
theorem rename_subst : ∀ (t : SkP) (σ : ℕ → SkP) (r : ℕ → ℕ),
    (t.subst σ).rename r = t.subst (fun i => (σ i).rename r)
  | .base _, _, _ => rfl
  | .arr a b, σ, r => by simp only [SkP.subst, SkP.rename, rename_subst a, rename_subst b]
  | .all κ b, σ, r => by
      simp only [SkP.subst, SkP.rename, krename_subst κ, rename_subst b, upSP_rename]

theorem krename_subst : ∀ (κ : KSkP) (σ : ℕ → SkP) (r : ℕ → ℕ),
    (κ.subst σ).rename r = κ.subst (fun i => (σ i).rename r)
  | .star, _, _ => rfl
  | .pi a κ, σ, r => by simp only [KSkP.subst, KSkP.rename, rename_subst a, krename_subst κ]
end

theorem upSP_comp_upR (σ : ℕ → SkP) (r : ℕ → ℕ) :
    (fun i => upSP σ (upR r i)) = upSP (fun i => σ (r i)) := by
  funext i; cases i <;> rfl

mutual
theorem subst_rename : ∀ (t : SkP) (σ : ℕ → SkP) (r : ℕ → ℕ),
    (t.rename r).subst σ = t.subst (fun i => σ (r i))
  | .base _, _, _ => rfl
  | .arr a b, σ, r => by simp only [SkP.subst, SkP.rename, subst_rename a, subst_rename b]
  | .all κ b, σ, r => by
      simp only [SkP.subst, SkP.rename, ksubst_rename κ, subst_rename b, upSP_comp_upR]

theorem ksubst_rename : ∀ (κ : KSkP) (σ : ℕ → SkP) (r : ℕ → ℕ),
    (κ.rename r).subst σ = κ.subst (fun i => σ (r i))
  | .star, _, _ => rfl
  | .pi a κ, σ, r => by simp only [KSkP.subst, KSkP.rename, subst_rename a, ksubst_rename κ]
end

theorem upSP_subst (σ τ : ℕ → SkP) :
    (fun i => (upSP σ i).subst (upSP τ)) = upSP (fun i => (σ i).subst τ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      simp only [upSP, subst_rename, rename_subst]

theorem upSP_base : upSP SkP.base = SkP.base := by
  funext j; cases j <;> rfl

mutual
theorem subst_base : ∀ t : SkP, t.subst SkP.base = t
  | .base _ => rfl
  | .arr a b => by simp only [SkP.subst, subst_base a, subst_base b]
  | .all κ b => by simp only [SkP.subst, upSP_base, ksubst_base κ, subst_base b]

theorem ksubst_base : ∀ κ : KSkP, κ.subst SkP.base = κ
  | .star => rfl
  | .pi a κ => by simp only [KSkP.subst, subst_base a, ksubst_base κ]
end

end SkPL

/-! ### The erasure -/

/-- The closed junk skeleton `∀X:∗. X`, the erasure of objects and kinds. -/
def junkP : SkP := .all .star (.base 0)

@[simp] theorem junkP_rename (r : ℕ → ℕ) : junkP.rename r = junkP := rfl
@[simp] theorem junkP_subst (σ : ℕ → SkP) : junkP.subst σ = junkP := rfl

mutual
/-- **The erasure of λP2 constructors into `SkP`.**  As `er`, except that a quantifier
`Π α:K. B` over a kind records the kind skeleton `erK K` of the bound variable. -/
def erP : (ℕ → Cls) → (ℕ → SkP) → Expr Srt → SkP
  | Δ, ρ, .var n => if IsC (Δ n) then ρ n else junkP
  | _, _, .sort _ => junkP
  | Δ, ρ, .app F _ => if IsC (appCls (cl Δ F)) then erP Δ ρ F else junkP
  | Δ, ρ, .lam A b =>
      if IsC (lamCls (cl Δ A) (cl (ncons (bindC (cl Δ A)) Δ) b)) then
        erP (ncons (bindC (cl Δ A)) Δ) (ncons junkP ρ) b
      else junkP
  | Δ, ρ, .pi A B =>
      if IsC (piCls (cl Δ A) (cl (ncons (bindC (cl Δ A)) Δ) B)) then
        match cl Δ A with
        | .kind _ => .all (erK Δ ρ A) (erP (ncons (bindC (cl Δ A)) Δ) (upSP ρ) B)
        | _ => .arr (erP Δ ρ A) (erP (ncons (bindC (cl Δ A)) Δ) (ncons junkP ρ) B)
      else junkP

/-- **The erasure of λP2 kinds into kind skeletons**: `erK (Π x:A. K') = .pi (erP A) (erK K')`
and `erK ∗ = .star` (everything else, which is never a typed kind, also goes to `.star`). -/
def erK : (ℕ → Cls) → (ℕ → SkP) → Expr Srt → KSkP
  | Δ, ρ, .pi A K => .pi (erP Δ ρ A) (erK (ncons (bindC (cl Δ A)) Δ) (ncons junkP ρ) K)
  | _, _, .var _ => .star
  | _, _, .sort _ => .star
  | _, _, .app _ _ => .star
  | _, _, .lam _ _ => .star
end

/-- Anything not classified as a constructor erases to `junkP`. -/
theorem erP_junk {Δ : ℕ → Cls} (ρ : ℕ → SkP) {M : Expr Srt} (h : ¬ IsC (cl Δ M)) :
    erP Δ ρ M = junkP := by
  cases M with
  | var n => simp only [erP, cl] at h ⊢; simp [h]
  | sort s => simp only [erP]
  | app F a => simp only [erP, cl] at h ⊢; simp [h]
  | lam A b => simp only [erP, cl] at h ⊢; simp [h]
  | pi A B => simp only [erP, cl] at h ⊢; simp [h]

theorem upSP_comp_liftRen (ρ : ℕ → SkP) (r : ℕ → ℕ) :
    (fun i => upSP ρ (Expr.liftRen r i)) = upSP (fun i => ρ (r i)) := by
  funext i; cases i <;> rfl

/-- **Erasure commutes with renaming.** -/
theorem erPK_rename (M : Expr Srt) : ∀ (Δ : ℕ → Cls) (ρ : ℕ → SkP) (r : ℕ → ℕ),
    erP Δ ρ (M.rename r) = erP (fun i => Δ (r i)) (fun i => ρ (r i)) M ∧
    erK Δ ρ (M.rename r) = erK (fun i => Δ (r i)) (fun i => ρ (r i)) M := by
  induction M with
  | var n => intro Δ ρ r; exact ⟨rfl, rfl⟩
  | sort s => intro Δ ρ r; exact ⟨rfl, rfl⟩
  | app F a ihF _ =>
      intro Δ ρ r
      refine ⟨?_, rfl⟩
      simp only [Expr.rename, erP, CoC.cl_rename, (ihF _ _ _).1]; rfl
  | lam A b _ ihb =>
      intro Δ ρ r
      refine ⟨?_, rfl⟩
      have e : (Δ ∘ r) = fun i => Δ (r i) := rfl
      simp only [Expr.rename, erP, CoC.cl_rename, CoC.ncons_comp_liftRen, (ihb _ _ _).1,
        ncons_comp_liftRen', e]
  | pi A B ihA ihB =>
      intro Δ ρ r
      have e : (Δ ∘ r) = fun i => Δ (r i) := rfl
      constructor
      · simp only [Expr.rename, erP, CoC.cl_rename, CoC.ncons_comp_liftRen, (ihA _ _ _).1,
          (ihA _ _ _).2, (ihB _ _ _).1, ncons_comp_liftRen', upSP_comp_liftRen, e]
      · simp only [Expr.rename, erK, CoC.cl_rename, (ihA _ _ _).1,
          (ihB _ _ _).2, ncons_comp_liftRen', e]

theorem erP_rename (M : Expr Srt) (Δ : ℕ → Cls) (ρ : ℕ → SkP) (r : ℕ → ℕ) :
    erP Δ ρ (M.rename r) = erP (fun i => Δ (r i)) (fun i => ρ (r i)) M :=
  (erPK_rename M Δ ρ r).1

theorem erK_rename (M : Expr Srt) (Δ : ℕ → Cls) (ρ : ℕ → SkP) (r : ℕ → ℕ) :
    erK Δ ρ (M.rename r) = erK (fun i => Δ (r i)) (fun i => ρ (r i)) M :=
  (erPK_rename M Δ ρ r).2

theorem ncons_junkP_rename (ρ : ℕ → SkP) (r : ℕ → ℕ) :
    (fun i => (ncons junkP ρ i).rename r) = ncons junkP (fun i => (ρ i).rename r) := by
  funext i; cases i <;> rfl

theorem ncons_junkP_subst (ρ : ℕ → SkP) (τ : ℕ → SkP) :
    (fun i => (ncons junkP ρ i).subst τ) = ncons junkP (fun i => (ρ i).subst τ) := by
  funext i; cases i <;> rfl

/-- **Erasure commutes with renaming of skeleton variables.** -/
theorem erPK_skRename (M : Expr Srt) : ∀ (Δ : ℕ → Cls) (ρ : ℕ → SkP) (r : ℕ → ℕ),
    (erP Δ ρ M).rename r = erP Δ (fun i => (ρ i).rename r) M ∧
    (erK Δ ρ M).rename r = erK Δ (fun i => (ρ i).rename r) M := by
  induction M with
  | var n => intro Δ ρ r; refine ⟨?_, rfl⟩; simp only [erP]; split <;> rfl
  | sort s => intro Δ ρ r; exact ⟨rfl, rfl⟩
  | app F a ihF _ =>
      intro Δ ρ r; refine ⟨?_, rfl⟩; simp only [erP]; split <;> simp [(ihF _ _ _).1]
  | lam A b _ ihb =>
      intro Δ ρ r
      refine ⟨?_, rfl⟩
      simp only [erP]
      split
      · rw [(ihb _ _ _).1, ncons_junkP_rename]
      · rfl
  | pi A B ihA ihB =>
      intro Δ ρ r
      constructor
      · simp only [erP]
        split
        · split
          · simp only [SkP.rename, (ihA _ _ _).2, (ihB _ _ _).1, SkPL.upSP_rename]
          · simp only [SkP.rename, (ihA _ _ _).1, (ihB _ _ _).1, ncons_junkP_rename]
        · rfl
      · simp only [erK, KSkP.rename, (ihA _ _ _).1, (ihB _ _ _).2, ncons_junkP_rename]

/-- **Erasure commutes with substitution of skeleton variables.** -/
theorem erPK_skSubst (M : Expr Srt) : ∀ (Δ : ℕ → Cls) (ρ : ℕ → SkP) (τ : ℕ → SkP),
    (erP Δ ρ M).subst τ = erP Δ (fun i => (ρ i).subst τ) M ∧
    (erK Δ ρ M).subst τ = erK Δ (fun i => (ρ i).subst τ) M := by
  induction M with
  | var n => intro Δ ρ τ; refine ⟨?_, rfl⟩; simp only [erP]; split <;> rfl
  | sort s => intro Δ ρ τ; exact ⟨rfl, rfl⟩
  | app F a ihF _ =>
      intro Δ ρ τ; refine ⟨?_, rfl⟩; simp only [erP]; split <;> simp [(ihF _ _ _).1]
  | lam A b _ ihb =>
      intro Δ ρ τ
      refine ⟨?_, rfl⟩
      simp only [erP]
      split
      · rw [(ihb _ _ _).1, ncons_junkP_subst]
      · rfl
  | pi A B ihA ihB =>
      intro Δ ρ τ
      constructor
      · simp only [erP]
        split
        · split
          · simp only [SkP.subst, (ihA _ _ _).2, (ihB _ _ _).1, SkPL.upSP_subst]
          · simp only [SkP.subst, (ihA _ _ _).1, (ihB _ _ _).1, ncons_junkP_subst]
        · rfl
      · simp only [erK, KSkP.subst, (ihA _ _ _).1, (ihB _ _ _).2, ncons_junkP_subst]

theorem erP_skSubst (M : Expr Srt) (Δ : ℕ → Cls) (ρ τ : ℕ → SkP) :
    (erP Δ ρ M).subst τ = erP Δ (fun i => (ρ i).subst τ) M := (erPK_skSubst M Δ ρ τ).1

theorem erK_skSubst (M : Expr Srt) (Δ : ℕ → Cls) (ρ τ : ℕ → SkP) :
    (erK Δ ρ M).subst τ = erK Δ (fun i => (ρ i).subst τ) M := (erPK_skSubst M Δ ρ τ).2

/-! ### Erasure and substitution -/

theorem liftP_hyp_ncons {Δ Δ' : ℕ → Cls} {ρ ρ' : ℕ → SkP} {σ : ℕ → Expr Srt}
    (hρ : ∀ n, IsC (Δ' n) → erP Δ ρ (σ n) = ρ' n) (c : Cls) :
    ∀ n, IsC (ncons c Δ' n) → erP (ncons c Δ) (ncons junkP ρ) (Expr.liftSub σ n) =
      ncons junkP ρ' n
  | 0, _ => by
      show erP (ncons c Δ) (ncons junkP ρ) (.var 0) = junkP
      unfold erP; split <;> rfl
  | n + 1, h => by
      simp only [Expr.liftSub_succ, erP_rename, ncons_succ]
      exact hρ n h

theorem liftP_hyp_upSP {Δ Δ' : ℕ → Cls} {ρ ρ' : ℕ → SkP} {σ : ℕ → Expr Srt}
    (hρ : ∀ n, IsC (Δ' n) → erP Δ ρ (σ n) = ρ' n) (c : Cls) (hc : IsC c) :
    ∀ n, IsC (ncons c Δ' n) → erP (ncons c Δ) (upSP ρ) (Expr.liftSub σ n) = upSP ρ' n
  | 0, _ => by
      show erP (ncons c Δ) (upSP ρ) (.var 0) = .base 0
      exact ite_eq_left hc
  | n + 1, h => by
      simp only [Expr.liftSub_succ, erP_rename, ncons_succ]
      show erP Δ (fun i => (ρ i).rename Nat.succ) (σ n) = (ρ' n).rename Nat.succ
      rw [← (erPK_skRename _ _ _ _).1, hρ n h]

theorem piCls_kind {cA c : Cls} {a : CoC.Sk} (h : piCls cA c = .kind a) : ∃ k, c = .kind k := by
  cases c with
  | kind k => exact ⟨k, rfl⟩
  | constr => simp [piCls] at h
  | obj => simp [piCls] at h

theorem ncons_bindC_ne_kind {Δ : ℕ → Cls} (hΔ : ∀ n a, Δ n ≠ .kind a) (c : Cls) :
    ∀ n a, ncons (bindC c) Δ n ≠ .kind a
  | 0, a => CoC.bindC_ne_kind c a
  | n + 1, a => hΔ n a

/-- **Erasure commutes with substitution** (types and kinds), for substitutions respecting the
classification whose substituted constructors erase to the new skeleton environment.  For kinds
the source classification must have no kind-classified variable (true of `ctxCl`). -/
theorem erPK_subst (M : Expr Srt) : ∀ {Δ Δ' : ℕ → Cls} {ρ ρ' : ℕ → SkP} {σ : ℕ → Expr Srt},
    (∀ n, cl Δ (σ n) = Δ' n) → (∀ n, IsC (Δ' n) → erP Δ ρ (σ n) = ρ' n) →
    (∀ n a, Δ' n ≠ .kind a) →
    erP Δ ρ (M.subst σ) = erP Δ' ρ' M ∧
      (∀ a, cl Δ' M = .kind a → erK Δ ρ (M.subst σ) = erK Δ' ρ' M) := by
  induction M with
  | var n =>
      intro Δ Δ' ρ ρ' σ hσ hρ hΔ'
      refine ⟨?_, fun a ha => absurd ha (hΔ' n a)⟩
      simp only [Expr.subst, erP]
      split
      · exact hρ n ‹_›
      · exact erP_junk ρ (by rw [hσ n]; assumption)
  | sort s => intro Δ Δ' ρ ρ' σ hσ hρ hΔ'; exact ⟨rfl, fun _ _ => rfl⟩
  | app F a ihF _ =>
      intro Δ Δ' ρ ρ' σ hσ hρ hΔ'
      refine ⟨by simp only [Expr.subst, erP, CoC.cl_subst F hσ, (ihF hσ hρ hΔ').1],
        fun k hk => absurd hk (CoC.appCls_ne_kind _ k)⟩
  | lam A b _ ihb =>
      intro Δ Δ' ρ ρ' σ hσ hρ hΔ'
      refine ⟨?_, fun k hk => absurd hk (CoC.lamCls_ne_kind _ _ k)⟩
      simp only [Expr.subst, erP, CoC.cl_subst A hσ]
      rw [CoC.cl_subst b (CoC.cl_liftSub hσ _),
        (ihb (CoC.cl_liftSub hσ _) (liftP_hyp_ncons hρ _) (ncons_bindC_ne_kind hΔ' _)).1]
  | pi A B ihA ihB =>
      intro Δ Δ' ρ ρ' σ hσ hρ hΔ'
      constructor
      · simp only [Expr.subst, erP, CoC.cl_subst A hσ]
        rw [CoC.cl_subst B (CoC.cl_liftSub hσ _)]
        split
        · split
          · rename_i a heq
            rw [(ihA hσ hρ hΔ').2 a heq,
              (ihB (CoC.cl_liftSub hσ _) (liftP_hyp_upSP hρ _ (by rw [heq]; trivial))
                (ncons_bindC_ne_kind hΔ' _)).1]
          · rw [(ihA hσ hρ hΔ').1, (ihB (CoC.cl_liftSub hσ _) (liftP_hyp_ncons hρ _)
              (ncons_bindC_ne_kind hΔ' _)).1]
        · rfl
      · intro k hk
        simp only [cl] at hk
        obtain ⟨k', hk'⟩ := piCls_kind hk
        simp only [Expr.subst, erK, CoC.cl_subst A hσ, (ihA hσ hρ hΔ').1,
          (ihB (CoC.cl_liftSub hσ _) (liftP_hyp_ncons hρ _) (ncons_bindC_ne_kind hΔ' _)).2 k' hk']

theorem erP_subst (M : Expr Srt) {Δ Δ' : ℕ → Cls} {ρ ρ' : ℕ → SkP} {σ : ℕ → Expr Srt}
    (hσ : ∀ n, cl Δ (σ n) = Δ' n) (hρ : ∀ n, IsC (Δ' n) → erP Δ ρ (σ n) = ρ' n)
    (hΔ' : ∀ n a, Δ' n ≠ .kind a) : erP Δ ρ (M.subst σ) = erP Δ' ρ' M :=
  (erPK_subst M hσ hρ hΔ').1

theorem erK_subst (M : Expr Srt) {Δ Δ' : ℕ → Cls} {ρ ρ' : ℕ → SkP} {σ : ℕ → Expr Srt}
    (hσ : ∀ n, cl Δ (σ n) = Δ' n) (hρ : ∀ n, IsC (Δ' n) → erP Δ ρ (σ n) = ρ' n)
    (hΔ' : ∀ n a, Δ' n ≠ .kind a) {a : CoC.Sk} (hM : cl Δ' M = .kind a) :
    erK Δ ρ (M.subst σ) = erK Δ' ρ' M :=
  (erPK_subst M hσ hρ hΔ').2 a hM

theorem ncons_ne_kind {Δ : ℕ → Cls} (hΔ : ∀ n a, Δ n ≠ .kind a) {c : Cls}
    (hc : ∀ a, c ≠ .kind a) : ∀ n a, ncons c Δ n ≠ .kind a
  | 0, a => hc a
  | n + 1, a => hΔ n a

theorem erP_single_hyp (U : Expr Srt) (Δ : ℕ → Cls) (ρ : ℕ → SkP) :
    ∀ n, IsC (ncons (cl Δ U) Δ n) → erP Δ ρ (Expr.single U n) = ncons (erP Δ ρ U) ρ n
  | 0, _ => rfl
  | n + 1, hn => by simp only [Expr.single, erP, ncons_succ] at hn ⊢; rw [ite_eq_left hn]

/-- Erasure of an instance, for an argument of any non-kind class. -/
theorem erPK_instantiate_ncons (B U : Expr Srt) (Δ : ℕ → Cls) (ρ : ℕ → SkP)
    (hΔ : ∀ n a, Δ n ≠ .kind a) (hU : ∀ a, cl Δ U ≠ .kind a) :
    erP Δ ρ (B.instantiate U) = erP (ncons (cl Δ U) Δ) (ncons (erP Δ ρ U) ρ) B ∧
      (∀ a, cl (ncons (cl Δ U) Δ) B = .kind a →
        erK Δ ρ (B.instantiate U) = erK (ncons (cl Δ U) Δ) (ncons (erP Δ ρ U) ρ) B) :=
  erPK_subst B (cl_single' U) (erP_single_hyp U Δ ρ) (ncons_ne_kind hΔ hU)

theorem erP_single_obj_hyp (N : Expr Srt) (Δ : ℕ → Cls) (ρ : ℕ → SkP) (t : SkP)
    (hN : ¬ IsC (cl Δ N)) :
    ∀ n, IsC (ncons (cl Δ N) Δ n) → erP Δ ρ (Expr.single N n) = ncons t ρ n
  | 0, h => absurd h hN
  | n + 1, hn => by simp only [Expr.single, erP, ncons_succ] at hn ⊢; rw [ite_eq_left hn]

/-- **Erasure is invariant under object substitution** (types). -/
theorem erP_instantiate_obj (B N : Expr Srt) (Δ : ℕ → Cls) (ρ : ℕ → SkP) (t : SkP)
    (hΔ : ∀ n a, Δ n ≠ .kind a) (hN : ¬ IsC (cl Δ N)) (hNk : ∀ a, cl Δ N ≠ .kind a) :
    erP Δ ρ (B.instantiate N) = erP (ncons (cl Δ N) Δ) (ncons t ρ) B :=
  erP_subst B (cl_single' N) (erP_single_obj_hyp N Δ ρ t hN) (ncons_ne_kind hΔ hNk)

/-- **Erasure is invariant under object substitution** (kinds). -/
theorem erK_instantiate_obj (B N : Expr Srt) (Δ : ℕ → Cls) (ρ : ℕ → SkP) (t : SkP)
    (hΔ : ∀ n a, Δ n ≠ .kind a) (hN : ¬ IsC (cl Δ N)) (hNk : ∀ a, cl Δ N ≠ .kind a)
    {a : CoC.Sk} (hB : cl (ncons (cl Δ N) Δ) B = .kind a) :
    erK Δ ρ (B.instantiate N) = erK (ncons (cl Δ N) Δ) (ncons t ρ) B :=
  erK_subst B (cl_single' N) (erP_single_obj_hyp N Δ ρ t hN) (ncons_ne_kind hΔ hNk) hB

theorem upSP_single (ρ : ℕ → SkP) (t : SkP) :
    (fun i => (upSP ρ i).subst (singleP t)) = ncons t ρ := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      simp only [upSP, SkPL.subst_rename, ncons_succ]
      have : (fun j => singleP t (Nat.succ j)) = SkP.base := rfl
      rw [this, SkPL.subst_base]

/-- **Erasure commutes with constructor substitution** (types):
`erP (B[U/α]) = (erP B)[erP U / α]`. -/
theorem erP_instantiate (B U : Expr Srt) (Δ : ℕ → Cls) (ρ : ℕ → SkP)
    (hΔ : ∀ n a, Δ n ≠ .kind a) (hU : ∀ a, cl Δ U ≠ .kind a) :
    erP Δ ρ (B.instantiate U) =
      (erP (ncons (cl Δ U) Δ) (upSP ρ) B).subst (singleP (erP Δ ρ U)) := by
  rw [erP_skSubst, upSP_single, (erPK_instantiate_ncons B U Δ ρ hΔ hU).1]

/-- **Erasure commutes with constructor substitution** (kinds), with `KSkP.subst`. -/
theorem erK_instantiate (B U : Expr Srt) (Δ : ℕ → Cls) (ρ : ℕ → SkP)
    (hΔ : ∀ n a, Δ n ≠ .kind a) (hU : ∀ a, cl Δ U ≠ .kind a)
    {a : CoC.Sk} (hB : cl (ncons (cl Δ U) Δ) B = .kind a) :
    erK Δ ρ (B.instantiate U) =
      (erK (ncons (cl Δ U) Δ) (upSP ρ) B).subst (singleP (erP Δ ρ U)) := by
  rw [erK_skSubst, upSP_single, (erPK_instantiate_ncons B U Δ ρ hΔ hU).2 a hB]

/-! ### Invariance under β-reduction of well-typed λP2 terms -/

theorem erP_app_isC {Δ : ℕ → Cls} {ρ : ℕ → SkP} {F a : Expr Srt} (h : IsC (cl Δ (.app F a))) :
    erP Δ ρ (.app F a) = erP Δ ρ F := ite_eq_left h

theorem erP_lam_isC {Δ : ℕ → Cls} {ρ : ℕ → SkP} {A b : Expr Srt} (h : IsC (cl Δ (.lam A b))) :
    erP Δ ρ (.lam A b) = erP (ncons (bindC (cl Δ A)) Δ) (ncons junkP ρ) b := ite_eq_left h

open CoC in
/-- **Erasure is invariant under β-reduction of well-typed λP2 terms**, for types (`erP`) and,
when the term is a kind, for kinds (`erK`). -/
theorem erPK_beta {Γ : List (Expr Srt)} {M M' X : Expr Srt}
    (h : HasType (cubeSpec lambdaP2) Γ M X) (hr : Beta M M') (ρ : ℕ → SkP) :
    erP (ctxCl Γ) ρ M = erP (ctxCl Γ) ρ M' ∧
      (X = .sort .box → erK (ctxCl Γ) ρ M = erK (ctxCl Γ) ρ M') := by
  induction hr generalizing Γ X ρ with
  | head A b a =>
      refine ⟨?_, fun hX => ?_⟩
      · by_cases hC : IsC (cl (ctxCl Γ) (.app (.lam A b) a))
        · obtain ⟨D, E, hF, ha, -⟩ := h.generation_app
          have hlC : IsC (cl (ctxCl Γ) (.lam A b)) := by
            simp only [cl] at hC ⊢
            revert hC
            cases lamCls (cl (ctxCl Γ) A) (cl (ncons (bindC (cl (ctxCl Γ) A)) (ctxCl Γ)) b) with
            | kind => simp [appCls, IsC]
            | constr k => simp [IsC]
            | obj => simp [appCls, IsC]
          have hnk := lam_dom_not_kind hF (by
            simp only [cl] at hlC ⊢
            revert hlC
            cases lamCls (cl (ctxCl Γ) A) (cl (ncons (bindC (cl (ctxCl Γ) A)) (ctxCl Γ)) b) <;>
              simp [IsC])
          obtain ⟨s, hPi⟩ := hF.product_type_sorted
          obtain ⟨s₁, s₂, s₃, hD, -, -, -⟩ := hPi.generation_pi
          obtain ⟨B₁, s', hb, hPi', hc'⟩ := hF.generation_lam
          have hca : cl (ctxCl Γ) a = .obj := by
            rw [classify ha (ne_box_of_hasType hD)]
            obtain ⟨t₁, t₂, t₃, hA, -, -, -⟩ := hPi'.generation_pi
            have hcAD : Converts A D :=
              Relation.EqvGen.symm _ _ (Converts.product_compatibility hc').1
            cases s₁ with
            | box =>
                exfalso
                cases t₁ with
                | star =>
                    have := sort_unique_conv hA hD hcAD
                    cases this
                | box =>
                    obtain ⟨k, hk⟩ := kind_cl hA
                    exact hnk k hk
            | star =>
                exact bindC_of_not_kind (not_kind hD (cube_star_box _ hD.valid))
          rw [erP_app_isC hC, erP_lam_isC hlC]
          rw [erP_instantiate_obj b a (ctxCl Γ) ρ junkP (ctxCl_ne_kind Γ)
            (by rw [hca]; simp [IsC]) (by rw [hca]; simp), hca, bindC_of_not_kind hnk]
        · rw [erP_junk ρ hC, erP_junk ρ (by rwa [← cl_beta h (.head A b a)])]
      · subst hX
        obtain ⟨s, hs⟩ := h.application_type_sorted
        exact (not_hasType_box lambdaP2 hs).elim
  | @app_left F F' U hr ih =>
      refine ⟨?_, fun hX => ?_⟩
      · obtain ⟨A, B, hF, hU, -⟩ := h.generation_app
        simp only [erP, ← cl_beta hF hr, (ih hF ρ).1]
      · subst hX
        obtain ⟨s, hs⟩ := h.application_type_sorted
        exact (not_hasType_box lambdaP2 hs).elim
  | @app_right F U U' hr ih =>
      refine ⟨rfl, fun hX => ?_⟩
      subst hX
      obtain ⟨s, hs⟩ := h.application_type_sorted
      exact (not_hasType_box lambdaP2 hs).elim
  | @lam_domain A A' b hr ih =>
      refine ⟨?_, fun hX => ?_⟩
      · obtain ⟨B, s, hb, hPi, -⟩ := h.generation_lam
        obtain ⟨s₁, hA⟩ := hPi.product_domain A B rfl
        simp only [erP, ← cl_beta hA hr]
      · subst hX
        obtain ⟨s, hs⟩ := h.abstraction_type_sorted
        exact (not_hasType_box lambdaP2 hs).elim
  | @lam_body A b b' hr ih =>
      refine ⟨?_, fun hX => ?_⟩
      · obtain ⟨B, s, hb, hPi, -⟩ := h.generation_lam
        have hcl := cl_beta hb hr
        have hih := (ih hb (ncons junkP ρ)).1
        simp only [ctxCl] at hcl hih
        simp only [erP, hcl, hih]
      · subst hX
        obtain ⟨s, hs⟩ := h.abstraction_type_sorted
        exact (not_hasType_box lambdaP2 hs).elim
  | @pi_domain A A' B hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, -, -⟩ := h.generation_pi
      refine ⟨?_, fun _ => ?_⟩
      · simp only [erP, ← cl_beta hA hr]
        split
        · split
          · rename_i a heq
            have hs₁ : s₁ = .box := by
              cases s₁ with
              | box => rfl
              | star => exact absurd heq (not_kind hA (cube_star_box _ hA.valid) a)
            subst hs₁
            rw [(ih hA ρ).2 rfl]
          · rw [(ih hA ρ).1]
        · rfl
      · simp only [erK, ← cl_beta hA hr, (ih hA ρ).1]
  | @pi_body A B B' hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrl, hc⟩ := h.generation_pi
      have hcl := cl_beta hB hr
      simp only [ctxCl] at hcl
      refine ⟨?_, fun hX => ?_⟩
      · simp only [erP, hcl]
        split
        · split
          · have hih := (ih hB (upSP ρ)).1
            simp only [ctxCl] at hih
            rw [hih]
          · have hih := (ih hB (ncons junkP ρ)).1
            simp only [ctxCl] at hih
            rw [hih]
        · rfl
      · subst hX
        have h₃ : s₃ = .box := (Converts.sort_inj hc).symm
        rw [hrl.1] at h₃
        subst h₃
        have hih := (ih hB (ncons junkP ρ)).2 rfl
        simp only [ctxCl] at hih
        simp only [erK, hih]

theorem erP_beta {Γ : List (Expr Srt)} {M M' X : Expr Srt}
    (h : HasType (cubeSpec lambdaP2) Γ M X) (hr : Beta M M') (ρ : ℕ → SkP) :
    erP (ctxCl Γ) ρ M = erP (ctxCl Γ) ρ M' := (erPK_beta h hr ρ).1

theorem erK_beta {Γ : List (Expr Srt)} {K K' : Expr Srt}
    (h : HasType (cubeSpec lambdaP2) Γ K (.sort .box)) (hr : Beta K K') (ρ : ℕ → SkP) :
    erK (ctxCl Γ) ρ K = erK (ctxCl Γ) ρ K' := (erPK_beta h hr ρ).2 rfl

theorem erP_reduces {Γ : List (Expr Srt)} {M M' X : Expr Srt}
    (h : HasType (cubeSpec lambdaP2) Γ M X) (hr : Reduces M M') (ρ : ℕ → SkP) :
    erP (ctxCl Γ) ρ M = erP (ctxCl Γ) ρ M' := by
  induction hr with
  | refl => rfl
  | tail hr₁ hr₂ ih => exact ih.trans (erP_beta (h.subject_reduces hr₁) hr₂ ρ)

theorem erK_reduces {Γ : List (Expr Srt)} {K K' : Expr Srt}
    (h : HasType (cubeSpec lambdaP2) Γ K (.sort .box)) (hr : Reduces K K') (ρ : ℕ → SkP) :
    erK (ctxCl Γ) ρ K = erK (ctxCl Γ) ρ K' := by
  induction hr with
  | refl => rfl
  | tail hr₁ hr₂ ih => exact ih.trans (erK_beta (h.subject_reduces hr₁) hr₂ ρ)

/-- **Erasure of types is invariant under β-conversion of well-typed λP2 terms.** -/
theorem erP_conv {Γ : List (Expr Srt)} {M M' X X' : Expr Srt}
    (h : HasType (cubeSpec lambdaP2) Γ M X) (h' : HasType (cubeSpec lambdaP2) Γ M' X')
    (hc : Converts M M') (ρ : ℕ → SkP) :
    erP (ctxCl Γ) ρ M = erP (ctxCl Γ) ρ M' := by
  obtain ⟨C, hMC, hM'C⟩ := hc.join
  exact (erP_reduces h hMC ρ).trans (erP_reduces h' hM'C ρ).symm

/-- **Erasure of kinds is invariant under β-conversion of well-typed λP2 kinds.** -/
theorem erK_conv {Γ : List (Expr Srt)} {K K' : Expr Srt}
    (h : HasType (cubeSpec lambdaP2) Γ K (.sort .box))
    (h' : HasType (cubeSpec lambdaP2) Γ K' (.sort .box))
    (hc : Converts K K') (ρ : ℕ → SkP) :
    erK (ctxCl Γ) ρ K = erK (ctxCl Γ) ρ K' := by
  obtain ⟨C, hKC, hK'C⟩ := hc.join
  exact (erK_reduces h hKC ρ).trans (erK_reduces h' hK'C ρ).symm

end ErasureP2

end PureTypeSystem
