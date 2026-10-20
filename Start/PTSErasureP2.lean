import Start.PTSExpansionRouteII
import Start.CoCSN

/-!
# Erasure of λP2 constructors to λ2 skeletons

Task `M29-EP-IMPREDICATIVE`, round 8, part A1.  The classical map from λP2 to λ2 that forgets
the dependency of types on objects (the map used in the strong normalization proofs of the cube):

* kinds are erased to their kind skeletons — this is `CoC.cl`'s `.kind k` component, with
  `CoC.kind_beta` / `CoC.kind_conv` (round 6);
* constructors are erased to λ2 type skeletons `RouteII.Sk` by `ErasureP2.er Δ ρ M`, where `Δ`
  classifies the free variables (as in `CoC.cl`) and `ρ` gives the skeleton of every free
  constructor variable.  Objects (and kinds) erase to the closed junk skeleton `junk = ∀X. X`;
  an object binder `Π x:A. B` erases to an arrow, a kind binder `Π α:K. B` (the rule `(□,∗)`) to a
  quantifier; object abstraction and object application are forgotten.

Results, all purely syntactic except the last:

* `ErasureP2.er_junk` — anything not classified as a constructor erases to `junk`;
* `ErasureP2.er_rename`, `ErasureP2.er_skRename`, `ErasureP2.er_skSubst` — erasure commutes
  with renaming of expressions and with renaming/substitution of skeletons;
* `ErasureP2.er_subst` — **erasure commutes with substitution**, for every class of substituted
  variable;
* `ErasureP2.er_instantiate_obj` — **erasure is invariant under object substitution** (an object
  never occurs in a skeleton);
* `ErasureP2.er_instantiate` — **erasure commutes with constructor substitution**:
  `er (B[U/α]) = (er B)[er U / α]`;
* `ErasureP2.er_beta`, `ErasureP2.er_reduces`, `ErasureP2.er_conv` — **erasure is invariant under
  β-reduction and β-conversion of well-typed λP2 terms** (the only place where typing is used:
  λP2 has no rule `(□,□)`, so no constructor abstracts over a constructor);
* `ErasureP2.er_beta_fails_coc` — **the first failing step for the calculus of constructions**:
  the λ2 erasure is not β-invariant at the typed coc redex `(λβ:∗. β) α`; Fω skeletons (with
  type-level abstraction, modulo β) are needed there.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PureTypeSystem

namespace ErasureP2

open LambdaPi (Srt)

abbrev SkT := RouteII.Sk

open CoC (Cls cl ncons ncons_zero ncons_succ bindC appCls lamCls piCls ctxCl)

/-! ### Skeleton renaming and substitution lemmas -/

namespace Sk2

open RouteII

theorem upR_comp (r s : ℕ → ℕ) : upR (fun i => r (s i)) = fun i => upR r (upR s i) := by
  funext i; cases i <;> rfl

theorem rename_comp : ∀ (t : Sk) (r s : ℕ → ℕ), (t.rename s).rename r = t.rename (fun i => r (s i))
  | .base _, _, _ => rfl
  | .arr a b, r, s => by simp only [Sk.rename, rename_comp a, rename_comp b]
  | .all b, r, s => by simp only [Sk.rename, rename_comp b, upR_comp]

theorem upS_rename (σ : ℕ → Sk) (r : ℕ → ℕ) :
    (fun i => (upS σ i).rename (upR r)) = upS (fun i => (σ i).rename r) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp only [upS, rename_comp]; rfl

theorem rename_subst : ∀ (t : Sk) (σ : ℕ → Sk) (r : ℕ → ℕ),
    (t.subst σ).rename r = t.subst (fun i => (σ i).rename r)
  | .base _, _, _ => rfl
  | .arr a b, σ, r => by simp only [Sk.subst, Sk.rename, rename_subst a, rename_subst b]
  | .all b, σ, r => by simp only [Sk.subst, Sk.rename, rename_subst b, upS_rename]

theorem upS_comp_upR (σ : ℕ → Sk) (r : ℕ → ℕ) :
    (fun i => upS σ (upR r i)) = upS (fun i => σ (r i)) := by
  funext i; cases i <;> rfl

theorem subst_rename : ∀ (t : Sk) (σ : ℕ → Sk) (r : ℕ → ℕ),
    (t.rename r).subst σ = t.subst (fun i => σ (r i))
  | .base _, _, _ => rfl
  | .arr a b, σ, r => by simp only [Sk.subst, Sk.rename, subst_rename a, subst_rename b]
  | .all b, σ, r => by simp only [Sk.subst, Sk.rename, subst_rename b, upS_comp_upR]

theorem upS_subst (σ τ : ℕ → Sk) :
    (fun i => (upS σ i).subst (upS τ)) = upS (fun i => (σ i).subst τ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      simp only [upS, subst_rename, rename_subst]

theorem upS_base : upS Sk.base = Sk.base := by
  funext j; cases j <;> rfl

theorem subst_base : ∀ t : Sk, t.subst Sk.base = t
  | .base _ => rfl
  | .arr a b => by simp only [Sk.subst, subst_base a, subst_base b]
  | .all b => by simp only [Sk.subst, upS_base, subst_base b]

end Sk2

/-! ### The erasure -/

/-- The closed junk skeleton `∀X. X`, the erasure of objects and kinds. -/
def junk : SkT := .all (.base 0)

@[simp] theorem junk_rename (r : ℕ → ℕ) : junk.rename r = junk := rfl
@[simp] theorem junk_subst (σ : ℕ → SkT) : junk.subst σ = junk := rfl

/-- Whether a class is the class of constructors. -/
def IsC : Cls → Prop
  | .constr _ => True
  | _ => False

instance (c : Cls) : Decidable (IsC c) := by
  cases c <;> simp only [IsC] <;> infer_instance

/-- **The erasure of λP2 constructors to λ2 skeletons.**  `Δ` classifies the free variables and
`ρ` gives the skeleton of each free constructor variable. -/
def er : (ℕ → Cls) → (ℕ → SkT) → Expr Srt → SkT
  | Δ, ρ, .var n => if IsC (Δ n) then ρ n else junk
  | _, _, .sort _ => junk
  | Δ, ρ, .app F _ => if IsC (appCls (cl Δ F)) then er Δ ρ F else junk
  | Δ, ρ, .lam A b =>
      if IsC (lamCls (cl Δ A) (cl (ncons (bindC (cl Δ A)) Δ) b)) then
        er (ncons (bindC (cl Δ A)) Δ) (ncons junk ρ) b
      else junk
  | Δ, ρ, .pi A B =>
      if IsC (piCls (cl Δ A) (cl (ncons (bindC (cl Δ A)) Δ) B)) then
        match cl Δ A with
        | .kind _ => .all (er (ncons (bindC (cl Δ A)) Δ) (RouteII.upS ρ) B)
        | _ => .arr (er Δ ρ A) (er (ncons (bindC (cl Δ A)) Δ) (ncons junk ρ) B)
      else junk

/-- Anything not classified as a constructor erases to `junk`. -/
theorem er_junk {Δ : ℕ → Cls} (ρ : ℕ → SkT) {M : Expr Srt} (h : ¬ IsC (cl Δ M)) :
    er Δ ρ M = junk := by
  cases M with
  | var n => simp only [er, cl] at h ⊢; simp [h]
  | sort s => rfl
  | app F a => simp only [er, cl] at h ⊢; simp [h]
  | lam A b => simp only [er, cl] at h ⊢; simp [h]
  | pi A B => simp only [er, cl] at h ⊢; simp [h]

/-! ### Erasure and renaming -/

theorem ncons_comp_liftRen' {α : Sort _} (x : α) (f : ℕ → α) (r : ℕ → ℕ) :
    (fun i => ncons x f (Expr.liftRen r i)) = ncons x (fun i => f (r i)) := by
  funext i; cases i <;> rfl

theorem upS_comp_liftRen (ρ : ℕ → SkT) (r : ℕ → ℕ) :
    (fun i => RouteII.upS ρ (Expr.liftRen r i)) = RouteII.upS (fun i => ρ (r i)) := by
  funext i; cases i <;> rfl

theorem er_rename (M : Expr Srt) : ∀ (Δ : ℕ → Cls) (ρ : ℕ → SkT) (r : ℕ → ℕ),
    er Δ ρ (M.rename r) = er (fun i => Δ (r i)) (fun i => ρ (r i)) M := by
  induction M with
  | var n => intro Δ ρ r; rfl
  | sort s => intro Δ ρ r; rfl
  | app F a ihF _ =>
      intro Δ ρ r
      simp only [Expr.rename, er, CoC.cl_rename, ihF]; rfl
  | lam A b _ ihb =>
      intro Δ ρ r
      have e : (Δ ∘ r) = fun i => Δ (r i) := rfl
      simp only [Expr.rename, er, CoC.cl_rename, CoC.ncons_comp_liftRen, ihb,
        ncons_comp_liftRen', e]
  | pi A B ihA ihB =>
      intro Δ ρ r
      have e : (Δ ∘ r) = fun i => Δ (r i) := rfl
      simp only [Expr.rename, er, CoC.cl_rename, CoC.ncons_comp_liftRen, ihA, ihB,
        ncons_comp_liftRen', upS_comp_liftRen, e]

/-- Erasure commutes with renaming of skeleton variables. -/
theorem er_skRename (M : Expr Srt) : ∀ (Δ : ℕ → Cls) (ρ : ℕ → SkT) (r : ℕ → ℕ),
    (er Δ ρ M).rename r = er Δ (fun i => (ρ i).rename r) M := by
  induction M with
  | var n => intro Δ ρ r; simp only [er]; split <;> rfl
  | sort s => intro Δ ρ r; rfl
  | app F a ihF _ => intro Δ ρ r; simp only [er]; split <;> simp [ihF]
  | lam A b _ ihb =>
      intro Δ ρ r
      simp only [er]
      split
      · rw [ihb]; congr 1; funext i; cases i <;> rfl
      · rfl
  | pi A B ihA ihB =>
      intro Δ ρ r
      simp only [er]
      split
      · split
        · simp only [RouteII.Sk.rename, ihB, Sk2.upS_rename]
        · simp only [RouteII.Sk.rename, ihA, ihB]
          congr 2; funext i; cases i <;> rfl
      · rfl

/-- Erasure commutes with substitution of skeleton variables. -/
theorem er_skSubst (M : Expr Srt) : ∀ (Δ : ℕ → Cls) (ρ : ℕ → SkT) (τ : ℕ → SkT),
    (er Δ ρ M).subst τ = er Δ (fun i => (ρ i).subst τ) M := by
  induction M with
  | var n => intro Δ ρ τ; simp only [er]; split <;> rfl
  | sort s => intro Δ ρ τ; rfl
  | app F a ihF _ => intro Δ ρ τ; simp only [er]; split <;> simp [ihF]
  | lam A b _ ihb =>
      intro Δ ρ τ
      simp only [er]
      split
      · rw [ihb]; congr 1; funext i; cases i <;> rfl
      · rfl
  | pi A B ihA ihB =>
      intro Δ ρ τ
      simp only [er]
      split
      · split
        · simp only [RouteII.Sk.subst, ihB, Sk2.upS_subst]
        · simp only [RouteII.Sk.subst, ihA, ihB]
          congr 2; funext i; cases i <;> rfl
      · rfl

/-! ### Erasure and substitution -/

/-- Lifting the hypotheses of `er_subst` under an object (or any non-quantifier) binder. -/
theorem lift_hyp_ncons {Δ Δ' : ℕ → Cls} {ρ ρ' : ℕ → SkT} {σ : ℕ → Expr Srt}
    (hρ : ∀ n, IsC (Δ' n) → er Δ ρ (σ n) = ρ' n) (c : Cls) :
    ∀ n, IsC (ncons c Δ' n) → er (ncons c Δ) (ncons junk ρ) (Expr.liftSub σ n) =
      ncons junk ρ' n
  | 0, _ => by
      show er (ncons c Δ) (ncons junk ρ) (.var 0) = junk
      unfold er; split <;> rfl
  | n + 1, h => by
      simp only [Expr.liftSub_succ, er_rename, ncons_succ]
      exact hρ n h

/-- Lifting the hypotheses of `er_subst` under a quantifier binder. -/
theorem lift_hyp_upS {Δ Δ' : ℕ → Cls} {ρ ρ' : ℕ → SkT} {σ : ℕ → Expr Srt}
    (hρ : ∀ n, IsC (Δ' n) → er Δ ρ (σ n) = ρ' n) (c : Cls) (hc : IsC c) :
    ∀ n, IsC (ncons c Δ' n) → er (ncons c Δ) (RouteII.upS ρ) (Expr.liftSub σ n) =
      RouteII.upS ρ' n
  | 0, _ => by
      show er (ncons c Δ) (RouteII.upS ρ) (.var 0) = .base 0
      exact if_pos hc
  | n + 1, h => by
      simp only [Expr.liftSub_succ, er_rename, ncons_succ]
      show er Δ (fun i => (ρ i).rename Nat.succ) (σ n) = (ρ' n).rename Nat.succ
      rw [← er_skRename, hρ n h]

theorem bindC_isC_of_kind {a : CoC.Sk} : IsC (bindC (.kind a)) := trivial

/-- **Erasure commutes with substitution.**  `σ` must respect the classification (as in
`CoC.cl_subst`), and the erasure of the substituted constructors must be the new skeleton
environment; object variables put no constraint. -/
theorem er_subst (M : Expr Srt) : ∀ {Δ Δ' : ℕ → Cls} {ρ ρ' : ℕ → SkT} {σ : ℕ → Expr Srt},
    (∀ n, cl Δ (σ n) = Δ' n) → (∀ n, IsC (Δ' n) → er Δ ρ (σ n) = ρ' n) →
    er Δ ρ (M.subst σ) = er Δ' ρ' M := by
  induction M with
  | var n =>
      intro Δ Δ' ρ ρ' σ hσ hρ
      simp only [Expr.subst, er]
      split
      · exact hρ n ‹_›
      · exact er_junk ρ (by rw [hσ n]; assumption)
  | sort s => intro Δ Δ' ρ ρ' σ hσ hρ; rfl
  | app F a ihF _ =>
      intro Δ Δ' ρ ρ' σ hσ hρ
      simp only [Expr.subst, er, CoC.cl_subst F hσ, ihF hσ hρ]
  | lam A b _ ihb =>
      intro Δ Δ' ρ ρ' σ hσ hρ
      simp only [Expr.subst, er, CoC.cl_subst A hσ]
      rw [CoC.cl_subst b (CoC.cl_liftSub hσ _), ihb (CoC.cl_liftSub hσ _) (lift_hyp_ncons hρ _)]
  | pi A B ihA ihB =>
      intro Δ Δ' ρ ρ' σ hσ hρ
      simp only [Expr.subst, er, CoC.cl_subst A hσ]
      rw [CoC.cl_subst B (CoC.cl_liftSub hσ _)]
      split
      · split
        · rename_i a heq
          rw [ihB (CoC.cl_liftSub hσ _) (lift_hyp_upS hρ _ (by rw [heq]; trivial))]
        · rw [ihA hσ hρ, ihB (CoC.cl_liftSub hσ _) (lift_hyp_ncons hρ _)]
      · rfl

theorem cl_single' {Δ : ℕ → Cls} (U : Expr Srt) : ∀ n, cl Δ (Expr.single U n) = ncons (cl Δ U) Δ n
  | 0 => rfl
  | _ + 1 => rfl

/-- Erasure of an instance, for an argument of any class: the bound variable takes the
erasure of the argument as its skeleton. -/
theorem er_instantiate_ncons (B U : Expr Srt) (Δ : ℕ → Cls) (ρ : ℕ → SkT) :
    er Δ ρ (B.instantiate U) = er (ncons (cl Δ U) Δ) (ncons (er Δ ρ U) ρ) B := by
  refine er_subst B (cl_single' U) ?_
  intro n hn
  cases n with
  | zero => rfl
  | succ n => simp only [Expr.single, er, ncons_succ] at hn ⊢; rw [if_pos hn]

/-- **Erasure is invariant under object substitution**: substituting an object `N` (anything not
classified as a constructor) leaves the skeleton unchanged, whatever skeleton the bound variable
was given. -/
theorem er_instantiate_obj (B N : Expr Srt) (Δ : ℕ → Cls) (ρ : ℕ → SkT) (t : SkT)
    (hN : ¬ IsC (cl Δ N)) :
    er Δ ρ (B.instantiate N) = er (ncons (cl Δ N) Δ) (ncons t ρ) B := by
  refine er_subst B (cl_single' N) ?_
  intro n hn
  cases n with
  | zero => exact absurd hn hN
  | succ n => simp only [Expr.single, er, ncons_succ] at hn ⊢; rw [if_pos hn]

/-- In particular the skeleton of the bound object variable is irrelevant. -/
theorem er_obj_irrel (B : Expr Srt) (Δ : ℕ → Cls) (ρ : ℕ → SkT) (t t' : SkT) :
    er (ncons .obj Δ) (ncons t ρ) B = er (ncons .obj Δ) (ncons t' ρ) B := by
  have h := er_instantiate_obj B (.sort .box) Δ ρ t (by simp [cl, IsC])
  have h' := er_instantiate_obj B (.sort .box) Δ ρ t' (by simp [cl, IsC])
  simp only [cl] at h h'
  rw [← h, ← h']

theorem upS_single (ρ : ℕ → SkT) (t : SkT) :
    (fun i => (RouteII.upS ρ i).subst (RouteII.single t)) = ncons t ρ := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      simp only [RouteII.upS, Sk2.subst_rename, ncons_succ]
      have : (fun j => RouteII.single t (Nat.succ j)) = RouteII.Sk.base := rfl
      rw [this, Sk2.subst_base]

/-- **Erasure commutes with constructor substitution**: for a constructor `U` substituted for a
quantified variable, `er (B[U/α]) = (er B)[er U / α]`. -/
theorem er_instantiate (B U : Expr Srt) (Δ : ℕ → Cls) (ρ : ℕ → SkT) :
    er Δ ρ (B.instantiate U) =
      (er (ncons (cl Δ U) Δ) (RouteII.upS ρ) B).subst (RouteII.single (er Δ ρ U)) := by
  rw [er_skSubst, upS_single, er_instantiate_ncons]

/-! ### Invariance under β-reduction of well-typed λP2 terms -/

theorem isC_bindC {c : Cls} (h : IsC (bindC c)) : ∃ k, c = .kind k := by
  cases c with
  | kind k => exact ⟨k, rfl⟩
  | constr => exact h.elim
  | obj => exact h.elim

theorem er_app_isC {Δ : ℕ → Cls} {ρ : ℕ → SkT} {F a : Expr Srt} (h : IsC (cl Δ (.app F a))) :
    er Δ ρ (.app F a) = er Δ ρ F := if_pos h

theorem er_lam_isC {Δ : ℕ → Cls} {ρ : ℕ → SkT} {A b : Expr Srt} (h : IsC (cl Δ (.lam A b))) :
    er Δ ρ (.lam A b) = er (ncons (bindC (cl Δ A)) Δ) (ncons junk ρ) b := if_pos h

theorem er_pi_isC {Δ : ℕ → Cls} {ρ : ℕ → SkT} {A B : Expr Srt} (h : IsC (cl Δ (.pi A B))) :
    er Δ ρ (.pi A B) = (match cl Δ A with
      | .kind _ => .all (er (ncons (bindC (cl Δ A)) Δ) (RouteII.upS ρ) B)
      | _ => .arr (er Δ ρ A) (er (ncons (bindC (cl Δ A)) Δ) (ncons junk ρ) B)) := if_pos h

/-- The erasure of a quantifier `Π α:K. B` over a kind of skeleton `a`. -/
theorem er_pi_kind {Δ : ℕ → Cls} {ρ : ℕ → SkT} {A B : Expr Srt} {a : CoC.Sk}
    (h : IsC (cl Δ (.pi A B))) (hA : cl Δ A = .kind a) :
    er Δ ρ (.pi A B) = .all (er (ncons (.constr a) Δ) (RouteII.upS ρ) B) := by
  rw [er_pi_isC h]
  split
  · rw [hA]; rfl
  · rename_i hne; exact absurd hA (hne a)

/-- The erasure of a product `Π x:A. B` over a domain which is not a kind: an arrow. -/
theorem er_pi_type {Δ : ℕ → Cls} {ρ : ℕ → SkT} {A B : Expr Srt}
    (h : IsC (cl Δ (.pi A B))) (hA : ∀ a, cl Δ A ≠ .kind a) :
    er Δ ρ (.pi A B) = .arr (er Δ ρ A) (er (ncons .obj Δ) (ncons junk ρ) B) := by
  rw [er_pi_isC h]
  split
  · rename_i a ha; exact absurd ha (hA a)
  · rw [CoC.bindC_of_not_kind hA]

open CoC in
/-- λP2 has no constructor abstracting over a kind: a typed abstraction classified as a
constructor has a domain which is not a kind. -/
theorem lam_dom_not_kind {Γ : List (Expr Srt)} {A b T : Expr Srt}
    (h : HasType (cubeSpec lambdaP2) Γ (.lam A b) T)
    (hc : IsC (cl (ctxCl Γ) (.lam A b))) : ∀ a, cl (ctxCl Γ) A ≠ .kind a := by
  intro a ha
  obtain ⟨B, s, hb, hPi, -⟩ := h.generation_lam
  obtain ⟨s₁, s₂, s₃, hA, hB, hr, -⟩ := hPi.generation_pi
  -- the body is a constructor, so its type `B` is a kind
  have hbC : IsC (cl (ncons (bindC (cl (ctxCl Γ) A)) (ctxCl Γ)) b) := by
    simp only [cl] at hc
    revert hc
    cases cl (ncons (bindC (cl (ctxCl Γ) A)) (ctxCl Γ)) b <;> simp [lamCls, IsC]
  have hcb := classify hb (ne_box_of_hasType hB)
  simp only [ctxCl] at hcb
  rw [hcb] at hbC
  have hBk : ∃ k, cl (ctxCl (A :: Γ)) B = .kind k := isC_bindC hbC
  -- hence `B : □`, so `s₂ = □`
  have hs₂ : s₂ = .box := by
    cases s₂ with
    | box => rfl
    | star =>
        obtain ⟨k, hk⟩ := hBk
        exact absurd hk (not_kind hB (cube_star_box _ hB.valid) k)
  -- the domain is a kind, so `A : □`, so `s₁ = □`
  have hs₁ : s₁ = .box := by
    cases s₁ with
    | box => rfl
    | star => exact absurd ha (not_kind hA (cube_star_box _ hA.valid) a)
  subst hs₁ hs₂
  exact absurd hr.2 (by simp [lambdaP2, CubeFeatures.allows])

open CoC in
/-- **Erasure is invariant under β-reduction of well-typed λP2 terms.** -/
theorem er_beta {Γ : List (Expr Srt)} {M M' X : Expr Srt}
    (h : HasType (cubeSpec lambdaP2) Γ M X) (hr : Beta M M') (ρ : ℕ → SkT) :
    er (ctxCl Γ) ρ M = er (ctxCl Γ) ρ M' := by
  induction hr generalizing Γ X ρ with
  | head A b a =>
      by_cases hC : IsC (cl (ctxCl Γ) (.app (.lam A b) a))
      · obtain ⟨D, E, hF, ha, -⟩ := h.generation_app
        have hlC : IsC (cl (ctxCl Γ) (.lam A b)) := by
          simp only [cl] at hC ⊢
          revert hC
          cases lamCls (cl (ctxCl Γ) A) (cl (ncons (bindC (cl (ctxCl Γ) A)) (ctxCl Γ)) b) with
          | kind => simp [appCls, IsC]
          | constr k => simp [IsC]
          | obj => simp [appCls, IsC]
        have hnk := lam_dom_not_kind hF hlC
        obtain ⟨s, hPi⟩ := hF.product_type_sorted
        obtain ⟨s₁, s₂, s₃, hD, -, -, -⟩ := hPi.generation_pi
        -- the argument is an object
        obtain ⟨B₁, s', hb, hPi', hc'⟩ := hF.generation_lam
        have hca : cl (ctxCl Γ) a = .obj := by
          rw [classify ha (ne_box_of_hasType hD)]
          obtain ⟨t₁, t₂, t₃, hA, -, -, -⟩ := hPi'.generation_pi
          have hcAD : Converts A D := Relation.EqvGen.symm _ _ (Converts.product_compatibility hc').1
          cases s₁ with
          | box =>
              -- `D` is a kind convertible with `A`; then `A` is a kind, contradiction
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
        rw [er_app_isC hC, er_lam_isC hlC]
        rw [er_instantiate_obj b a (ctxCl Γ) ρ junk (by rw [hca]; simp [IsC]), hca,
          bindC_of_not_kind hnk]
      · rw [er_junk ρ hC, er_junk ρ (by rwa [← cl_beta h (.head A b a)])]
  | @app_left F F' U hr ih =>
      obtain ⟨A, B, hF, hU, -⟩ := h.generation_app
      simp only [er, ← cl_beta hF hr, ih hF]
  | @app_right F U U' hr ih => rfl
  | @lam_domain A A' b hr ih =>
      obtain ⟨B, s, hb, hPi, -⟩ := h.generation_lam
      obtain ⟨s₁, hA⟩ := hPi.product_domain A B rfl
      simp only [er, ← cl_beta hA hr]
  | @lam_body A b b' hr ih =>
      obtain ⟨B, s, hb, hPi, -⟩ := h.generation_lam
      have hcl := cl_beta hb hr
      have hih := ih hb (ncons junk ρ)
      simp only [ctxCl] at hcl hih
      simp only [er, hcl, hih]
  | @pi_domain A A' B hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, -, -⟩ := h.generation_pi
      simp only [er, ← cl_beta hA hr, ih hA]
  | @pi_body A B B' hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, -, -⟩ := h.generation_pi
      have hcl := cl_beta hB hr
      have hih := ih hB
      simp only [ctxCl] at hcl hih
      simp only [er, hcl, hih]

theorem er_reduces {Γ : List (Expr Srt)} {M M' X : Expr Srt}
    (h : HasType (cubeSpec lambdaP2) Γ M X) (hr : Reduces M M') (ρ : ℕ → SkT) :
    er (ctxCl Γ) ρ M = er (ctxCl Γ) ρ M' := by
  induction hr with
  | refl => rfl
  | tail hr₁ hr₂ ih => exact ih.trans (er_beta (h.subject_reduces hr₁) hr₂ ρ)

/-- **Erasure is invariant under β-conversion of well-typed λP2 terms** (two convertible
terms typed in the same context). -/
theorem er_conv {Γ : List (Expr Srt)} {M M' X X' : Expr Srt}
    (h : HasType (cubeSpec lambdaP2) Γ M X) (h' : HasType (cubeSpec lambdaP2) Γ M' X')
    (hc : Converts M M') (ρ : ℕ → SkT) :
    er (ctxCl Γ) ρ M = er (ctxCl Γ) ρ M' := by
  obtain ⟨C, hMC, hM'C⟩ := hc.join
  exact (er_reduces h hMC ρ).trans (er_reduces h' hM'C ρ).symm

end ErasureP2

end PureTypeSystem

namespace PureTypeSystem

namespace ErasureP2

open LambdaPi (Srt)
open CoC (ctxCl)

/-! ### The erasure does not extend to the calculus of constructions as it stands -/

/-- In `[α : ∗]`, the redex `(λβ:∗. β) α` of the calculus of constructions (already of `λω`). -/
def omegaRedex : Expr Srt := .app (.lam (.sort .star) (.var 0)) (.var 0)

/-- The context `[α : ∗]`. -/
abbrev ctxStar : List (Expr Srt) := List.cons (.sort .star) List.nil

theorem omegaRedex_typed : HasType (cubeSpec coc) ctxStar omegaRedex (.sort .star) := by
  have hax : HasType (cubeSpec coc) List.nil (Expr.sort Srt.star) (.sort .box) := .ax ⟨rfl, rfl⟩
  have h1 : HasType (cubeSpec coc) ctxStar (.sort .star) (.sort .box) := .weaken hax hax
  have h2 : HasType (cubeSpec coc) (.sort .star :: ctxStar) (.var 0) (.sort .star) := .var h1
  have h3 : HasType (cubeSpec coc) (.sort .star :: ctxStar) (.sort .star) (.sort .box) :=
    .weaken h1 h1
  have hpi : HasType (cubeSpec coc) ctxStar (.pi (.sort .star) (.sort .star)) (.sort .box) :=
    .product h1 h3 ⟨rfl, rfl⟩
  have hlam : HasType (cubeSpec coc) ctxStar (.lam (.sort .star) (.var 0))
      (.pi (.sort .star) (.sort .star)) := .abstraction h2 hpi
  have hv : HasType (cubeSpec coc) ctxStar (.var 0) (.sort .star) := .var hax
  exact .application hlam hv

/-- **The first failing step for coc**: the β-invariance `er_beta` fails at a redex of a
constructor abstracting over a constructor (rule `(□,□)`): `(λβ:∗. β) α` erases to the junk
skeleton, its contractum `α` to the type variable `α`.  A λ2 skeleton has no type-level
abstraction; the target has to be Fω types (with type-level λ and application) taken modulo
β, as in Geuvers' proof for the calculus of constructions. -/
theorem er_beta_fails_coc :
    HasType (cubeSpec coc) ctxStar omegaRedex (.sort .star) ∧
      Beta omegaRedex (.var 0) ∧
      er (ctxCl ctxStar) RouteII.Sk.base omegaRedex ≠
        er (ctxCl ctxStar) RouteII.Sk.base (.var 0) := by
  refine ⟨omegaRedex_typed, .head _ _ _, ?_⟩
  decide

end ErasureP2

end PureTypeSystem
