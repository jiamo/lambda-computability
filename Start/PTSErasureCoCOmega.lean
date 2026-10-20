import Start.CoCSN
import Start.PTSErasureP2

/-!
# Round 11, part A1: the Fω interpretation of coc constructors, over an arbitrary base

Route (ii) for coc needs an erasure of coc constructors that is invariant under conversion
(`ErasureP2.er_beta_fails_coc` shows that a λ2-skeleton erasure is not).  Following Geuvers'
short proof of strong normalization for the calculus of constructions, kinds and constructors
are interpreted directly in a semantics instead of in Fω syntax modulo β.

The repository already has this interpretation for saturated sets (`CoC.interp`,
`Start/CoCModel.lean`) with its invariance under conversion (`CoC.interp_conv`,
`Start/CoCSN.lean`).  Route (ii) needs it with the round-10 judgement candidates at `∗`.  This
module therefore abstracts the base: `V B` and `interpK 𝔄` are parametric in a type `B` of
"candidates" and in an algebra `𝔄 : KAlg B` giving the default element and the two product
constructions (`piK` quantifies over the semantic kind `V B a` of the bound constructor
variable; `piO` is the object product).  Every structural lemma is proved for every algebra:

* `KSkω`, `erKω` (object products dropped), and `V_erKω : V B k = Vω B (erKω k)`;
* `interpK_rename`, `interpK_subst`, `interpK_instantiate` — the substitution lemma
  `⟦T[U/α]⟧ξ = ⟦T⟧(ξ, ⟦U⟧ξ)` (object substitutions are transparent);
* `interpK_agree` — irrelevant values do not matter;
* `interpK_beta`, `interpK_reduces`, **`interpK_conv`** — invariance of the interpretation of
  well-typed coc kinds and types under conversion (`erω_conv` of the round-11 plan), for every
  corner of the cube;
* `interpK_omegaRedex` — the equation refuted for the λ2 erasure by `er_beta_fails_coc` holds.
-/

set_option autoImplicit false

namespace PureTypeSystem

namespace ErasureCoC

open LambdaPi (Srt)
open CoC (Sk Cls cl ncons ncons_zero ncons_succ ncons_comp_succ ncons_comp_liftRen bindC
  cl_rename cl_subst cl_liftSub cl_single RelC WC ctxCl lamCls_eq_constr domSk_eq_arr
  domSk_eq_arrO bindC_of_not_kind wc_of_hasType cl_beta relC_of_sorted domSk)

/-! ### Kind skeletons with object products dropped -/

/-- Fω kind skeletons: `∗` and arrows. -/
inductive KSkω where
  | star : KSkω
  | arr : KSkω → KSkω → KSkω
  deriving DecidableEq

/-- The erasure of coc kind skeletons: object products are dropped, constructor products
kept. -/
def erKω : Sk → KSkω
  | .star => .star
  | .arrO k => erKω k
  | .arr a k => .arr (erKω a) (erKω k)

/-- Semantic kinds over a base `B`, indexed by Fω kind skeletons. -/
def Vω (B : Type) : KSkω → Type
  | .star => B
  | .arr κ₁ κ₂ => Vω B κ₁ → Vω B κ₂

/-- Semantic kinds over a base `B`, indexed by coc kind skeletons. -/
def V (B : Type) : Sk → Type
  | .star => B
  | .arrO k => V B k
  | .arr a k => V B a → V B k

/-- The two indexings agree: `V B k` is `Vω B (erKω k)`. -/
theorem V_erKω (B : Type) : ∀ k : Sk, V B k = Vω B (erKω k)
  | .star => rfl
  | .arrO k => V_erKω B k
  | .arr a k => by
      show (V B a → V B k) = (Vω B (erKω a) → Vω B (erKω k))
      rw [V_erKω B a, V_erKω B k]

/-- The semantic operations at `∗`: a default element and the two products. -/
structure KAlg (B : Type) where
  /-- The default element (for round-10 candidates: the candidate of normalizing terms). -/
  dflt : B
  /-- The product over a constructor variable of skeleton `a`. -/
  piK : (a : Sk) → B → (V B a → B) → B
  /-- The object product. -/
  piO : B → B → B

variable {B : Type} (𝔄 : KAlg B)

/-- The canonical (default) element of each semantic kind. -/
def canonK : (k : Sk) → V B k
  | .star => 𝔄.dflt
  | .arrO k => canonK k
  | .arr _ k => fun _ => canonK k

/-- Valuations: every variable receives a value at every skeleton. -/
abbrev ValK (B : Type) := Nat → (k : Sk) → V B k

/-- The value of a constructor variable of skeleton `a`; default at other skeletons. -/
def extK (a : Sk) (v : V B a) : (k : Sk) → V B k :=
  fun k => if h : a = k then h ▸ v else canonK 𝔄 k

@[simp] theorem extK_self (a : Sk) (v : V B a) : extK 𝔄 a v a = v := by
  simp [extK]

/-- **The interpretation of coc kinds and constructors** at an expected skeleton, total: where
the shapes do not match it returns the default element. -/
def interpK : (Nat → Cls) → Expr Srt → (k : Sk) → ValK B → V B k
  | _, .var n, k, ξ => ξ n k
  | _, .sort _, k, _ => canonK 𝔄 k
  | Δ, .app F U, k, ξ =>
      match cl Δ U with
      | .constr a => interpK Δ F (.arr a k) ξ (interpK Δ U a ξ)
      | .kind _ => interpK Δ F (.arrO k) ξ
      | .obj => interpK Δ F (.arrO k) ξ
  | Δ, .lam A b, .arr a k, ξ =>
      fun v => interpK (ncons (bindC (cl Δ A)) Δ) b k (ncons (extK 𝔄 a v) ξ)
  | Δ, .lam A b, .arrO k, ξ => interpK (ncons (bindC (cl Δ A)) Δ) b k (ncons (canonK 𝔄) ξ)
  | _, .lam _ _, .star, _ => 𝔄.dflt
  | Δ, .pi A B', .star, ξ =>
      match cl Δ A with
      | .kind a => 𝔄.piK a (interpK Δ A .star ξ)
          (fun v => interpK (ncons (.constr a) Δ) B' .star (ncons (extK 𝔄 a v) ξ))
      | .constr _ => 𝔄.piO (interpK Δ A .star ξ)
          (interpK (ncons .obj Δ) B' .star (ncons (canonK 𝔄) ξ))
      | .obj => 𝔄.piO (interpK Δ A .star ξ)
          (interpK (ncons .obj Δ) B' .star (ncons (canonK 𝔄) ξ))
  | _, .pi _ _, .arrO k, _ => canonK 𝔄 k
  | _, .pi _ _, .arr a k, _ => canonK 𝔄 (.arr a k)

theorem interpK_rename (M : Expr Srt) (Δ : Nat → Cls) (ρ : Nat → Nat) (k : Sk) (ξ : ValK B) :
    interpK 𝔄 Δ (M.rename ρ) k ξ = interpK 𝔄 (Δ ∘ ρ) M k (ξ ∘ ρ) := by
  induction M generalizing Δ ρ k ξ with
  | var n => rfl
  | sort s => rfl
  | app F U ihF ihU =>
      simp only [Expr.rename, interpK, cl_rename]
      cases cl (Δ ∘ ρ) U <;> simp only [ihF, ihU] <;> rfl
  | lam A b ihA ihb =>
      cases k with
      | star => rfl
      | arrO k =>
          simp only [Expr.rename, interpK, cl_rename, ihb, ncons_comp_liftRen]
          rfl
      | arr a k =>
          funext v
          simp only [Expr.rename, interpK, cl_rename, ihb, ncons_comp_liftRen]
  | pi A B ihA ihB =>
      cases k with
      | arrO k => rfl
      | arr a k => rfl
      | star =>
          simp only [Expr.rename, interpK, cl_rename]
          cases cl (Δ ∘ ρ) A <;> simp only [ihA, ihB, ncons_comp_liftRen] <;> rfl

/-- The valuation induced by a substitution. -/
def substValK (Δ : Nat → Cls) (σ : Nat → Expr Srt) (ξ : ValK B) : ValK B :=
  fun n k => interpK 𝔄 Δ (σ n) k ξ

theorem substValK_liftSub (Δ : Nat → Cls) (σ : Nat → Expr Srt) (ξ : ValK B) (c : Cls)
    (e : (k : Sk) → V B k) :
    substValK 𝔄 (ncons c Δ) (Expr.liftSub σ) (ncons e ξ) = ncons e (substValK 𝔄 Δ σ ξ) := by
  funext n k
  cases n with
  | zero => rfl
  | succ n =>
      simp only [substValK, Expr.liftSub_succ, interpK_rename, ncons_comp_succ, ncons_succ]

/-- **The substitution lemma** for every class-respecting substitution. -/
theorem interpK_subst (M : Expr Srt) {Δ Δ' : Nat → Cls} {σ : Nat → Expr Srt}
    (hσ : ∀ n, cl Δ (σ n) = Δ' n) (k : Sk) (ξ : ValK B) :
    interpK 𝔄 Δ (M.subst σ) k ξ = interpK 𝔄 Δ' M k (substValK 𝔄 Δ σ ξ) := by
  induction M generalizing Δ Δ' σ k ξ with
  | var n => rfl
  | sort s => rfl
  | app F U ihF ihU =>
      simp only [Expr.subst, interpK, cl_subst U hσ]
      cases cl Δ' U <;> simp only [ihF hσ, ihU hσ] <;> rfl
  | lam A b ihA ihb =>
      cases k with
      | star => rfl
      | arrO k =>
          simp only [Expr.subst, interpK, cl_subst A hσ]
          rw [ihb (cl_liftSub hσ _), substValK_liftSub]
      | arr a k =>
          funext v
          simp only [Expr.subst, interpK, cl_subst A hσ]
          rw [ihb (cl_liftSub hσ _), substValK_liftSub]
  | pi A B ihA ihB =>
      cases k with
      | arrO k => rfl
      | arr a k => rfl
      | star =>
          simp only [Expr.subst, interpK, cl_subst A hσ]
          cases cl Δ' A with
          | kind a =>
              simp only [ihA hσ]
              congr 1
              funext v
              rw [ihB (cl_liftSub hσ _), substValK_liftSub]
          | constr a =>
              simp only [ihA hσ]
              rw [ihB (cl_liftSub hσ _), substValK_liftSub]
          | obj =>
              simp only [ihA hσ]
              rw [ihB (cl_liftSub hσ _), substValK_liftSub]

theorem substValK_single (Δ : Nat → Cls) (U : Expr Srt) (ξ : ValK B) :
    substValK 𝔄 Δ (Expr.single U) ξ = ncons (fun k => interpK 𝔄 Δ U k ξ) ξ := by
  funext n k
  cases n <;> rfl

/-- **Instantiation**: `⟦b[U/x]⟧ξ = ⟦b⟧(ξ, ⟦U⟧ξ)`. -/
theorem interpK_instantiate (b U : Expr Srt) (Δ : Nat → Cls) (k : Sk) (ξ : ValK B) :
    interpK 𝔄 Δ (b.instantiate U) k ξ =
      interpK 𝔄 (ncons (cl Δ U) Δ) b k (ncons (fun k => interpK 𝔄 Δ U k ξ) ξ) := by
  rw [Expr.instantiate, interpK_subst 𝔄 b (cl_single U), substValK_single]

/-! ### Irrelevant values -/

/-- Two valuations agree on the relevant values of the variables. -/
def AgreeK (Δ : Nat → Cls) (ξ ξ' : ValK B) : Prop := ∀ n k, RelC (Δ n) k → ξ n k = ξ' n k

theorem AgreeK.ncons {Δ : Nat → Cls} {ξ ξ' : ValK B} (h : AgreeK Δ ξ ξ') (c : Cls)
    (e : (k : Sk) → V B k) : AgreeK (ncons c Δ) (ncons e ξ) (ncons e ξ') := by
  intro n k hk
  cases n with
  | zero => rfl
  | succ n => exact h n k hk

/-- **Irrelevant values do not matter.** -/
theorem interpK_agree (M : Expr Srt) {Δ : Nat → Cls} {ξ ξ' : ValK B} {k : Sk} (hM : WC Δ M)
    (hξ : AgreeK Δ ξ ξ') (hk : RelC (cl Δ M) k) :
    interpK 𝔄 Δ M k ξ = interpK 𝔄 Δ M k ξ' := by
  induction M generalizing Δ ξ ξ' k with
  | var n => exact hξ n k hk
  | sort s => rfl
  | app F U ihF ihU =>
      obtain ⟨hF, hU, hok⟩ := hM
      rcases hk.app with ⟨a, ha⟩ | ha
      · rw [ha] at hok
        have hcU : cl Δ U = .constr a := hok
        simp only [interpK, hcU]
        rw [ihF hF hξ (.inl ha), ihU hU hξ (.inl hcU)]
      · rw [ha] at hok
        have hcU : cl Δ U = .obj := hok
        simp only [interpK, hcU]
        exact ihF hF hξ (.inl ha)
  | lam A b ihA ihb =>
      obtain ⟨hA, hb⟩ := hM
      obtain ⟨k₀, hb₀, rfl⟩ := hk.lam
      rcases hcA : cl Δ A with a | a | _
      · rw [hcA] at hb hb₀
        simp only [domSk, interpK, hcA]
        funext v
        exact ihb hb (hξ.ncons _ _) (.inl hb₀)
      · rw [hcA] at hb hb₀
        simp only [domSk, interpK, hcA]
        exact ihb hb (hξ.ncons _ _) (.inl hb₀)
      · rw [hcA] at hb hb₀
        simp only [domSk, interpK, hcA]
        exact ihb hb (hξ.ncons _ _) (.inl hb₀)
  | pi A B ihA ihB =>
      obtain ⟨hA, hB, hpA, hpB⟩ := hM
      have := hk.pi
      subst this
      simp only [interpK]
      rcases hcA : cl Δ A with a | a | _
      · rw [hcA] at hB hpB
        simp only [ihA hA hξ (.of_piOK (hcA ▸ hpA))]
        congr 1
        funext v
        exact ihB hB (hξ.ncons _ _) (.of_piOK hpB)
      · rw [hcA] at hB hpB
        simp only [bindC] at hB hpB
        simp only [ihA hA hξ (.of_piOK (hcA ▸ hpA))]
        rw [ihB hB (hξ.ncons _ _) (.of_piOK hpB)]
      · rw [hcA] at hB hpB
        simp only [bindC] at hB hpB
        simp only [ihA hA hξ (.of_piOK (hcA ▸ hpA))]
        rw [ihB hB (hξ.ncons _ _) (.of_piOK hpB)]

/-! ### Invariance under conversion of well-typed coc terms -/

variable {f : CubeFeatures}

/-- **The interpretation of legal kinds and constructors is invariant under reduction.** -/
theorem interpK_beta {Γ : List (Expr Srt)} {M M' X : Expr Srt}
    (h : HasType (cubeSpec f) Γ M X) (hr : Beta M M') {k : Sk} (hk : RelC (cl (ctxCl Γ) M) k)
    (ξ : ValK B) : interpK 𝔄 (ctxCl Γ) M k ξ = interpK 𝔄 (ctxCl Γ) M' k ξ := by
  induction hr generalizing Γ X k ξ with
  | head A b U =>
      have hwc := wc_of_hasType h
      obtain ⟨⟨_, hb⟩, _, hok⟩ := hwc
      rcases hk.app with ⟨a, ha⟩ | ha
      · rw [ha] at hok
        have hcU : cl (ctxCl Γ) U = .constr a := hok
        obtain ⟨k₀, hb₀, hk₀⟩ := lamCls_eq_constr ha
        obtain ⟨hcA, rfl⟩ := domSk_eq_arr hk₀.symm
        rw [interpK_instantiate, hcU]
        simp only [interpK, hcU]
        rw [hcA] at hb hb₀ ⊢
        apply interpK_agree 𝔄 b hb _ (.inl hb₀)
        intro n k' hk'
        cases n with
        | zero =>
            have := RelC.constr_eq hk'
            subst this
            simp
        | succ n => rfl
      · rw [ha] at hok
        have hcU : cl (ctxCl Γ) U = .obj := hok
        obtain ⟨k₀, hb₀, hk₀⟩ := lamCls_eq_constr ha
        obtain ⟨hcA, rfl⟩ := domSk_eq_arrO hk₀.symm
        rw [interpK_instantiate, hcU]
        simp only [interpK, hcU]
        rw [bindC_of_not_kind hcA] at hb hb₀ ⊢
        apply interpK_agree 𝔄 b hb _ (.inl hb₀)
        intro n k' hk'
        cases n with
        | zero => exact hk'.not_obj.elim
        | succ n => rfl
  | @app_left F F' U hr ih =>
      obtain ⟨A, B, hF, hU, -⟩ := h.generation_app
      obtain ⟨_, _, hok⟩ := wc_of_hasType h
      rcases hk.app with ⟨a, ha⟩ | ha
      · rw [ha] at hok
        have hcU : cl (ctxCl Γ) U = .constr a := hok
        simp only [interpK, hcU]
        rw [ih hF (.inl ha)]
      · rw [ha] at hok
        have hcU : cl (ctxCl Γ) U = .obj := hok
        simp only [interpK, hcU]
        rw [ih hF (.inl ha)]
  | @app_right F U U' hr ih =>
      obtain ⟨A, B, hF, hU, -⟩ := h.generation_app
      obtain ⟨_, _, hok⟩ := wc_of_hasType h
      have hcl := cl_beta hU hr
      rcases hk.app with ⟨a, ha⟩ | ha
      · rw [ha] at hok
        have hcU : cl (ctxCl Γ) U = .constr a := hok
        have hcU' : cl (ctxCl Γ) U' = .constr a := hcl ▸ hcU
        simp only [interpK, hcU, hcU']
        rw [ih hU (.inl hcU)]
      · rw [ha] at hok
        have hcU : cl (ctxCl Γ) U = .obj := hok
        have hcU' : cl (ctxCl Γ) U' = .obj := hcl ▸ hcU
        simp only [interpK, hcU, hcU']
        rfl
  | @lam_domain A A' b hr _ =>
      obtain ⟨B, s, hb, hPi, -⟩ := h.generation_lam
      obtain ⟨s₁, hA⟩ := hPi.product_domain A B rfl
      have hcl := cl_beta hA hr
      cases k <;> simp only [interpK, hcl] <;> rfl
  | @lam_body A b b' hr ih =>
      obtain ⟨B, s, hb, hPi, -⟩ := h.generation_lam
      obtain ⟨k₀, hb₀, rfl⟩ := hk.lam
      have ih' := fun ξ => ih hb (.inl hb₀) ξ
      simp only [ctxCl] at ih'
      rcases hcA : cl (ctxCl Γ) A with a | a | _
      · simp only [domSk, interpK]
        funext v
        exact ih' _
      · simp only [domSk, interpK]
        exact ih' _
      · simp only [domSk, interpK]
        exact ih' _
  | @pi_domain A A' B hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, -, -⟩ := h.generation_pi
      have := hk.pi
      subst this
      have hcl := cl_beta hA hr
      have hA' := ih hA (relC_of_sorted hA) ξ
      simp only [interpK]
      rw [← hcl, hA']
  | @pi_body A B B' hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, -, -⟩ := h.generation_pi
      have := hk.pi
      subst this
      have ih' := fun ξ => ih hB (relC_of_sorted hB) ξ
      simp only [ctxCl] at ih'
      simp only [interpK]
      rcases hcA : cl (ctxCl Γ) A with a | a | _ <;>
        (rw [hcA] at ih'; simp only [bindC] at ih'; simp only [ih']) <;> rfl

theorem interpK_reduces {Γ : List (Expr Srt)} {A C : Expr Srt} {s : Srt}
    (h : HasType (cubeSpec f) Γ A (.sort s)) (hr : Reduces A C) (ξ : ValK B) :
    interpK 𝔄 (ctxCl Γ) A .star ξ = interpK 𝔄 (ctxCl Γ) C .star ξ := by
  induction hr with
  | refl => rfl
  | tail hr₁ hr₂ ih =>
      have hB := h.subject_reduces hr₁
      exact ih.trans (interpK_beta 𝔄 hB hr₂ (relC_of_sorted hB) ξ)

/-- **`erω_conv`: the interpretation of well-typed kinds and types is invariant under
conversion**, for every base algebra and every corner of the cube (in particular coc). -/
theorem interpK_conv {Γ : List (Expr Srt)} {A B' : Expr Srt} {s t : Srt}
    (hA : HasType (cubeSpec f) Γ A (.sort s)) (hB : HasType (cubeSpec f) Γ B' (.sort t))
    (hc : Converts A B') (ξ : ValK B) :
    interpK 𝔄 (ctxCl Γ) A .star ξ = interpK 𝔄 (ctxCl Γ) B' .star ξ := by
  obtain ⟨C, hAC, hBC⟩ := hc.join
  exact (interpK_reduces 𝔄 hA hAC ξ).trans (interpK_reduces 𝔄 hB hBC ξ).symm

/-- **The equation refuted for the λ2 erasure holds**: in the context `[∗]`, the interpretation
of `(λx:∗. x) x` equals that of `x`, for every base algebra and valuation (compare
`ErasureP2.er_beta_fails_coc`). -/
theorem interpK_omegaRedex (ξ : ValK B) :
    interpK 𝔄 (ctxCl ErasureP2.ctxStar) ErasureP2.omegaRedex .star ξ =
      interpK 𝔄 (ctxCl ErasureP2.ctxStar) (.var 0) .star ξ :=
  interpK_reduces 𝔄 ErasureP2.omegaRedex_typed (.single (.head _ _ _)) ξ

end ErasureCoC

end PureTypeSystem
