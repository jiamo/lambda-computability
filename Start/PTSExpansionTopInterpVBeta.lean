import Start.PTSExpansionTopInterpV

/-!
# Series V, round 3, run 2, part A1: invariance of `interpV` under conversion
(row M29-EP-TOP-SORT-FUNDAMENTAL)

The `cocTop` analogue of `ErasureCoC.interpK_beta` / `interpK_conv`, relative to a closed
skeleton valuation `θ`:

* **`interpV_beta`** — the interpretation of a typable `cocTop` expression is invariant under a
  β-step, at every skeleton relevant for its (evaluated) class;
* `interpV_reduces`, **`interpV_conv`** — invariance of the interpretation of sorted `cocTop`
  expressions (types and kinds, including kinds built from kind variables) under reduction and
  conversion.
-/

set_option autoImplicit false

namespace PureTypeSystem.TopSkel

open CoC (Sk Cls cl ncons bindC domSk RelC WC lamCls_eq_constr domSk_eq_arr domSk_eq_arrO
  bindC_of_not_kind)
open ErasureCoC (V KAlg ValK interpK interpK_instantiate interpK_agree)

variable {B : Type} (𝔄 : KAlg B)

/-- The evaluated context classifier at a declaration of a sorted `A` (not `K : □`). -/
theorem evalCtx_cons (θ : Nat → Sk) {Γ : List (Expr Srt3)} {A : Expr Srt3} {s : Srt3}
    (hA : HasType cocTop Γ A (.sort s)) (hs : s ≠ .top) :
    evalCls θ ∘ ctxClV (A :: Γ) =
      ncons (bindC (cl (evalCls θ ∘ ctxClV Γ) (A.mapSort srtC))) (evalCls θ ∘ ctxClV Γ) := by
  rw [ctxClV_cons_of_ne (ne_box_of_sorted hA hs), evalCls_ncons, evalCls_bindV,
    cl_toC θ A _ (wcv_of_hasType hA)]

theorem cl_toC_beta (θ : Nat → Sk) {Γ : List (Expr Srt3)} {U U' T : Expr Srt3}
    (h : HasType cocTop Γ U T) (hr : Beta U U') :
    cl (evalCls θ ∘ ctxClV Γ) (U.mapSort srtC) = cl (evalCls θ ∘ ctxClV Γ) (U'.mapSort srtC) := by
  rw [cl_toC θ U _ (wcv_of_hasType h), cl_toC θ U' _ (wcv_of_hasType (h.subject_reduction hr)),
    clV_beta h hr]

theorem relC_toC_of_sorted (θ : Nat → Sk) {Γ : List (Expr Srt3)} {A : Expr Srt3} {s : Srt3}
    (h : HasType cocTop Γ A (.sort s)) (hs : s ≠ .top) :
    RelC (cl (evalCls θ ∘ ctxClV Γ) (A.mapSort srtC)) .star := by
  apply RelC.of_piOK
  rw [cl_toC θ A _ (wcv_of_hasType h)]
  exact piOK_evalCls_of_sorted θ h hs

/-- **The interpretation relative to `θ` is invariant under a β-step.** -/
theorem interpV_beta (θ : Nat → Sk) {Γ : List (Expr Srt3)} {M M' X : Expr Srt3}
    (h : HasType cocTop Γ M X) (hr : Beta M M') {k : Sk}
    (hk : RelC (cl (evalCls θ ∘ ctxClV Γ) (M.mapSort srtC)) k) (ξ : ValK B) :
    interpV 𝔄 θ (ctxClV Γ) M k ξ = interpV 𝔄 θ (ctxClV Γ) M' k ξ := by
  induction hr generalizing Γ X k ξ with
  | head A b U =>
      simp only [interpV, Expr.mapSort_instantiate] at hk ⊢
      have hwc := wc_toC θ h
      simp only [Expr.mapSort] at hwc hk ⊢
      obtain ⟨⟨_, hb⟩, _, hok⟩ := hwc
      rcases hk.app with ⟨a, ha⟩ | ha
      · rw [ha] at hok
        have hcU : cl (evalCls θ ∘ ctxClV Γ) (U.mapSort srtC) = .constr a := hok
        obtain ⟨k₀, hb₀, hk₀⟩ := lamCls_eq_constr ha
        obtain ⟨hcA, rfl⟩ := domSk_eq_arr hk₀.symm
        rw [interpK_instantiate, hcU]
        simp only [interpK, hcU]
        rw [hcA] at hb hb₀ ⊢
        apply interpK_agree 𝔄 _ hb _ (.inl hb₀)
        intro n k' hk'
        cases n with
        | zero =>
            have := RelC.constr_eq hk'
            subst this
            simp
        | succ n => rfl
      · rw [ha] at hok
        have hcU : cl (evalCls θ ∘ ctxClV Γ) (U.mapSort srtC) = .obj := hok
        obtain ⟨k₀, hb₀, hk₀⟩ := lamCls_eq_constr ha
        obtain ⟨hcA, rfl⟩ := domSk_eq_arrO hk₀.symm
        rw [interpK_instantiate, hcU]
        simp only [interpK, hcU]
        rw [bindC_of_not_kind hcA] at hb hb₀ ⊢
        apply interpK_agree 𝔄 _ hb _ (.inl hb₀)
        intro n k' hk'
        cases n with
        | zero => exact hk'.not_obj.elim
        | succ n => rfl
  | @app_left F F' U hr ih =>
      obtain ⟨A, B, hF, hU, -⟩ := h.generation_app
      have hwc := wc_toC θ h
      simp only [interpV, Expr.mapSort] at hk hwc ih ⊢
      obtain ⟨_, _, hok⟩ := hwc
      rcases hk.app with ⟨a, ha⟩ | ha
      · rw [ha] at hok
        have hcU : cl (evalCls θ ∘ ctxClV Γ) (U.mapSort srtC) = .constr a := hok
        simp only [interpK, hcU]
        rw [ih hF (.inl ha)]
      · rw [ha] at hok
        have hcU : cl (evalCls θ ∘ ctxClV Γ) (U.mapSort srtC) = .obj := hok
        simp only [interpK, hcU]
        rw [ih hF (.inl ha)]
  | @app_right F U U' hr ih =>
      obtain ⟨A, B, hF, hU, -⟩ := h.generation_app
      have hwc := wc_toC θ h
      have hcl := cl_toC_beta θ hU hr
      simp only [interpV, Expr.mapSort] at hk hwc ih ⊢
      obtain ⟨_, _, hok⟩ := hwc
      rcases hk.app with ⟨a, ha⟩ | ha
      · rw [ha] at hok
        have hcU : cl (evalCls θ ∘ ctxClV Γ) (U.mapSort srtC) = .constr a := hok
        have hcU' : cl (evalCls θ ∘ ctxClV Γ) (U'.mapSort srtC) = .constr a := hcl ▸ hcU
        simp only [interpK, hcU, hcU']
        rw [ih hU (.inl hcU)]
      · rw [ha] at hok
        have hcU : cl (evalCls θ ∘ ctxClV Γ) (U.mapSort srtC) = .obj := hok
        have hcU' : cl (evalCls θ ∘ ctxClV Γ) (U'.mapSort srtC) = .obj := hcl ▸ hcU
        simp only [interpK, hcU, hcU']
        rfl
  | @lam_domain A A' b hr _ =>
      obtain ⟨B, s, hb, hPi, -⟩ := h.generation_lam
      obtain ⟨s₁, hA⟩ := hPi.product_domain A B rfl
      have hcl := cl_toC_beta θ hA hr
      simp only [interpV, Expr.mapSort]
      cases k <;> simp only [interpK, hcl] <;> rfl
  | @lam_body A b b' hr ih =>
      obtain ⟨B, s, hb, hPi, -⟩ := h.generation_lam
      obtain ⟨s₁, s₂, s₃, hA, hB, hrl, -⟩ := hPi.generation_pi
      have hctx := evalCtx_cons θ hA (rule_dom hrl)
      simp only [interpV, Expr.mapSort] at hk ih ⊢
      obtain ⟨k₀, hb₀, rfl⟩ := hk.lam
      have ih' := fun ξ => ih hb (by rw [hctx]; exact .inl hb₀) ξ
      rw [hctx] at ih'
      rcases hcA : cl (evalCls θ ∘ ctxClV Γ) (A.mapSort srtC) with a | a | _
      · simp only [domSk, interpK]
        funext v
        exact ih' _
      · simp only [domSk, interpK]
        exact ih' _
      · simp only [domSk, interpK]
        exact ih' _
  | @pi_domain A A' B hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrl, -⟩ := h.generation_pi
      simp only [interpV, Expr.mapSort] at hk ih ⊢
      have := hk.pi
      subst this
      have hcl := cl_toC_beta θ hA hr
      have hA' := ih hA (relC_toC_of_sorted θ hA (rule_dom hrl)) ξ
      simp only [interpK]
      rw [← hcl, hA']
  | @pi_body A B B' hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrl, -⟩ := h.generation_pi
      have hctx := evalCtx_cons θ hA (rule_dom hrl)
      simp only [interpV, Expr.mapSort] at hk ih ⊢
      have := hk.pi
      subst this
      have ih' := fun ξ => ih hB (relC_toC_of_sorted θ hB (rule_cod hrl)) ξ
      rw [hctx] at ih'
      simp only [interpK]
      rcases hcA : cl (evalCls θ ∘ ctxClV Γ) (A.mapSort srtC) with a | a | _ <;>
        (rw [hcA] at ih'; simp only [bindC] at ih'; simp only [ih']) <;> rfl

theorem interpV_reduces (θ : Nat → Sk) {Γ : List (Expr Srt3)} {A C : Expr Srt3} {s : Srt3}
    (h : HasType cocTop Γ A (.sort s)) (hs : s ≠ .top) (hr : Reduces A C) (ξ : ValK B) :
    interpV 𝔄 θ (ctxClV Γ) A .star ξ = interpV 𝔄 θ (ctxClV Γ) C .star ξ := by
  induction hr with
  | refl => rfl
  | tail hr₁ hr₂ ih =>
      have hB := h.subject_reduces hr₁
      exact ih.trans (interpV_beta 𝔄 θ hB hr₂ (relC_toC_of_sorted θ hB hs) ξ)

/-- **The interpretation relative to `θ` of sorted `cocTop` expressions is invariant under
conversion.** -/
theorem interpV_conv (θ : Nat → Sk) {Γ : List (Expr Srt3)} {A B' : Expr Srt3} {s t : Srt3}
    (hA : HasType cocTop Γ A (.sort s)) (hs : s ≠ .top) (hB : HasType cocTop Γ B' (.sort t))
    (ht : t ≠ .top) (hc : Converts A B') (ξ : ValK B) :
    interpV 𝔄 θ (ctxClV Γ) A .star ξ = interpV 𝔄 θ (ctxClV Γ) B' .star ξ := by
  obtain ⟨C, hAC, hBC⟩ := hc.join
  exact (interpV_reduces 𝔄 θ hA hs hAC ξ).trans (interpV_reduces 𝔄 θ hB ht hBC ξ).symm

end PureTypeSystem.TopSkel
