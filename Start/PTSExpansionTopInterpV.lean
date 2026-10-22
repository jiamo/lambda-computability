import Start.PTSExpansionTopClassifyV
import Start.PTSErasureCoCOmega

/-!
# Series V, round 3, run 2, part A1: the interpretation of `cocTop` kinds and constructors
relative to a closed skeleton valuation (row M29-EP-TOP-SORT-FUNDAMENTAL)

A closed skeleton valuation `θ : Nat → CoC.Sk` evaluates the skeleton variables `svar i` of
`Start/PTSExpansionTopSkel.lean`; a class `c : ClsV` evaluates to a closed class
`evalCls θ c : CoC.Cls`.  The interpretation `interpV 𝔄 θ Δ M` of a `cocTop` expression is the
abstract interpretation `ErasureCoC.interpK 𝔄` of its coc image `(M.mapSort srtC)` (sorts `□` and `Δ` both
become `□`, which are interpreted alike), in the *evaluated* classifier `evalCls θ ∘ Δ`.  A kind
variable `K` whose class is `kind (svar ℓ)` thus ranges over the semantic kind `V B (θ ℓ)` — this
is the space `VV θ (svar ℓ)` of the skeleton module, with the dependency on `θ` resolved by
evaluating the class first.

* `evalSk`, `evalCls`, and their commutation with `bindV`, `domV`, `lamV`, `piV` (unconditional)
  and `appV` (away from constructors of variable skeleton, `evalCls_appV`);
* **`cl_toC`** — on well-classified expressions the coc classifier of the image, in the evaluated
  context classifier, is the evaluated `clV`;
* `interpV`, `interpV_rename`, **`interpV_subst`**, `interpV_instantiate` — the substitution lemma
  for every class-respecting substitution;
* **`interpV_subst_kind`** — the new case: substituting expressions for variables of evaluated
  class `kind (θ' ℓ)`; the side condition is exactly that `θ'` extends `θ` by the skeleton of
  the substituted kind (`interpV_kindVar_cond`).

* **`wc_toC`** — the coc image of a `cocTop`-typable expression is well classified in the
  evaluated context classifier (the input `interpV_beta` needs at the β-redex).

Invariance under conversion (`interpV_beta`, `interpV_conv`) is in
`Start/PTSExpansionTopInterpVBeta.lean`.
-/

set_option autoImplicit false

namespace PureTypeSystem.TopSkel

open CoC (Sk Cls cl ncons bindC domSk appCls lamCls piCls)
open ErasureCoC (V KAlg ValK interpK substValK)

/-- Evaluation of skeleton variables. -/
def evalSk (θ : Nat → Sk) : SkV → Sk
  | .star => .star
  | .arrO k => .arrO (evalSk θ k)
  | .arr a k => .arr (evalSk θ a) (evalSk θ k)
  | .svar i => θ i

def evalCls (θ : Nat → Sk) : ClsV → Cls
  | .kind k => .kind (evalSk θ k)
  | .constr k => .constr (evalSk θ k)
  | .obj => .obj

@[simp] theorem evalSk_ofSk (θ : Nat → Sk) (k : Sk) : evalSk θ (ofSk k) = k := by
  induction k with
  | star => rfl
  | arrO k ih => simp [ofSk, evalSk, ih]
  | arr a k iha ihk => simp [ofSk, evalSk, iha, ihk]

theorem evalCls_bindV (θ : Nat → Sk) (c : ClsV) : evalCls θ (bindV c) = bindC (evalCls θ c) := by
  cases c <;> rfl

theorem evalSk_domV (θ : Nat → Sk) (c : ClsV) (k : SkV) :
    evalSk θ (domV c k) = domSk (evalCls θ c) (evalSk θ k) := by
  cases c <;> rfl

theorem evalCls_lamV (θ : Nat → Sk) (cA c : ClsV) :
    evalCls θ (lamV cA c) = lamCls (evalCls θ cA) (evalCls θ c) := by
  cases c <;> simp only [lamV, evalCls, lamCls, evalSk_domV]

theorem evalCls_piV (θ : Nat → Sk) (cA c : ClsV) :
    evalCls θ (piV cA c) = piCls (evalCls θ cA) (evalCls θ c) := by
  cases c <;> simp only [piV, evalCls, piCls, evalSk_domV, evalSk]

theorem evalCls_appV (θ : Nat → Sk) (c : ClsV) (hc : ∀ i, c ≠ .constr (.svar i)) :
    evalCls θ (appV c) = appCls (evalCls θ c) := by
  rcases c with k | k | _
  · rfl
  · cases k with
    | star => rfl
    | arrO k => rfl
    | arr a k => rfl
    | svar i => exact absurd rfl (hc i)
  · rfl

theorem evalCls_ncons (θ : Nat → Sk) (c : ClsV) (Δ : Nat → ClsV) :
    evalCls θ ∘ ncons c Δ = ncons (evalCls θ c) (evalCls θ ∘ Δ) := by
  funext n; cases n <;> rfl

/-! ### The coc image of a `cocTop` expression -/

/-- `∗ ↦ ∗`; `□, Δ ↦ □`. -/
def srtC : Srt3 → LambdaPi.Srt
  | .star => .star
  | _ => .box


/-- **The coc classifier of the image is the evaluated classifier** (well-classified
expressions). -/
theorem cl_toC (θ : Nat → Sk) (M : Expr Srt3) :
    ∀ (Δ : Nat → ClsV), WCV Δ M → cl (evalCls θ ∘ Δ) (M.mapSort srtC) = evalCls θ (clV Δ M) := by
  induction M with
  | var n => intro Δ _; rfl
  | sort s => intro Δ _; cases s <;> rfl
  | app F U ihF _ =>
      intro Δ h
      simp only [Expr.mapSort, cl] at ihF ⊢
      rw [ihF Δ h.2.1, clV, evalCls_appV θ _ h.1]
  | lam A b ihA ihb =>
      intro Δ h
      simp only [Expr.mapSort, cl] at ihA ihb ⊢
      rw [ihA Δ h.1, ← evalCls_bindV, ← evalCls_ncons, ihb _ h.2, clV, evalCls_lamV]
  | pi A B ihA ihB =>
      intro Δ h
      simp only [Expr.mapSort, cl] at ihA ihB ⊢
      rw [ihA Δ h.1, ← evalCls_bindV, ← evalCls_ncons, ihB _ h.2, clV, evalCls_piV]

/-! ### The interpretation relative to `θ` -/

variable {B : Type} (𝔄 : KAlg B)

/-- **The interpretation of `cocTop` kinds and constructors relative to `θ`.** -/
def interpV (θ : Nat → Sk) (Δ : Nat → ClsV) (M : Expr Srt3) (k : Sk) (ξ : ValK B) : V B k :=
  interpK 𝔄 (evalCls θ ∘ Δ) (M.mapSort srtC) k ξ

/-- The valuation induced by a substitution of `cocTop` expressions. -/
def substValV (θ : Nat → Sk) (Δ : Nat → ClsV) (σ : Nat → Expr Srt3) (ξ : ValK B) : ValK B :=
  fun n k => interpV 𝔄 θ Δ (σ n) k ξ

theorem interpV_rename (θ : Nat → Sk) (M : Expr Srt3) (Δ : Nat → ClsV) (ρ : Nat → Nat) (k : Sk)
    (ξ : ValK B) : interpV 𝔄 θ Δ (M.rename ρ) k ξ = interpV 𝔄 θ (Δ ∘ ρ) M k (ξ ∘ ρ) := by
  simp only [interpV, Expr.mapSort_rename, ErasureCoC.interpK_rename]
  rfl

/-- **The substitution lemma for `interpV`**, for every substitution respecting the evaluated
classes; source and target may use different skeleton valuations `θ'` and `θ`. -/
theorem interpV_subst (M : Expr Srt3) {θ θ' : Nat → Sk} {Δ Δ' : Nat → ClsV}
    {σ : Nat → Expr Srt3} (hσ : ∀ n, cl (evalCls θ ∘ Δ) (((σ n).mapSort srtC)) = evalCls θ' (Δ' n))
    (k : Sk) (ξ : ValK B) :
    interpV 𝔄 θ Δ (M.subst σ) k ξ = interpV 𝔄 θ' Δ' M k (substValV 𝔄 θ Δ σ ξ) := by
  simp only [interpV, Expr.mapSort_subst]
  exact ErasureCoC.interpK_subst 𝔄 (M.mapSort srtC) (Δ' := evalCls θ' ∘ Δ') (fun n => hσ n) k ξ

/-- The side condition of `interpV_subst` for well-classified substituends. -/
theorem interpV_subst_cond {θ θ' : Nat → Sk} {Δ Δ' : Nat → ClsV} {σ : Nat → Expr Srt3}
    (hw : ∀ n, WCV Δ (σ n)) (hσ : ∀ n, evalCls θ (clV Δ (σ n)) = evalCls θ' (Δ' n)) :
    ∀ n, cl (evalCls θ ∘ Δ) (((σ n).mapSort srtC)) = evalCls θ' (Δ' n) := fun n => by
  rw [cl_toC θ _ Δ (hw n), hσ n]

/-- **The new case: a kind substituted for a kind variable.**  For a variable of class
`kind (svar ℓ)` and a well-classified substituend `N` of class `kind a`, the side condition of
`interpV_subst` is exactly that the source valuation `θ'` assigns to `ℓ` the evaluated skeleton
of `N`: `θ'` extends `θ` by the skeleton of `N`. -/
theorem interpV_kindVar_cond {θ θ' : Nat → Sk} {Δ : Nat → ClsV} {N : Expr Srt3} {a : SkV}
    {ℓ : Nat} (hN : WCV Δ N) (ha : clV Δ N = .kind a) :
    cl (evalCls θ ∘ Δ) (N.mapSort srtC) = evalCls θ' (.kind (.svar ℓ)) ↔ θ' ℓ = evalSk θ a := by
  rw [cl_toC θ N Δ hN, ha]
  simp only [evalCls, evalSk, Cls.kind.injEq]
  exact eq_comm

/-- The substitution lemma in the kind-variable form: substituting well-classified expressions
whose (evaluated) classes match, with kind variables sent to kinds of the skeleton `θ'` gives
them. -/
theorem interpV_subst_kind (M : Expr Srt3) {θ θ' : Nat → Sk} {Δ Δ' : Nat → ClsV}
    {σ : Nat → Expr Srt3} (hw : ∀ n, WCV Δ (σ n))
    (hσ : ∀ n, evalCls θ (clV Δ (σ n)) = evalCls θ' (Δ' n)) (k : Sk) (ξ : ValK B) :
    interpV 𝔄 θ Δ (M.subst σ) k ξ = interpV 𝔄 θ' Δ' M k (substValV 𝔄 θ Δ σ ξ) :=
  interpV_subst 𝔄 M (interpV_subst_cond hw hσ) k ξ

theorem substValV_single (θ : Nat → Sk) (Δ : Nat → ClsV) (U : Expr Srt3) (ξ : ValK B) :
    substValV 𝔄 θ Δ (Expr.single U) ξ = ncons (fun k => interpV 𝔄 θ Δ U k ξ) ξ := by
  funext n k
  cases n <;> rfl

/-- **Instantiation**: `⟦b[U/x]⟧ξ = ⟦b⟧(ξ, ⟦U⟧ξ)` for well-classified `U`. -/
theorem interpV_instantiate (b U : Expr Srt3) (θ : Nat → Sk) (Δ : Nat → ClsV) (hU : WCV Δ U)
    (k : Sk) (ξ : ValK B) :
    interpV 𝔄 θ Δ (b.instantiate U) k ξ =
      interpV 𝔄 θ (ncons (clV Δ U) Δ) b k (ncons (fun k => interpV 𝔄 θ Δ U k ξ) ξ) := by
  rw [Expr.instantiate, interpV_subst_kind 𝔄 b (θ' := θ) (Δ' := ncons (clV Δ U) Δ)
    (fun n => by cases n <;> first | exact hU | trivial) (fun n => by cases n <;> rfl),
    substValV_single]

/-! ### Well-classification of the coc image -/

open CoC (WC PiOK AppOK)

theorem piOK_evalCls_of_sorted (θ : Nat → Sk) {Γ : List (Expr Srt3)} {A : Expr Srt3} {s : Srt3}
    (h : HasType cocTop Γ A (.sort s)) (hs : s ≠ .top) :
    PiOK (evalCls θ (clV (ctxClV Γ) A)) := by
  cases s with
  | top => exact absurd rfl hs
  | box =>
      obtain ⟨k, hk⟩ := kindV_cl h
      exact .inr ⟨evalSk θ k, by rw [hk]; rfl⟩
  | star =>
      left
      rw [classifyFull h (by intro h; cases h) (by intro h; cases h)]
      rfl

theorem appOK_evalCls (θ : Nat → Sk) (cA cB : ClsV) :
    AppOK (evalCls θ (bindV (piV cA cB))) (evalCls θ (bindV cA)) := by
  cases cB with
  | kind k => cases cA <;> rfl
  | constr => trivial
  | obj => trivial

/-- **The coc image of a `cocTop`-typable expression is well classified** in the evaluated
context classifier, for every closed skeleton valuation. -/
theorem wc_toC (θ : Nat → Sk) {Γ : List (Expr Srt3)} {M T : Expr Srt3}
    (h : HasType cocTop Γ M T) : WC (evalCls θ ∘ ctxClV Γ) (M.mapSort srtC) := by
  induction M generalizing Γ T with
  | var n => trivial
  | sort s => trivial
  | app F U ihF ihU =>
      obtain ⟨A, B, hF, hU, -⟩ := h.generation_app
      obtain ⟨s, hPi⟩ := hF.product_type_sorted
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, -⟩ := hPi.generation_pi
      refine ⟨ihF hF, ihU hU, ?_⟩
      rw [cl_toC θ F _ (wcv_of_hasType hF), cl_toC θ U _ (wcv_of_hasType hU),
        classifyFull hF (by intro h; cases h) (by intro h; cases h),
        classifyFull hU (ne_box_of_sorted hA (rule_dom hr)) (fun e => top_untypable (e ▸ hA))]
      exact appOK_evalCls θ _ _
  | lam A b ihA ihb =>
      obtain ⟨B, s, hb, hPi, -⟩ := h.generation_lam
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, -⟩ := hPi.generation_pi
      have hb' := ihb hb
      rw [ctxClV_cons_of_ne (ne_box_of_sorted hA (rule_dom hr)), evalCls_ncons, evalCls_bindV,
        ← cl_toC θ A _ (wcv_of_hasType hA)] at hb'
      exact ⟨ihA hA, hb'⟩
  | pi A B ihA ihB =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, -⟩ := h.generation_pi
      have hB' := ihB hB
      have hpB := piOK_evalCls_of_sorted θ hB (rule_cod hr)
      have hBw := wcv_of_hasType hB
      rw [ctxClV_cons_of_ne (ne_box_of_sorted hA (rule_dom hr))] at hB' hpB hBw
      rw [evalCls_ncons, evalCls_bindV, ← cl_toC θ A _ (wcv_of_hasType hA)] at hB'
      refine ⟨ihA hA, hB', ?_, ?_⟩
      · show PiOK (cl _ (A.mapSort srtC))
        rw [cl_toC θ A _ (wcv_of_hasType hA)]
        exact piOK_evalCls_of_sorted θ hA (rule_dom hr)
      · have e := cl_toC θ B _ hBw
        rw [evalCls_ncons, evalCls_bindV, ← cl_toC θ A _ (wcv_of_hasType hA)] at e
        show PiOK (cl _ (B.mapSort srtC))
        rw [e]; exact hpB

end PureTypeSystem.TopSkel
