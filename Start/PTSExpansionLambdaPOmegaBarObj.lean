/-
**Toward expansion postponement for λPω̲ (M29-EP-CUBE-REST): object-level hereditary
substitution.**

Step 2 of the plan for λPω̲.

* `Expr.Vis M k`: the variable `k` occurs at a position that the erasure looks at (the head of an
  application, the body of an abstraction, either part of a product).
* `erase_isKindB_reduces_subst`: if `X` is normal and `k` is not visible in `X`, every reduct of
  `X[k := N]` has the erasure and the kind shape of `X`, for every `N` (purely syntactic).
* `not_vis_of_typed` (λPω̲): an object variable is never visible in a constructor, a kind or a type
  (objects never occur at the head of a constructor).  So object substitution never changes the
  erasure of a normal type.
* `HasTypeNW.head_lookup_obj`: the type of a spine headed by an object variable is a codomain of
  the type of the variable, up to erasure.
* `HasTypeNW.hsubst_obj`: **object-level hereditary substitution** for the canonical λPω̲
  judgement, by induction on the erasure of the type of the substituted object variable.
-/

import Start.PTSExpansionLambdaPOmegaBarCanon

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

universe u

namespace Expr

variable {S : Type u}

/-- The variable `k` is visible: it is reached from the root through heads of applications,
bodies of abstractions and parts of products. -/
def Vis : Expr S → Nat → Prop
  | var n, k => n = k
  | sort _, _ => False
  | app F _, k => Vis F k
  | lam _ b, k => Vis b (k + 1)
  | pi A B, k => Vis A k ∨ Vis B (k + 1)

theorem vis_of_headVar : ∀ (F : Expr S) (k : Nat), F.headVar = some k → F.Vis k
  | var n, k, h => by simpa [headVar, Vis] using h
  | app F _, k, h => vis_of_headVar F k h
  | sort _, _, h => by cases h
  | lam _ _, _, h => by cases h
  | pi _ _, _, h => by cases h

end Expr

theorem Reduces.lam_inv {S : Type u} {A b N : Expr S} (h : Reduces (.lam A b) N) :
    ∃ A' b', N = .lam A' b' ∧ Reduces A A' ∧ Reduces b b' := by
  induction h with
  | refl => exact ⟨A, b, rfl, .refl, .refl⟩
  | tail _ h ih =>
      obtain ⟨A', b', rfl, hA, hb⟩ := ih
      cases h with
      | lam_domain h => exact ⟨_, _, rfl, hA.tail h, hb⟩
      | lam_body h => exact ⟨_, _, rfl, hA, hb.tail h⟩

/-- **Invisible substitution preserves the erasure and the kind shape.**  If `X` is normal and
`k` is not visible in `X`, every reduct of `X[k := N]` has the erasure and the kind shape of
`X`. -/
theorem erase_isKindB_reduces_subst {S : Type u} (N : Expr S) :
    ∀ (X : Expr S) (k : Nat), Normal X → ¬ X.Vis k →
      ∀ Y, Reduces (X.subst (Expr.substAt N k)) Y → Y.erase = X.erase ∧ Y.isKindB = X.isKindB := by
  intro X
  induction X with
  | var n =>
      intro k _ hk Y hY
      obtain ⟨m, hm⟩ := Expr.substAt_ne N k n hk
      have hY' : Reduces (Expr.var m) Y := by simpa only [Expr.subst, hm] using hY
      rw [← (Normal.var m).reduces_eq hY']
      exact ⟨rfl, rfl⟩
  | sort s =>
      intro k _ _ Y hY
      rw [Reduces.sort_eq hY]
      exact ⟨rfl, rfl⟩
  | app f a ihf _ =>
      intro k hn hk Y hY
      have hne : f.headVar ≠ some k := fun h => hk (Expr.vis_of_headVar f k h)
      have hf := subst_noLam N k f hn.app_left hn.app_not_lam hne
      obtain ⟨X', b', rfl, hX'⟩ := Reduces.app_inv_of_noLam hf hY
      exact ⟨(ihf k hn.app_left hk X' hX').1, rfl⟩
  | lam A b _ ihb =>
      intro k hn hk Y hY
      obtain ⟨A', b', rfl, _, hb⟩ := Reduces.lam_inv hY
      rw [← Expr.substAt_succ] at hb
      exact ⟨(ihb (k + 1) hn.lam_body hk b' hb).1, rfl⟩
  | pi A B ihA ihB =>
      intro k hn hk Y hY
      simp only [Expr.Vis, not_or] at hk
      obtain ⟨A', B', rfl, hA, hB⟩ := Reduces.pi_inv hY
      rw [← Expr.substAt_succ] at hB
      have h1 := ihA k hn.pi_domain hk.1 A' hA
      have h2 := ihB (k + 1) hn.pi_body hk.2 B' hB
      exact ⟨by simp only [Expr.erase, h1.1, h2.1], by simp only [Expr.isKindB, h2.2]⟩

/-! ### Typing facts for λPω̲ -/

open LambdaPi (Srt)

/-- The λPω̲ specification. -/
abbrev PWbar : Specification Srt := cubeSpec lambdaPOmegaBar

/-- `x` is an object variable of `Θ`: its declared type is not a syntactic kind. -/
def ObjVar (Θ : List (Expr Srt)) (x : Nat) : Prop :=
  ∀ U, Lookup Θ x U → U.isKindB = false

theorem ObjVar.cons {Θ : List (Expr Srt)} {x : Nat} (h : ObjVar Θ x) (A : Expr Srt) :
    ObjVar (A :: Θ) (x + 1) := by
  intro U hU
  cases hU with
  | succ _ hU => rw [Expr.isKindB_rename]; exact h _ hU

theorem ObjVar.of_cons {Θ : List (Expr Srt)} {x : Nat} {A : Expr Srt}
    (h : ObjVar (A :: Θ) (x + 1)) : ObjVar Θ x := by
  intro U hU
  have := h _ (.succ A hU)
  rwa [Expr.isKindB_rename] at this

theorem objVar_zero {Θ : List (Expr Srt)} {A : Expr Srt} (hA : A.isKindB = false) :
    ObjVar (A :: Θ) 0 := by
  intro U hU
  cases hU
  rw [Expr.isKindB_rename]; exact hA

/-- Whatever has type `□` is a syntactic kind. -/
theorem isKindB_of_box {f : CubeFeatures} :
    ∀ {Γ : List (Expr Srt)} {U : Expr Srt}, HasType (cubeSpec f) Γ U (.sort .box) →
      U.isKindB = true := by
  intro Γ U h
  induction U generalizing Γ with
  | var n =>
      obtain ⟨D, hD, hc⟩ := h.generation
      obtain ⟨s, hs⟩ := lookup_sorted h.valid hD
      exact (CoC.not_conv_box hs (.symm _ _ hc)).elim
  | sort s => rfl
  | app F a _ _ =>
      obtain ⟨s, hs⟩ := h.application_type_sorted
      exact (not_hasType_box f hs).elim
  | lam A b _ _ =>
      obtain ⟨s, hs⟩ := h.abstraction_type_sorted
      exact (not_hasType_box f hs).elim
  | pi A B _ ihB =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := h.generation_pi
      have h₃ : s₃ = .box := (Converts.sort_inj hc).symm
      rw [hr.1] at h₃
      subst h₃
      exact ihB hB

/-- A syntactic kind that is sorted has sort `□`. -/
theorem box_of_isKindB {f : CubeFeatures} :
    ∀ {Γ : List (Expr Srt)} {K : Expr Srt} {s : Srt}, HasType (cubeSpec f) Γ K (.sort s) →
      K.isKindB = true → s = .box := by
  intro Γ K s h hK
  induction K generalizing Γ s with
  | var n => simp [Expr.isKindB] at hK
  | app F a _ _ => simp [Expr.isKindB] at hK
  | lam A b _ _ => simp [Expr.isKindB] at hK
  | sort t =>
      obtain ⟨t', ⟨rfl, rfl⟩, hc⟩ := h.generation
      exact Converts.sort_inj hc
  | pi A B _ ihB =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := h.generation_pi
      have h₂ := ihB hB hK
      rw [Converts.sort_inj hc, hr.1, h₂]

/-- The sort of a sorted expression that is not a syntactic kind is `∗`. -/
theorem star_of_not_isKindB {f : CubeFeatures} {Γ : List (Expr Srt)} {U : Expr Srt} {s : Srt}
    (h : HasType (cubeSpec f) Γ U (.sort s)) (hU : U.isKindB = false) : s = .star := by
  cases s with
  | star => rfl
  | box => rw [isKindB_of_box h] at hU; cases hU

theorem not_isKindB_of_star {f : CubeFeatures} {Γ : List (Expr Srt)} {U : Expr Srt}
    (h : HasType (cubeSpec f) Γ U (.sort .star)) : U.isKindB = false := by
  cases hU : U.isKindB with
  | false => rfl
  | true => cases box_of_isKindB h hU

/-- **An object variable is invisible in kinds and constructors** (λPω̲). -/
theorem not_vis_of_typed :
    ∀ (M : Expr Srt) {Θ : List (Expr Srt)} {k : Nat} {T : Expr Srt},
      HasType PWbar Θ M T → ObjVar Θ k →
      (T = .sort .box ∨ HasType PWbar Θ T (.sort .box)) → ¬ M.Vis k := by
  intro M
  induction M with
  | var n =>
      intro Θ k T h hobj hT hvis
      simp only [Expr.Vis] at hvis
      subst hvis
      obtain ⟨D, hD, hc⟩ := h.generation
      obtain ⟨s, hs⟩ := lookup_sorted h.valid hD
      have hstar := star_of_not_isKindB hs (hobj D hD)
      subst hstar
      rcases hT with rfl | hT
      · exact CoC.not_conv_box hs (.symm _ _ hc)
      · cases CoC.sort_unique_conv hT hs hc
  | sort s => intro _ _ _ _ _ _ hvis; exact hvis
  | app F a ihF _ =>
      intro Θ k T h hobj hT hvis
      obtain ⟨C, D, hF, ha, hc⟩ := h.generation_app
      rcases CoC.type_sorted hF with heq | ⟨s, hs⟩
      · cases heq
      obtain ⟨s₁, s₂, s₃, hC, hD, hr, hc'⟩ := hs.generation_pi
      have hDa := hD.instantiate ha
      have hs₂ : s₂ = .box := by
        rcases hT with rfl | hT
        · exact (CoC.not_conv_box hDa (.symm _ _ hc)).elim
        · exact (CoC.sort_unique_conv hT hDa hc).symm
      have hs' : s = .box := by rw [Converts.sort_inj hc', hr.1, hs₂]
      subst hs'
      exact ihF hF hobj (.inr hs) hvis
  | lam A b _ ihb =>
      intro Θ k T h hobj hT hvis
      obtain ⟨B, s, hb, hPi, hc⟩ := h.generation_lam
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc'⟩ := hPi.generation_pi
      have hs₂ : s₂ = .box := by
        cases s₂ with
        | box => rfl
        | star =>
            have hs : s = .star := by rw [Converts.sort_inj hc', hr.1]
            subst hs
            rcases hT with rfl | hT
            · exact (CoC.not_conv_box hPi (.symm _ _ hc)).elim
            · cases CoC.sort_unique_conv hT hPi hc
      subst hs₂
      exact ihb hb (hobj.cons A) (.inr hB) hvis
  | pi A B ihA ihB =>
      intro Θ k T h hobj hT hvis
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, _⟩ := h.generation_pi
      have hsort : ∀ {Θ' : List (Expr Srt)} {X : Expr Srt} {t : Srt},
          HasType PWbar Θ' X (.sort t) →
            ((Expr.sort t : Expr Srt) = .sort .box ∨
              HasType PWbar Θ' (.sort t) (.sort .box)) := by
        intro Θ' X t hX
        cases t with
        | box => exact .inl rfl
        | star => exact .inr (cube_star_box _ hX.valid)
      rcases hvis with hv | hv
      · exact ihA hA hobj (hsort hA) hv
      · exact ihB hB (hobj.cons A) (hsort hB) hv

/-- An object variable is invisible in every type of a judgement. -/
theorem not_vis_type {Θ : List (Expr Srt)} {k : Nat} {M T : Expr Srt}
    (h : HasType PWbar Θ M T) (hobj : ObjVar Θ k) : ¬ T.Vis k := by
  rcases CoC.type_sorted h with rfl | ⟨s, hs⟩
  · intro hv; exact hv
  · cases s with
    | box => exact not_vis_of_typed T hs hobj (.inl rfl)
    | star => exact not_vis_of_typed T hs hobj (.inr (cube_star_box _ hs.valid))

/-- An object variable is invisible in every sorted expression. -/
theorem not_vis_sorted {Θ : List (Expr Srt)} {k : Nat} {X : Expr Srt} {s : Srt}
    (h : HasType PWbar Θ X (.sort s)) (hobj : ObjVar Θ k) : ¬ X.Vis k := by
  cases s with
  | box => exact not_vis_of_typed X h hobj (.inl rfl)
  | star => exact not_vis_of_typed X h hobj (.inr (cube_star_box _ h.valid))

/-! ### Object-level hereditary substitution -/

theorem lookup_append_isKindB :
    ∀ (Δ : List (Expr Srt)) {A : Expr Srt} {Γ : List (Expr Srt)} {U : Expr Srt},
      Lookup (Δ ++ A :: Γ) Δ.length U → U.isKindB = A.isKindB
  | [], A, Γ, U, h => by
      cases h
      exact Expr.isKindB_rename _ _
  | D :: Δ, A, Γ, U, h => by
      simp only [List.cons_append, List.length_cons] at h
      cases h with
      | succ _ h => rw [Expr.isKindB_rename]; exact lookup_append_isKindB Δ h

theorem objVar_append (Δ : List (Expr Srt)) {A : Expr Srt} {Γ : List (Expr Srt)}
    (hA : A.isKindB = false) : ObjVar (Δ ++ A :: Γ) Δ.length := by
  intro U hU
  rw [lookup_append_isKindB Δ hU]
  exact hA

namespace HasTypeNW

/-- **Spines headed by an object variable.**  Their type is a type, and its erasure is a
codomain of the erasure of the type of the head. -/
theorem head_lookup_obj {Θ : List (Expr Srt)} {F T : Expr Srt} (h : HasTypeNW PWbar Θ F T) :
    ∀ x, F.headVar = some x → ObjVar Θ x →
      ∃ U, Lookup Θ x U ∧ STy.ArrSuffix T.erase U.erase ∧ HasType PWbar Θ T (.sort .star) := by
  induction h with
  | ax _ => intro x hx; cases hx
  | @var Γ A s hA _ =>
      intro x hx hobj
      cases hx
      have hAk : A.isKindB = false := by
        have := hobj _ (.zero A Γ)
        rwa [Expr.isKindB_rename] at this
      have hA' := hA.toHasType
      have hs := star_of_not_isKindB hA' hAk
      subst hs
      exact ⟨_, .zero _ _, .refl _, .weaken hA' hA'⟩
  | @weaken Γ M B A s hM hA ihM _ =>
      intro x hx hobj
      rw [Expr.headVar_rename] at hx
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
      obtain ⟨U, hU, hs, hB⟩ := ihM y hy hobj.of_cons
      exact ⟨_, .succ A hU, by rw [Expr.erase_rename, Expr.erase_rename]; exact hs,
        .weaken hB hA.toHasType⟩
  | product => intro x hx; cases hx
  | abstraction => intro x hx; cases hx
  | @application Γ F a C D B' hF ha hr _ _ ihF _ =>
      intro x hx hobj
      obtain ⟨U, hU, hs, hPi⟩ := ihF x hx hobj
      obtain ⟨s₁, s₂, s₃, hC, hD, hrr, hcc⟩ := hPi.generation_pi
      have hs₂ : s₂ = .star := by rw [← hrr.1]; exact (Converts.sort_inj hcc).symm
      subst hs₂
      have hs₁ : s₁ = .star := by
        have hal := hrr.2
        cases s₁ with
        | star => rfl
        | box => simp [CubeFeatures.allows, lambdaPOmegaBar] at hal
      subst hs₁
      have hDn : Normal D := hF.normal.2.1.pi_body
      have hvis : ¬ D.Vis 0 := not_vis_sorted hD (objVar_zero (not_isKindB_of_star hC))
      have he := (erase_isKindB_reduces_subst a D 0 hDn hvis B' hr).1
      refine ⟨U, hU, by rw [he]; exact .cod hs, ?_⟩
      have hDa := hD.instantiate ha.toHasType
      exact hDa.subject_reduces hr

theorem hsubst_obj_aux (n : Nat) :
    ∀ (A : Expr Srt), A.erase.size = n → A.isKindB = false → ∀ (Γ : List (Expr Srt))
      (N : Expr Srt), HasTypeNW PWbar Γ N A →
      ∀ Θ M B, HasTypeNW PWbar Θ M B → ∀ Δ, Θ = Δ ++ A :: Γ →
        ∃ Δ' M' B', CtxSubstRed N Δ Δ' ∧ Reduces (M.subst (Expr.substAt N Δ.length)) M' ∧
          Reduces (B.subst (Expr.substAt N Δ.length)) B' ∧ HasTypeNW PWbar (Δ' ++ Γ) M' B' := by
  have hw : SystemWeaklyNormalizing PWbar := fun Γ hΓ M hM =>
    weaklyNormalizing_of_stronglyNormalizing (cube_stronglyNormalizing _ Γ hΓ M hM)
  induction n using Nat.strong_induction_on with
  | _ n IHn =>
  intro A hAn hAk Γ N hN Θ M B h
  have ctxn : ∀ {Δ' : List (Expr Srt)} {M' B' : Expr Srt}, HasTypeNW PWbar (Δ' ++ Γ) M' B' →
      ∀ X ∈ Δ', Normal X := fun h X hX => h.normal.2.2 X (List.mem_append_left _ hX)
  induction h with
  | ax _ => intro Δ heq; cases Δ <;> simp at heq
  | @var Θ₀ A₀ s hA₀ ih =>
      intro Δ heq
      cases Δ with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          refine ⟨[], N, A₀, .nil, ?_, ?_, hN⟩
          · exact .refl
          · simp only [List.length_nil, Expr.substAt_zero, Expr.subst_lift_single]
            exact .refl
      | cons D Δ₀ =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          obtain ⟨Δ', D', T', hc, hD, hT, hD'⟩ := ih Δ₀ rfl
          simp only [Expr.subst] at hT
          rw [Reduces.sort_eq hT] at hD'
          refine ⟨D' :: Δ', .var 0, D'.rename Nat.succ, .cons hc hD, ?_, ?_, .var hD'⟩
          · simp only [List.length_cons, Expr.substAt_succ]
            exact .refl
          · simp only [List.length_cons, Expr.substAt_succ, Expr.rename_succ_subst_lift]
            exact hD.rename _
  | @weaken Θ₀ M₀ B₀ A₀ s hM hA ihM ihA =>
      intro Δ heq
      cases Δ with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          refine ⟨[], M₀, B₀, .nil, ?_, ?_, hM⟩ <;>
            simp only [List.length_nil, Expr.substAt_zero, Expr.subst_lift_single] <;> exact .refl
      | cons D Δ₀ =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          obtain ⟨Δ₁, M', B', hc₁, hMr, hBr, hM'⟩ := ihM Δ₀ rfl
          obtain ⟨Δ₂, D', T', hc₂, hD, hT, hD'⟩ := ihA Δ₀ rfl
          simp only [Expr.subst] at hT
          rw [Reduces.sort_eq hT] at hD'
          obtain rfl := hc₁.unique hc₂ (ctxn hM') (ctxn hD')
          refine ⟨D' :: Δ₁, M'.rename Nat.succ, B'.rename Nat.succ, .cons hc₁ hD, ?_, ?_,
            .weaken hM' hD'⟩ <;>
            simp only [List.length_cons, Expr.substAt_succ, Expr.rename_succ_subst_lift]
          · exact hMr.rename _
          · exact hBr.rename _
  | @product Θ C E s₁ s₂ s₃ hC hE hr ihC ihE =>
      intro Δ heq
      obtain ⟨Δ₁, C', T₁, hc₁, hCr, hT₁, hC'⟩ := ihC Δ heq
      obtain ⟨Δ₂, E', T₂, hc₂, hEr, hT₂, hE'⟩ := ihE (C :: Δ) (by rw [heq]; rfl)
      simp only [Expr.subst] at hT₁
      rw [Reduces.sort_eq hT₁] at hC'
      simp only [Expr.subst] at hT₂
      rw [Reduces.sort_eq hT₂] at hE'
      cases hc₂ with
      | @cons _ Δ₂' _ C'' hc₂ hC'' =>
          have hn := hE'.normal.2.2
          obtain rfl : C'' = C' := Reduces.normal_unique hC'' hCr
            (hn _ (List.mem_cons_self ..)) hC'.normal.1
          obtain rfl := hc₂.unique hc₁ (fun X hX => hn X (by simp [hX])) (ctxn hC')
          refine ⟨Δ₂', .pi C'' E', .sort s₃, hc₁, ?_, .refl, .product hC' hE' hr⟩
          simp only [Expr.subst, ← Expr.substAt_succ]
          exact Reduces.pi hCr hEr
  | @abstraction Θ C b E s hb hP ihb ihP =>
      intro Δ heq
      obtain ⟨Δ₂, b', E', hc₂, hbr, hEr, hb'⟩ := ihb (C :: Δ) (by rw [heq]; rfl)
      obtain ⟨Δ₁, X, T₁, hc₁, hXr, hT₁, hX⟩ := ihP Δ heq
      simp only [Expr.subst] at hT₁
      rw [Reduces.sort_eq hT₁] at hX
      simp only [Expr.subst] at hXr
      obtain ⟨C₁, E₁, rfl, hC₁, hE₁⟩ := Reduces.pi_inv hXr
      cases hc₂ with
      | @cons _ Δ₂' _ C'' hc₂ hC'' =>
          have hn := hb'.normal
          have hXn := hX.normal.1
          obtain rfl : C'' = C₁ := Reduces.normal_unique hC'' hC₁
            (hn.2.2 _ (List.mem_cons_self ..)) hXn.pi_domain
          rw [← Expr.substAt_succ] at hE₁
          obtain rfl : E' = E₁ := Reduces.normal_unique hEr hE₁ hn.2.1 hXn.pi_body
          obtain rfl := hc₂.unique hc₁ (fun X hX => hn.2.2 X (by simp [hX])) (ctxn hX)
          refine ⟨Δ₂', .lam C'' b', .pi C'' E', hc₁, ?_, ?_, .abstraction hb' hX⟩
          · simp only [Expr.subst, ← Expr.substAt_succ]
            exact Reduces.lam hC'' hbr
          · simp only [Expr.subst, ← Expr.substAt_succ]
            exact Reduces.pi hC'' hE₁
  | @application Θ F a C D B₀ hF ha hr hB₀ happ ihF iha =>
      intro Δ heq
      obtain ⟨Δ₁, F', T', hc₁, hFr, hTr, hF'⟩ := ihF Δ heq
      simp only [Expr.subst] at hTr
      obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Reduces.pi_inv hTr
      obtain ⟨Δ₂, a', C', hc₂, har, hCr, ha'⟩ := iha Δ heq
      obtain rfl : C' = A₁ := Reduces.normal_unique hCr hA₁ ha'.normal.2.1
        hF'.normal.2.1.pi_domain
      obtain rfl := hc₂.unique hc₁ (ctxn ha') (ctxn hF')
      set σ := Expr.substAt N Δ.length with hσdef
      have hTy : Reduces ((D.instantiate a).subst σ) (B₁.instantiate a') := by
        rw [← Expr.instantiate_subst]
        exact Reduces.instantiate hB₁ har
      have hB₀σ : Reduces ((D.instantiate a).subst σ) (B₀.subst σ) := hr.subst σ
      by_cases hlam : ∃ C₀ e, F' = .lam C₀ e
      · obtain ⟨C₀, e, rfl⟩ := hlam
        obtain ⟨E₀, s, heqT, he, hPi'⟩ := hF'.lam_inv _ _ rfl
        obtain ⟨rfl, rfl⟩ := Expr.pi.inj heqT
        have hhead : F.headVar = some Δ.length := by
          by_contra hne
          exact subst_noLam N Δ.length F happ.app_left happ.app_not_lam hne _ hFr C' e rfl
        have hobjΘ : ObjVar Θ Δ.length := by rw [heq]; exact objVar_append Δ hAk
        obtain ⟨U, hU, hs, hPiS⟩ := hF.head_lookup_obj _ hhead hobjΘ
        rw [heq] at hU
        have hUA := lookup_append_erase Δ hU
        obtain ⟨s₁, s₂, s₃, hCt, hDt, hrr, hcc⟩ := hPiS.generation_pi
        have hs₂ : s₂ = .star := by rw [← hrr.1]; exact (Converts.sort_inj hcc).symm
        subst hs₂
        have hCn : Normal C := hF.normal.2.1.pi_domain
        have hDn : Normal D := hF.normal.2.1.pi_body
        have hCe := (erase_isKindB_reduces_subst N C Δ.length hCn
          (not_vis_sorted hCt hobjΘ) C' hA₁).1
        have hlt : C'.erase.size < n := by
          rw [hCe, ← hAn, ← hUA]
          exact hs.dom_lt
        have hB₁' : Reduces (D.subst (Expr.substAt N (Δ.length + 1))) B₁ := by
          rw [Expr.substAt_succ]; exact hB₁
        have hB₁k : B₁.isKindB = false := by
          rw [(erase_isKindB_reduces_subst N D (Δ.length + 1) hDn
            (not_vis_sorted hDt (hobjΘ.cons C)) B₁ hB₁').2]
          exact not_isKindB_of_star hDt
        have hC'k : C'.isKindB = false := by
          cases hk : C'.isKindB with
          | false => rfl
          | true =>
              obtain ⟨t₁, t₂, t₃, hC't, hB₁t, hr', _⟩ := hPi'.toHasType.generation_pi
              have ht₁ := box_of_isKindB hC't hk
              subst ht₁
              have hal := hr'.2
              cases t₂ with
              | star => simp [CubeFeatures.allows, lambdaPOmegaBar] at hal
              | box => rw [isKindB_of_box hB₁t] at hB₁k; cases hB₁k
        obtain ⟨Δ', e', E', hc', her, hEr, he'⟩ :=
          IHn _ hlt C' rfl hC'k (Δ₂ ++ Γ) a' ha' _ e B₁ he ([]) rfl
        cases hc'
        simp only [List.length_nil, Expr.substAt_zero, List.nil_append] at her hEr he'
        refine ⟨Δ₂, e', E', hc₁, ?_, ?_, he'⟩
        · simp only [Expr.subst]
          exact ((Reduces.app hFr har).tail (Beta.head C' e a')).trans her
        · exact Reduces.to_normal hB₀σ (hTy.trans hEr) he'.normal.2.1
      · simp only [not_exists] at hlam
        have happ' : Normal (.app F' a') :=
          Normal.app_of hF'.normal.1 ha'.normal.1 hlam
        have hT : HasType PWbar (Δ₂ ++ Γ) (.app F' a') (B₁.instantiate a') :=
          .application hF'.toHasType ha'.toHasType
        obtain ⟨B'', hred, hnorm⟩ := hw _ hT.valid _ ⟨_, .inr hT⟩
        refine ⟨Δ₂, .app F' a', B'', hc₁, ?_, ?_, .application hF' ha' hred hnorm happ'⟩
        · simp only [Expr.subst]
          exact Reduces.app hFr har
        · exact Reduces.to_normal hB₀σ (hTy.trans hred) hnorm

/-- **Object-level hereditary substitution** for the canonical λPω̲ judgement: substituting a
canonical object `N : A` (`A` a type) into a canonical derivation yields, after normalization, a
canonical derivation. -/
theorem hsubst_obj {Γ : List (Expr Srt)} {N A M B : Expr Srt} (hAk : A.isKindB = false)
    (hN : HasTypeNW PWbar Γ N A) (hM : HasTypeNW PWbar (A :: Γ) M B) :
    ∃ M' B', Reduces (M.instantiate N) M' ∧ Reduces (B.instantiate N) B' ∧
      HasTypeNW PWbar Γ M' B' := by
  obtain ⟨Δ', M', B', hc, hM', hB', h⟩ :=
    hsubst_obj_aux _ A rfl hAk Γ N hN _ M B hM ([]) rfl
  cases hc
  exact ⟨M', B', hM', hB', h⟩

end HasTypeNW

end PureTypeSystem
