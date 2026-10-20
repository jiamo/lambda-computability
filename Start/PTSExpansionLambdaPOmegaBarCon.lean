/-
**Expansion postponement for λPω̲ (M29-EP-CUBE-REST): constructor-level hereditary
substitution.**

Step 3 of the plan for λPω̲.

* `Expr.NoKindVal`, `isKindB_subst'`, `skelK_subst'`: the kind shape and the kind skeleton are
  invariant under every substitution whose values are not syntactic kinds.
* `conv_box_of_isKindB`, `not_isKindB_of_sorted_type`: a term typed by a sorted type is not a
  syntactic kind (so constructors and objects are never kinds).
* `skelK_reduces`: the kind skeleton of a sorted expression is invariant under reduction.
* `HasType.subst_at`: typed substitution at depth (`Δ ++ K :: Γ`).
* `HasTypeNW.head_lookup_con`: the type of a spine headed by a constructor variable is a kind
  whose skeleton is a codomain of the skeleton of the variable's kind.
* `HasTypeNW.hsubst_con`: **constructor-level hereditary substitution** for the canonical λPω̲
  judgement, by strong induction on the size of the skeleton of the variable's kind.  A created
  redex at an object binder is fired by `hsubst_obj`; a created redex at a constructor binder
  recurses at the skeleton of the binder's kind, which is a proper part of the skeleton of the
  variable's kind.
-/

import Start.PTSExpansionLambdaPOmegaBarObj

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

universe u

namespace Expr

variable {S : Type u}

/-- Substitutions whose values are not syntactic kinds. -/
def NoKindVal (σ : Nat → Expr S) : Prop := ∀ n, (σ n).isKindB = false

theorem NoKindVal.lift {σ : Nat → Expr S} (h : NoKindVal σ) : NoKindVal (liftSub σ) := by
  intro n
  cases n with
  | zero => rfl
  | succ n => simp only [liftSub, isKindB_rename]; exact h n

theorem isKindB_subst' (M : Expr S) {σ : Nat → Expr S} (hσ : NoKindVal σ) :
    (M.subst σ).isKindB = M.isKindB := by
  induction M generalizing σ with
  | var n => exact hσ n
  | sort s => rfl
  | app f a _ _ => rfl
  | lam A b _ _ => rfl
  | pi A B _ ihB => exact ihB hσ.lift

/-- The kind skeleton is invariant under every substitution of non-kinds. -/
theorem skelK_subst' (M : Expr S) {σ : Nat → Expr S} (hσ : NoKindVal σ) :
    (M.subst σ).skelK = M.skelK := by
  induction M generalizing σ with
  | var n => exact skelK_of_not_kind _ (hσ n)
  | sort s => rfl
  | app f a _ _ => rfl
  | lam A b _ _ => rfl
  | pi A B ihA ihB =>
      simp only [subst, skelK, isKindB_subst' A hσ, isKindB_subst' B hσ.lift, ihA hσ, ihB hσ.lift]

theorem noKindVal_substAt {N : Expr S} (hN : N.isKindB = false) :
    ∀ k, NoKindVal (substAt N k)
  | 0 => by
      intro n
      cases n with
      | zero => exact hN
      | succ n => rfl
  | k + 1 => by rw [substAt_succ]; exact (noKindVal_substAt hN k).lift

end Expr

open LambdaPi (Srt)

/-! ### Typing facts -/

/-- The type of a syntactic kind is convertible to `□`. -/
theorem conv_box_of_isKindB {f : CubeFeatures} :
    ∀ {Γ : List (Expr Srt)} {X T : Expr Srt}, HasType (cubeSpec f) Γ X T →
      X.isKindB = true → Converts T (.sort .box) := by
  intro Γ X T h hX
  induction X generalizing Γ T with
  | var n => simp [Expr.isKindB] at hX
  | app F a _ _ => simp [Expr.isKindB] at hX
  | lam A b _ _ => simp [Expr.isKindB] at hX
  | sort s =>
      obtain ⟨t', ⟨rfl, rfl⟩, hc⟩ := h.generation
      exact hc
  | pi A B _ ihB =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := h.generation_pi
      have h₂ : s₂ = .box := Converts.sort_inj (ihB hB hX)
      rw [hr.1, h₂] at hc
      exact hc

/-- A term whose type is sorted is not a syntactic kind. -/
theorem not_isKindB_of_sorted_type {f : CubeFeatures} {Γ : List (Expr Srt)} {X T : Expr Srt}
    {s : Srt} (h : HasType (cubeSpec f) Γ X T) (hT : HasType (cubeSpec f) Γ T (.sort s)) :
    X.isKindB = false := by
  cases hk : X.isKindB with
  | false => rfl
  | true => exact (CoC.not_conv_box hT (conv_box_of_isKindB h hk)).elim

/-- Two expressions with the same sort have the same kind shape. -/
theorem isKindB_eq_of_sort {f : CubeFeatures} {Γ Γ' : List (Expr Srt)} {X Y : Expr Srt}
    {s : Srt} (hX : HasType (cubeSpec f) Γ X (.sort s)) (hY : HasType (cubeSpec f) Γ' Y (.sort s)) :
    Y.isKindB = X.isKindB := by
  cases s with
  | box => rw [isKindB_of_box hX, isKindB_of_box hY]
  | star => rw [not_isKindB_of_star hX, not_isKindB_of_star hY]

/-- **The kind skeleton of a sorted expression is invariant under reduction.** -/
theorem skelK_reduces {f : CubeFeatures} :
    ∀ (X : Expr Srt) {Γ : List (Expr Srt)} {s : Srt} {Y : Expr Srt},
      HasType (cubeSpec f) Γ X (.sort s) → Reduces X Y → Y.skelK = X.skelK := by
  intro X
  induction X with
  | sort t => intro Γ s Y _ hY; rw [Reduces.sort_eq hY]
  | pi A B ihA ihB =>
      intro Γ s Y h hY
      obtain ⟨s₁, s₂, s₃, hA, hB, _, _⟩ := h.generation_pi
      obtain ⟨A', B', rfl, hAr, hBr⟩ := Reduces.pi_inv hY
      have hA' := hA.subject_reduces hAr
      have hB' := hB.subject_reduces hBr
      simp only [Expr.skelK, isKindB_eq_of_sort hA hA', isKindB_eq_of_sort hB hB',
        ihA hA hAr, ihB hB hBr]
  | var n =>
      intro Γ s Y h hY
      have hs := star_of_not_isKindB h rfl
      subst hs
      rw [Expr.skelK_of_not_kind _ (not_isKindB_of_star (h.subject_reduces hY))]; rfl
  | app F a _ _ =>
      intro Γ s Y h hY
      have hs := star_of_not_isKindB h rfl
      subst hs
      rw [Expr.skelK_of_not_kind _ (not_isKindB_of_star (h.subject_reduces hY))]; rfl
  | lam C b _ _ =>
      intro Γ s Y h hY
      have hs := star_of_not_isKindB h rfl
      subst hs
      rw [Expr.skelK_of_not_kind _ (not_isKindB_of_star (h.subject_reduces hY))]; rfl

/-- The context `Δ` after substituting `N` for the variable below it. -/
def ctxSubstAt (N : Expr Srt) : List (Expr Srt) → List (Expr Srt)
  | [] => []
  | D :: Δ => D.subst (Expr.substAt N Δ.length) :: ctxSubstAt N Δ

theorem typedSubstitution_at {P : Specification Srt} {Γ : List (Expr Srt)} {N K : Expr Srt}
    (hN : HasType P Γ N K) : ∀ Δ : List (Expr Srt), ValidContext P (Δ ++ K :: Γ) →
      ValidContext P (ctxSubstAt N Δ ++ Γ) ∧
        TypedSubstitution P (Δ ++ K :: Γ) (ctxSubstAt N Δ ++ Γ) (Expr.substAt N Δ.length)
  | [], _ => ⟨hN.valid, TypedSubstitution.single hN⟩
  | D :: Δ, hv => by
      cases hv with
      | @cons _ _ s hv hD =>
          obtain ⟨hv', hσ⟩ := typedSubstitution_at hN Δ hv
          have hD' := hD.subst hv' _ hσ
          refine ⟨.cons hv' hD', ?_⟩
          have := hσ.lift hD'
          rw [List.length_cons, Expr.substAt_succ]
          exact this

/-- Typed substitution at depth. -/
theorem HasType.subst_at {P : Specification Srt} {Γ Δ : List (Expr Srt)} {N K X T : Expr Srt}
    (hN : HasType P Γ N K) (h : HasType P (Δ ++ K :: Γ) X T) :
    HasType P (ctxSubstAt N Δ ++ Γ) (X.subst (Expr.substAt N Δ.length))
      (T.subst (Expr.substAt N Δ.length)) := by
  obtain ⟨hv, hσ⟩ := typedSubstitution_at hN Δ h.valid
  exact h.subst hv _ hσ

theorem lookup_append_skelK :
    ∀ (Δ : List (Expr Srt)) {A : Expr Srt} {Γ : List (Expr Srt)} {U : Expr Srt},
      Lookup (Δ ++ A :: Γ) Δ.length U → U.skelK = A.skelK
  | [], A, Γ, U, h => by
      cases h
      exact Expr.skelK_rename _ _
  | D :: Δ, A, Γ, U, h => by
      simp only [List.cons_append, List.length_cons] at h
      cases h with
      | succ _ h => rw [Expr.skelK_rename]; exact lookup_append_skelK Δ h

/-- `x` is a constructor variable of `Θ`: its declared type is a syntactic kind. -/
def ConVar (Θ : List (Expr Srt)) (x : Nat) : Prop :=
  ∀ U, Lookup Θ x U → U.isKindB = true

theorem ConVar.of_cons {Θ : List (Expr Srt)} {x : Nat} {A : Expr Srt}
    (h : ConVar (A :: Θ) (x + 1)) : ConVar Θ x := by
  intro U hU
  have := h _ (.succ A hU)
  rwa [Expr.isKindB_rename] at this

theorem conVar_append (Δ : List (Expr Srt)) {A : Expr Srt} {Γ : List (Expr Srt)}
    (hA : A.isKindB = true) : ConVar (Δ ++ A :: Γ) Δ.length := by
  intro U hU
  rw [lookup_append_isKindB Δ hU]
  exact hA

namespace HasTypeNW

/-- **Spines headed by a constructor variable.**  Their type is a kind whose skeleton is a
codomain of the skeleton of the kind of the head. -/
theorem head_lookup_con {Θ : List (Expr Srt)} {F T : Expr Srt} (h : HasTypeNW PWbar Θ F T) :
    ∀ x, F.headVar = some x → ConVar Θ x →
      ∃ U, Lookup Θ x U ∧ STy.ArrSuffix T.skelK U.skelK ∧ HasType PWbar Θ T (.sort .box) := by
  induction h with
  | ax _ => intro x hx; cases hx
  | @var Γ A s hA _ =>
      intro x hx hcon
      cases hx
      have hAk : A.isKindB = true := by
        have := hcon _ (.zero A Γ)
        rwa [Expr.isKindB_rename] at this
      have hA' := hA.toHasType
      have hs := box_of_isKindB hA' hAk
      subst hs
      exact ⟨_, .zero _ _, .refl _, .weaken hA' hA'⟩
  | @weaken Γ M B A s hM hA ihM _ =>
      intro x hx hcon
      rw [Expr.headVar_rename] at hx
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
      obtain ⟨U, hU, hs, hB⟩ := ihM y hy hcon.of_cons
      exact ⟨_, .succ A hU, by rw [Expr.skelK_rename, Expr.skelK_rename]; exact hs,
        .weaken hB hA.toHasType⟩
  | product => intro x hx; cases hx
  | abstraction => intro x hx; cases hx
  | @application Γ F a C D B' hF ha hr _ _ ihF _ =>
      intro x hx hcon
      obtain ⟨U, hU, hs, hPi⟩ := ihF x hx hcon
      obtain ⟨s₁, s₂, s₃, hC, hD, hrr, hcc⟩ := hPi.generation_pi
      have hs₂ : s₂ = .box := by rw [← hrr.1]; exact (Converts.sort_inj hcc).symm
      subst hs₂
      have hDk : D.isKindB = true := isKindB_of_box hD
      have hDa : HasType PWbar Γ (D.instantiate a) (.sort .box) := hD.instantiate ha.toHasType
      have hak : a.isKindB = false := not_isKindB_of_sorted_type ha.toHasType hC
      have hska : (D.instantiate a).skelK = D.skelK :=
        Expr.skelK_subst' D (Expr.noKindVal_substAt hak 0)
      have hsk : B'.skelK = D.skelK := (skelK_reduces _ hDa hr).trans hska
      refine ⟨U, hU, ?_, hDa.subject_reduces hr⟩
      rw [hsk]
      cases hCk : C.isKindB <;> simp only [Expr.skelK, hCk, hDk, if_true] at hs <;>
        exact .cod hs

theorem hsubst_con_aux (n : Nat) :
    ∀ (K : Expr Srt), K.skelK.size = n → K.isKindB = true → K ≠ .sort .box →
      ∀ (Γ : List (Expr Srt))
      (N : Expr Srt), HasTypeNW PWbar Γ N K →
      ∀ Θ M B, HasTypeNW PWbar Θ M B → ∀ Δ, Θ = Δ ++ K :: Γ →
        ∃ Δ' M' B', CtxSubstRed N Δ Δ' ∧ Reduces (M.subst (Expr.substAt N Δ.length)) M' ∧
          Reduces (B.subst (Expr.substAt N Δ.length)) B' ∧ HasTypeNW PWbar (Δ' ++ Γ) M' B' := by
  have hw : SystemWeaklyNormalizing PWbar := fun Γ hΓ M hM =>
    weaklyNormalizing_of_stronglyNormalizing (cube_stronglyNormalizing _ Γ hΓ M hM)
  induction n using Nat.strong_induction_on with
  | _ n IHn =>
  intro K hKn hKk hKne Γ N hN Θ M B h
  have ctxn : ∀ {Δ' : List (Expr Srt)} {M' B' : Expr Srt}, HasTypeNW PWbar (Δ' ++ Γ) M' B' →
      ∀ X ∈ Δ', Normal X := fun h X hX => h.normal.2.2 X (List.mem_append_left _ hX)
  have hNk : N.isKindB = false := by
    rcases CoC.type_sorted hN.toHasType with hKb | ⟨s, hKs⟩
    · exact absurd hKb hKne
    · exact not_isKindB_of_sorted_type hN.toHasType hKs
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
        have hconΘ : ConVar Θ Δ.length := by rw [heq]; exact conVar_append Δ hKk
        obtain ⟨U, hU, hs, hPiS⟩ := hF.head_lookup_con _ hhead hconΘ
        rw [heq] at hU
        have hUK := lookup_append_skelK Δ hU
        obtain ⟨s₁, s₂, s₃, hCt, hDt, hrr, hcc⟩ := hPiS.generation_pi
        have hs₂ : s₂ = .box := by rw [← hrr.1]; exact (Converts.sort_inj hcc).symm
        subst hs₂
        have hDk : D.isKindB = true := isKindB_of_box hDt
        rw [heq] at hCt
        have hCσ := HasType.subst_at hN.toHasType hCt
        simp only [Expr.subst] at hCσ
        have hC'σ := hCσ.subject_reduces hA₁
        have hskel : C'.skelK = C.skelK :=
          (skelK_reduces _ hCσ hA₁).trans (Expr.skelK_subst' C (Expr.noKindVal_substAt hNk _))
        have hC'kC : C'.isKindB = C.isKindB := isKindB_eq_of_sort hCt hC'σ
        have hfin : ∀ e' E', Reduces (e.instantiate a') e' → Reduces (B₁.instantiate a') E' →
            HasTypeNW PWbar (Δ₂ ++ Γ) e' E' →
            ∃ Δ' M' B', CtxSubstRed N Δ Δ' ∧
              Reduces ((Expr.app F a).subst σ) M' ∧
              Reduces (B₀.subst σ) B' ∧ HasTypeNW PWbar (Δ' ++ Γ) M' B' := by
          intro e' E' her hEr he'
          refine ⟨Δ₂, e', E', hc₁, ?_, ?_, he'⟩
          · simp only [Expr.subst]
            exact ((Reduces.app hFr har).tail (Beta.head C' e a')).trans her
          · exact Reduces.to_normal hB₀σ (hTy.trans hEr) he'.normal.2.1
        cases hCk : C.isKindB with
        | false =>
            obtain ⟨e', E', her, hEr, he'⟩ := HasTypeNW.hsubst_obj (hC'kC.trans hCk) ha' he
            exact hfin e' E' her hEr he'
        | true =>
            have hlt : C'.skelK.size < n := by
              rw [hskel, ← hKn, ← hUK]
              simp only [Expr.skelK, hCk, hDk, if_true] at hs
              exact hs.dom_lt
            obtain ⟨Δ', e', E', hc', her, hEr, he'⟩ :=
              IHn _ hlt C' rfl (hC'kC.trans hCk) (CoC.ne_box_of_hasType hC'σ) (Δ₂ ++ Γ) a' ha' _ e B₁ he ([]) rfl
            cases hc'
            simp only [List.length_nil, Expr.substAt_zero, List.nil_append] at her hEr he'
            exact hfin e' E' her hEr he'
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

/-- **Constructor-level hereditary substitution** for the canonical λPω̲ judgement:
substituting a canonical constructor `N : K` (`K` a kind) into a canonical derivation yields,
after normalization, a canonical derivation. -/
theorem hsubst_con {Γ : List (Expr Srt)} {N K M B : Expr Srt}
    (hK : K.isKindB = true) (hN : HasTypeNW PWbar Γ N K)
    (hM : HasTypeNW PWbar (K :: Γ) M B) :
    ∃ M' B', Reduces (M.instantiate N) M' ∧ Reduces (B.instantiate N) B' ∧
      HasTypeNW PWbar Γ M' B' := by
  have hKne : K ≠ .sort .box := by
    have hv := hM.toHasType.valid
    cases hv with
    | cons _ hKs => exact CoC.ne_box_of_hasType hKs
  obtain ⟨Δ', M', B', hc, hM', hB', h⟩ :=
    hsubst_con_aux _ K rfl hK hKne Γ N hN _ M B hM ([]) rfl
  cases hc
  exact ⟨M', B', hM', hB', h⟩

end HasTypeNW

end PureTypeSystem
