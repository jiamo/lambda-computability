import Start.PTSCube

/-!
# The kinds of the cube corners without dependent types

This library's own module (task `M23-FOMEGA`, first step of the classification of
`systemFOmega`-legal expressions).

* `PureTypeSystem.not_hasType_conv_box` — in every corner, an expression with a sort as type is
  never convertible to `□`;
* `PureTypeSystem.IsKind` — the kinds `∗ | K₁ → K₂` (closed, built from `∗` by products);
* `PureTypeSystem.isKind_of_hasType_box` — in a corner without `(∗,□)` (no dependent types),
  every expression of type `□` is a kind, syntactically;
* `PureTypeSystem.hasType_box_iff_isKind` — in `systemFOmega`, in a valid context,
  `Γ ⊢ K : □ ↔ IsKind K`;
* `PureTypeSystem.IsConstr tv` — type constructors over the type variables `tv`: type variables,
  arrows, quantifications over kinds, abstractions over kinds and applications (no sort, no term
  variable, no term-level subexpression);
* `PureTypeSystem.isConstr_of_hasType`, `systemFOmega_constr` — every expression whose type has
  type `□` is a constructor over the kind-declared variables of its context (`kindMask Γ`).

Strong normalization of `F^ω` is not proved here.
-/

set_option autoImplicit false

namespace PureTypeSystem

open LambdaPi (Srt)

/-- In every corner, a sorted expression is never convertible to `□`. -/
theorem not_hasType_conv_box (f : CubeFeatures) {Γ : List (Expr Srt)} {A : Expr Srt} {s : Srt}
    (hA : HasType (cubeSpec f) Γ A (.sort s)) (hc : Converts A (.sort .box)) : False := by
  obtain ⟨C, hAC, hBC⟩ := hc.join
  have hC : (Expr.sort Srt.box : Expr Srt) = C := (Normal.sort _).reduces_eq hBC
  subst hC
  exact not_hasType_box f (hA.subject_reduces hAC)

/-- Every declared type of a valid context is sorted. -/
theorem lookup_sorted {S : Type*} {P : Specification S} {Γ : List (Expr S)}
    (hΓ : ValidContext P Γ) {n : Nat} {A : Expr S} (hn : Lookup Γ n A) :
    ∃ s, HasType P Γ A (.sort s) := by
  induction hΓ generalizing n A with
  | nil => cases hn
  | @cons Γ B s hΓ hB ih =>
      cases hn with
      | zero => exact ⟨s, .weaken hB hB⟩
      | succ _ hn =>
          obtain ⟨t, ht⟩ := ih hn
          exact ⟨t, .weaken ht hB⟩

/-- Kinds: `∗` and products of kinds. -/
inductive IsKind : Expr Srt → Prop
  | star : IsKind (.sort .star)
  | pi {K₁ K₂ : Expr Srt} : IsKind K₁ → IsKind K₂ → IsKind (.pi K₁ K₂)

/-- In a corner without dependent types, every expression of type `□` is a kind. -/
theorem isKind_of_hasType_box (f : CubeFeatures) (hdep : f.dep = false) {Γ : List (Expr Srt)}
    {K : Expr Srt} (h : HasType (cubeSpec f) Γ K (.sort .box)) : IsKind K := by
  induction K generalizing Γ with
  | var n =>
      obtain ⟨A, hn, hc⟩ := h.generation
      obtain ⟨s, hs⟩ := lookup_sorted h.valid hn
      exact (not_hasType_conv_box f hs (.symm _ _ hc)).elim
  | sort s =>
      obtain ⟨t, ⟨rfl, rfl⟩, _⟩ := h.generation
      exact .star
  | app g a _ _ =>
      obtain ⟨s, hs⟩ := h.application_type_sorted
      exact (not_hasType_box f hs).elim
  | lam A b _ _ =>
      obtain ⟨B, s, _, _, hc⟩ := h.generation_lam
      exact (Converts.pi_not_sort (.symm _ _ hc)).elim
  | pi A B ihA ihB =>
      obtain ⟨s₁, s₂, s₃, hA, hB, ⟨h₃₂, hr⟩, hc⟩ := h.generation_pi
      have h₃ : s₃ = Srt.box := (Converts.sort_inj hc).symm
      subst h₃ h₃₂
      cases s₁ with
      | star => simp [CubeFeatures.allows, hdep] at hr
      | box => exact .pi (ihA hA) (ihB hB)

/-- With type operators, every kind has type `□` in every valid context. -/
theorem hasType_box_of_isKind (f : CubeFeatures) (hops : f.ops = true) {K : Expr Srt}
    (hK : IsKind K) {Γ : List (Expr Srt)} (hΓ : ValidContext (cubeSpec f) Γ) :
    HasType (cubeSpec f) Γ K (.sort .box) := by
  induction hK generalizing Γ with
  | star => exact cube_star_box f hΓ
  | pi _ _ ih₁ ih₂ =>
      have h₁ := ih₁ hΓ
      exact .product h₁ (ih₂ (.cons hΓ h₁)) ⟨rfl, by simp [CubeFeatures.allows, hops]⟩

/-- **Kinds of `F^ω`.**  In a valid context, `Γ ⊢ K : □` in `systemFOmega` exactly when `K` is
a kind. -/
theorem hasType_box_iff_isKind {Γ : List (Expr Srt)} (hΓ : ValidContext (cubeSpec systemFOmega) Γ)
    (K : Expr Srt) : HasType (cubeSpec systemFOmega) Γ K (.sort .box) ↔ IsKind K :=
  ⟨isKind_of_hasType_box _ rfl, fun hK => hasType_box_of_isKind _ rfl hK hΓ⟩

namespace IsKind

/-- Kinds are closed. -/
theorem rename_eq {K : Expr Srt} (hK : IsKind K) (ρ : Nat → Nat) : K.rename ρ = K := by
  induction hK generalizing ρ with
  | star => rfl
  | pi _ _ ih₁ ih₂ => simp only [Expr.rename, ih₁, ih₂]

theorem of_rename {K : Expr Srt} {ρ : Nat → Nat} (h : IsKind (K.rename ρ)) : IsKind K := by
  induction K generalizing ρ with
  | var n => cases h
  | sort s => cases s with
    | star => exact .star
    | box => cases h
  | app _ _ _ _ => cases h
  | lam _ _ _ _ => cases h
  | pi A B ihA ihB =>
      cases h with
      | pi h₁ h₂ => exact .pi (ihA h₁) (ihB h₂)

/-- Kinds are normal. -/
theorem normal {K : Expr Srt} (hK : IsKind K) : Normal K := by
  induction hK with
  | star => exact Normal.sort _
  | pi _ _ ih₁ ih₂ => exact Normal.pi ih₁ ih₂

/-- In every corner, the only sort of a kind is `□`. -/
theorem sort_eq (f : CubeFeatures) {K : Expr Srt} (hK : IsKind K) {Γ : List (Expr Srt)}
    {s : Srt} (h : HasType (cubeSpec f) Γ K (.sort s)) : s = .box := by
  induction hK generalizing Γ s with
  | star =>
      obtain ⟨t, ⟨_, rfl⟩, hc⟩ := h.generation
      exact Converts.sort_inj hc
  | pi _ _ _ ih₂ =>
      obtain ⟨s₁, s₂, s₃, _, hB, ⟨h₃₂, _⟩, hc⟩ := h.generation_pi
      rw [Converts.sort_inj hc, h₃₂]
      exact ih₂ hB

end IsKind

/-- Extend a predicate on de Bruijn indices by a value for the new index `0`. -/
def consMask (p : Prop) (tv : Nat → Prop) : Nat → Prop
  | 0 => p
  | n + 1 => tv n

/-- The type variables of a context: the indices declared with a kind. -/
def kindMask : List (Expr Srt) → Nat → Prop
  | [] => fun _ => False
  | A :: Γ => consMask (IsKind A) (kindMask Γ)

/-- Type constructors over a set `tv` of type variables: type variables, arrows and
quantifications over kinds, type-level abstractions over kinds and type-level applications.
They contain no term variable, no term-level subexpression and no sort. -/
inductive IsConstr : (Nat → Prop) → Expr Srt → Prop
  | var {tv : Nat → Prop} {n : Nat} : tv n → IsConstr tv (.var n)
  | arrow {tv : Nat → Prop} {A B : Expr Srt} : IsConstr tv A →
      IsConstr (consMask (IsKind A) tv) B → IsConstr tv (.pi A B)
  | forallK {tv : Nat → Prop} {K B : Expr Srt} : IsKind K →
      IsConstr (consMask (IsKind K) tv) B → IsConstr tv (.pi K B)
  | lam {tv : Nat → Prop} {K b : Expr Srt} : IsKind K →
      IsConstr (consMask (IsKind K) tv) b → IsConstr tv (.lam K b)
  | app {tv : Nat → Prop} {F G : Expr Srt} : IsConstr tv F → IsConstr tv G →
      IsConstr tv (.app F G)

theorem consMask_liftRen {p q : Prop} (hpq : p → q) {tv tv' : Nat → Prop} {ρ : Nat → Nat}
    (hρ : ∀ n, tv n → tv' (ρ n)) : ∀ n, consMask p tv n → consMask q tv' (Expr.liftRen ρ n)
  | 0, h => hpq h
  | n + 1, h => hρ n h

theorem IsConstr.rename {tv : Nat → Prop} {M : Expr Srt} (h : IsConstr tv M) {tv' : Nat → Prop}
    {ρ : Nat → Nat} (hρ : ∀ n, tv n → tv' (ρ n)) : IsConstr tv' (M.rename ρ) := by
  induction h generalizing tv' ρ with
  | var hn => exact .var (hρ _ hn)
  | @arrow tv A B _ _ ihA ihB =>
      refine .arrow (ihA hρ) (ihB (consMask_liftRen ?_ hρ))
      intro hk; exact (hk.rename_eq ρ).symm ▸ hk
  | @forallK tv K B hK _ ih =>
      refine .forallK ((hK.rename_eq ρ).symm ▸ hK) (ih (consMask_liftRen ?_ hρ))
      intro hk; exact (hk.rename_eq ρ).symm ▸ hk
  | @lam tv K b hK _ ih =>
      refine .lam ((hK.rename_eq ρ).symm ▸ hK) (ih (consMask_liftRen ?_ hρ))
      intro hk; exact (hk.rename_eq ρ).symm ▸ hk
  | app _ _ ihF ihG => exact .app (ihF hρ) (ihG hρ)

/-- **Constructors of `F^ω`.**  In a corner with type operators but without dependent types
(such as `systemFOmega`), every expression whose type has type `□` is a type constructor over the
type variables of its context. -/
theorem isConstr_of_hasType (f : CubeFeatures) (hdep : f.dep = false) (hops : f.ops = true)
    {Γ : List (Expr Srt)} {M T : Expr Srt} (h : HasType (cubeSpec f) Γ M T) :
    HasType (cubeSpec f) Γ T (.sort .box) → IsConstr (kindMask Γ) M := by
  induction h with
  | @ax s t hst =>
      intro hT
      obtain ⟨rfl, rfl⟩ := hst
      exact (not_hasType_box f hT).elim
  | @var Γ A s hA =>
      intro hT
      exact .var (IsKind.of_rename (isKind_of_hasType_box f hdep hT))
  | @weaken Γ M B A s hM hA ihM _ =>
      intro hT
      have hB := hasType_box_of_isKind f hops
        (IsKind.of_rename (isKind_of_hasType_box f hdep hT)) hM.valid
      exact (ihM hB).rename (fun n hn => hn)
  | @product Γ A B s₁ s₂ s₃ hA hB hr ihA ihB =>
      intro hT
      obtain ⟨t, ⟨rfl, rfl⟩, _⟩ := hT.generation
      obtain ⟨rfl, hr⟩ := hr
      have hB' := ihB (cube_star_box f hB.valid)
      cases s₁ with
      | star => exact .arrow (ihA (cube_star_box f hA.valid)) hB'
      | box => exact .forallK (isKind_of_hasType_box f hdep hA) hB'
  | @abstraction Γ A b B s hb hPi ihb _ =>
      intro hT
      cases isKind_of_hasType_box f hdep hT with
      | pi hA hB => exact .lam hA (ihb (hasType_box_of_isKind f hops hB hb.valid))
  | @application Γ g a A B hg ha ihg iha =>
      intro hT
      have hK := isKind_of_hasType_box f hdep hT
      obtain ⟨s, hs⟩ := hg.product_type_sorted
      obtain ⟨s₁, s₂, s₃, hA, hB, ⟨_, hr⟩, _⟩ := hs.generation_pi
      have h₂ : s₂ = .box := hK.sort_eq f (HasType.instantiate hB ha)
      subst h₂
      have hA' : HasType (cubeSpec f) Γ A (.sort .box) := by
        cases s₁ with
        | star => simp [CubeFeatures.allows, hdep] at hr
        | box => exact hA
      have hPi : HasType (cubeSpec f) Γ (.pi A B) (.sort .box) :=
        .product hA' hB ⟨rfl, by simp [CubeFeatures.allows, hops]⟩
      exact .app (ihg hPi) (iha hA')
  | @conversion Γ M A B s hM hB hc ihM _ =>
      intro hT
      have hK := isKind_of_hasType_box f hdep hT
      apply ihM
      obtain ⟨t, rfl⟩ | ⟨t, ht⟩ := hM.regularity
      · rw [hK.normal.eq_of_converts (Normal.sort _) (.symm _ _ hc)] at hT
        exact hT
      · obtain ⟨C, hAC, hBC⟩ := hc.join
        have hBC' := hK.normal.reduces_eq hBC
        subst hBC'
        have := hK.sort_eq f (ht.subject_reduces hAC)
        subst this
        exact ht

/-- The classification of `systemFOmega`-legal constructors: if `Γ ⊢ A : K` with `Γ ⊢ K : □`, then
`K` is a kind and `A` is a type constructor over the kind-declared variables of `Γ`. -/
theorem systemFOmega_constr {Γ : List (Expr Srt)} {A K : Expr Srt}
    (hA : HasType (cubeSpec systemFOmega) Γ A K)
    (hK : HasType (cubeSpec systemFOmega) Γ K (.sort .box)) :
    IsKind K ∧ IsConstr (kindMask Γ) A :=
  ⟨isKind_of_hasType_box _ rfl hK, isConstr_of_hasType _ rfl rfl hA hK⟩

end PureTypeSystem
