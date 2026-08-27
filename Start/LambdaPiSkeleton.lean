/-
**The simple skeleton of a `λΠ` type.**

The strong normalization proof for `λΠ` (Harper–Honsell–Plotkin) goes by forgetting the
dependency: a type of `λΠ` is mapped to a *simple* type, its **skeleton**, in which a product
`Π x:A. B` becomes an arrow `A° → B°` and everything else becomes the base type.  This module
defines the skeleton and proves the two facts that make it usable:

* `LambdaPi.skel` — the skeleton of a term, computed in a list of simple types giving the
  skeletons of the variables in scope, and its behaviour under renaming and substitution
  (`LambdaPi.skel_rename`, `LambdaPi.skel_subst`, `LambdaPi.skel_inst`);
* `LambdaPi.IsKindSyn` — the syntactic shape of a kind (`∗`, or a product ending in `∗`), which
  is what a *type variable* declares; `LambdaPi.isKindSyn_of_isKind` shows that every kind of the
  calculus has this shape, and `LambdaPi.not_isKindSyn_of_typing_star` that a type is never of
  this shape;
* `LambdaPi.TypeLevel` — a term is *type-level* when it is a kind or a family, and the inversion
  lemmas `LambdaPi.TypeLevel.pi`, `.lam`, `.app`, `.var` which say that the immediate subterms
  in type position of a type-level term are again type-level;
* `LambdaPi.skel_irrel` — **the skeleton only depends on the type variables**: two skeleton
  contexts that agree at the positions declaring a kind give the same skeleton to a type-level
  term.  This is the formal counterpart of the fact that an object variable never occurs in type
  position, and it is what makes the skeleton invariant under β-reduction
  (`LambdaPi.skel_step`, `LambdaPi.skel_red`, `LambdaPi.skel_conv`).
-/

import Start.LambdaPiUnique

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

/-! ### Simple types and the skeleton -/

/-- Simple types: the base type and arrows. -/
inductive STy where
  | base : STy
  | arrow : STy → STy → STy
  deriving DecidableEq, Repr

/-- The **skeleton** of a term, in a list giving the skeletons of the variables in scope: a
product becomes an arrow, an abstraction is transparent (its skeleton is that of its body), an
application is transparent (its skeleton is that of its function part), and the sorts and the
variables not in scope get the base type. -/
def skel : List STy → Tm → STy
  | _, Tm.sort _ => STy.base
  | Γs, Tm.var n => Γs.getD n STy.base
  | Γs, Tm.pi A B => STy.arrow (skel Γs A) (skel (skel Γs A :: Γs) B)
  | Γs, Tm.lam A b => skel (skel Γs A :: Γs) b
  | Γs, Tm.app f _ => skel Γs f

@[simp] theorem skel_sort (Γs : List STy) (s : Srt) : skel Γs (Tm.sort s) = STy.base := rfl

@[simp] theorem skel_var (Γs : List STy) (n : ℕ) : skel Γs (Tm.var n) = Γs.getD n STy.base := rfl

@[simp] theorem skel_pi (Γs : List STy) (A B : Tm) :
    skel Γs (Tm.pi A B) = STy.arrow (skel Γs A) (skel (skel Γs A :: Γs) B) := rfl

@[simp] theorem skel_lam (Γs : List STy) (A b : Tm) :
    skel Γs (Tm.lam A b) = skel (skel Γs A :: Γs) b := rfl

@[simp] theorem skel_app (Γs : List STy) (f a : Tm) : skel Γs (Tm.app f a) = skel Γs f := rfl

/-- The skeleton is stable under a renaming that respects the skeletons of the variables. -/
theorem skel_rename {ρ : ℕ → ℕ} {Γs Δs : List STy}
    (h : ∀ n, Δs.getD (ρ n) STy.base = Γs.getD n STy.base) (t : Tm) :
    skel Δs (rename ρ t) = skel Γs t := by
  induction t generalizing ρ Γs Δs with
  | var n => simpa using h n
  | sort s => rfl
  | app f _ ihf _ => simpa using ihf h
  | lam A b ihA ihb =>
      have hA := ihA h
      have h' : ∀ n, (skel Δs (rename ρ A) :: Δs).getD (upr ρ n) STy.base =
          (skel Γs A :: Γs).getD n STy.base := by
        intro n
        cases n with
        | zero => simpa [upr] using hA
        | succ n => simpa [upr] using h n
      simpa using ihb h'
  | pi A B ihA ihB =>
      have hA := ihA h
      have h' : ∀ n, (skel Δs (rename ρ A) :: Δs).getD (upr ρ n) STy.base =
          (skel Γs A :: Γs).getD n STy.base := by
        intro n
        cases n with
        | zero => simpa [upr] using hA
        | succ n => simpa [upr] using h n
      rw [rename_pi, skel_pi, ihB h', hA, skel_pi]

/-- Shifting a term does not change its skeleton, provided the skeleton context is extended. -/
theorem skel_rename_succ (X : STy) (Γs : List STy) (t : Tm) :
    skel (X :: Γs) (rename Nat.succ t) = skel Γs t :=
  skel_rename (fun n => by simp) t

@[simp] theorem skel_shift (X : STy) (Γs : List STy) (t : Tm) :
    skel (X :: Γs) (shift t) = skel Γs t :=
  skel_rename_succ X Γs t

/-- The skeleton is stable under a substitution that respects the skeletons of the variables. -/
theorem skel_subst {σ : ℕ → Tm} {Γs Δs : List STy}
    (h : ∀ n, skel Δs (σ n) = Γs.getD n STy.base) (t : Tm) :
    skel Δs (subst σ t) = skel Γs t := by
  induction t generalizing σ Γs Δs with
  | var n => simpa using h n
  | sort s => rfl
  | app f _ ihf _ => simpa using ihf h
  | lam A b ihA ihb =>
      have hA := ihA h
      have h' : ∀ n, skel (skel Δs (subst σ A) :: Δs) (up σ n) =
          (skel Γs A :: Γs).getD n STy.base := by
        intro n
        cases n with
        | zero => simpa using hA
        | succ n => rw [up_succ, skel_rename_succ]; simpa using h n
      simpa using ihb h'
  | pi A B ihA ihB =>
      have hA := ihA h
      have h' : ∀ n, skel (skel Δs (subst σ A) :: Δs) (up σ n) =
          (skel Γs A :: Γs).getD n STy.base := by
        intro n
        cases n with
        | zero => simpa using hA
        | succ n => rw [up_succ, skel_rename_succ]; simpa using h n
      rw [subst_pi, skel_pi, ihB h', hA, skel_pi]

/-- The skeleton of a single substitution. -/
theorem skel_inst (Γs : List STy) (t a : Tm) :
    skel Γs (t[a]) = skel (skel Γs a :: Γs) t := by
  refine skel_subst (fun n => ?_) t
  cases n with
  | zero => rfl
  | succ n => simp

/-! ### The syntactic shape of a kind -/

/-- The syntactic shape of a kind: the sort `∗`, or a product whose codomain is again of this
shape.  Every kind of the calculus is of this shape (`LambdaPi.isKindSyn_of_isKind`). -/
inductive IsKindSyn : Tm → Prop
  | star : IsKindSyn (Tm.sort Srt.star)
  | pi {A K : Tm} : IsKindSyn K → IsKindSyn (Tm.pi A K)

theorem IsKindSyn.rename {K : Tm} (h : IsKindSyn K) (ρ : ℕ → ℕ) :
    IsKindSyn (LambdaPi.rename ρ K) := by
  induction h generalizing ρ with
  | star => exact IsKindSyn.star
  | pi _ ih => exact IsKindSyn.pi (ih _)

theorem IsKindSyn.of_rename {K : Tm} {ρ : ℕ → ℕ} (h : IsKindSyn (LambdaPi.rename ρ K)) :
    IsKindSyn K := by
  induction K generalizing ρ with
  | var n => cases h
  | sort s =>
      cases s with
      | star => exact IsKindSyn.star
      | box => cases h
  | app f a => cases h
  | lam A b => cases h
  | pi A B _ ihB =>
      cases h with
      | pi hK => exact IsKindSyn.pi (ihB hK)

@[simp] theorem isKindSyn_shift_iff (K : Tm) : IsKindSyn (shift K) ↔ IsKindSyn K :=
  ⟨fun h => h.of_rename, fun h => h.rename _⟩

/-! ### Sorts of convertible types -/

/-- A term is typed by at most one sort. -/
theorem Typing.sort_eq {Γ : Ctx} {X : Tm} {s s' : Srt} (h : Typing Γ X (Tm.sort s))
    (h' : Typing Γ X (Tm.sort s')) : s = s' :=
  sort_conv_inj (h.unique h')

/-- Convertible terms are typed by the same sort. -/
theorem Typing.sort_eq_of_conv {Γ : Ctx} (hΓ : Wf Γ) {X Y : Tm} {s s' : Srt}
    (hX : Typing Γ X (Tm.sort s)) (hY : Typing Γ Y (Tm.sort s')) (hc : Conv X Y) : s = s' := by
  obtain ⟨v, hXv, hYv⟩ := hc.church_rosser
  exact (hX.red hΓ hXv).sort_eq (hY.red hΓ hYv)

/-! ### Kinds have the syntactic shape of a kind -/

/-- **Every kind is syntactically a kind**: a term typed by `□` is `∗` or a product ending
in `∗`. -/
theorem isKindSyn_of_isKind {Γ : Ctx} (hΓ : Wf Γ) {K : Tm} (h : IsKind Γ K) : IsKindSyn K := by
  induction K generalizing Γ with
  | sort s =>
      obtain ⟨rfl, _⟩ := h.sort_inv
      exact IsKindSyn.star
  | var n =>
      obtain ⟨A, hA, hconv⟩ := h.var_inv
      obtain ⟨s, hs⟩ := hΓ.lookup_typed hA
      exact absurd hconv (fun hc => not_conv_box_of_typing hΓ hs hc)
  | app f a =>
      obtain ⟨A, B, hf, ha, hconv⟩ := h.app_inv
      rcases hf.validity hΓ with hbox | ⟨s, hs⟩
      · exact absurd hbox (by simp)
      · obtain ⟨_, t, _, _, hB, _⟩ := hs.pi_inv
        exact absurd hconv (fun hc => not_conv_box_of_typing hΓ (hB.inst ha) hc)
  | lam A b =>
      obtain ⟨B, s, hP, _, hconv⟩ := h.lam_inv
      exact absurd hconv (fun hc => not_conv_box_of_typing hΓ hP hc)
  | pi A B _ ihB =>
      obtain ⟨s, t, _, hA, hB, hconv⟩ := h.pi_inv
      cases sort_conv_inj hconv
      exact IsKindSyn.pi (ihB (Wf.cons hΓ hA) hB)

/-- A type is never syntactically a kind. -/
theorem not_isKindSyn_of_typing_star {Γ : Ctx} (hΓ : Wf Γ) {A : Tm} (hsyn : IsKindSyn A)
    (h : Typing Γ A (Tm.sort Srt.star)) : False := by
  induction hsyn generalizing Γ with
  | star =>
      obtain ⟨_, hconv⟩ := h.sort_inv
      exact Srt.noConfusion (sort_conv_inj hconv)
  | @pi A K _ ih =>
      obtain ⟨s, t, _, hA, hK, hconv⟩ := h.pi_inv
      cases sort_conv_inj hconv
      exact ih (Wf.cons hΓ hA) hK

/-! ### Type-level terms -/

/-- A term is **type-level** when it is a kind or a type family: the terms that may occur in the
type position of a judgement. -/
def TypeLevel (Γ : Ctx) (B : Tm) : Prop := IsKind Γ B ∨ IsType Γ B

theorem TypeLevel.typing {Γ : Ctx} {B : Tm} (h : TypeLevel Γ B) : ∃ T, Typing Γ B T := by
  rcases h with h | ⟨K, hK, _⟩
  · exact ⟨_, h⟩
  · exact ⟨_, hK⟩

/-- A term typed by a sort is type-level. -/
theorem typeLevel_of_typing_sort {Γ : Ctx} {X : Tm} {s : Srt} (h : Typing Γ X (Tm.sort s)) :
    TypeLevel Γ X := by
  cases s with
  | box => exact Or.inl h
  | star => exact Or.inr (isType_of_typing_star h)

/-- A variable is never a kind. -/
theorem not_isKind_var {Γ : Ctx} (hΓ : Wf Γ) {n : ℕ} (h : IsKind Γ (Tm.var n)) : False := by
  cases isKindSyn_of_isKind hΓ h

/-- An abstraction is never a kind. -/
theorem not_isKind_lam {Γ : Ctx} (hΓ : Wf Γ) {A b : Tm} (h : IsKind Γ (Tm.lam A b)) : False := by
  cases isKindSyn_of_isKind hΓ h

/-- An application is never a kind. -/
theorem not_isKind_app {Γ : Ctx} (hΓ : Wf Γ) {f a : Tm} (h : IsKind Γ (Tm.app f a)) : False := by
  cases isKindSyn_of_isKind hΓ h

/-- The domain of a type-level product is a type. -/
theorem TypeLevel.pi_dom {Γ : Ctx} {A B : Tm} (h : TypeLevel Γ (Tm.pi A B)) :
    Typing Γ A (Tm.sort Srt.star) := by
  obtain ⟨T, hT⟩ := h.typing
  obtain ⟨s, t, hr, hA, _, _⟩ := hT.pi_inv
  cases hr
  exact hA

/-- The codomain of a type-level product is type-level. -/
theorem TypeLevel.pi_cod {Γ : Ctx} {A B : Tm} (h : TypeLevel Γ (Tm.pi A B)) :
    TypeLevel (A :: Γ) B := by
  obtain ⟨T, hT⟩ := h.typing
  obtain ⟨_, _, _, _, hB, _⟩ := hT.pi_inv
  exact typeLevel_of_typing_sort hB

/-- The domain of a type-level abstraction is a type. -/
theorem TypeLevel.lam_dom {Γ : Ctx} {A b : Tm} (h : TypeLevel Γ (Tm.lam A b)) :
    Typing Γ A (Tm.sort Srt.star) := by
  obtain ⟨T, hT⟩ := h.typing
  obtain ⟨B, s, hP, _, _⟩ := hT.lam_inv
  obtain ⟨s', t', hr, hA, _, _⟩ := hP.pi_inv
  cases hr
  exact hA

/-- The body of a type-level abstraction is type-level: a family abstracts a family. -/
theorem TypeLevel.lam_body {Γ : Ctx} (hΓ : Wf Γ) {A b : Tm} (h : TypeLevel Γ (Tm.lam A b)) :
    TypeLevel (A :: Γ) b := by
  rcases h with hk | ⟨K, hK, hKbox⟩
  · exact absurd hk (fun hh => not_isKind_lam hΓ hh)
  · obtain ⟨B, s, hP, hb, hconv⟩ := hK.lam_inv
    cases hP.sort_eq_of_conv hΓ hKbox hconv
    obtain ⟨_, t', _, _, hB, hconv'⟩ := hP.pi_inv
    cases sort_conv_inj hconv'
    exact Or.inr ⟨B, hb, hB⟩

/-- The function part of a type-level application is type-level. -/
theorem TypeLevel.app_fun {Γ : Ctx} (hΓ : Wf Γ) {f a : Tm} (h : TypeLevel Γ (Tm.app f a)) :
    TypeLevel Γ f := by
  rcases h with hk | ⟨K, hK, hKbox⟩
  · exact absurd hk (fun hh => not_isKind_app hΓ hh)
  · obtain ⟨A₀, B₀, hf, ha, hconv⟩ := hK.app_inv
    rcases hf.validity hΓ with hbox | ⟨s, hs⟩
    · exact absurd hbox (by simp)
    · obtain ⟨_, t', _, _, hB₀, hconv'⟩ := hs.pi_inv
      cases sort_conv_inj hconv'
      cases (hB₀.inst ha).sort_eq_of_conv hΓ hKbox hconv
      exact Or.inr ⟨_, hf, hs⟩

/-- A type-level variable declares a kind. -/
theorem TypeLevel.var_isKind {Γ : Ctx} (hΓ : Wf Γ) {n : ℕ} {A : Tm}
    (h : TypeLevel Γ (Tm.var n)) (hl : Lookup Γ n A) : IsKind Γ A := by
  rcases h with hk | ⟨K, hK, hKbox⟩
  · exact absurd hk (fun hh => not_isKind_var hΓ hh)
  · obtain ⟨A', hl', hconv⟩ := hK.var_inv
    cases hl.det hl'
    obtain ⟨s, hs⟩ := hΓ.lookup_typed hl
    cases hs.sort_eq_of_conv hΓ hKbox hconv
    exact hs

/-- Type-levelness is preserved by reduction. -/
theorem TypeLevel.red {Γ : Ctx} (hΓ : Wf Γ) {B B' : Tm} (h : TypeLevel Γ B) (hr : Red B B') :
    TypeLevel Γ B' := by
  rcases h with hk | ⟨K, hK, hKbox⟩
  · exact Or.inl (hk.red hΓ hr)
  · exact Or.inr ⟨K, hK.red hΓ hr, hKbox⟩

/-! ### The skeleton only sees the type variables -/

/-- The position `n` of a context declares a kind. -/
def KindPos (Γ : Ctx) (n : ℕ) : Prop := IsKindSyn (Γ.getD n (Tm.sort Srt.box))

/-- Two skeleton contexts **agree** over `Γ` when they assign the same simple type to every
position declaring a kind.  The positions declaring a type — the object variables — may differ. -/
def SkAgree (Γ : Ctx) (Γs Δs : List STy) : Prop :=
  ∀ n, KindPos Γ n → Γs.getD n STy.base = Δs.getD n STy.base

theorem SkAgree.refl (Γ : Ctx) (Γs : List STy) : SkAgree Γ Γs Γs := fun _ _ => rfl

/-- Extending both skeleton contexts by the same simple type preserves agreement. -/
theorem SkAgree.cons {Γ : Ctx} {Γs Δs : List STy} (h : SkAgree Γ Γs Δs) (A : Tm) (X : STy) :
    SkAgree (A :: Γ) (X :: Γs) (X :: Δs) := by
  intro n hn
  cases n with
  | zero => rfl
  | succ n => simpa using h n hn

/-- Extending by an *object* variable: the two skeleton contexts may be extended by different
simple types, because the position does not declare a kind. -/
theorem SkAgree.cons_type {Γ : Ctx} (hΓ : Wf Γ) {Γs Δs : List STy} (h : SkAgree Γ Γs Δs) {A : Tm}
    (hA : Typing Γ A (Tm.sort Srt.star)) (X Y : STy) : SkAgree (A :: Γ) (X :: Γs) (Y :: Δs) := by
  intro n hn
  cases n with
  | zero => exact absurd hn (fun hk => not_isKindSyn_of_typing_star hΓ hk hA)
  | succ n => simpa using h n hn

/-- The declared type of a variable is syntactically a kind exactly when its context entry is. -/
theorem Lookup.isKindSyn_iff {Γ : Ctx} {n : ℕ} {A : Tm} (h : Lookup Γ n A) :
    IsKindSyn A ↔ KindPos Γ n := by
  induction h with
  | zero Γ A => simp [KindPos]
  | @succ Γ n A B _ ih => simpa [KindPos] using ih

/-- **The skeleton of a type-level term only depends on the type variables.**  This is the
formal content of the stratification: an object variable never occurs in type position, so
changing the simple type assigned to it changes nothing. -/
theorem skel_irrel {B : Tm} : ∀ {Γ : Ctx} {Γs Δs : List STy}, Wf Γ → SkAgree Γ Γs Δs →
    TypeLevel Γ B → skel Γs B = skel Δs B := by
  induction B with
  | sort s => intro _ _ _ _ _ _; rfl
  | var n =>
      intro Γ Γs Δs hΓ hag hB
      obtain ⟨T, hT⟩ := hB.typing
      obtain ⟨A, hl, _⟩ := hT.var_inv
      have hkind : IsKind Γ A := hB.var_isKind hΓ hl
      have : KindPos Γ n := hl.isKindSyn_iff.mp (isKindSyn_of_isKind hΓ hkind)
      simpa using hag n this
  | app f a ihf _ =>
      intro Γ Γs Δs hΓ hag hB
      simpa using ihf hΓ hag (hB.app_fun hΓ)
  | lam A b ihA ihb =>
      intro Γ Γs Δs hΓ hag hB
      have hA : Typing Γ A (Tm.sort Srt.star) := hB.lam_dom
      have hAeq : skel Γs A = skel Δs A := ihA hΓ hag (typeLevel_of_typing_sort hA)
      have hb := ihb (Wf.cons hΓ hA) (hag.cons A (skel Γs A)) (hB.lam_body hΓ)
      simp only [skel_lam, hAeq] at hb ⊢
      exact hb
  | pi A B ihA ihB =>
      intro Γ Γs Δs hΓ hag hB
      have hA : Typing Γ A (Tm.sort Srt.star) := hB.pi_dom
      have hAeq : skel Γs A = skel Δs A := ihA hΓ hag (typeLevel_of_typing_sort hA)
      have hb := ihB (Wf.cons hΓ hA) (hag.cons A (skel Γs A)) hB.pi_cod
      simp only [skel_pi, hAeq] at hb ⊢
      exact congrArg _ hb

/-! ### The skeleton is invariant under conversion -/

/-- **β-reduction does not change the skeleton of a type-level term.** -/
theorem skel_step {B B' : Tm} (hst : Step B B') : ∀ {Γ : Ctx} (Γs : List STy), Wf Γ →
    TypeLevel Γ B → skel Γs B = skel Γs B' := by
  induction hst with
  | beta C M N =>
      intro Γ Γs hΓ hB
      have hlam : TypeLevel Γ (Tm.lam C M) := hB.app_fun hΓ
      have hC : Typing Γ C (Tm.sort Srt.star) := hlam.lam_dom
      have hM : TypeLevel (C :: Γ) M := hlam.lam_body hΓ
      rw [skel_app, skel_lam, skel_inst]
      exact skel_irrel (Wf.cons hΓ hC)
        ((SkAgree.refl Γ Γs).cons_type hΓ hC (skel Γs C) (skel Γs N)) hM
  | appL a _ ih =>
      intro Γ Γs hΓ hB
      simpa using ih Γs hΓ (hB.app_fun hΓ)
  | appR f _ _ => intro _ _ _ _; rfl
  | lamL b hst' ih =>
      intro Γ Γs hΓ hB
      have hA := hB.lam_dom
      have := ih Γs hΓ (typeLevel_of_typing_sort hA)
      simp only [skel_lam, this]
  | lamR A _ ih =>
      intro Γ Γs hΓ hB
      have hA := hB.lam_dom
      simpa using ih (skel Γs A :: Γs) (Wf.cons hΓ hA) (hB.lam_body hΓ)
  | piL B hst' ih =>
      intro Γ Γs hΓ hB'
      have hA := hB'.pi_dom
      have := ih Γs hΓ (typeLevel_of_typing_sort hA)
      simp only [skel_pi, this]
  | piR A _ ih =>
      intro Γ Γs hΓ hB'
      have hA := hB'.pi_dom
      have := ih (skel Γs A :: Γs) (Wf.cons hΓ hA) hB'.pi_cod
      simp only [skel_pi, this]

/-- Many-step reduction does not change the skeleton of a type-level term. -/
theorem skel_red {Γ : Ctx} (hΓ : Wf Γ) (Γs : List STy) {B B' : Tm} (hB : TypeLevel Γ B)
    (hr : Red B B') : skel Γs B = skel Γs B' := by
  induction hr with
  | refl => rfl
  | @tail u v hru hst ih =>
      exact ih.trans (skel_step hst Γs hΓ (hB.red hΓ hru))

/-- **Conversion does not change the skeleton of a type-level term.** -/
theorem skel_conv {Γ : Ctx} (hΓ : Wf Γ) (Γs : List STy) {A B : Tm} (hA : TypeLevel Γ A)
    (hB : TypeLevel Γ B) (hc : Conv A B) : skel Γs A = skel Γs B := by
  obtain ⟨v, hAv, hBv⟩ := hc.church_rosser
  exact (skel_red hΓ Γs hA hAv).trans (skel_red hΓ Γs hB hBv).symm

end LambdaPi
