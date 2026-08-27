/-
**Uniqueness of types and the stratification of `λΠ`.**

`Start/LambdaPiTyping.lean` develops the metatheory of the typing judgement of `λΠ` up to subject
reduction.  This module adds the two structural facts about that judgement which the rest of the
theory of the calculus rests on.

* `LambdaPi.Lookup.det` — a variable has at most one type in a context;
* `LambdaPi.Typing.unique` — **uniqueness of types**: two types of the same term in the same
  context are convertible;
* `LambdaPi.not_typing_box` — the top sort `□` has no type, so it is not a term of the calculus;
* `LambdaPi.IsKind`, `LambdaPi.IsType`, `LambdaPi.IsObject` — the three levels of `λΠ`: kinds
  (typed by `□`), types or families (typed by a kind) and objects (typed by a type);
* `LambdaPi.not_isType_isKind`, `LambdaPi.not_isKind_and_object`, … — the levels are mutually
  exclusive, and `LambdaPi.Typing.level` — in a well-formed context every typable term lies on
  exactly one of them.

The stratification is what makes the calculus predicative in the informal sense: a term is either
a kind, or a family, or an object, and no term is two of these at once.  It is proved from
uniqueness of types together with the fact that convertible sorts are equal
(`LambdaPi.sort_conv_inj`).
-/

import Start.LambdaPiTyping

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

/-! ### Determinism of the context lookup -/

/-- A variable has at most one type in a context. -/
theorem Lookup.det {Γ : Ctx} {n : ℕ} {A B : Tm} (hA : Lookup Γ n A) (hB : Lookup Γ n B) :
    A = B := by
  induction hA generalizing B with
  | zero Γ A =>
      cases hB with
      | zero => rfl
  | succ C _ ih =>
      cases hB with
      | succ _ hB' => exact congrArg shift (ih hB')

/-! ### Uniqueness of types -/

/-- **Uniqueness of types**: any two types of a term in a fixed context are convertible.

The proof is by induction on the term, inverting both derivations; the only place where the
induction hypothesis is used at a *different* term is the application case, where the two
codomains are compared. -/
theorem Typing.unique {Γ : Ctx} {t A B : Tm} (hA : Typing Γ t A) (hB : Typing Γ t B) :
    Conv A B := by
  induction t generalizing Γ A B with
  | sort s =>
      obtain ⟨_, hcA⟩ := hA.sort_inv
      obtain ⟨_, hcB⟩ := hB.sort_inv
      exact hcA.symm.trans hcB
  | var n =>
      obtain ⟨A', hA', hcA⟩ := hA.var_inv
      obtain ⟨B', hB', hcB⟩ := hB.var_inv
      cases hA'.det hB'
      exact hcA.symm.trans hcB
  | pi A₀ B₀ ihA₀ ihB₀ =>
      obtain ⟨_, t₁, _, _, hB₁, hcA⟩ := hA.pi_inv
      obtain ⟨_, t₂, _, _, hB₂, hcB⟩ := hB.pi_inv
      cases sort_conv_inj (ihB₀ hB₁ hB₂)
      exact hcA.symm.trans hcB
  | lam A₀ b _ ihb =>
      obtain ⟨B₁, _, _, hb₁, hcA⟩ := hA.lam_inv
      obtain ⟨B₂, _, _, hb₂, hcB⟩ := hB.lam_inv
      exact hcA.symm.trans ((Conv.piR A₀ (ihb hb₁ hb₂)).trans hcB)
  | app f a ihf _ =>
      obtain ⟨_, B₁, hf₁, _, hcA⟩ := hA.app_inv
      obtain ⟨_, B₂, hf₂, _, hcB⟩ := hB.app_inv
      have hpi := ihf hf₁ hf₂
      have hB : Conv B₁ B₂ := pi_inj_right hpi
      exact hcA.symm.trans ((hB.subst (scons a ids)).trans hcB)

/-- The top sort `□` is not a term of the calculus: it has no type in any context. -/
theorem not_typing_box {Γ : Ctx} {C : Tm} (h : Typing Γ (Tm.sort Srt.box) C) : False := by
  obtain ⟨hs, _⟩ := h.sort_inv
  exact Srt.noConfusion hs

/-! ### The three levels of the calculus -/

/-- A **kind** of `λΠ`: a term whose type is the top sort `□`.  These are `∗` itself and the
products `Π x:A. K` of a kind over a type. -/
def IsKind (Γ : Ctx) (K : Tm) : Prop := Typing Γ K (Tm.sort Srt.box)

/-- A **type** (or type family) of `λΠ`: a term whose type is a kind.  The types proper are the
terms of `∗`; the families are the terms of a product kind. -/
def IsType (Γ : Ctx) (A : Tm) : Prop := ∃ K, Typing Γ A K ∧ IsKind Γ K

/-- An **object** of `λΠ`: a term whose type is a type. -/
def IsObject (Γ : Ctx) (t : Tm) : Prop := ∃ A, Typing Γ t A ∧ IsType Γ A

/-- The sort `∗` is a kind. -/
theorem isKind_star (Γ : Ctx) : IsKind Γ (Tm.sort Srt.star) := Typing.ax Γ

/-- A term of `∗` is a type. -/
theorem isType_of_typing_star {Γ : Ctx} {A : Tm} (h : Typing Γ A (Tm.sort Srt.star)) :
    IsType Γ A := ⟨_, h, isKind_star Γ⟩

/-- A term convertible to the top sort reduces to it, so a term typable in a well-formed context
cannot be convertible to `□`. -/
theorem not_conv_box_of_typing {Γ : Ctx} (hΓ : Wf Γ) {A C : Tm} (h : Typing Γ A C)
    (hconv : Conv A (Tm.sort Srt.box)) : False := by
  obtain ⟨v, hAv, hbv⟩ := hconv.church_rosser
  have hv : v = Tm.sort Srt.box := Red.sort_inv hbv
  subst hv
  exact not_typing_box (h.red hΓ hAv)

/-- No term is both a type and a kind. -/
theorem not_isType_isKind {Γ : Ctx} (hΓ : Wf Γ) {A : Tm} (h₁ : IsType Γ A) (h₂ : IsKind Γ A) :
    False := by
  obtain ⟨K, hAK, hK⟩ := h₁
  exact not_conv_box_of_typing hΓ hK (hAK.unique h₂)

/-- No term is both an object and a kind. -/
theorem not_isObject_isKind {Γ : Ctx} (hΓ : Wf Γ) {t : Tm} (h₁ : IsObject Γ t) (h₂ : IsKind Γ t) :
    False := by
  obtain ⟨A, htA, K, hAK, _⟩ := h₁
  exact not_conv_box_of_typing hΓ hAK (htA.unique h₂)

/-- No term is both an object and a type. -/
theorem not_isObject_isType {Γ : Ctx} (hΓ : Wf Γ) {t : Tm} (h₁ : IsObject Γ t) (h₂ : IsType Γ t) :
    False := by
  obtain ⟨A, htA, K, hAK, hK⟩ := h₁
  obtain ⟨K', htK', hK'⟩ := h₂
  -- The two types `A` and `K'` of `t` are convertible; passing to a common reduct, the kind `K`
  -- of `A` is convertible to `□`, which `not_conv_box_of_typing` excludes.
  obtain ⟨v, hAv, hK'v⟩ := (htA.unique htK').church_rosser
  exact not_conv_box_of_typing hΓ hK ((hAK.red hΓ hAv).unique (hK'.red hΓ hK'v))

/-- In a well-formed context, a typable term is a kind, a type or an object. -/
theorem Typing.level {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) (hΓ : Wf Γ) :
    IsKind Γ t ∨ IsType Γ t ∨ IsObject Γ t := by
  rcases h.validity hΓ with rfl | ⟨s, hs⟩
  · exact Or.inl h
  · cases s with
    | box => exact Or.inr (Or.inl ⟨A, h, hs⟩)
    | star => exact Or.inr (Or.inr ⟨A, h, isType_of_typing_star hs⟩)

end LambdaPi
