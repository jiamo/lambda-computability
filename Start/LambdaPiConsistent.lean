/-
**Consistency of `λΠ`.**

Strong normalization (`Start/LambdaPiSN.lean`) makes the logical reading of `λΠ` available: a
typable term reduces to a normal form, and the normal forms of a given type can be classified.
This module carries out the classification in the only context that matters for consistency — a
context whose declarations are all sorts — and deduces that the calculus, read as a logic through
the propositions-as-types correspondence, proves nothing:

* `LambdaPi.SortCtx` — a context all of whose declarations are sorts;
* `LambdaPi.not_typing_normal_app` — in such a context no *normal* application is typable, since
  the head of the application would have to be a variable declared with a sort, and a sort is not
  a product;
* `LambdaPi.not_typing_var_zero` — **consistency**: an atomic type variable has no inhabitant,
  i.e. there is no term `t` with `α : ∗ ⊢ t : α`;
* `LambdaPi.not_typing_pi_star_var` — for comparison, the *polymorphic* empty type `Π α:∗. α` is
  not even a type of `λΠ`: the product rule of the calculus only allows `∗`-typed domains, so
  `λΠ` has no quantification over types.
-/

import Start.LambdaPiSN

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

/-! ### Conversion cannot relate a variable to a sort or a product -/

theorem not_conv_sort_var {s : Srt} {n : ℕ} (h : Conv (Tm.sort s) (Tm.var n)) : False := by
  obtain ⟨v, hv₁, hv₂⟩ := h.church_rosser
  rw [hv₁.sort_inv] at hv₂
  exact absurd hv₂.var_inv (by simp)

theorem not_conv_pi_var {A B : Tm} {n : ℕ} (h : Conv (Tm.pi A B) (Tm.var n)) : False := by
  obtain ⟨v, hv₁, hv₂⟩ := h.church_rosser
  obtain ⟨A', B', rfl, _, _⟩ := hv₁.pi_inv
  exact absurd hv₂.var_inv (by simp)

/-! ### Contexts of sorts -/

/-- A context all of whose declarations are sorts: the base types of the logic. -/
def SortCtx (Γ : Ctx) : Prop := ∀ n C, Lookup Γ n C → ∃ s, C = Tm.sort s

theorem sortCtx_nil : SortCtx [] := by
  intro n C h
  cases h

/-- The context declaring a single type variable `α : ∗`. -/
theorem sortCtx_star : SortCtx [Tm.sort Srt.star] := by
  intro n C h
  cases h with
  | zero => exact ⟨Srt.star, rfl⟩
  | succ _ h' => cases h'

/-! ### No typable normal application -/

/-- In a context of sorts, a **normal application is never typable**: its head would be a variable
whose declared type is a sort, and a sort is not a product. -/
theorem not_typing_normal_app {Γ : Ctx} (hΓs : SortCtx Γ) :
    ∀ f a C, Normal (Tm.app f a) → Typing Γ (Tm.app f a) C → False := by
  intro f
  induction f with
  | var n =>
      intro a C _ h
      obtain ⟨A, B, hf, _, _⟩ := h.app_inv
      obtain ⟨D, hl, hc⟩ := hf.var_inv
      obtain ⟨s, rfl⟩ := hΓs n D hl
      exact not_conv_sort_pi hc
  | sort s =>
      intro a C _ h
      obtain ⟨A, B, hf, _, _⟩ := h.app_inv
      obtain ⟨_, hc⟩ := hf.sort_inv
      exact not_conv_sort_pi hc
  | pi A0 B0 _ _ =>
      intro a C _ h
      obtain ⟨A, B, hf, _, _⟩ := h.app_inv
      obtain ⟨_, _, _, _, _, hc⟩ := hf.pi_inv
      exact not_conv_sort_pi hc
  | lam A0 b0 _ _ =>
      intro a C hn _
      exact hn (b0[a]) (Step.beta A0 b0 a)
  | app f0 a0 ih _ =>
      intro a C hn h
      obtain ⟨A, B, hf, _, _⟩ := h.app_inv
      exact ih a0 (Tm.pi A B) (fun w hw => hn (Tm.app w a) (Step.appL a hw)) hf

/-! ### Consistency -/

/-- **Consistency of `λΠ`**: a type variable has no inhabitant.  In the context declaring
`α : ∗` — the propositions-as-types reading of an atomic proposition with no assumptions — no term
has type `α`.

The proof is the classical one: by strong normalization the putative inhabitant reduces to a
normal form of the same type, and none of the five shapes of a normal term can have type `α`.  A
sort, a product and an abstraction have a sort, a sort and a product as their type, and an
application is excluded by `LambdaPi.not_typing_normal_app`; the only variable in scope is `α`
itself, whose type is `∗`. -/
theorem not_typing_var_zero (t : Tm) : ¬ Typing [Tm.sort Srt.star] t (Tm.var 0) := by
  intro h
  have hΓ : Wf [Tm.sort Srt.star] := Wf.cons Wf.nil (Typing.ax [])
  obtain ⟨u, hru, hnu⟩ := h.hasNormalForm hΓ
  have hu : Typing [Tm.sort Srt.star] u (Tm.var 0) := h.red hΓ hru
  cases u with
  | var n =>
      obtain ⟨D, hl, hc⟩ := hu.var_inv
      obtain ⟨s, rfl⟩ := sortCtx_star n D hl
      exact not_conv_sort_var hc
  | sort s =>
      obtain ⟨_, hc⟩ := hu.sort_inv
      exact not_conv_sort_var hc
  | pi A B =>
      obtain ⟨_, _, _, _, _, hc⟩ := hu.pi_inv
      exact not_conv_sort_var hc
  | lam A b =>
      obtain ⟨B, _, _, _, hc⟩ := hu.lam_inv
      exact not_conv_pi_var hc
  | app f a => exact not_typing_normal_app sortCtx_star f a _ hnu hu

/-- The **polymorphic empty type is not a type of `λΠ`**: the product rule of the calculus
requires the domain to be `∗`-typed, and `∗` is typed by `□`, so `Π α:∗. α` cannot be formed.
This is why consistency is stated for a type variable and not for `Π α:∗. α`, as it would be in a
polymorphic calculus. -/
theorem not_typing_pi_star_var {Γ : Ctx} {s : Srt} :
    ¬ Typing Γ (Tm.pi (Tm.sort Srt.star) (Tm.var 0)) (Tm.sort s) := by
  intro h
  obtain ⟨s', t', hr, hA, _, _⟩ := h.pi_inv
  cases hr
  obtain ⟨_, hc⟩ := hA.sort_inv
  exact Srt.noConfusion (sort_conv_inj hc)

end LambdaPi
