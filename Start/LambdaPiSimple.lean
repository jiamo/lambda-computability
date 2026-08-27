/-
**The simply typed skeleton of a `λΠ` derivation.**

`Start/LambdaPiSkeleton.lean` maps every type of `λΠ` to a *simple* type, its skeleton, and shows
that the skeleton is invariant under conversion.  This module uses the skeleton to erase a
dependent derivation to a simply typed one: a term typable in `λΠ` is typable, *as a raw term*, in
the simply typed λ-calculus over the single base type `LambdaPi.STy.base`.

* `LambdaPi.STyping` — the simple typing judgement on `λΠ` raw terms: the sorts are constants of
  the base type, a product is a constant of the base type, an abstraction has an arrow type and an
  application eliminates one;
* `LambdaPi.skelCtx` — the skeleton of a context;
* `LambdaPi.Typing.styping` — **erasure**: `Γ ⊢ t : A` implies `Γ° ⊢ t : A°`.

Erasure is the first half of the Harper–Honsell–Plotkin proof of strong normalization for `λΠ`:
the second half is that the simply typed terms are strongly normalizing, which is proved by
Tait's method in `Start/LambdaPiSN.lean` and does not mention the dependent judgement at all.
-/

import Start.LambdaPiSkeleton

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

/-! ### Simple typing of raw terms -/

/-- The simple typing judgement on the raw terms of `λΠ`, in a context of simple types.  The two
sorts and the products are constants of the base type, and the annotation of an abstraction is
required to be simply typable, so that a derivation bounds the whole term and not only its
skeleton. -/
inductive STyping : List STy → Tm → STy → Prop
  | sort (Γs : List STy) (s : Srt) : STyping Γs (Tm.sort s) STy.base
  | var (Γs : List STy) (n : ℕ) : STyping Γs (Tm.var n) (Γs.getD n STy.base)
  | pi {Γs : List STy} {A B : Tm} {σ τ : STy} : STyping Γs A σ →
      STyping (skel Γs A :: Γs) B τ → STyping Γs (Tm.pi A B) STy.base
  | lam {Γs : List STy} {A b : Tm} {σ τ : STy} : STyping Γs A σ →
      STyping (skel Γs A :: Γs) b τ → STyping Γs (Tm.lam A b) (STy.arrow (skel Γs A) τ)
  | app {Γs : List STy} {f a : Tm} {σ τ : STy} : STyping Γs f (STy.arrow σ τ) →
      STyping Γs a σ → STyping Γs (Tm.app f a) τ

/-- Inverting a simple typing of a product: the domain is simply typable. -/
theorem STyping.pi_inv {Γs : List STy} {A B : Tm} {υ : STy} (h : STyping Γs (Tm.pi A B) υ) :
    ∃ σ, STyping Γs A σ := by
  cases h with
  | pi hA _ => exact ⟨_, hA⟩

/-! ### The skeleton of a context -/

/-- The skeleton of a context: each entry is given the skeleton it has in the skeleton of the
context below it. -/
def skelCtx : Ctx → List STy
  | [] => []
  | A :: Γ => skel (skelCtx Γ) A :: skelCtx Γ

@[simp] theorem skelCtx_nil : skelCtx [] = [] := rfl

@[simp] theorem skelCtx_cons (A : Tm) (Γ : Ctx) :
    skelCtx (A :: Γ) = skel (skelCtx Γ) A :: skelCtx Γ := rfl

/-- The skeleton of the type declared for a variable is the simple type the skeleton context
assigns to that variable. -/
theorem Lookup.skel_eq {Γ : Ctx} {n : ℕ} {A : Tm} (h : Lookup Γ n A) :
    skel (skelCtx Γ) A = (skelCtx Γ).getD n STy.base := by
  induction h with
  | zero Γ A => simp
  | @succ Γ n A B _ ih => simpa using ih

/-! ### Erasure -/

/-- **Erasure**: a term typable in `λΠ` is simply typable, as a raw term, with its skeleton as its
simple type. -/
theorem Typing.styping {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) (hΓ : Wf Γ) :
    STyping (skelCtx Γ) t (skel (skelCtx Γ) A) := by
  induction h with
  | ax Γ => exact STyping.sort _ _
  | @var Γ n A hl => rw [hl.skel_eq]; exact STyping.var _ _
  | @pi Γ A B s t _ hA hB ihA ihB =>
      exact STyping.pi (ihA hΓ) (ihB (Wf.cons hΓ hA))
  | @lam Γ A B b s hP hb ihP ihb =>
      obtain ⟨σ, hAσ⟩ := (ihP hΓ).pi_inv
      obtain ⟨s', t', _, hA, _, _⟩ := hP.pi_inv
      have hb' := ihb (Wf.cons hΓ hA)
      exact STyping.lam hAσ hb'
  | @app Γ f a A B hf ha ihf iha =>
      have hf' := ihf hΓ
      have ha' := iha hΓ
      rw [skel_pi] at hf'
      have hstar : Typing Γ A (Tm.sort Srt.star) := by
        rcases hf.validity hΓ with hbox | ⟨s, hs⟩
        · exact absurd hbox (by simp)
        · obtain ⟨s', t', hr, hA, _, _⟩ := hs.pi_inv
          cases hr
          exact hA
      have hBlevel : TypeLevel (A :: Γ) B := by
        rcases hf.validity hΓ with hbox | ⟨s, hs⟩
        · exact absurd hbox (by simp)
        · obtain ⟨s', t', _, _, hB, _⟩ := hs.pi_inv
          exact typeLevel_of_typing_sort hB
      have hskel : skel (skel (skelCtx Γ) a :: skelCtx Γ) B =
          skel (skel (skelCtx Γ) A :: skelCtx Γ) B :=
        skel_irrel (Wf.cons hΓ hstar)
          ((SkAgree.refl Γ (skelCtx Γ)).cons_type hΓ hstar _ _) hBlevel
      rw [skel_inst, hskel]
      exact STyping.app hf' ha'
  | @conv Γ t A B s ht hB hc iht _ =>
      have hAlevel : TypeLevel Γ A := by
        rcases ht.validity hΓ with rfl | ⟨s', hs'⟩
        · exact absurd (not_conv_box_of_typing hΓ hB hc.symm) (by simp)
        · exact typeLevel_of_typing_sort hs'
      have := iht hΓ
      rwa [skel_conv hΓ (skelCtx Γ) hAlevel (typeLevel_of_typing_sort hB) hc] at this

end LambdaPi
