/-
**Polymorphic data in System F**, and the consequences of strong normalization.

The Church numerals of `Start/Church.lean` are untyped terms; in System F they all receive the one
polymorphic type `∀ α. (α → α) → α → α`, which is what makes the calculus a programming language
rather than a curiosity.  This file types them, types the successor, and records the two
consequences of `SystemF.sn_of_typing` that need confluence as well: a typable term has a normal
form, and that normal form is unique.

* `SystemF.natTy` — the polymorphic type of the numerals, and `SystemF.typing_church` — **every
  Church numeral has it**;
* `SystemF.typing_succ` — the successor combinator has type `nat → nat`; its derivation
  instantiates the argument's quantifier, which is exactly what the simply typed calculus cannot
  do with a single numeral type;
* `SystemF.exists_unique_normal_form` — **a typable term has exactly one normal form**, from
  strong normalization together with the confluence theorem of `Start/Reduction.lean`.
-/

import Start.SystemFSR

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace SystemF

open Lambda

/-! ### The Church numerals -/

/-- The polymorphic type of the Church numerals, `∀ α. (α → α) → α → α`. -/
def natTy : FTy :=
  FTy.all (FTy.arrow (FTy.arrow (FTy.var 0) (FTy.var 0)) (FTy.arrow (FTy.var 0) (FTy.var 0)))

@[simp] theorem tyShift_natTy : tyShift natTy = natTy := rfl

/-- The body of a Church numeral is typable in the context of its two abstractions. -/
theorem typing_iterate (Γ : List FTy) (n : ℕ) :
    Typing (FTy.var 0 :: FTy.arrow (FTy.var 0) (FTy.var 0) :: Γ)
      (Lambda.iterate (Lambda.var 1) (Lambda.var 0) n) (FTy.var 0) := by
  induction n with
  | zero => exact Typing.var (by simp)
  | succ n ih =>
      rw [Lambda.iterate_succ]
      exact Typing.app (Typing.var (by simp)) ih

/-- **Every Church numeral has the polymorphic numeral type.** -/
theorem typing_church (n : ℕ) : Typing [] (Lambda.church n) natTy := by
  rw [Lambda.church_eq_iterate]
  refine Typing.tlam ?_
  exact Typing.lam (Typing.lam (typing_iterate [] n))

/-- The successor combinator has type `nat → nat`; the derivation instantiates the quantifier of
its argument. -/
theorem typing_succ : Typing [] Lambda.succ (FTy.arrow natTy natTy) := by
  refine Typing.lam ?_
  refine Typing.tlam ?_
  have hctx : ([natTy].map tyShift) = [natTy] := by simp
  rw [hctx]
  refine Typing.lam (Typing.lam ?_)
  have hn : Typing (FTy.var 0 :: FTy.arrow (FTy.var 0) (FTy.var 0) :: [natTy])
      (Lambda.var 2) natTy := Typing.var (by simp)
  have hn' : Typing (FTy.var 0 :: FTy.arrow (FTy.var 0) (FTy.var 0) :: [natTy])
      (Lambda.var 2)
      (FTy.arrow (FTy.arrow (FTy.var 0) (FTy.var 0)) (FTy.arrow (FTy.var 0) (FTy.var 0))) := by
    have h := Typing.tapp (B := FTy.var 0) hn
    simpa [natTy, tyInst, tySubst, tyScons, ups] using h
  have hf : Typing (FTy.var 0 :: FTy.arrow (FTy.var 0) (FTy.var 0) :: [natTy])
      (Lambda.var 1) (FTy.arrow (FTy.var 0) (FTy.var 0)) := Typing.var (by simp)
  have hx : Typing (FTy.var 0 :: FTy.arrow (FTy.var 0) (FTy.var 0) :: [natTy])
      (Lambda.var 0) (FTy.var 0) := Typing.var (by simp)
  exact Typing.app hf (Typing.app (Typing.app hn' hf) hx)

/-! ### Unique normal forms -/

/-- Nothing reduces out of a normal term. -/
theorem eq_of_reduces_normal {u w : Lambda} (hu : Lambda.is_normal u)
    (h : Lambda.reduces u w) : u = w := by
  cases h with
  | refl _ => rfl
  | step _ t₂ _ hstep _ => exact absurd hstep (hu t₂)

/-- **A typable term has exactly one normal form.** -/
theorem exists_unique_normal_form {Γ : List FTy} {t : Lambda} {A : FTy} (h : Typing Γ t A) :
    ∃! u : Lambda, Lambda.reduces t u ∧ Lambda.is_normal u := by
  obtain ⟨u, hu, hnu⟩ := hasNormalForm_of_typing h
  refine ⟨u, ⟨hu, hnu⟩, ?_⟩
  rintro v ⟨hv, hnv⟩
  obtain ⟨w, hw₁, hw₂⟩ := Lambda.confluence_theorem hv hu
  rw [eq_of_reduces_normal hnv hw₁, eq_of_reduces_normal hnu hw₂]

end SystemF
