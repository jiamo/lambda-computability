/-
Bounded free variables in `λΠ`, and the fact that convertible substitutions act convertibly on
terms whose free variables are bounded.

These are the two facts needed to build the *syntactic category* of `Start/LambdaPiCat.lean`,
whose morphisms are substitutions taken up to conversion: composition is only well defined
because a well-typed term over `Γ` mentions no variable beyond the length of `Γ`.

* `LambdaPi.Bnd k t` — every free variable of `t` is `< k`;
* `LambdaPi.Typing.bnd` — a term typable in `Γ`, and its type, are bounded by `Γ.length`;
* `LambdaPi.conv_subst_congr` — substitutions that are convertible on the relevant variables
  give convertible results.
-/

import Start.LambdaPiTyping

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

/-- `Bnd k t` says that all free variables of `t` are smaller than `k`. -/
def Bnd : ℕ → Tm → Prop
  | k, Tm.var n => n < k
  | _, Tm.sort _ => True
  | k, Tm.app f a => Bnd k f ∧ Bnd k a
  | k, Tm.lam A b => Bnd k A ∧ Bnd (k + 1) b
  | k, Tm.pi A B => Bnd k A ∧ Bnd (k + 1) B

@[simp] theorem Bnd_var (k n : ℕ) : Bnd k (Tm.var n) ↔ n < k := Iff.rfl
@[simp] theorem Bnd_sort (k : ℕ) (s : Srt) : Bnd k (Tm.sort s) := trivial
@[simp] theorem Bnd_app (k : ℕ) (f a : Tm) : Bnd k (Tm.app f a) ↔ Bnd k f ∧ Bnd k a := Iff.rfl
@[simp] theorem Bnd_lam (k : ℕ) (A b : Tm) :
    Bnd k (Tm.lam A b) ↔ Bnd k A ∧ Bnd (k + 1) b := Iff.rfl
@[simp] theorem Bnd_pi (k : ℕ) (A B : Tm) :
    Bnd k (Tm.pi A B) ↔ Bnd k A ∧ Bnd (k + 1) B := Iff.rfl

theorem Bnd.mono {k m : ℕ} {t : Tm} (h : Bnd k t) (hk : k ≤ m) : Bnd m t := by
  induction t generalizing k m with
  | var n => exact lt_of_lt_of_le h hk
  | sort s => trivial
  | app f a ihf iha => exact ⟨ihf h.1 hk, iha h.2 hk⟩
  | lam A b ihA ihb => exact ⟨ihA h.1 hk, ihb h.2 (by omega)⟩
  | pi A B ihA ihB => exact ⟨ihA h.1 hk, ihB h.2 (by omega)⟩

theorem Bnd.rename {k m : ℕ} {ρ : ℕ → ℕ} {t : Tm} (h : Bnd k t) (hρ : ∀ n, n < k → ρ n < m) :
    Bnd m (LambdaPi.rename ρ t) := by
  induction t generalizing k m ρ with
  | var n => exact hρ n h
  | sort s => trivial
  | app f a ihf iha => exact ⟨ihf h.1 hρ, iha h.2 hρ⟩
  | lam A b ihA ihb =>
      refine ⟨ihA h.1 hρ, ihb h.2 ?_⟩
      intro n hn
      cases n with
      | zero => simp [upr]
      | succ n => exact Nat.succ_lt_succ (hρ n (by omega))
  | pi A B ihA ihB =>
      refine ⟨ihA h.1 hρ, ihB h.2 ?_⟩
      intro n hn
      cases n with
      | zero => simp [upr]
      | succ n => exact Nat.succ_lt_succ (hρ n (by omega))

theorem Bnd.shift {k : ℕ} {t : Tm} (h : Bnd k t) : Bnd (k + 1) (shift t) :=
  h.rename (fun n hn => by omega)

theorem Bnd.subst {k m : ℕ} {σ : ℕ → Tm} {t : Tm} (h : Bnd k t)
    (hσ : ∀ n, n < k → Bnd m (σ n)) : Bnd m (LambdaPi.subst σ t) := by
  induction t generalizing k m σ with
  | var n => exact hσ n h
  | sort s => trivial
  | app f a ihf iha => exact ⟨ihf h.1 hσ, iha h.2 hσ⟩
  | lam A b ihA ihb =>
      refine ⟨ihA h.1 hσ, ihb h.2 ?_⟩
      intro n hn
      cases n with
      | zero => simp
      | succ n => exact (hσ n (by omega)).shift
  | pi A B ihA ihB =>
      refine ⟨ihA h.1 hσ, ihB h.2 ?_⟩
      intro n hn
      cases n with
      | zero => simp
      | succ n => exact (hσ n (by omega)).shift

theorem Bnd.inst {k : ℕ} {t a : Tm} (ht : Bnd (k + 1) t) (ha : Bnd k a) : Bnd k (t[a]) := by
  refine ht.subst ?_
  intro n hn
  cases n with
  | zero => exact ha
  | succ n => exact (by omega : n < k)

theorem Lookup.lt {Γ : Ctx} {n : ℕ} {A : Tm} (h : Lookup Γ n A) : n < Γ.length := by
  induction h with
  | zero Γ A => simp
  | succ B _ ih => simpa using Nat.succ_lt_succ ih

/-- Every entry of the context only mentions the variables to its right. -/
def CtxBnd : Ctx → Prop
  | [] => True
  | A :: Γ => Bnd Γ.length A ∧ CtxBnd Γ

theorem Lookup.bnd {Γ : Ctx} (hΓ : CtxBnd Γ) {n : ℕ} {A : Tm} (h : Lookup Γ n A) :
    Bnd Γ.length A := by
  induction h with
  | zero Γ A => simpa using (hΓ.1).shift
  | succ B _ ih =>
      rename_i Γ' n' A' _
      simpa using (ih hΓ.2).shift

/-- A typable term and its type only mention variables of the context. -/
theorem Typing.bnd {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) :
    CtxBnd Γ → Bnd Γ.length t ∧ Bnd Γ.length A := by
  induction h with
  | ax Γ => intro _; exact ⟨trivial, trivial⟩
  | var hA => intro hΓ; exact ⟨hA.lt, hA.bnd hΓ⟩
  | @pi Γ A B s t hr hA hB ihA ihB =>
      intro hΓ
      have h₁ := ihA hΓ
      have h₂ := ihB ⟨by simpa using h₁.1, hΓ⟩
      exact ⟨⟨h₁.1, by simpa using h₂.1⟩, trivial⟩
  | @lam Γ A B b s hP hb ihP ihb =>
      intro hΓ
      have h₁ := ihP hΓ
      have hA : Bnd Γ.length A := h₁.1.1
      have h₂ := ihb ⟨hA, hΓ⟩
      exact ⟨⟨hA, by simpa using h₂.1⟩, h₁.1⟩
  | @app Γ f a A B hf ha ihf iha =>
      intro hΓ
      have h₁ := ihf hΓ
      have h₂ := iha hΓ
      exact ⟨⟨h₁.1, h₂.1⟩, Bnd.inst h₁.2.2 h₂.1⟩
  | conv _ _ _ iht ihB =>
      intro hΓ
      exact ⟨(iht hΓ).1, (ihB hΓ).1⟩

theorem Wf.ctxBnd {Γ : Ctx} (h : Wf Γ) : CtxBnd Γ := by
  induction h with
  | nil => trivial
  | @cons Γ A s hΓ hA ih => exact ⟨(hA.bnd ih).1, ih⟩

/-- A term typable in a well-formed context only mentions variables of that context. -/
theorem Typing.bnd_of_wf {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) (hΓ : Wf Γ) :
    Bnd Γ.length t ∧ Bnd Γ.length A :=
  h.bnd hΓ.ctxBnd

/-- Substitutions that are convertible on the free variables of `t` act convertibly on `t`. -/
theorem conv_subst_congr {k : ℕ} {σ τ : ℕ → Tm} {t : Tm} (ht : Bnd k t)
    (h : ∀ n, n < k → Conv (σ n) (τ n)) : Conv (LambdaPi.subst σ t) (LambdaPi.subst τ t) := by
  induction t generalizing k σ τ with
  | var n => exact h n ht
  | sort s => exact Conv.refl _
  | app f a ihf iha => exact Conv.app (ihf ht.1 h) (iha ht.2 h)
  | lam A b ihA ihb =>
      refine Conv.lam (ihA ht.1 h) (ihb ht.2 ?_)
      intro n hn
      cases n with
      | zero => exact Conv.refl _
      | succ n => exact (h n (by omega)).rename Nat.succ
  | pi A B ihA ihB =>
      refine Conv.pi (ihA ht.1 h) (ihB ht.2 ?_)
      intro n hn
      cases n with
      | zero => exact Conv.refl _
      | succ n => exact (h n (by omega)).rename Nat.succ

end LambdaPi
