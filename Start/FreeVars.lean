/-
Free variables: the structural bound `Lambda.freeBelow` and its stability properties.

`Start/SelfInterpreter.lean` defines `Lambda.freeBelow k t` ("every free variable of `t` is
`< k`").  This file collects the closure properties of the notion — several of them were
previously proved inside `Start/BohmOut.lean` and are shared from here — and adds the fact that
**reduction does not create free variables**:

* `Lambda.freeBelow_mono`, `Lambda.freeBelow_lift`, `Lambda.freeBelow_subst`;
* `Lambda.isClosedAt_of_freeBelow`, `Lambda.isClosed_of_freeBelow_zero`,
  `Lambda.freeBelow_zero_iff_isClosed` — so `freeBelow 0` and `IsClosed` agree;
* `Lambda.freeBelow_lamN_iff`, `Lambda.freeBelow_appList_iff` — the free variables of an iterated
  abstraction and of an application to a list of arguments;
* `Lambda.freeBelow_step`, `Lambda.freeBelow_reduces`, `Lambda.IsClosed.reduces` — a reduct of a
  closed term is closed.
-/

import Start.Bohm
import Start.SelfInterpreter

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-! ## Structural closedness helpers -/

theorem freeBelow_mono : ∀ {t : Lambda} {k l : ℕ}, k ≤ l → freeBelow k t → freeBelow l t := by
  intro t
  induction t with
  | var n => intro k l hkl h; exact lt_of_lt_of_le h hkl
  | app a b iha ihb => intro k l hkl h; exact ⟨iha hkl h.1, ihb hkl h.2⟩
  | lam t ih => intro k l hkl h; exact ih (Nat.succ_le_succ hkl) h

theorem freeBelow_lift : ∀ {t : Lambda} {k : ℕ}, freeBelow k t → ∀ j,
    freeBelow (k + 1) (Lambda.lift 1 j t) := by
  intro t
  induction t with
  | var n =>
      intro k h j
      by_cases hn : n < j
      · simp only [Lambda.lift, if_pos hn]
        exact Nat.lt_succ_of_lt h
      · simp only [Lambda.lift, if_neg hn]
        exact Nat.succ_lt_succ h
  | app a b iha ihb => intro k h j; exact ⟨iha h.1 j, ihb h.2 j⟩
  | lam t ih => intro k h j; exact ih (k := k + 1) h (j + 1)

theorem isClosedAt_of_freeBelow :
    ∀ {t : Lambda} {k : ℕ}, freeBelow k t → Lambda.IsClosedAt t k := by
  intro t
  induction t with
  | var n =>
      intro k h
      exact Lambda.IsClosedAt_var n k h
  | app a b iha ihb => intro k h; exact Lambda.IsClosedAt_app (iha h.1) (ihb h.2)
  | lam t ih => intro k h; exact Lambda.IsClosedAt_lam (ih h)

theorem isClosed_of_freeBelow_zero {t : Lambda} (h : freeBelow 0 t) : Lambda.IsClosed t :=
  (Lambda.IsClosedAt_zero_iff_IsClosed t).1 (isClosedAt_of_freeBelow h)

theorem freeBelow_lamN_iff : ∀ (n : ℕ) {t : Lambda} {k : ℕ},
    freeBelow k (lamN n t) ↔ freeBelow (k + n) t := by
  intro n
  induction n with
  | zero => intro t k; simp
  | succ n ih =>
      intro t k
      rw [lamN_succ]
      change freeBelow (k + 1) (lamN n t) ↔ _
      rw [ih (k := k + 1), show k + 1 + n = k + (n + 1) from by omega]

theorem freeBelow_lamN (n : ℕ) {t : Lambda} {k : ℕ} (h : freeBelow (k + n) t) :
    freeBelow k (lamN n t) := (freeBelow_lamN_iff n).2 h

theorem freeBelow_appList_iff : ∀ (l : List Lambda) {t : Lambda} {k : ℕ},
    freeBelow k (appList t l) ↔ freeBelow k t ∧ ∀ a ∈ l, freeBelow k a := by
  intro l
  induction l with
  | nil => intro t k; simp [appList]
  | cons a l ih =>
      intro t k
      rw [appList_cons, ih]
      constructor
      · rintro ⟨⟨ht, ha⟩, hl⟩
        refine ⟨ht, ?_⟩
        intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact ha
        · exact hl b hb
      · rintro ⟨ht, hl⟩
        exact ⟨⟨ht, hl a List.mem_cons_self⟩,
          fun b hb => hl b (List.mem_cons_of_mem a hb)⟩

theorem freeBelow_appList (l : List Lambda) {t : Lambda} {k : ℕ} (ht : freeBelow k t)
    (hl : ∀ a ∈ l, freeBelow k a) : freeBelow k (appList t l) :=
  (freeBelow_appList_iff l).2 ⟨ht, hl⟩

/-! ## Parallel substitution by closed terms -/

/-! ## Substitution and reduction -/

/-- Substitution of a term with free variables `< k` into a term with free variables `< k+1`. -/
theorem freeBelow_subst : ∀ (t : Lambda) (s : Lambda) (x k : ℕ), freeBelow (k + 1) t →
    freeBelow k s → x ≤ k → freeBelow k (Lambda.subst s x t) := by
  intro t
  induction t with
  | var m =>
      intro s x k h hs hx
      by_cases h1 : m = x
      · simpa [Lambda.subst, h1] using hs
      · by_cases h2 : m > x
        · simp only [Lambda.subst, h1, h2, if_false, if_true, freeBelow]
          simp only [freeBelow] at h
          omega
        · simp only [Lambda.subst, h1, h2, if_false, freeBelow]
          omega
  | app a b iha ihb =>
      intro s x k h hs hx
      exact ⟨iha s x k h.1 hs hx, ihb s x k h.2 hs hx⟩
  | lam u ih =>
      intro s x k h hs hx
      exact ih (Lambda.lift 1 0 s) (x + 1) (k + 1) h (freeBelow_lift hs 0) (Nat.succ_le_succ hx)

theorem freeBelow_zero_iff_isClosed (t : Lambda) : freeBelow 0 t ↔ Lambda.IsClosed t :=
  ⟨isClosed_of_freeBelow_zero, freeBelow_zero_of_isClosed⟩

/-- Reduction does not create free variables. -/
theorem freeBelow_step {t t' : Lambda} (h : Lambda.step t t') :
    ∀ k : ℕ, freeBelow k t → freeBelow k t' := by
  induction h with
  | beta t₁ t₂ =>
      intro k h
      exact freeBelow_subst t₁ t₂ 0 k h.1 h.2 (Nat.zero_le k)
  | app_left _ _ _ _ ih => intro k h; exact ⟨ih k h.1, h.2⟩
  | app_right _ _ _ _ ih => intro k h; exact ⟨h.1, ih k h.2⟩
  | lam _ _ _ ih => intro k h; exact ih (k + 1) h

theorem freeBelow_reduces {t t' : Lambda} (h : Lambda.reduces t t') :
    ∀ k : ℕ, freeBelow k t → freeBelow k t' := by
  induction h with
  | refl _ => exact fun _ h => h
  | step _ _ _ hs _ ih => exact fun k h => ih k (freeBelow_step hs k h)

/-- A reduct of a closed term is closed. -/
theorem IsClosed.reduces {t t' : Lambda} (hcl : Lambda.IsClosed t) (h : Lambda.reduces t t') :
    Lambda.IsClosed t' :=
  isClosed_of_freeBelow_zero (freeBelow_reduces h 0 (freeBelow_zero_of_isClosed hcl))

end Lambda
