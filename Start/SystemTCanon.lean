/-
Subject reduction and canonicity for Gödel's System T.

`Start/SystemT.lean` proves strong normalization: every typable term has a normal form.  That
alone does not say *which* normal form: a priori a closed term of type `nat` could normalize to
something that is not a numeral.  This file closes that gap.

* `GodelT.typing_weaken` / `GodelT.typing_subst` — the two structural lemmas about the typing
  relation (weakening and substitution);
* `GodelT.typing_step` / `GodelT.typing_reduces` — **subject reduction**: reduction preserves
  types;
* `GodelT.eq_num_of_closed_normal` — a closed normal form of type `nat` is a numeral;
* `GodelT.exists_reduces_num` — **canonicity**: every closed term of type `nat` reduces to a
  numeral.  Together with strong normalization this makes every closed System T term of type
  `nat → nat` a genuine total function `ℕ → ℕ`, which is the proof-theoretic content of Gödel's
  system (its definable functions are exactly the provably total functions of Peano arithmetic).
* `GodelT.reduces_addTm` — a concrete instance: the term `addTm` represents addition.
-/

import Start.SystemT

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GodelT

------------------------------------------------------------------------
-- Reflexive transitive closure of reduction
------------------------------------------------------------------------

theorem reduces.trans {t u v : Tm} (h : reduces t u) (h' : reduces u v) : reduces t v := by
  induction h with
  | refl _ => exact h'
  | step hs _ ih => exact reduces.step hs (ih h')

theorem reduces_succ {t u : Tm} (h : reduces t u) : reduces (Tm.succ t) (Tm.succ u) := by
  induction h with
  | refl _ => exact reduces.refl _
  | step hs _ ih => exact reduces.step (step.succ _ _ hs) ih

------------------------------------------------------------------------
-- Weakening
------------------------------------------------------------------------

/-- **Weakening.** Inserting a new variable into the context, and lifting the term accordingly,
preserves typing. -/
theorem typing_weaken {Γ : List Ty} {t : Tm} {A : Ty} (h : Typing Γ t A) :
    ∀ (Γ₁ Γ₂ : List Ty) (B : Ty), Γ = Γ₁ ++ Γ₂ →
      Typing (Γ₁ ++ B :: Γ₂) (lift 1 Γ₁.length t) A := by
  induction h with
  | @var Γ i A hi =>
      rintro Γ₁ Γ₂ B rfl
      by_cases hik : i < Γ₁.length
      · simp only [lift, if_pos hik]
        refine Typing.var ?_
        rw [List.getElem?_append_left hik]
        rw [List.getElem?_append_left hik] at hi
        exact hi
      · have hge : Γ₁.length ≤ i := Nat.le_of_not_lt hik
        rw [List.getElem?_append_right hge] at hi
        simp only [lift, hik, if_false]
        refine Typing.var ?_
        rw [List.getElem?_append_right (by omega)]
        have : i + 1 - Γ₁.length = (i - Γ₁.length) + 1 := by omega
        rw [this, List.getElem?_cons_succ]
        exact hi
  | @app Γ a b A B _ _ iha ihb =>
      rintro Γ₁ Γ₂ C rfl
      exact Typing.app (iha Γ₁ Γ₂ C rfl) (ihb Γ₁ Γ₂ C rfl)
  | @lam Γ t A B _ ih =>
      rintro Γ₁ Γ₂ C rfl
      refine Typing.lam ?_
      have := ih (A :: Γ₁) Γ₂ C rfl
      simpa [lift] using this
  | zero => rintro Γ₁ Γ₂ B rfl; exact Typing.zero
  | @succ Γ t _ ih =>
      rintro Γ₁ Γ₂ B rfl
      exact Typing.succ (ih Γ₁ Γ₂ B rfl)
  | @natrec Γ z f n A _ _ _ ihz ihf ihn =>
      rintro Γ₁ Γ₂ B rfl
      exact Typing.natrec (ihz Γ₁ Γ₂ B rfl) (ihf Γ₁ Γ₂ B rfl) (ihn Γ₁ Γ₂ B rfl)

/-- Weakening by a whole block of variables at the front of the context. -/
theorem typing_weaken_list {Γ₂ : List Ty} {v : Tm} {B : Ty} (h : Typing Γ₂ v B) :
    ∀ Γ₁ : List Ty, Typing (Γ₁ ++ Γ₂) (lift Γ₁.length 0 v) B := by
  intro Γ₁
  induction Γ₁ with
  | nil => simpa [lift_zero] using h
  | cons C Γ₁ ih =>
      have := typing_weaken ih [] (Γ₁ ++ Γ₂) C rfl
      have hlift : lift 1 0 (lift Γ₁.length 0 v) = lift (Γ₁.length + 1) 0 v := by
        rw [Nat.add_comm, lift_add]
      simpa [hlift] using this

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

/-- **Substitution preserves typing.** -/
theorem typing_subst {Γ : List Ty} {t : Tm} {A : Ty} (h : Typing Γ t A) :
    ∀ (Γ₁ Γ₂ : List Ty) (B : Ty) (v : Tm), Γ = Γ₁ ++ B :: Γ₂ → Typing Γ₂ v B →
      Typing (Γ₁ ++ Γ₂) (subst (lift Γ₁.length 0 v) Γ₁.length t) A := by
  induction h with
  | @var Γ i A hi =>
      rintro Γ₁ Γ₂ B v rfl hv
      rcases lt_trichotomy i Γ₁.length with hlt | heq | hgt
      · rw [List.getElem?_append_left hlt] at hi
        have : i ≠ Γ₁.length := by omega
        simp only [subst, this, if_false, Nat.not_lt.mpr (le_of_lt hlt)]
        exact Typing.var (by rw [List.getElem?_append_left hlt]; exact hi)
      · subst heq
        rw [List.getElem?_append_right (le_refl _)] at hi
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        simp only [subst]
        exact typing_weaken_list hv Γ₁
      · rw [List.getElem?_append_right (by omega)] at hi
        have h1 : i - Γ₁.length = (i - Γ₁.length - 1) + 1 := by omega
        rw [h1, List.getElem?_cons_succ] at hi
        simp only [subst, if_neg (by omega : i ≠ Γ₁.length), gt_iff_lt, if_pos hgt]
        refine Typing.var ?_
        rw [List.getElem?_append_right (by omega)]
        have h2 : i - 1 - Γ₁.length = i - Γ₁.length - 1 := by omega
        rw [h2]
        exact hi
  | @app Γ a b A B _ _ iha ihb =>
      rintro Γ₁ Γ₂ C v rfl hv
      exact Typing.app (iha Γ₁ Γ₂ C v rfl hv) (ihb Γ₁ Γ₂ C v rfl hv)
  | @lam Γ t A B _ ih =>
      rintro Γ₁ Γ₂ C v rfl hv
      refine Typing.lam ?_
      have := ih (A :: Γ₁) Γ₂ C v rfl hv
      have hlift : lift (A :: Γ₁).length 0 v = lift 1 0 (lift Γ₁.length 0 v) := by
        simp only [List.length_cons]
        rw [Nat.add_comm, lift_add]
      rw [hlift] at this
      simpa [subst] using this
  | zero => rintro Γ₁ Γ₂ B v rfl hv; exact Typing.zero
  | @succ Γ t _ ih =>
      rintro Γ₁ Γ₂ B v rfl hv
      exact Typing.succ (ih Γ₁ Γ₂ B v rfl hv)
  | @natrec Γ z f n A _ _ _ ihz ihf ihn =>
      rintro Γ₁ Γ₂ B v rfl hv
      exact Typing.natrec (ihz Γ₁ Γ₂ B v rfl hv) (ihf Γ₁ Γ₂ B v rfl hv) (ihn Γ₁ Γ₂ B v rfl hv)

/-- Substitution for the variable `0`, the form used by β-reduction. -/
theorem typing_subst_zero {Γ : List Ty} {t v : Tm} {A B : Ty}
    (h : Typing (B :: Γ) t A) (hv : Typing Γ v B) : Typing Γ (subst v 0 t) A := by
  have := typing_subst h [] Γ B v rfl hv
  simpa [lift_zero] using this

------------------------------------------------------------------------
-- Subject reduction
------------------------------------------------------------------------

/-- **Subject reduction.** A single reduction step preserves the type. -/
theorem typing_step {Γ : List Ty} {t : Tm} {A : Ty} (h : Typing Γ t A) :
    ∀ t', step t t' → Typing Γ t' A := by
  induction h with
  | var hi => intro t' hs; cases hs
  | @app Γ a b A B ha _ iha ihb =>
      intro t' hs
      cases hs with
      | beta s c => cases ha with
        | lam hs' => exact typing_subst_zero hs' ‹Typing Γ b A›
      | appL _ a' _ hst => exact Typing.app (iha a' hst) ‹Typing Γ b A›
      | appR _ _ b' hst => exact Typing.app ha (ihb b' hst)
  | @lam Γ t A B _ ih =>
      intro t' hs
      cases hs with
      | lam _ s' hst => exact Typing.lam (ih s' hst)
  | zero => intro t' hs; cases hs
  | @succ Γ t _ ih =>
      intro t' hs
      cases hs with
      | succ _ s' hst => exact Typing.succ (ih s' hst)
  | @natrec Γ z f n A hz hf hn ihz ihf ihn =>
      intro t' hs
      cases hs with
      | recZero _ _ => exact hz
      | recSucc _ _ m =>
          cases hn with
          | succ hm => exact Typing.app (Typing.app hf hm) (Typing.natrec hz hf hm)
      | recL _ z' _ _ hst => exact Typing.natrec (ihz z' hst) hf hn
      | recM _ _ f' _ hst => exact Typing.natrec hz (ihf f' hst) hn
      | recR _ _ _ n' hst => exact Typing.natrec hz hf (ihn n' hst)

/-- Subject reduction for arbitrarily many steps. -/
theorem typing_reduces {Γ : List Ty} {t u : Tm} {A : Ty} (h : Typing Γ t A)
    (hr : reduces t u) : Typing Γ u A := by
  induction hr with
  | refl _ => exact h
  | step hs _ ih => exact ih (typing_step h _ hs)

------------------------------------------------------------------------
-- Canonicity
------------------------------------------------------------------------

theorem IsNormal.app_left {a b : Tm} (h : IsNormal (Tm.app a b)) : IsNormal a :=
  fun _ ha' => h _ (step.appL _ _ _ ha')

theorem IsNormal.succ_arg {t : Tm} (h : IsNormal (Tm.succ t)) : IsNormal t :=
  fun _ ht' => h _ (step.succ _ _ ht')

theorem IsNormal.natrec_arg {z f n : Tm} (h : IsNormal (Tm.natrec z f n)) : IsNormal n :=
  fun _ hn' => h _ (step.recR _ _ _ _ hn')

/-- The canonical shape of a closed normal form at a given type. -/
def Canon : Ty → Tm → Prop
  | Ty.nat, t => ∃ n, t = num n
  | Ty.arrow _ _, t => ∃ s, t = Tm.lam s

theorem canon_of_typing_aux {Γ : List Ty} {t : Tm} {A : Ty} (h : Typing Γ t A) :
    Γ = [] → IsNormal t → Canon A t := by
  induction h with
  | @var Γ i A hi => rintro rfl _; simp at hi
  | @app Γ a b A B _ _ iha _ =>
      intro hΓ hn
      obtain ⟨s, rfl⟩ := iha hΓ hn.app_left
      exact absurd (step.beta s b) (hn _)
  | lam _ => intro _ _; exact ⟨_, rfl⟩
  | zero => intro _ _; exact ⟨0, rfl⟩
  | @succ Γ t _ ih =>
      intro hΓ hn
      obtain ⟨n, rfl⟩ := ih hΓ hn.succ_arg
      exact ⟨n + 1, rfl⟩
  | @natrec Γ z f n A _ _ _ _ _ ihn =>
      intro hΓ hn
      obtain ⟨k, rfl⟩ := ihn hΓ hn.natrec_arg
      cases k with
      | zero => exact absurd (step.recZero z f) (hn _)
      | succ k => exact absurd (step.recSucc z f (num k)) (hn _)

/-- A closed normal form of type `nat` is a numeral. -/
theorem eq_num_of_closed_normal {t : Tm} (h : Typing [] t Ty.nat) (hn : IsNormal t) :
    ∃ n, t = num n := canon_of_typing_aux h rfl hn

/-- A closed normal form of a function type is an abstraction. -/
theorem eq_lam_of_closed_normal {t : Tm} {A B : Ty} (h : Typing [] t (Ty.arrow A B))
    (hn : IsNormal t) : ∃ s, t = Tm.lam s := canon_of_typing_aux h rfl hn

/-- **Canonicity for System T.** Every closed term of type `nat` reduces to a numeral. -/
theorem exists_reduces_num {t : Tm} (h : Typing [] t Ty.nat) : ∃ n, reduces t (num n) := by
  obtain ⟨u, hu, hnu⟩ := hasNormalForm_of_typing h
  obtain ⟨n, rfl⟩ := eq_num_of_closed_normal (typing_reduces h hu) hnu
  exact ⟨n, hu⟩

/-- Every closed System T term of type `nat → nat` denotes a total function: on each numeral
input it reduces to a numeral output. -/
theorem exists_reduces_num_app {t : Tm} (h : Typing [] t (Ty.arrow Ty.nat Ty.nat)) (m : ℕ) :
    ∃ n, reduces (Tm.app t (num m)) (num n) :=
  exists_reduces_num (Typing.app h (typing_num [] m))

------------------------------------------------------------------------
-- Representability: `addTm` computes addition
------------------------------------------------------------------------

theorem lift_num (k x : ℕ) (n : ℕ) : lift k x (num n) = num n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [num, lift, ih]

theorem subst_num (v : Tm) (x : ℕ) (n : ℕ) : subst v x (num n) = num n := by
  induction n generalizing v x with
  | zero => rfl
  | succ n ih => simp [num, subst, ih]

theorem reduces_natrec_num (m n : ℕ) :
    reduces (Tm.natrec (num n) (Tm.lam (Tm.lam (Tm.succ (Tm.var 0)))) (num m)) (num (m + n)) := by
  induction m with
  | zero => rw [Nat.zero_add]; exact reduces.step (step.recZero _ _) (reduces.refl _)
  | succ m ih =>
      refine reduces.step (step.recSucc _ _ _) ?_
      refine reduces.step (step.appL _ _ _ (step.beta _ _)) ?_
      have h1 : subst (num m) 0 (Tm.lam (Tm.succ (Tm.var 0)))
          = Tm.lam (Tm.succ (Tm.var 0)) := by simp [subst]
      rw [h1]
      refine reduces.step (step.beta _ _) ?_
      have h2 : subst (Tm.natrec (num n) (Tm.lam (Tm.lam (Tm.succ (Tm.var 0)))) (num m)) 0
            (Tm.succ (Tm.var 0))
          = Tm.succ (Tm.natrec (num n) (Tm.lam (Tm.lam (Tm.succ (Tm.var 0)))) (num m)) := by
        simp [subst]
      rw [h2]
      have hmn : m + 1 + n = (m + n) + 1 := by omega
      rw [hmn]
      exact reduces_succ ih

/-- **`addTm` represents addition**: applied to the numerals of `m` and `n` it reduces to the
numeral of `m + n`. -/
theorem reduces_addTm (m n : ℕ) :
    reduces (Tm.app (Tm.app addTm (num m)) (num n)) (num (m + n)) := by
  refine reduces.step (step.appL _ _ _ (step.beta _ _)) ?_
  have h1 : subst (num m) 0
      (Tm.lam (Tm.natrec (Tm.var 0) (Tm.lam (Tm.lam (Tm.succ (Tm.var 0)))) (Tm.var 1)))
      = Tm.lam (Tm.natrec (Tm.var 0) (Tm.lam (Tm.lam (Tm.succ (Tm.var 0)))) (num m)) := by
    simp [subst, lift_num]
  rw [h1]
  refine reduces.step (step.beta _ _) ?_
  have h2 : subst (num n) 0
      (Tm.natrec (Tm.var 0) (Tm.lam (Tm.lam (Tm.succ (Tm.var 0)))) (num m))
      = Tm.natrec (num n) (Tm.lam (Tm.lam (Tm.succ (Tm.var 0)))) (num m) := by
    simp [subst, subst_num]
  rw [h2]
  exact reduces_natrec_num m n

end GodelT
