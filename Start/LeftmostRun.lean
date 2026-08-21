/-
Running the leftmost-outermost strategy for a fixed number of steps.

`Start/Leftmost.lean` proves that the normal order strategy is normalizing.  What the
complexity-theoretic developments need on top of that is a *clock*: a total, primitive recursive
"run for `k` steps" function, together with the fact that a term has a normal form exactly when
some finite run reaches one.

* `Lambda.nstep` is the leftmost step made total (normal forms are fixed points), and
  `Lambda.nstep_code` arithmetizes it (`Lambda.nstep_code_primrec`).
* `Lambda.hasNormalForm_iff_exists_normal_iterate` — `t` has a normal form iff `nstep^[k] t` is
  normal for some `k`; `Lambda.haltTime t` is the least such `k`, and
  `Lambda.nf t` the normal form itself.
* `Lambda.isNormal_code` and `Lambda.haltsBy_code` are the primitive recursive tests "this code
  is a normal form" and "this code reaches a normal form within `k` leftmost steps".
* `Lambda.hasNormalForm_lam` — a `λ`-abstraction normalizes iff its body does, which lets one
  replace an arbitrary term by a *closed* one with the same halting behaviour
  (`Lambda.hasNormalForm_closure_iff`).
-/

import Start.CodeArith
import Start.Leftmost
import Start.NormalizationUndecidable

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- The total leftmost step
------------------------------------------------------------------------

/-- One leftmost-outermost reduction step, made total: normal forms are fixed. -/
def nstep (t : Lambda) : Lambda := (Lambda.step_normal t).getD t

/-- The code-level total leftmost step. -/
def nstep_code (c : ℕ) : ℕ := (Lambda.code_step' c).getD c

theorem nstep_code_primrec : Primrec nstep_code := by
  have h : Primrec (fun c : ℕ => (Lambda.code_step' c).getD c) :=
    Primrec.option_getD.comp Lambda.code_step'_primrec Primrec.id
  exact h

@[simp] theorem nstep_code_correct (t : Lambda) :
    nstep_code (Lambda.encode t) = Lambda.encode (nstep t) := by
  rw [nstep_code, nstep, Lambda.code_step'_eq_step_normal]
  cases Lambda.step_normal t <;> rfl

theorem nstep_code_iterate (t : Lambda) (k : ℕ) :
    nstep_code^[k] (Lambda.encode t) = Lambda.encode (nstep^[k] t) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      nstep_code_correct, ih]

theorem nstep_code_iterate_primrec : Primrec₂ (fun c k : ℕ => nstep_code^[k] c) := by
  have hstep : Primrec₂ (fun (_ : ℕ) (p : ℕ × ℕ) => nstep_code p.2) :=
    nstep_code_primrec.comp (Primrec.snd.comp Primrec.snd)
  have h := Primrec.nat_rec (f := fun c : ℕ => c) (g := fun (_ : ℕ) (p : ℕ × ℕ) => nstep_code p.2)
    Primrec.id hstep
  refine h.of_eq (fun c k => ?_)
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ← ih]

/-- A term reduces to its leftmost successor. -/
theorem reduces_nstep (t : Lambda) : Lambda.reduces t (nstep t) := by
  rcases hs : Lambda.step_normal t with _ | t'
  · rw [show nstep t = t by simp [nstep, hs]]
    exact Lambda.reduces.refl t
  · have : nstep t = t' := by simp [nstep, hs]
    rw [this]
    exact Lambda.reduces.step _ _ _ (step_of_step_normal hs) (Lambda.reduces.refl _)

theorem reduces_nstep_iterate (t : Lambda) (k : ℕ) : Lambda.reduces t (nstep^[k] t) := by
  induction k generalizing t with
  | zero => simpa using Lambda.reduces.refl t
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      exact Lambda.reduces_trans (reduces_nstep t) (ih _)

theorem nstep_of_is_normal {t : Lambda} (h : Lambda.is_normal t) : nstep t = t := by
  simp [nstep, step_normal_eq_none_of_is_normal h]

theorem nstep_iterate_of_is_normal {t : Lambda} (h : Lambda.is_normal t) (k : ℕ) :
    nstep^[k] t = t := Function.iterate_fixed (nstep_of_is_normal h) k

/-- Once the run has reached a normal form it stays there. -/
theorem nstep_iterate_stable {t : Lambda} {k : ℕ} (h : Lambda.is_normal (nstep^[k] t))
    {j : ℕ} (hj : k ≤ j) : nstep^[j] t = nstep^[k] t := by
  obtain ⟨d, rfl⟩ : ∃ d, j = k + d := ⟨j - k, by omega⟩
  rw [Nat.add_comm, Function.iterate_add_apply, nstep_iterate_of_is_normal h]

/-- The leftmost run realises every leftmost reduction sequence. -/
theorem exists_iterate_of_nred {t u : Lambda} (h : NRed t u) : ∃ k, nstep^[k] t = u := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbu ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      rw [Function.iterate_succ_apply', hk]
      simp [nstep, hbu]

/-- **The leftmost run detects normalization.** -/
theorem hasNormalForm_iff_exists_normal_iterate (t : Lambda) :
    HasNormalForm t ↔ ∃ k, Lambda.is_normal (nstep^[k] t) := by
  constructor
  · rintro ⟨u, hu, hnu⟩
    obtain ⟨k, hk⟩ := exists_iterate_of_nred (nred_of_reduces_normal u hnu t hu)
    exact ⟨k, by rw [hk]; exact hnu⟩
  · rintro ⟨k, hk⟩
    exact ⟨nstep^[k] t, reduces_nstep_iterate t k, hk⟩

/-- The number of leftmost steps a normalizing term takes to reach its normal form. -/
def haltTime (t : Lambda) : ℕ := sInf {k | Lambda.is_normal (nstep^[k] t)}

theorem is_normal_nstep_haltTime {t : Lambda} (h : HasNormalForm t) :
    Lambda.is_normal (nstep^[haltTime t] t) :=
  Nat.sInf_mem ((hasNormalForm_iff_exists_normal_iterate t).1 h)

theorem haltTime_le {t : Lambda} {k : ℕ} (h : Lambda.is_normal (nstep^[k] t)) :
    haltTime t ≤ k := Nat.sInf_le h

/-- The normal form reached by the leftmost run. -/
def nf (t : Lambda) : Lambda := nstep^[haltTime t] t

theorem reduces_nf (t : Lambda) : Lambda.reduces t (nf t) := reduces_nstep_iterate t _

theorem nf_eq_of_reduces_normal {t u : Lambda} (h : Lambda.reduces t u)
    (hu : Lambda.is_normal u) : nf t = u := by
  have hnf : Lambda.is_normal (nf t) := is_normal_nstep_haltTime ⟨u, h, hu⟩
  obtain ⟨v, hv1, hv2⟩ := Lambda.confluence_theorem (reduces_nf t) h
  rw [Lambda.reduces_normal_eq hnf hv1, Lambda.reduces_normal_eq hu hv2]

------------------------------------------------------------------------
-- Primitive recursive halting tests
------------------------------------------------------------------------

/-- **Progress**: if the leftmost strategy has no step to make, the term is a normal form.
(The converse is `Lambda.step_normal_eq_none_of_is_normal`.) -/
theorem is_normal_of_step_normal_eq_none :
    ∀ {t : Lambda}, Lambda.step_normal t = none → Lambda.is_normal t := by
  intro t
  induction t with
  | var n => intro _; exact Lambda.var_normal n
  | lam u ih =>
      intro h
      rw [step_normal_lam] at h
      rcases hu : Lambda.step_normal u with _ | u'
      · exact Lambda.lam_normal (ih hu)
      · rw [hu] at h; simp at h
  | app a b iha ihb =>
      intro h
      cases a with
      | lam P => rw [step_normal_beta] at h; simp at h
      | var n =>
          rw [step_normal_app_of_ne_lam (by simp)] at h
          rcases ha : Lambda.step_normal (Lambda.var n) with _ | a'
          · rcases hb : Lambda.step_normal b with _ | b'
            · exact Lambda.app_normal (iha ha) (ihb hb) (by simp)
            · rw [ha, hb] at h; simp at h
          · rw [ha] at h; simp at h
      | app c d =>
          rw [step_normal_app_of_ne_lam (by simp)] at h
          rcases ha : Lambda.step_normal (Lambda.app c d) with _ | a'
          · rcases hb : Lambda.step_normal b with _ | b'
            · exact Lambda.app_normal (iha ha) (ihb hb) (by simp)
            · rw [ha, hb] at h; simp at h
          · rw [ha] at h; simp at h

/-- The primitive recursive test "this code is the code of a normal form". -/
def isNormal_code (c : ℕ) : Bool := decide (Lambda.code_step' c = none)

theorem isNormal_code_primrec : Primrec isNormal_code := by
  have h : PrimrecPred (fun c : ℕ => Lambda.code_step' c = none) :=
    Primrec.eq.comp Lambda.code_step'_primrec (Primrec.const none)
  obtain ⟨_inst, h⟩ := h
  exact h.of_eq (fun c => by simp [isNormal_code])

@[simp] theorem isNormal_code_correct (t : Lambda) :
    isNormal_code (Lambda.encode t) = Bool.true ↔ Lambda.is_normal t := by
  rw [isNormal_code, Lambda.code_step'_eq_step_normal]
  constructor
  · intro h
    rcases hs : Lambda.step_normal t with _ | t'
    · exact is_normal_of_step_normal_eq_none hs
    · rw [hs] at h; simp at h
  · intro h
    rw [step_normal_eq_none_of_is_normal h]
    simp

/-- The primitive recursive test "this code reaches a normal form within `k` leftmost steps". -/
def haltsBy_code (c k : ℕ) : Bool := isNormal_code (nstep_code^[k] c)

theorem haltsBy_code_primrec : Primrec₂ haltsBy_code :=
  isNormal_code_primrec.comp nstep_code_iterate_primrec

@[simp] theorem haltsBy_code_correct (t : Lambda) (k : ℕ) :
    haltsBy_code (Lambda.encode t) k = Bool.true ↔ Lambda.is_normal (nstep^[k] t) := by
  rw [haltsBy_code, nstep_code_iterate, isNormal_code_correct]

theorem hasNormalForm_iff_exists_haltsBy_code (t : Lambda) :
    HasNormalForm t ↔ ∃ k, haltsBy_code (Lambda.encode t) k = Bool.true := by
  simp [hasNormalForm_iff_exists_normal_iterate]

------------------------------------------------------------------------
-- Closing a term off
------------------------------------------------------------------------

theorem is_normal_lam {u : Lambda} (h : Lambda.is_normal u) : Lambda.is_normal (Lambda.lam u) := by
  intro t' hstep
  cases hstep with
  | lam _ t' hst => exact h t' hst

/-- A `λ`-abstraction normalizes exactly when its body does. -/
theorem hasNormalForm_lam (u : Lambda) : HasNormalForm (Lambda.lam u) ↔ HasNormalForm u := by
  constructor
  · rintro ⟨v, hv, hnv⟩
    obtain ⟨N, rfl, hN⟩ := reduces_lam_shape hv
    exact ⟨N, hN, is_normal_of_lam hnv⟩
  · rintro ⟨v, hv, hnv⟩
    exact ⟨Lambda.lam v, Lambda.reduces_lam hv, is_normal_lam hnv⟩

/-- Closing a term off with `k` abstractions. -/
def closure : ℕ → Lambda → Lambda
  | 0, t => t
  | (k + 1), t => Lambda.lam (closure k t)

theorem hasNormalForm_closure_iff (k : ℕ) (t : Lambda) :
    HasNormalForm (closure k t) ↔ HasNormalForm t := by
  induction k with
  | zero => rfl
  | succ k ih => rw [closure, hasNormalForm_lam, ih]

theorem freeMax_closure (k : ℕ) (t : Lambda) : freeMax (closure k t) = freeMax t - k := by
  induction k generalizing t with
  | zero => simp [closure]
  | succ k ih => rw [closure, freeMax_lam, ih]; omega

/-- Closing a term off with `freeMax t` abstractions makes it closed. -/
theorem isClosed_closure (t : Lambda) : IsClosed (closure (freeMax t) t) := by
  rw [isClosed_iff_freeMax_eq_zero, freeMax_closure]
  omega

end Lambda

end
