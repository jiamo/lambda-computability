/-
Joint Kolmogorov complexity and the easy half of symmetry of information.

The *joint* complexity of a pair `(x, y)` is the complexity `K (Nat.pair x y)` of its code under
Mathlib's pairing bijection.  This module relates it to the plain and conditional complexities of
the components, using the lambda terms `Lambda.natPair'`, `Lambda.unpairLeft_impl` and
`Lambda.unpairRight_impl` from `Start/Combinators.lean` (with their correctness theorems from
`Start/Pairing.lean` and closedness from `Start/Realizer.lean`).

* `Lambda.kolm_apply_le` — a realizer of a total function raises complexity by at most an
  additive constant: `K (f n) ≤ K n + size F + 1`.
* `Lambda.exists_const_kolm_pair_le` — **`K(x, y) ≤ K(y) + K(x | y) + O(1)`**: a description of
  `y` together with a description of `x` given `y` describes the pair.  This is the (easy,
  constant-overhead) half of the Kolmogorov–Levin symmetry-of-information estimate; the converse
  `K(y) + K(x | y) ≤ K(x, y) + O(log)` genuinely needs the logarithmic term and is not proved
  here.
* `Lambda.exists_const_kolm_pair_le_add` — subadditivity `K(x, y) ≤ K(x) + K(y) + O(1)`.
* `Lambda.exists_const_kolm_fst_le` / `Lambda.exists_const_kolm_snd_le` — the components are no
  more complex than the pair, `K(x) ≤ K(x, y) + O(1)` and `K(y) ≤ K(x, y) + O(1)`.
* `Lambda.exists_const_kolmCond_of_pair` — `K(x | ⟨x, y⟩) ≤ O(1)`: the pair determines its
  components with constant conditional complexity.
-/

import Start.KolmogorovCond
import Start.Realizer

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Applying a realizer costs an additive constant
------------------------------------------------------------------------

/-- Feeding a shortest program for `n` to a realizer `F` of a total function `f` gives a program
for `f n`, so `K (f n) ≤ K n + size F + 1`. -/
theorem kolm_apply_le {F : Lambda} {f : ℕ → ℕ} (hF : Realizes F f) (n : ℕ) :
    kolm (f n) ≤ kolm n + size F + 1 := by
  obtain ⟨p, hp, hps⟩ := exists_program_of_kolm n
  have hclosed : Lambda.IsClosed (Lambda.app F p) := Lambda.IsClosed_app hF.1 hp.1
  have hred : Lambda.reduces (Lambda.app F p) (Lambda.church (f n)) :=
    Lambda.reduces_trans (Lambda.reduces_app_right (t1 := F) hp.2) (hF.2 n)
  have := kolm_le_of_isProgramFor (t := Lambda.app F p) (s := f n) ⟨hclosed, hred⟩
  simp only [size_app] at this
  omega

/-- Likewise for conditional complexity: `K (f n | y) ≤ K(n | y) + size F + 4`, the witness being
`λw. F (t w)`. -/
theorem kolmCond_apply_le {F : Lambda} {f : ℕ → ℕ} (hF : Realizes F f) (n y : ℕ) :
    kolmCond (f n) y ≤ kolmCond n y + size F + 4 := by
  obtain ⟨t, ht, hts⟩ := exists_condProgram_of_kolmCond n y
  set c : Lambda := Lambda.lam (Lambda.app F (Lambda.app t (Lambda.var 0))) with hc
  have hcclosed : Lambda.IsClosed c := by
    intro a x
    have hexp : Lambda.subst a x c =
        Lambda.lam (Lambda.app (Lambda.subst (Lambda.lift 1 0 a) (x + 1) F)
          (Lambda.app (Lambda.subst (Lambda.lift 1 0 a) (x + 1) t)
            (Lambda.subst (Lambda.lift 1 0 a) (x + 1) (Lambda.var 0)))) := rfl
    have hv : Lambda.subst (Lambda.lift 1 0 a) (x + 1) (Lambda.var 0) = Lambda.var 0 := by
      simp [Lambda.subst]
    rw [hexp, hF.1, ht.1, hv]
  have hcred : Lambda.reduces (Lambda.app c (Lambda.church y)) (Lambda.church (f n)) := by
    refine Lambda.reduces.step _ _ _
      (Lambda.step.beta (Lambda.app F (Lambda.app t (Lambda.var 0))) (Lambda.church y)) ?_
    have hsub : Lambda.subst (Lambda.church y) 0 (Lambda.app F (Lambda.app t (Lambda.var 0)))
        = Lambda.app F (Lambda.app t (Lambda.church y)) := by
      have hexp : Lambda.subst (Lambda.church y) 0 (Lambda.app F (Lambda.app t (Lambda.var 0))) =
          Lambda.app (Lambda.subst (Lambda.church y) 0 F)
            (Lambda.app (Lambda.subst (Lambda.church y) 0 t)
              (Lambda.subst (Lambda.church y) 0 (Lambda.var 0))) := rfl
      have hv : Lambda.subst (Lambda.church y) 0 (Lambda.var 0) = Lambda.church y := by
        simp [Lambda.subst]
      rw [hexp, hF.1, ht.1, hv]
    rw [hsub]
    exact Lambda.reduces_trans (Lambda.reduces_app_right (t1 := F) ht.2) (hF.2 n)
  have := kolmCond_le_of_isCondProgramFor (t := c) (s := f n) (y := y) ⟨hcclosed, hcred⟩
  simp only [hc, size_lam, size_app, size_var] at this
  omega

------------------------------------------------------------------------
-- The components are no more complex than the pair
------------------------------------------------------------------------

theorem exists_const_kolm_fst_le : ∃ c : ℕ, ∀ x y : ℕ, kolm x ≤ kolm (Nat.pair x y) + c := by
  refine ⟨size Lambda.unpairLeft_impl + 1, fun x y => ?_⟩
  have h := kolm_apply_le Realizes.left (Nat.pair x y)
  simpa [Nat.unpair_pair, Nat.add_assoc] using h

theorem exists_const_kolm_snd_le : ∃ c : ℕ, ∀ x y : ℕ, kolm y ≤ kolm (Nat.pair x y) + c := by
  refine ⟨size Lambda.unpairRight_impl + 1, fun x y => ?_⟩
  have h := kolm_apply_le Realizes.right (Nat.pair x y)
  simpa [Nat.unpair_pair, Nat.add_assoc] using h

/-- Given the pair, its first component has constant conditional complexity. -/
theorem exists_const_kolmCond_of_pair :
    ∃ c : ℕ, ∀ x y : ℕ, kolmCond x (Nat.pair x y) ≤ c := by
  refine ⟨size Lambda.unpairLeft_impl + 6, fun x y => ?_⟩
  have h := kolmCond_apply_le Realizes.left (Nat.pair x y) (Nat.pair x y)
  have h2 := kolmCond_self_le_two (Nat.pair x y)
  simp only [Nat.unpair_pair] at h
  omega

------------------------------------------------------------------------
-- The easy half of symmetry of information
------------------------------------------------------------------------

/-- **`K(x, y) ≤ K(y) + K(x | y) + O(1)`.**  The witness is `(λw. natPair' (t w) w) p`, where `p`
is a shortest program for `y` and `t` a shortest conditional program for `x` given `y`; sharing
the single occurrence of `p` is what keeps the overhead constant. -/
theorem exists_const_kolm_pair_le :
    ∃ c : ℕ, ∀ x y : ℕ, kolm (Nat.pair x y) ≤ kolmCond x y + kolm y + c := by
  refine ⟨size Lambda.natPair' + 7, fun x y => ?_⟩
  obtain ⟨t, ht, hts⟩ := exists_condProgram_of_kolmCond x y
  obtain ⟨p, hp, hps⟩ := exists_program_of_kolm y
  set b : Lambda :=
    Lambda.app (Lambda.app Lambda.natPair' (Lambda.app t (Lambda.var 0))) (Lambda.var 0) with hb
  set c : Lambda := Lambda.lam b with hc
  have hcclosed : Lambda.IsClosed c := by
    intro a k
    have hexp : Lambda.subst a k c =
        Lambda.lam (Lambda.app (Lambda.app
            (Lambda.subst (Lambda.lift 1 0 a) (k + 1) Lambda.natPair')
            (Lambda.app (Lambda.subst (Lambda.lift 1 0 a) (k + 1) t)
              (Lambda.subst (Lambda.lift 1 0 a) (k + 1) (Lambda.var 0))))
          (Lambda.subst (Lambda.lift 1 0 a) (k + 1) (Lambda.var 0))) := rfl
    have hv : Lambda.subst (Lambda.lift 1 0 a) (k + 1) (Lambda.var 0) = Lambda.var 0 := by
      simp [Lambda.subst]
    rw [hexp, natPair'_closed, ht.1, hv]
  -- the composite is closed and computes the pair
  have hclosed : Lambda.IsClosed (Lambda.app c p) := Lambda.IsClosed_app hcclosed hp.1
  have hxred : Lambda.reduces (Lambda.app t p) (Lambda.church x) :=
    Lambda.reduces_trans (Lambda.reduces_app_right (t1 := t) hp.2) ht.2
  have hred : Lambda.reduces (Lambda.app c p) (Lambda.church (Nat.pair x y)) := by
    refine Lambda.reduces.step _ _ _ (Lambda.step.beta b p) ?_
    have hsub : Lambda.subst p 0 b =
        Lambda.app (Lambda.app Lambda.natPair' (Lambda.app t p)) p := by
      have hexp : Lambda.subst p 0 b =
          Lambda.app (Lambda.app (Lambda.subst p 0 Lambda.natPair')
              (Lambda.app (Lambda.subst p 0 t) (Lambda.subst p 0 (Lambda.var 0))))
            (Lambda.subst p 0 (Lambda.var 0)) := rfl
      have hv : Lambda.subst p 0 (Lambda.var 0) = p := by simp [Lambda.subst]
      rw [hexp, natPair'_closed, ht.1, hv]
    rw [hsub]
    refine Lambda.reduces_trans
      (Lambda.reduces_app_left (t2 := p) (Lambda.reduces_app_right
        (t1 := Lambda.natPair') hxred)) ?_
    exact Lambda.reduces_trans
      (Lambda.reduces_app_right (t1 := Lambda.app Lambda.natPair' (Lambda.church x)) hp.2)
      (Lambda.natPair'_works x y)
  have hle := kolm_le_of_isProgramFor
    (t := Lambda.app c p) (s := Nat.pair x y) ⟨hclosed, hred⟩
  simp only [hc, hb, size_app, size_lam, size_var] at hle
  omega

/-- Subadditivity: `K(x, y) ≤ K(x) + K(y) + O(1)`. -/
theorem exists_const_kolm_pair_le_add :
    ∃ c : ℕ, ∀ x y : ℕ, kolm (Nat.pair x y) ≤ kolm x + kolm y + c := by
  obtain ⟨c, hc⟩ := exists_const_kolm_pair_le
  refine ⟨c + 1, fun x y => ?_⟩
  have h1 := hc x y
  have h2 := kolmCond_le_kolm_succ x y
  omega

end Lambda

end
