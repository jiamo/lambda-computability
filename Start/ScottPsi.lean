/-
Scott's `D∞`, step three: the embeddings of the levels into the limit.

For each `n` this file constructs a continuous map `psi n : D n →𝒄 D∞` which is a section of
the projection `x ↦ x.app n`: it sends `z` to the least element of the limit whose `n`-th
component is `z` (below level `n` it projects `z` down, above level `n` it embeds `z` up).

Main results:

* `ScottDinf.psi_app_self` — `(psi n z).app n = z`;
* `ScottDinf.psi_app_le`   — `psi n (x.app n) ≤ x`, so `(psi n, · .app n)` is an ep-pair
  between `D n` and `D∞`;
* `ScottDinf.psi_theta`    — `psi n (x.app n) = theta n x`, identifying the finite
  approximations of `Start/ScottDinf.lean` with the image of the embedding.
-/

import Start.ScottDinf

set_option relaxedAutoImplicit false
set_option autoImplicit false

open OmegaCompletePartialOrder

namespace ScottDinf

noncomputable section

/-- Transport along an equality of levels. -/
def castD {a b : ℕ} (h : a = b) (x : D a) : D b := h ▸ x

@[simp] theorem castD_self {a : ℕ} (h : a = a) (x : D a) : castD h x = x := rfl

theorem castD_mono {a b : ℕ} (h : a = b) {x y : D a} (hxy : x ≤ y) : castD h x ≤ castD h y := by
  cases h; exact hxy

/-- The components *below* level `n` of the embedding of `z : D n`: iterated projections.
Above level `n` the value is junk (the least element); the definition is only used for
`k ≤ n`. -/
def downSeq : ∀ (n : ℕ) (_z : D n) (k : ℕ), D k
  | 0, z, 0 => z
  | 0, _, (k + 1) => botD (k + 1)
  | (n + 1), z, 0 => downSeq n (prj n z) 0
  | (n + 1), z, (k + 1) =>
      if _ : k + 1 ≤ n then downSeq n (prj n z) (k + 1)
      else if h2 : k = n then castD (congrArg (fun m => m + 1) h2.symm) z
      else botD (k + 1)

@[simp] theorem downSeq_zero_zero (z : D 0) : downSeq 0 z 0 = z := rfl

theorem downSeq_succ_zero (n : ℕ) (z : D (n + 1)) :
    downSeq (n + 1) z 0 = downSeq n (prj n z) 0 := rfl

theorem downSeq_succ_of_le {n k : ℕ} (z : D (n + 1)) (h : k + 1 ≤ n) :
    downSeq (n + 1) z (k + 1) = downSeq n (prj n z) (k + 1) := by
  simp [downSeq, h]

theorem downSeq_succ_diag (n : ℕ) (z : D (n + 1)) :
    downSeq (n + 1) z (n + 1) = z := by
  simp [downSeq]

theorem downSeq_self : ∀ (n : ℕ) (z : D n), downSeq n z n = z
  | 0, _ => rfl
  | (n + 1), z => downSeq_succ_diag n z

/-- Below the level, `downSeq` steps down by one projection. -/
theorem prj_downSeq : ∀ (n k : ℕ) (z : D n), k + 1 ≤ n →
    prj k (downSeq n z (k + 1)) = downSeq n z k := by
  intro n
  induction n with
  | zero => intro k z h; omega
  | succ n ih =>
      intro k z h
      by_cases hk : k + 1 ≤ n
      · rw [downSeq_succ_of_le z hk]
        cases k with
        | zero =>
            rw [downSeq_succ_zero]
            exact ih 0 (prj n z) hk
        | succ j =>
            rw [downSeq_succ_of_le z (by omega : j + 1 ≤ n)]
            exact ih (j + 1) (prj n z) hk
      · have hkn : k = n := by omega
        subst hkn
        rw [downSeq_succ_diag]
        cases k with
        | zero => rw [downSeq_succ_zero, downSeq_self]
        | succ j =>
            rw [downSeq_succ_of_le z (by omega : j + 1 ≤ j + 1), downSeq_self]

theorem downSeq_mono : ∀ (n : ℕ) (k : ℕ) {z z' : D n}, z ≤ z' → downSeq n z k ≤ downSeq n z' k := by
  intro n
  induction n with
  | zero =>
      intro k z z' h
      cases k with
      | zero => exact h
      | succ k => exact le_refl _
  | succ n ih =>
      intro k z z' h
      cases k with
      | zero =>
          rw [downSeq_succ_zero, downSeq_succ_zero]
          exact ih 0 ((prj n).monotone h)
      | succ j =>
          by_cases hj : j + 1 ≤ n
          · rw [downSeq_succ_of_le z hj, downSeq_succ_of_le z' hj]
            exact ih (j + 1) ((prj n).monotone h)
          · by_cases hj2 : j = n
            · subst hj2
              rw [downSeq_succ_diag, downSeq_succ_diag]
              exact h
            · simp [downSeq, hj, hj2]

/-- The components of the embedding of `z : D n` into the limit. -/
def psiSeq (n : ℕ) (z : D n) : ∀ k, D k
  | 0 => downSeq n z 0
  | (k + 1) => if k + 1 ≤ n then downSeq n z (k + 1) else emb k (psiSeq n z k)

theorem psiSeq_of_le {n k : ℕ} (z : D n) (h : k ≤ n) : psiSeq n z k = downSeq n z k := by
  cases k with
  | zero => rfl
  | succ j => simp [psiSeq, h]

theorem psiSeq_of_gt {n k : ℕ} (z : D n) (h : ¬ (k + 1 ≤ n)) :
    psiSeq n z (k + 1) = emb k (psiSeq n z k) := by
  simp [psiSeq, h]

theorem psiSeq_coherent (n : ℕ) (z : D n) : Coherent (psiSeq n z) := by
  intro k
  by_cases h : k + 1 ≤ n
  · rw [psiSeq_of_le z h, psiSeq_of_le z (by omega : k ≤ n)]
    exact prj_downSeq n k z h
  · rw [psiSeq_of_gt z h, prj_emb]

/-- The embedding of level `n` into the limit. -/
def psiFun (n : ℕ) (z : D n) : Dinf := ⟨psiSeq n z, psiSeq_coherent n z⟩

@[simp] theorem psiFun_app (n : ℕ) (z : D n) (k : ℕ) : (psiFun n z).app k = psiSeq n z k := rfl

theorem psiSeq_self (n : ℕ) (z : D n) : psiSeq n z n = z := by
  rw [psiSeq_of_le z (le_refl n), downSeq_self]

/-- The embedding is a section of the `n`-th projection. -/
@[simp] theorem psiFun_app_self (n : ℕ) (z : D n) : (psiFun n z).app n = z := psiSeq_self n z

theorem psiSeq_mono (n : ℕ) {z z' : D n} (h : z ≤ z') : ∀ k, psiSeq n z k ≤ psiSeq n z' k := by
  intro k
  induction k with
  | zero => exact downSeq_mono n 0 h
  | succ k ih =>
      by_cases hk : k + 1 ≤ n
      · rw [psiSeq_of_le z hk, psiSeq_of_le z' hk]
        exact downSeq_mono n (k + 1) h
      · rw [psiSeq_of_gt z hk, psiSeq_of_gt z' hk]
        exact (emb k).monotone ih

theorem psiFun_mono (n : ℕ) : Monotone (psiFun n) := fun _ _ h => fun k => psiSeq_mono n h k

------------------------------------------------------------------------
-- Comparison with the finite approximations
------------------------------------------------------------------------

theorem downSeq_app (x : Dinf) : ∀ (n k : ℕ), k ≤ n → downSeq n (x.app n) k = x.app k := by
  intro n
  induction n with
  | zero => intro k h; interval_cases k; rfl
  | succ n ih =>
      intro k h
      cases k with
      | zero =>
          rw [downSeq_succ_zero, x.coherent]
          exact ih 0 (Nat.zero_le n)
      | succ j =>
          by_cases hj : j + 1 ≤ n
          · rw [downSeq_succ_of_le _ hj, x.coherent]
            exact ih (j + 1) hj
          · have : j + 1 = n + 1 := by omega
            have hj2 : j = n := by omega
            subst hj2
            rw [downSeq_succ_diag]

theorem psiSeq_app (x : Dinf) (n : ℕ) : ∀ k, psiSeq n (x.app n) k = approxSeq n x k := by
  intro k
  induction k with
  | zero =>
      change downSeq n (x.app n) 0 = x.app 0
      exact downSeq_app x n 0 (Nat.zero_le n)
  | succ k ih =>
      by_cases hk : k + 1 ≤ n
      · rw [psiSeq_of_le _ hk, downSeq_app x n (k + 1) hk, approxSeq_of_le x hk]
      · rw [psiSeq_of_gt _ hk, approxSeq_of_gt x hk, ih]

/-- The embedding of the `n`-th component of `x` is the `n`-th finite approximation of `x`. -/
theorem psi_theta (n : ℕ) (x : Dinf) : psiFun n (x.app n) = theta n x := by
  ext k
  exact psiSeq_app x n k

------------------------------------------------------------------------
-- Continuity
------------------------------------------------------------------------

/-- Taking the `n`-th component is continuous. -/
theorem ωScottContinuous_app (n : ℕ) : ωScottContinuous (fun x : Dinf => x.app n) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  exact ⟨fun _ _ h => h n, fun c => rfl⟩

/-- A map into the limit is continuous as soon as all its components are. -/
theorem ωScottContinuous_of_app {A : Type} [OmegaCompletePartialOrder A] {g : A → Dinf}
    (h : ∀ n, ωScottContinuous (fun a => (g a).app n)) : ωScottContinuous g := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun a b hab n => (h n).monotone hab, ?_⟩
  intro c
  ext n
  rw [Dinf.ωSup_app]
  have := (h n).map_ωSup c
  refine this.trans ?_
  congr 1

theorem ωScottContinuous_downSeq : ∀ (n k : ℕ),
    ωScottContinuous (fun z : D n => downSeq n z k) := by
  intro n
  induction n with
  | zero =>
      intro k
      cases k with
      | zero => exact ωScottContinuous.id
      | succ k => exact ωScottContinuous.const
  | succ n ih =>
      intro k
      cases k with
      | zero =>
          exact (ih 0).comp (prj n).ωScottContinuous
      | succ j =>
          by_cases hj : j + 1 ≤ n
          · have : (fun z : D (n + 1) => downSeq (n + 1) z (j + 1))
                = fun z : D (n + 1) => downSeq n (prj n z) (j + 1) := by
              funext z
              exact downSeq_succ_of_le z hj
            rw [this]
            exact (ih (j + 1)).comp (prj n).ωScottContinuous
          · by_cases hj2 : j = n
            · subst hj2
              have : (fun z : D (j + 1) => downSeq (j + 1) z (j + 1)) = id := by
                funext z
                exact downSeq_succ_diag j z
              rw [this]
              exact ωScottContinuous.id
            · have : (fun z : D (n + 1) => downSeq (n + 1) z (j + 1))
                  = fun _ : D (n + 1) => botD (j + 1) := by
                funext z
                simp [downSeq, hj, hj2]
              rw [this]
              exact ωScottContinuous.const

theorem ωScottContinuous_psiSeq (n : ℕ) : ∀ k,
    ωScottContinuous (fun z : D n => psiSeq n z k) := by
  intro k
  induction k with
  | zero => exact ωScottContinuous_downSeq n 0
  | succ k ih =>
      by_cases hk : k + 1 ≤ n
      · have : (fun z : D n => psiSeq n z (k + 1)) = fun z : D n => downSeq n z (k + 1) := by
          funext z
          exact psiSeq_of_le z hk
        rw [this]
        exact ωScottContinuous_downSeq n (k + 1)
      · have : (fun z : D n => psiSeq n z (k + 1))
            = fun z : D n => emb k (psiSeq n z k) := by
          funext z
          exact psiSeq_of_gt z hk
        rw [this]
        exact (emb k).ωScottContinuous.comp ih

/-- The embedding of level `n` into the limit, as a continuous map. -/
def psi (n : ℕ) : D n →𝒄 Dinf :=
  ContinuousHom.ofFun (psiFun n) (ωScottContinuous_of_app fun k => ωScottContinuous_psiSeq n k)

@[simp] theorem psi_apply (n : ℕ) (z : D n) : psi n z = psiFun n z := rfl

/-- The embedding followed by the projection is below the identity. -/
theorem psi_app_le (n : ℕ) (x : Dinf) : psiFun n (x.app n) ≤ x := by
  rw [psi_theta]
  exact theta_le n x

end

end ScottDinf
