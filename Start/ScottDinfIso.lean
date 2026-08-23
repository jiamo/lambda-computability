/-
Scott's `D∞`, step four: the isomorphism `D∞ ≅ [D∞ →𝒄 D∞]`.

This is the punchline of the inverse-limit construction: the inverse limit of the tower

  `D 0 = Bool`,  `D (n+1) = [D n →𝒄 D n]`

is isomorphic, as an ω-cpo, to its own continuous function space.  Consequently `D∞` is a
nontrivial reflexive object, and the untyped λ-calculus has a model in it.

Main results:

* `ScottDinf.Phi`   — the application map `D∞ → [D∞ →𝒄 D∞]`;
* `ScottDinf.Psi`   — its inverse;
* `ScottDinf.dinfOrderIso` — `D∞ ≃o (D∞ →𝒄 D∞)`.
-/

import Start.ScottPsi

set_option relaxedAutoImplicit false
set_option autoImplicit false

open OmegaCompletePartialOrder

namespace ScottDinf

noncomputable section

------------------------------------------------------------------------
-- More facts about the embeddings `psi`
------------------------------------------------------------------------

/-- The embedding `psi n` is left adjoint to the `n`-th projection. -/
theorem psi_le_iff {n : ℕ} {z : D n} {w : Dinf} : psiFun n z ≤ w ↔ z ≤ w.app n := by
  constructor
  · intro h
    have h' := Dinf.le_def.mp h n
    rwa [psiFun_app_self] at h'
  · intro h
    calc psiFun n z ≤ psiFun n (w.app n) := psiFun_mono n h
      _ = theta n w := psi_theta n w
      _ ≤ w := theta_le n w

theorem downSeq_succ_le {n k : ℕ} (z : D (n + 1)) (h : k ≤ n) :
    downSeq (n + 1) z k = downSeq n (prj n z) k := by
  cases k with
  | zero => exact downSeq_succ_zero n z
  | succ k => exact downSeq_succ_of_le z h

/-- Below level `n`, embedding from level `n+1` is the same as first projecting down. -/
theorem psi_succ_app_of_le {n k : ℕ} (w : D (n + 1)) (h : k ≤ n) :
    (psiFun (n + 1) w).app k = (psiFun n (prj n w)).app k := by
  rw [psiFun_app, psiFun_app, psiSeq_of_le w (by omega), psiSeq_of_le (prj n w) h,
    downSeq_succ_le w h]

theorem psi_succ_app (n : ℕ) (w : D (n + 1)) : (psiFun (n + 1) w).app n = prj n w := by
  rw [psi_succ_app_of_le w (le_refl n), psiFun_app_self]

/-- The embeddings are compatible with the embeddings of the tower. -/
theorem psi_emb (n : ℕ) (z : D n) : psiFun (n + 1) (emb n z) = psiFun n z := by
  ext k
  induction k with
  | zero => rw [psi_succ_app_of_le _ (Nat.zero_le n), prj_emb]
  | succ k ih =>
      by_cases hk : k + 1 ≤ n
      · rw [psi_succ_app_of_le _ hk, prj_emb]
      · rcases Nat.lt_or_ge n (k + 1) with hlt | hge
        · -- `k ≥ n`
          rcases Nat.eq_or_lt_of_le hlt with heq | hlt2
          · -- `k + 1 = n + 1`
            have hkn : k = n := by omega
            subst hkn
            clear heq hlt hk ih
            rw [psiFun_app, psiFun_app, psiSeq_self, psiSeq_of_gt z (by omega),
              psiSeq_self]
          · -- `k + 1 > n + 1`
            rw [psiFun_app, psiFun_app, psiSeq_of_gt _ (by omega), psiSeq_of_gt z (by omega)]
            rw [← psiFun_app, ← psiFun_app, ih]
        · omega

/-- The finite approximations are monotone in their argument. -/
theorem approxSeq_mono_arg (n : ℕ) {x y : Dinf} (h : x ≤ y) :
    ∀ k, approxSeq n x k ≤ approxSeq n y k := by
  intro k
  induction k with
  | zero => exact Dinf.le_def.mp h 0
  | succ k ih =>
      by_cases hk : k + 1 ≤ n
      · rw [approxSeq_of_le x hk, approxSeq_of_le y hk]
        exact Dinf.le_def.mp h (k + 1)
      · rw [approxSeq_of_gt x hk, approxSeq_of_gt y hk]
        exact (emb k).monotone ih

theorem theta_mono_arg (n : ℕ) {x y : Dinf} (h : x ≤ y) : theta n x ≤ theta n y :=
  fun k => approxSeq_mono_arg n h k

------------------------------------------------------------------------
-- The application map `Φ`
------------------------------------------------------------------------

/-- The level-`n` approximation of the application of `x` to `y`. -/
def mulLevel (x : Dinf) (n : ℕ) : Dinf →𝒄 D n :=
  ContinuousHom.ofFun (fun y : Dinf => toFn (x.app (n + 1)) (y.app n))
    ((toFn (x.app (n + 1))).ωScottContinuous.comp (ωScottContinuous_app n))

@[simp] theorem mulLevel_apply (x : Dinf) (n : ℕ) (y : Dinf) :
    mulLevel x n y = toFn (x.app (n + 1)) (y.app n) := rfl

/-- The approximations of the application increase with the level. -/
theorem mulLevel_le_prj (x : Dinf) (n : ℕ) (y : Dinf) :
    mulLevel x n y ≤ prj n (mulLevel x (n + 1) y) := by
  have hx : x.app (n + 1) = prj (n + 1) (x.app (n + 2)) := (x.coherent (n + 1)).symm
  have hy : emb n (y.app n) ≤ y.app (n + 1) := by
    calc emb n (y.app n) = emb n (prj n (y.app (n + 1))) := by rw [y.coherent]
      _ ≤ y.app (n + 1) := emb_prj_le n _
  calc mulLevel x n y = toFn (prj (n + 1) (x.app (n + 2))) (y.app n) := by
        rw [mulLevel_apply, hx]
    _ = prj n (toFn (x.app (n + 2)) (emb n (y.app n))) := prj_succ_apply n _ _
    _ ≤ prj n (toFn (x.app (n + 2)) (y.app (n + 1))) :=
        (prj n).monotone ((toFn (x.app (n + 2))).monotone hy)
    _ = prj n (mulLevel x (n + 1) y) := rfl

/-- The chain of approximations of the application map of `x`. -/
def appChain (x : Dinf) : Chain (Dinf →𝒄 Dinf) where
  toFun n := (psi n).comp (mulLevel x n)
  monotone' := by
    refine monotone_nat_of_le_succ ?_
    intro n y
    change psiFun n (mulLevel x n y) ≤ psiFun (n + 1) (mulLevel x (n + 1) y)
    rw [psi_le_iff, psi_succ_app]
    exact mulLevel_le_prj x n y

@[simp] theorem appChain_apply (x : Dinf) (n : ℕ) (y : Dinf) :
    appChain x n y = psiFun n (toFn (x.app (n + 1)) (y.app n)) := rfl

/-- **Application in `D∞`**: the continuous map determined by an element of `D∞`. -/
def Phi (x : Dinf) : Dinf →𝒄 Dinf := ωSup (appChain x)

/-- The chain obtained by evaluating a chain of continuous maps at a point. -/
def evalChain (c : Chain (Dinf →𝒄 Dinf)) (y : Dinf) : Chain Dinf where
  toFun n := c n y
  monotone' _ _ h := c.monotone h y

@[simp] theorem evalChain_apply (c : Chain (Dinf →𝒄 Dinf)) (y : Dinf) (n : ℕ) :
    evalChain c y n = c n y := rfl

/-- Evaluating a supremum of continuous maps is computing a supremum pointwise. -/
theorem ωSup_hom_apply (c : Chain (Dinf →𝒄 Dinf)) (y : Dinf) :
    ωSup c y = ωSup (evalChain c y) := rfl

/-- Evaluating `Φ` is computing a supremum pointwise. -/
theorem Phi_apply (x y : Dinf) : Phi x y = ωSup (evalChain (appChain x) y) := rfl

/-- Above level `n`, the terms of the approximating chain all have the same `n`-th
component. -/
theorem appChain_app_of_le (x : Dinf) (n : ℕ) (z : D n) :
    ∀ m, n ≤ m → (appChain x m (psiFun n z)).app n = toFn (x.app (n + 1)) z := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rw [appChain_apply, psiFun_app_self, psiFun_app_self]
  | succ m hm ih =>
      rw [appChain_apply, psi_succ_app_of_le _ hm]
      have hgt : ¬ (m + 1 ≤ n) := by omega
      have hstep : (psiFun n z).app (m + 1) = emb m ((psiFun n z).app m) := by
        rw [psiFun_app, psiFun_app, psiSeq_of_gt z hgt]
      have hprj : prj m (toFn (x.app (m + 2)) ((psiFun n z).app (m + 1)))
          = toFn (x.app (m + 1)) ((psiFun n z).app m) := by
        rw [hstep, ← prj_succ_apply m (x.app (m + 2)) ((psiFun n z).app m), x.coherent (m + 1)]
      rw [hprj]
      exact ih

/-- **The application map computes the expected value on the image of `psi n`.** -/
theorem Phi_app_psi (x : Dinf) (n : ℕ) (z : D n) :
    (Phi x (psiFun n z)).app n = toFn (x.app (n + 1)) z := by
  rw [Phi_apply, Dinf.ωSup_app]
  refine le_antisymm (ωSup_le _ _ ?_) ?_
  · intro m
    change (appChain x m (psiFun n z)).app n ≤ toFn (x.app (n + 1)) z
    rcases Nat.le_total n m with hm | hm
    · exact le_of_eq (appChain_app_of_le x n z m hm)
    · have hle : appChain x m (psiFun n z) ≤ appChain x n (psiFun n z) :=
        (appChain x).monotone hm _
      refine le_trans (Dinf.le_def.mp hle n) ?_
      exact le_of_eq (appChain_app_of_le x n z n (le_refl n))
  · refine le_ωSup_of_le n ?_
    exact le_of_eq (appChain_app_of_le x n z n (le_refl n)).symm

theorem Phi_mono : Monotone Phi := by
  intro x x' h
  refine ωSup_le_ωSup_of_le ?_
  intro n
  refine ⟨n, fun y => ?_⟩
  change psiFun n (toFn (x.app (n + 1)) (y.app n)) ≤ psiFun n (toFn (x'.app (n + 1)) (y.app n))
  exact psiFun_mono n (toFn_le_iff.mp (Dinf.le_def.mp h (n + 1)) _)

------------------------------------------------------------------------
-- The inverse `Ψ`
------------------------------------------------------------------------

/-- The components of the element of `D∞` corresponding to a continuous map. -/
def PsiSeq (f : Dinf →𝒄 Dinf) : ∀ n, D n
  | 0 => (f (psiFun 0 (botD 0))).app 0
  | (n + 1) =>
      ofFn (ContinuousHom.ofFun (fun z : D n => (f (psi n z)).app n)
        ((ωScottContinuous_app n).comp (f.ωScottContinuous.comp (psi n).ωScottContinuous)))

@[simp] theorem PsiSeq_succ (f : Dinf →𝒄 Dinf) (n : ℕ) (z : D n) :
    toFn (PsiSeq f (n + 1)) z = (f (psiFun n z)).app n := rfl

theorem PsiSeq_coherent (f : Dinf →𝒄 Dinf) : Coherent (PsiSeq f) := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
      refine toFn_ext ?_
      intro z
      rw [prj_succ_apply, PsiSeq_succ, psi_emb, PsiSeq_succ]
      exact (f (psiFun n z)).coherent n

/-- **The inverse of application**: the element of `D∞` corresponding to a continuous map. -/
def Psi (f : Dinf →𝒄 Dinf) : Dinf := ⟨PsiSeq f, PsiSeq_coherent f⟩

@[simp] theorem Psi_app (f : Dinf →𝒄 Dinf) (n : ℕ) : (Psi f).app n = PsiSeq f n := rfl

theorem Psi_mono : Monotone Psi := by
  intro f g h
  refine Dinf.le_def.mpr ?_
  intro n
  cases n with
  | zero => exact Dinf.le_def.mp (h (psiFun 0 (botD 0))) 0
  | succ n =>
      rw [toFn_le_iff]
      intro z
      rw [Psi_app, Psi_app, PsiSeq_succ, PsiSeq_succ]
      exact Dinf.le_def.mp (h (psiFun n z)) n

------------------------------------------------------------------------
-- The isomorphism
------------------------------------------------------------------------

theorem Psi_Phi_succ (x : Dinf) (n : ℕ) : (Psi (Phi x)).app (n + 1) = x.app (n + 1) := by
  refine toFn_ext ?_
  intro z
  rw [Psi_app, PsiSeq_succ, Phi_app_psi]

/-- `Ψ` is a left inverse of `Φ`. -/
theorem Psi_Phi (x : Dinf) : Psi (Phi x) = x := by
  ext n
  cases n with
  | zero =>
      rw [← (Psi (Phi x)).coherent 0, Psi_Phi_succ x 0, x.coherent 0]
  | succ n => exact Psi_Phi_succ x n

/-- The diagonal chain of finite approximations used to invert `Φ`. -/
def diagChain (f : Dinf →𝒄 Dinf) (y : Dinf) : Chain Dinf where
  toFun n := theta n (f (theta n y))
  monotone' _ m h :=
    le_trans (theta_mono h _) (theta_mono_arg m (f.monotone (theta_mono h y)))

@[simp] theorem diagChain_apply (f : Dinf →𝒄 Dinf) (y : Dinf) (n : ℕ) :
    diagChain f y n = theta n (f (theta n y)) := rfl

theorem Phi_Psi_apply (f : Dinf →𝒄 Dinf) (y : Dinf) :
    Phi (Psi f) y = ωSup (diagChain f y) := by
  have hchain : evalChain (appChain (Psi f)) y = diagChain f y := by
    have hpt : ∀ n : ℕ, evalChain (appChain (Psi f)) y n = diagChain f y n := by
      intro n
      change psiFun n (toFn ((Psi f).app (n + 1)) (y.app n)) = theta n (f (theta n y))
      rw [Psi_app, PsiSeq_succ, psi_theta, psi_theta]
    ext n k
    exact congrArg (fun w : Dinf => w.app k) (hpt n)
  rw [Phi_apply, hchain]

/-- `Ψ` is a right inverse of `Φ`. -/
theorem Phi_Psi (f : Dinf →𝒄 Dinf) : Phi (Psi f) = f := by
  refine DFunLike.ext _ _ ?_
  intro y
  rw [Phi_Psi_apply]
  refine le_antisymm (ωSup_le _ _ ?_) ?_
  · intro n
    exact le_trans (theta_le n _) (f.monotone (theta_le n y))
  · conv_lhs => rw [← ωSup_thetaChain y, f.continuous]
    refine ωSup_le _ _ ?_
    intro n
    change f (theta n y) ≤ ωSup (diagChain f y)
    conv_lhs => rw [← ωSup_thetaChain (f (theta n y))]
    refine ωSup_le _ _ ?_
    intro m
    change theta m (f (theta n y)) ≤ ωSup (diagChain f y)
    refine le_ωSup_of_le (max m n) ?_
    change theta m (f (theta n y)) ≤ theta (max m n) (f (theta (max m n) y))
    exact le_trans (theta_mono (le_max_left m n) _)
      (theta_mono_arg _ (f.monotone (theta_mono (le_max_right m n) y)))

/-- **Scott's theorem**: `D∞` is isomorphic to its own space of continuous self-maps. -/
def dinfOrderIso : Dinf ≃o (Dinf →𝒄 Dinf) where
  toFun := Phi
  invFun := Psi
  left_inv := Psi_Phi
  right_inv := Phi_Psi
  map_rel_iff' := by
    intro x y
    change Phi x ≤ Phi y ↔ x ≤ y
    exact ⟨fun h => by simpa only [Psi_Phi] using Psi_mono h, fun h => Phi_mono h⟩

@[simp] theorem dinfOrderIso_apply (x : Dinf) : dinfOrderIso x = Phi x := rfl

@[simp] theorem dinfOrderIso_symm_apply (f : Dinf →𝒄 Dinf) : dinfOrderIso.symm f = Psi f := rfl

------------------------------------------------------------------------
-- Consequences
------------------------------------------------------------------------

/-- `Φ` and `Ψ` form a Galois insertion (in fact an isomorphism). -/
theorem Phi_le_iff {x : Dinf} {f : Dinf →𝒄 Dinf} : Phi x ≤ f ↔ x ≤ Psi f := by
  constructor
  · intro h
    have h' := Psi_mono h
    rwa [Psi_Phi] at h'
  · intro h
    have h' := Phi_mono h
    rwa [Phi_Psi] at h'

/-- Application is continuous in the function argument as well. -/
theorem Phi_continuous : ωScottContinuous Phi := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨Phi_mono, fun c => ?_⟩
  refine le_antisymm ?_ (ωSup_le _ _ fun i => Phi_mono (le_ωSup c i))
  rw [Phi_le_iff]
  refine ωSup_le _ _ fun i => ?_
  rw [← Phi_le_iff]
  exact le_ωSup (c.map ⟨Phi, Phi_mono⟩) i

theorem Psi_le_iff {f : Dinf →𝒄 Dinf} {x : Dinf} : Psi f ≤ x ↔ f ≤ Phi x := by
  constructor
  · intro h
    have h' := Phi_mono h
    rwa [Phi_Psi] at h'
  · intro h
    have h' := Psi_mono h
    rwa [Psi_Phi] at h'

/-- Abstraction is continuous. -/
theorem Psi_continuous : ωScottContinuous Psi := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨Psi_mono, fun c => ?_⟩
  refine le_antisymm ?_ (ωSup_le _ _ fun i => Psi_mono (le_ωSup c i))
  rw [Psi_le_iff]
  refine ωSup_le _ _ fun i => ?_
  rw [← Psi_le_iff]
  exact le_ωSup (c.map ⟨Psi, Psi_mono⟩) i

/-- `D∞` has at least two elements, so the model is not degenerate. -/
theorem dinf_nontrivial : ∃ x y : Dinf, x ≠ y := by
  refine ⟨psiFun 0 true, psiFun 0 false, ?_⟩
  intro h
  have h0 : (true : D 0) = (false : D 0) := by
    rw [← psiFun_app_self 0 true, ← psiFun_app_self 0 false, h]
  exact Bool.noConfusion h0

/-- **`D∞` is a reflexive object**: the continuous function space is a retract of `D∞`,
and in fact isomorphic to it. -/
theorem dinf_reflexive : (∀ f : Dinf →𝒄 Dinf, Phi (Psi f) = f) ∧ (∀ x : Dinf, Psi (Phi x) = x) :=
  ⟨Phi_Psi, Psi_Phi⟩

end

end ScottDinf
