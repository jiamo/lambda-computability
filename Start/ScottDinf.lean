/-
Scott's `D∞`, step two: the inverse limit of the tower, as an ω-cpo.

`D∞` is the set of *coherent* sequences `x : ∀ n, D n`, those with `prj n (x (n+1)) = x n`,
ordered componentwise.  Suprema of chains are computed componentwise, which makes `D∞` an
ω-complete partial order with a least element.

The main content of this file is the family of finite approximations `theta n x` of an element
`x` of `D∞` — the element that agrees with `x` up to level `n` and is embedded upwards from
level `n` on — and the theorem `ScottDinf.ωSup_thetaChain` that every element of `D∞` is the
supremum of its finite approximations.  This is the key lemma of the inverse-limit
construction.
-/

import Start.ScottTower

set_option relaxedAutoImplicit false
set_option autoImplicit false

open OmegaCompletePartialOrder

namespace ScottDinf

noncomputable section

/-- A sequence is coherent when each level is the projection of the next. -/
def Coherent (x : ∀ n, D n) : Prop := ∀ n, prj n (x (n + 1)) = x n

theorem coherent_ωSup (c : Chain (∀ n, D n)) (h : ∀ i ∈ c, Coherent i) : Coherent (ωSup c) := by
  intro n
  change prj n (ωSup (c.map (Pi.evalOrderHom (n + 1)))) = ωSup (c.map (Pi.evalOrderHom n))
  rw [(prj n).continuous]
  congr 1
  ext i
  exact h (c i) ⟨i, rfl⟩ n

/-- The inverse limit `D∞` of the tower. -/
def Dinf : Type := {x : ∀ n, D n // Coherent x}

instance : OmegaCompletePartialOrder Dinf :=
  OmegaCompletePartialOrder.subtype Coherent coherent_ωSup

namespace Dinf

/-- The `n`-th component of an element of `D∞`. -/
def app (x : Dinf) (n : ℕ) : D n := x.val n

theorem coherent (x : Dinf) (n : ℕ) : prj n (x.app (n + 1)) = x.app n := x.2 n

@[ext] theorem ext {x y : Dinf} (h : ∀ n, x.app n = y.app n) : x = y :=
  Subtype.ext (funext h)

theorem le_def {x y : Dinf} : x ≤ y ↔ ∀ n, x.app n ≤ y.app n := Iff.rfl

/-- The `n`-th component, as a monotone map. -/
def appMono (n : ℕ) : Dinf →o D n where
  toFun x := x.app n
  monotone' _ _ h := h n

@[simp] theorem ωSup_app (c : Chain Dinf) (n : ℕ) :
    (ωSup c).app n = ωSup (c.map (appMono n)) := rfl

/-- The bottom element of `D∞`. -/
def botDinf : Dinf := ⟨fun n => botD n, fun n => prj_botD n⟩

@[simp] theorem botDinf_app (n : ℕ) : botDinf.app n = botD n := rfl

theorem botDinf_le (x : Dinf) : botDinf ≤ x :=
  Dinf.le_def.mpr fun n => botD_le n (x.app n)

end Dinf

------------------------------------------------------------------------
-- Finite approximations
------------------------------------------------------------------------

/-- The components of the `n`-th finite approximation of `x`: below level `n` it agrees with
`x`, above level `n` it is embedded upwards. -/
def approxSeq (n : ℕ) (x : Dinf) : ∀ k, D k
  | 0 => x.app 0
  | (k + 1) => if k + 1 ≤ n then x.app (k + 1) else emb k (approxSeq n x k)

theorem approxSeq_of_le {n k : ℕ} (x : Dinf) (h : k ≤ n) : approxSeq n x k = x.app k := by
  cases k with
  | zero => rfl
  | succ k => simp [approxSeq, h]

theorem approxSeq_of_gt {n k : ℕ} (x : Dinf) (h : ¬ (k + 1 ≤ n)) :
    approxSeq n x (k + 1) = emb k (approxSeq n x k) := by
  simp [approxSeq, h]

theorem approxSeq_coherent (n : ℕ) (x : Dinf) : Coherent (approxSeq n x) := by
  intro k
  by_cases h : k + 1 ≤ n
  · rw [approxSeq_of_le x h, approxSeq_of_le x (by omega : k ≤ n), x.coherent]
  · rw [approxSeq_of_gt x h, prj_emb]

/-- The `n`-th finite approximation of `x`. -/
def theta (n : ℕ) (x : Dinf) : Dinf := ⟨approxSeq n x, approxSeq_coherent n x⟩

@[simp] theorem theta_app (n : ℕ) (x : Dinf) (k : ℕ) :
    (theta n x).app k = approxSeq n x k := rfl

theorem approxSeq_le (n : ℕ) (x : Dinf) : ∀ k, approxSeq n x k ≤ x.app k := by
  intro k
  induction k with
  | zero => exact le_refl _
  | succ k ih =>
      by_cases h : k + 1 ≤ n
      · rw [approxSeq_of_le x h]
      · rw [approxSeq_of_gt x h]
        calc emb k (approxSeq n x k) ≤ emb k (x.app k) := (emb k).monotone ih
          _ = emb k (prj k (x.app (k + 1))) := by rw [x.coherent]
          _ ≤ x.app (k + 1) := emb_prj_le k _

theorem theta_le (n : ℕ) (x : Dinf) : theta n x ≤ x := fun k => approxSeq_le n x k

theorem approxSeq_mono {n m : ℕ} (h : n ≤ m) (x : Dinf) :
    ∀ k, approxSeq n x k ≤ approxSeq m x k := by
  intro k
  induction k with
  | zero => exact le_refl _
  | succ k ih =>
      by_cases hn : k + 1 ≤ n
      · rw [approxSeq_of_le x hn, approxSeq_of_le x (by omega : k + 1 ≤ m)]
      · by_cases hm : k + 1 ≤ m
        · rw [approxSeq_of_gt x hn, approxSeq_of_le x hm]
          calc emb k (approxSeq n x k) ≤ emb k (x.app k) := (emb k).monotone (approxSeq_le n x k)
            _ = emb k (prj k (x.app (k + 1))) := by rw [x.coherent]
            _ ≤ x.app (k + 1) := emb_prj_le k _
        · rw [approxSeq_of_gt x hn, approxSeq_of_gt x hm]
          exact (emb k).monotone ih

theorem theta_mono {n m : ℕ} (h : n ≤ m) (x : Dinf) : theta n x ≤ theta m x :=
  fun k => approxSeq_mono h x k

/-- The chain of finite approximations of `x`. -/
def thetaChain (x : Dinf) : Chain Dinf where
  toFun n := theta n x
  monotone' _ _ h := theta_mono h x

/-- **Every element of `D∞` is the supremum of its finite approximations.** -/
theorem ωSup_thetaChain (x : Dinf) : ωSup (thetaChain x) = x := by
  ext k
  rw [Dinf.ωSup_app]
  refine le_antisymm (ωSup_le _ _ ?_) ?_
  · intro i
    exact approxSeq_le i x k
  · refine le_ωSup_of_le k ?_
    exact le_of_eq (approxSeq_of_le x (le_refl k)).symm

end

end ScottDinf
