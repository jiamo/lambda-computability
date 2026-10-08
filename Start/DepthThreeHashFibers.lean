import Start.DepthThreeHashTriangular
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
directory `lean/OAI/Computability/DepthThree/HashFibers.lean`, family 112,
paper "Beyond the square-root exponent for depth-three Boolean circuits".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.DepthThree*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace DepthThreeLowerBound
namespace BinaryHash

noncomputable section

variable {d r : ℕ}

def hashF2_fiberEquiv (w : Data d) (hw : w ≠ 0) (a : Output r) :
    {u : Seed d r // hashF2 u w = a} ≃ (Nonpivot (r := r) w hw → F2) where
  toFun u := (triangularEquiv (r := r) w hw u.1).2
  invFun b := ⟨(triangularEquiv (r := r) w hw).symm (a, b), by
    rw [← triangularEquiv_fst w hw]
    exact congrArg Prod.fst
      ((triangularEquiv (r := r) w hw).apply_symm_apply (a, b))⟩
  left_inv u := by
    apply Subtype.ext
    apply (triangularEquiv (r := r) w hw).injective
    change (triangularEquiv (r := r) w hw)
      ((triangularEquiv (r := r) w hw).symm
        (a, (triangularEquiv (r := r) w hw u.1).2)) =
      triangularEquiv (r := r) w hw u.1
    rw [Equiv.apply_symm_apply]
    exact Prod.ext ((triangularEquiv_fst w hw u.1).trans u.2).symm rfl
  right_inv b := by
    change ((triangularEquiv (r := r) w hw)
      ((triangularEquiv (r := r) w hw).symm (a, b))).2 = b
    rw [Equiv.apply_symm_apply]

theorem hashF2_fiber_card (w : Data d) (hw : w ≠ 0) (a : Output r) :
    Fintype.card {u : Seed d r // hashF2 u w = a} = 2 ^ (d - 1) := by
  classical
  calc
    Fintype.card {u : Seed d r // hashF2 u w = a} =
        Fintype.card (Nonpivot (r := r) w hw → F2) :=
      Fintype.card_congr (hashF2_fiberEquiv w hw a)
    _ = 2 ^ (d - 1) := by
      change Fintype.card (Nonpivot (r := r) w hw → ZMod 2) = 2 ^ (d - 1)
      rw [Fintype.card_fun, ZMod.card, card_nonpivot (r := r) w hw]

theorem hashF2_surjective (w : Data d) (hw : w ≠ 0) :
    Function.Surjective (fun u : Seed d r => hashF2 u w) := by
  intro a
  let u : {u : Seed d r // hashF2 u w = a} :=
    (hashF2_fiberEquiv w hw a).symm (fun _ => 0)
  exact ⟨u.1, u.2⟩

def hashF2_collisionEquiv (x y : Data d) :
    {u : Seed d r // hashF2 u x = hashF2 u y} ≃
      {u : Seed d r // hashF2 u (x - y) = 0} :=
  Equiv.subtypeEquivRight fun u => by
    rw [hashF2_sub_data, sub_eq_zero]

theorem hashF2_collision_card (x y : Data d) (hxy : x ≠ y) :
    Fintype.card {u : Seed d r // hashF2 u x = hashF2 u y} = 2 ^ (d - 1) := by
  calc
    Fintype.card {u : Seed d r // hashF2 u x = hashF2 u y} =
        Fintype.card {u : Seed d r // hashF2 u (x - y) = 0} :=
      Fintype.card_congr (hashF2_collisionEquiv (r := r) x y)
    _ = 2 ^ (d - 1) :=
      hashF2_fiber_card (x - y) (sub_ne_zero.mpr hxy) 0

end

end BinaryHash
end DepthThreeLowerBound

