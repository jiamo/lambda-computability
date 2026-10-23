import Start.TLCA4Hit5Index
import Start.TLCA4StageGen

/-!
# TLCA open problem 4: the components of a stage pattern have distinct indices
(row M20-TLCA4-BETAETA; big round 2, item A2, rebuilt in run 6 after the move to a new project)

For a stage pattern (`StageS x s g`, `StageG x g`, `Start/TLCA4StageGen.lean`) the components
`gⁿ s` of the stages `s (gⁿ s) W` are pairwise βη-distinct: applied to a fresh variable `y` twice,
`gⁿ s y y` weakly reduces to `x^{n+1} (y …)`, and the `x`-depth of such a term is a βη-invariant
(`XDepth.unique`).

* `toLam_iterX`, `iterT_stage_app` — `gⁿ s y W →w x^{n+1} (y (g y) W')`;
* **`stage_index_unique`** — `gⁿ s =βη gᵐ s` implies `n = m`;
* instances `hit5_comp_index_unique`, `hit6_comp_index_unique`, `hit8_comp_index_unique`.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (betaEtaReduces betaEtaStep)

theorem toLam_iterX (x : ℕ) : ∀ (k : ℕ) (t : Tm), toLam (iterX x k t) = xPow (.var x) k (toLam t)
  | 0, _ => rfl
  | k + 1, t => by
    show Lambda.app (.var x) (toLam (iterX x k t)) = _
    rw [toLam_iterX x k t]; rfl

/-- `gⁿ s Z W →w x^{n+1} (Z (g Z) W')`. -/
theorem iterT_stage_app {x : ℕ} {s g : Tm} (hs : StageS x s g) (hg : StageG x g) (n : ℕ)
    (Z W : Tm) : ∃ W', Relation.ReflTransGen WStep (app (app (iterT g n s) Z) W)
      (iterX x (n + 1) (app (app Z (app g Z)) W')) := by
  obtain ⟨W₁, h₁⟩ := iterT_g_app (s := s) hg n Z W
  obtain ⟨W₂, h₂⟩ := hs Z W₁
  refine ⟨W₂, h₁.trans ?_⟩
  have := rtg_iterX x h₂ n
  rwa [show app (var x) (app (app Z (app g Z)) W₂) = iterX x 1 (app (app Z (app g Z)) W₂) from rfl,
    iterX_add, Nat.add_comm 1 n] at this

/-- `gⁿ s y y` has `x`-depth `n + 1` with head `y = x + 1`. -/
theorem iterT_stage_xdepth {x : ℕ} {s g : Tm} (hs : StageS x s g) (hg : StageG x g) (n : ℕ) :
    XDepth x (x + 1) (n + 1) (toLam (app (app (iterT g n s) (var (x + 1))) (var (x + 1)))) := by
  obtain ⟨W, h⟩ := iterT_stage_app hs hg n (var (x + 1)) (var (x + 1))
  have e := toLam_rtg h
  rw [toLam_iterX] at e
  refine ⟨_, 2, Lambda.betaEtaConv.of_reduces (Lambda.betaEtaReduces.of_reduces e), ?_⟩
  exact .app _ (.app _ (.var _))

/-- **The components of a stage pattern are pairwise βη-distinct.** -/
theorem stage_index_unique {x : ℕ} {s g : Tm} (hs : StageS x s g) (hg : StageG x g) {n m : ℕ}
    (h : Lambda.betaEtaConv (toLam (iterT g n s)) (toLam (iterT g m s))) : n = m := by
  have h1 := iterT_stage_xdepth hs hg n
  have h2 := (iterT_stage_xdepth hs hg m).of_conv (conv_app2 h (.var (x + 1)) (.var (x + 1)))
  have := XDepth.unique (by omega) h1 h2
  omega

theorem hit5_comp_index_unique {x n m : ℕ}
    (h : Lambda.betaEtaConv (toLam (iterT (h5u x) n (h5s x))) (toLam (iterT (h5u x) m (h5s x)))) :
    n = m :=
  stage_index_unique (hit5_stageS x) (hit5_stageG x) h

theorem hit6_comp_index_unique {x n m : ℕ}
    (h : Lambda.betaEtaConv (toLam (iterT (h6g x) n (h6s x))) (toLam (iterT (h6g x) m (h6s x)))) :
    n = m :=
  stage_index_unique (hit6_stageS x) (hit6_stageG x) h

theorem hit8_comp_index_unique {x n m : ℕ}
    (h : Lambda.betaEtaConv (toLam (iterT (h8g x) n (h8s x))) (toLam (iterT (h8g x) m (h8s x)))) :
    n = m :=
  stage_index_unique (hit8_stageS x) (hit8_stageG x) h

end TLCA4
