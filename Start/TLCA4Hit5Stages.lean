import Start.TLCA4Candidates
import Start.TLCA4QStages
import Start.TLCA4StatmanStep

/-!
# TLCA open problem 4: the stages of `hit5 = M ∘ M ∘ BM ∘ BB ∘ BM ∘ B ∘ B`
(row M20-TLCA4-BETAETA; series V, big round, run 8, item A3, plan 4.4 step 1)

`hit5` is the first length-7 spine hit without a factor `T` (`Start/TLCA4Candidates.lean`).
Write `u = B (B x)`, `v = BM u`, `w = BB v`, `s = BM w`; then `hit5 x = M (M s)` syntactically.
Weak reduction gives

* `w A Z W →w x (A (u A) (Z W))` (`h5w_app`);
* `s A W →w x (A (u A) (w A W))` (`h5s_app`);
* `uⁿ s Z W →w xⁿ (s Z W)` (`h5A_app`, with `uⁿ s = h5A x n`);
* **`h5_stage_step`** — `s (uⁿ s) W →w x^{n+1} (s (uⁿ⁺¹ s) (w (uⁿ s) W))`;
* **`hit5_stage`** — `hit5 x →w x^{tri n} (s (uⁿ s) Wₙ)` for every `n`, with the tail
  `W₀ = M s`, `Wₙ₊₁ = w (uⁿ s) Wₙ` (`h5W`); `hit5_stage_betaEta` for the λ-translations.

So `hit5` has the stage pattern of `T` and `Q`: the `x`-prefix reaches the triangular numbers
exactly at the stages `s (uⁿ s) Wₙ`, whose first two arguments are the components `s = u⁰ s`
and `uⁿ s` (normal forms `λzw. xⁿ⁺¹ (z U_z (λd. x (z U_z (w d))))`, `U_z = λab. x (z a b)`;
`Start/TLCA4Hit5Components.lean`), and the tail `Wₙ` is only ever passed along linearly.
-/

set_option autoImplicit false

namespace TLCA4

open Tm

/-- `u = B (B x)`. -/
def h5u (x : ℕ) : Tm := app B (app B (var x))
/-- `v = B M u`. -/
def h5v (x : ℕ) : Tm := app (app B M) (h5u x)
/-- `w = B B v`. -/
def h5w (x : ℕ) : Tm := app (app B B) (h5v x)
/-- `s = B M w`. -/
def h5s (x : ℕ) : Tm := app (app B M) (h5w x)
/-- The components `uⁿ s`. -/
def h5A (x n : ℕ) : Tm := iterT (h5u x) n (h5s x)
/-- The tails: `W₀ = M s`, `Wₙ₊₁ = w (uⁿ s) Wₙ`. -/
def h5W (x : ℕ) : ℕ → Tm
  | 0 => app M (h5s x)
  | n + 1 => app (app (h5w x) (h5A x n)) (h5W x n)

/-- `hit5 x = M (M s)` syntactically. -/
theorem hit5_act (x : ℕ) : actList hit5 (var x) = app M (app M (h5s x)) := rfl

/-- `w A Z W →w x (A (u A) (Z W))`. -/
theorem h5w_app (x : ℕ) (A Z W : Tm) :
    Relation.ReflTransGen WStep (app (app (app (h5w x) A) Z) W)
      (app (var x) (app (app A (app (h5u x) A)) (app Z W))) := by
  unfold h5w h5v h5u
  refine .head (WStep.appL _ (WStep.appL _ (WStep.b _ _ _))) ?_
  refine .head (WStep.b _ _ _) ?_
  refine .head (WStep.appL _ (WStep.b _ _ _)) ?_
  refine .head (WStep.appL _ (WStep.m _)) ?_
  refine .head (WStep.appL _ (WStep.b _ _ _)) ?_
  exact .single (WStep.b _ _ _)

/-- `s A W →w x (A (u A) (w A W))`. -/
theorem h5s_app (x : ℕ) (A W : Tm) :
    Relation.ReflTransGen WStep (app (app (h5s x) A) W)
      (app (var x) (app (app A (app (h5u x) A)) (app (app (h5w x) A) W))) := by
  unfold h5s
  refine .head (WStep.appL _ (WStep.b _ _ _)) ?_
  refine .head (WStep.m _ |> WStep.appL _) ?_
  exact h5w_app x A (app (h5w x) A) W

/-- `uⁿ s Z W →w xⁿ (s Z W)`. -/
theorem h5A_app (x : ℕ) : ∀ (n : ℕ) (Z W : Tm),
    Relation.ReflTransGen WStep (app (app (h5A x n) Z) W) (iterX x n (app (app (h5s x) Z) W))
  | 0, _, _ => .refl
  | n + 1, Z, W => by
    show Relation.ReflTransGen WStep
      (app (app (app (app B (app B (var x))) (h5A x n)) Z) W)
      (app (var x) (iterX x n (app (app (h5s x) Z) W)))
    refine .head (WStep.appL _ (WStep.b _ _ _)) ?_
    refine .head (WStep.b _ _ _) ?_
    exact rtg_appR _ (h5A_app x n Z W)

/-- **One stage**: `s (uⁿ s) W →w x^{n+1} (s (uⁿ⁺¹ s) (w (uⁿ s) W))`. -/
theorem h5_stage_step (x n : ℕ) (W : Tm) :
    Relation.ReflTransGen WStep (app (app (h5s x) (h5A x n)) W)
      (iterX x (n + 1) (app (app (h5s x) (h5A x (n + 1))) (app (app (h5w x) (h5A x n)) W))) :=
  (h5s_app x (h5A x n) W).trans (rtg_appR _ (h5A_app x n _ _))

/-- **The stages of `hit5 x`**: `hit5 x →w x^{tri n} (s (uⁿ s) Wₙ)`. -/
theorem hit5_stage (x : ℕ) : ∀ n : ℕ,
    Relation.ReflTransGen WStep (actList hit5 (var x))
      (iterX x (tri n) (app (app (h5s x) (h5A x n)) (h5W x n)))
  | 0 => by
    rw [hit5_act]
    exact .head (WStep.m _) (.single (WStep.appL _ (WStep.m _)))
  | n + 1 => by
    refine (hit5_stage x n).trans ?_
    have h := rtg_iterX x (h5_stage_step x n (h5W x n)) (tri n)
    rw [iterX_add, show n + 1 + tri n = tri (n + 1) by simp only [tri]; omega] at h
    exact h

/-- The polynomial `hit5` applied to `x` is weakly equivalent to every stage. -/
theorem hit5_stage_weq (x n : ℕ) :
    WEq (app (polyOf hit5) (var x)) (iterX x (tri n) (app (app (h5s x) (h5A x n)) (h5W x n))) :=
  (hit5_weq (var x)).trans (weq_of_rtg (hit5_stage x n))

/-- The stages as β-reductions of the λ-translations. -/
theorem hit5_stage_betaEta (x n : ℕ) :
    Lambda.reduces (toLam (actList hit5 (var x)))
      (toLam (iterX x (tri n) (app (app (h5s x) (h5A x n)) (h5W x n)))) :=
  toLam_rtg (hit5_stage x n)

end TLCA4
