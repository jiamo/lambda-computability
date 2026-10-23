import Start.TLCA4QUnfold
import Start.TLCA4TNotFixpoint

/-!
# TLCA open problem 4: the stages of `Q x` (row M20-TLCA4-Q-NOT-FIXPOINT;
series V, big round, run 1, item A1)

`Q = M ∘ M ∘ (B M) ∘ B ∘ B` and `Q x →w M (M A₀[B x])` (`Q_unfold`).  This module generalizes the
components `Aₙ` of the `T` proof from the variable `x` to an arbitrary argument `y`
(`A₀[y] = B M (B y)`, `Aₙ₊₁[y] = B y Aₙ[y]`) and records the weak head reduction of `Q x`, with the
tail `R = M A₀[B x]` (a reduct of `T (B x)`) carried along unchanged:

* `tAy_app` — `Aₙ[y] Z →w yⁿ (M (B y Z))`;
* `MtAy_step` — `M Aₙ[y] →w yⁿ (M Aₙ₊₁[y])`;
* `iterT_Bx_app` — `(B x)ⁿ W R →w xⁿ (W R)`: each `y = B x` at the head fires one `x`;
* `MtAy_tail_step` — `M Aₙ[B x] R →w xⁿ (M Aₙ₊₁[B x] R)`;
* **`Q_stage`** — `Q x →w x^{tri n} (M Aₙ₊₁[B x] R)` for every `n` (`tri n = n (n + 1) / 2`);
* `Q_stage_betaEta` — the same as a β-reduction of the λ-translations.

So the x-prefix of the head reducts of `Q x` reaches the triangular numbers exactly at the
`M`-stages, the stage pattern of `T` with every `y` counted as one `x`.  `Q_not_fixedPoint` is
**not** proved here: the missing step is a βη-closed shape for the reducts of `Q x` (see the
evidence note, series V, big round, run 1).
-/

set_option autoImplicit false

namespace TLCA4

open Tm

/-- `A₀[y] = B M (B y)`, `Aₙ₊₁[y] = B y Aₙ[y]`, for an arbitrary term `y`. -/
def tAy (y : Tm) : ℕ → Tm
  | 0 => app (app B M) (app B y)
  | n + 1 => app (app B y) (tAy y n)

/-- `iterT f r u = f (f (… (f u)))` with `r` copies of `f`. -/
def iterT (f : Tm) : ℕ → Tm → Tm
  | 0, u => u
  | r + 1, u => app f (iterT f r u)

theorem tAy_var (x : ℕ) : ∀ n : ℕ, tAy (var x) n = tA x n
  | 0 => rfl
  | n + 1 => by simp only [tAy, tA, tAy_var x n]

theorem iterT_var (x : ℕ) : ∀ (r : ℕ) (u : Tm), iterT (var x) r u = iterX x r u
  | 0, _ => rfl
  | r + 1, u => by simp only [iterT, iterX, iterT_var x r u]

/-- `Aₙ[y] Z →w yⁿ (M (B y Z))`. -/
theorem tAy_app (y : Tm) : ∀ (n : ℕ) (Z : Tm),
    Relation.ReflTransGen WStep (app (tAy y n) Z) (iterT y n (app M (app (app B y) Z)))
  | 0, _ => .single (WStep.b _ _ _)
  | n + 1, Z => (Relation.ReflTransGen.single (WStep.b _ _ _)).trans (rtg_appR _ (tAy_app y n Z))

/-- `M Aₙ[y] →w yⁿ (M Aₙ₊₁[y])`. -/
theorem MtAy_step (y : Tm) (n : ℕ) :
    Relation.ReflTransGen WStep (app M (tAy y n)) (iterT y n (app M (tAy y (n + 1)))) :=
  (Relation.ReflTransGen.single (WStep.m _)).trans (tAy_app y n (tAy y n))

/-- `(B x)ⁿ W R →w xⁿ (W R)`. -/
theorem iterT_Bx_app (x : ℕ) : ∀ (n : ℕ) (W R : Tm),
    Relation.ReflTransGen WStep (app (iterT (app B (var x)) n W) R) (iterX x n (app W R))
  | 0, _, _ => .refl
  | n + 1, W, R =>
    (Relation.ReflTransGen.single (WStep.b _ _ _)).trans (rtg_appR _ (iterT_Bx_app x n W R))

theorem rtg_iterX (x : ℕ) {u v : Tm} (h : Relation.ReflTransGen WStep u v) :
    ∀ r : ℕ, Relation.ReflTransGen WStep (iterX x r u) (iterX x r v)
  | 0 => h
  | r + 1 => rtg_appR _ (rtg_iterX x h r)

theorem iterX_add (x : ℕ) : ∀ (r s : ℕ) (u : Tm), iterX x r (iterX x s u) = iterX x (s + r) u
  | 0, _, _ => rfl
  | r + 1, s, u => by simp only [iterX, iterX_add x r s u]; rfl

/-- `M Aₙ[B x] R →w xⁿ (M Aₙ₊₁[B x] R)`: one `M`-stage with the tail `R` carried along. -/
theorem MtAy_tail_step (x n : ℕ) (R : Tm) :
    Relation.ReflTransGen WStep (app (app M (tAy (app B (var x)) n)) R)
      (iterX x n (app (app M (tAy (app B (var x)) (n + 1))) R)) :=
  (rtg_appL (MtAy_step _ n) R).trans (iterT_Bx_app x n _ R)

/-- The tail `R = M A₀[B x]`, a reduct of `T (B x)`. -/
def qTail (x : ℕ) : Tm := app M (tAy (app B (var x)) 0)

theorem qK_eq (x : ℕ) : qK x = app M (qTail x) := rfl

/-- The tail is a weak reduct of `T (B x)`. -/
theorem tT_Bx_reduces_qTail (x : ℕ) :
    Relation.ReflTransGen WStep (app tT (app B (var x))) (qTail x) :=
  (Relation.ReflTransGen.single (WStep.b _ _ _)).tail (WStep.appR _ (WStep.b _ _ _))

theorem qTail_stages (x : ℕ) : ∀ n : ℕ,
    Relation.ReflTransGen WStep (app (qTail x) (qTail x))
      (iterX x (tri n) (app (app M (tAy (app B (var x)) (n + 1))) (qTail x)))
  | 0 => MtAy_tail_step x 0 _
  | n + 1 => by
    refine (qTail_stages x n).trans ?_
    have h := rtg_iterX x (MtAy_tail_step x (n + 1) (qTail x)) (tri n)
    rw [iterX_add, show n + 1 + tri n = tri (n + 1) by simp only [tri]; omega] at h
    exact h

/-- **The stages of `Q x`**: `Q x →w x^{tri n} (M Aₙ₊₁[B x] R)` with `R = M A₀[B x]`. -/
theorem Q_stage (x n : ℕ) :
    Relation.ReflTransGen WStep (app tQ (var x))
      (iterX x (tri n) (app (app M (tAy (app B (var x)) (n + 1))) (qTail x))) :=
  ((Q_unfold x).1.tail (WStep.m _)).trans (qTail_stages x n)

/-- The same stages as β-reductions of the λ-translations. -/
theorem Q_stage_betaEta (x n : ℕ) :
    Lambda.reduces (toLam (app tQ (var x)))
      (toLam (iterX x (tri n) (app (app M (tAy (app B (var x)) (n + 1))) (qTail x)))) :=
  toLam_rtg (Q_stage x n)

end TLCA4
