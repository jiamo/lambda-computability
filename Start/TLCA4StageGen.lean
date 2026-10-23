import Start.TLCA4Hit5Stages

/-!
# TLCA open problem 4: a generic stage lemma for `M ∘ M ∘ BM ∘ G`
(row M20-TLCA4-BETAETA; series V, big round, run 8, item A3, plan 4.4 step 3)

Q, hit5, hit6 and hit8 share one stage pattern.  This module states it abstractly.  Let `s`, `g` be
combinatory terms and `x` a variable with

* `s A W →w x (A (g A) W')` for some `W'` (`StageS`), and
* `g A Z W →w x (A Z W')` for some `W'` (`StageG`).

Then

* `iterT_g_app` — `gⁿ s Z W →w xⁿ (s Z W')` for some `W'`;
* **`stage_step_gen`** — `s (gⁿ s) W →w x^{n+1} (s (gⁿ⁺¹ s) W')` for some `W'`;
* **`stage_gen`** — `M (M s) →w x^{tri n} (s (gⁿ s) W)` for every `n`, for some `W`.

Instances: hit5 (`g = B (B x)`, `s = BM (BB (BM g))`: `hit5_stageS`, `hit5_stageG`), hit6
(`g = B²M F`, `s = BM g`, `F = B (BB (B x))`: **`hit6_stage`**) and hit8 (`g = B³M F`,
`s = BM g`: **`hit8_stage`**), so hit6 (≡ hit7 up to βη) and hit8 (≡ hit9) have the triangular
stage pattern too; so does Q (`g = B (B x)`, `s = BM g`: `Q_stage_gen`).  (hit10, with third
monomial `B²M`, is not of this form.)
-/

set_option autoImplicit false

namespace TLCA4

open Tm

/-- `s A W →w x (A (g A) W')`. -/
def StageS (x : ℕ) (s g : Tm) : Prop :=
  ∀ A W : Tm, ∃ W', Relation.ReflTransGen WStep (app (app s A) W)
    (app (var x) (app (app A (app g A)) W'))

/-- `g A Z W →w x (A Z W')`. -/
def StageG (x : ℕ) (g : Tm) : Prop :=
  ∀ A Z W : Tm, ∃ W', Relation.ReflTransGen WStep (app (app (app g A) Z) W)
    (app (var x) (app (app A Z) W'))

theorem iterT_g_app {x : ℕ} {s g : Tm} (hg : StageG x g) :
    ∀ (n : ℕ) (Z W : Tm), ∃ W', Relation.ReflTransGen WStep (app (app (iterT g n s) Z) W)
      (iterX x n (app (app s Z) W'))
  | 0, _, W => ⟨W, .refl⟩
  | n + 1, Z, W => by
    obtain ⟨W₁, h₁⟩ := hg (iterT g n s) Z W
    obtain ⟨W₂, h₂⟩ := iterT_g_app hg n Z W₁
    exact ⟨W₂, h₁.trans (rtg_appR _ h₂)⟩

/-- **One stage**: `s (gⁿ s) W →w x^{n+1} (s (gⁿ⁺¹ s) W')`. -/
theorem stage_step_gen {x : ℕ} {s g : Tm} (hs : StageS x s g) (hg : StageG x g) (n : ℕ)
    (W : Tm) : ∃ W', Relation.ReflTransGen WStep (app (app s (iterT g n s)) W)
      (iterX x (n + 1) (app (app s (iterT g (n + 1) s)) W')) := by
  obtain ⟨W₁, h₁⟩ := hs (iterT g n s) W
  obtain ⟨W₂, h₂⟩ := iterT_g_app (s := s) hg n (app g (iterT g n s)) W₁
  exact ⟨W₂, h₁.trans (rtg_appR _ h₂)⟩

/-- **The stages**: `M (M s) →w x^{tri n} (s (gⁿ s) W)`. -/
theorem stage_gen {x : ℕ} {s g : Tm} (hs : StageS x s g) (hg : StageG x g) :
    ∀ n : ℕ, ∃ W, Relation.ReflTransGen WStep (app M (app M s))
      (iterX x (tri n) (app (app s (iterT g n s)) W))
  | 0 => ⟨app M s, .head (WStep.m _) (.single (WStep.appL _ (WStep.m _)))⟩
  | n + 1 => by
    obtain ⟨W, h⟩ := stage_gen hs hg n
    obtain ⟨W', h'⟩ := stage_step_gen hs hg n W
    refine ⟨W', h.trans ?_⟩
    have h2 := rtg_iterX x h' (tri n)
    rw [iterX_add, show n + 1 + tri n = tri (n + 1) by simp only [tri]; omega] at h2
    exact h2

theorem hit5_stageS (x : ℕ) : StageS x (h5s x) (h5u x) :=
  fun A W => ⟨_, h5s_app x A W⟩

theorem hit5_stageG (x : ℕ) : StageG x (h5u x) := by
  intro A Z W
  refine ⟨W, ?_⟩
  unfold h5u
  refine .head (WStep.appL _ (WStep.b _ _ _)) ?_
  exact .single (WStep.b _ _ _)

/-! ### hit6 = M ∘ M ∘ BM ∘ B²M ∘ B ∘ BB ∘ B -/

/-- `F = B (BB (B x))`. -/
def h6F (x : ℕ) : Tm := app B (app (app B B) (app B (var x)))
/-- `g = B²M F`. -/
def h6g (x : ℕ) : Tm := app (app B (app B M)) (h6F x)
/-- `s = BM g`. -/
def h6s (x : ℕ) : Tm := app (app B M) (h6g x)

theorem hit6_act (x : ℕ) : actList hit6 (var x) = app M (app M (h6s x)) := rfl

/-- `F A Z Y W →w x (A Z (Y W))`. -/
theorem h6F_app (x : ℕ) (A Z Y W : Tm) :
    Relation.ReflTransGen WStep (app (app (app (app (h6F x) A) Z) Y) W)
      (app (var x) (app (app A Z) (app Y W))) := by
  unfold h6F
  refine .head (WStep.appL _ (WStep.appL _ (WStep.b _ _ _))) ?_
  refine .head (WStep.appL _ (WStep.appL _ (WStep.b _ _ _))) ?_
  refine .head (WStep.b _ _ _) ?_
  exact .single (WStep.b _ _ _)

/-- `g A Z W →w x (A Z (F A Z W))`. -/
theorem h6g_app (x : ℕ) (A Z W : Tm) :
    Relation.ReflTransGen WStep (app (app (app (h6g x) A) Z) W)
      (app (var x) (app (app A Z) (app (app (app (h6F x) A) Z) W))) := by
  unfold h6g
  refine .head (WStep.appL _ (WStep.appL _ (WStep.b _ _ _))) ?_
  refine .head (WStep.appL _ (WStep.b _ _ _)) ?_
  refine .head (WStep.appL _ (WStep.m _)) ?_
  exact h6F_app x A Z _ W

theorem hit6_stageG (x : ℕ) : StageG x (h6g x) :=
  fun A Z W => ⟨_, h6g_app x A Z W⟩

theorem hit6_stageS (x : ℕ) : StageS x (h6s x) (h6g x) := by
  intro A W
  refine ⟨app (app (app (h6F x) A) (app (h6g x) A)) W, ?_⟩
  unfold h6s
  refine .head (WStep.appL _ (WStep.b _ _ _)) ?_
  refine .head (WStep.appL _ (WStep.m _)) ?_
  exact h6g_app x A (app (h6g x) A) W

/-- **The stages of `hit6 x`**: `hit6 x →w x^{tri n} (s (gⁿ s) W)` for every `n`. -/
theorem hit6_stage (x n : ℕ) : ∃ W, Relation.ReflTransGen WStep (actList hit6 (var x))
    (iterX x (tri n) (app (app (h6s x) (iterT (h6g x) n (h6s x))) W)) := by
  rw [hit6_act]
  exact stage_gen (hit6_stageS x) (hit6_stageG x) n

/-! ### hit8 = M ∘ M ∘ BM ∘ B³M ∘ B ∘ BB ∘ B -/

/-- `g = B³M F`. -/
def h8g (x : ℕ) : Tm := app (app B (app B (app B M))) (h6F x)
/-- `s = BM g`. -/
def h8s (x : ℕ) : Tm := app (app B M) (h8g x)

theorem hit8_act (x : ℕ) : actList hit8 (var x) = app M (app M (h8s x)) := rfl

/-- `g A Z W →w x (A Z (W (F A Z W)))`. -/
theorem h8g_app (x : ℕ) (A Z W : Tm) :
    Relation.ReflTransGen WStep (app (app (app (h8g x) A) Z) W)
      (app (var x) (app (app A Z) (app W (app (app (app (h6F x) A) Z) W)))) := by
  unfold h8g
  refine .head (WStep.appL _ (WStep.appL _ (WStep.b _ _ _))) ?_
  refine .head (WStep.appL _ (WStep.b _ _ _)) ?_
  refine .head (WStep.b _ _ _) ?_
  refine .head (WStep.m _) ?_
  exact h6F_app x A Z W _

theorem hit8_stageG (x : ℕ) : StageG x (h8g x) :=
  fun A Z W => ⟨_, h8g_app x A Z W⟩

theorem hit8_stageS (x : ℕ) : StageS x (h8s x) (h8g x) := by
  intro A W
  refine ⟨app W (app (app (app (h6F x) A) (app (h8g x) A)) W), ?_⟩
  unfold h8s
  refine .head (WStep.appL _ (WStep.b _ _ _)) ?_
  refine .head (WStep.appL _ (WStep.m _)) ?_
  exact h8g_app x A (app (h8g x) A) W

/-- **The stages of `hit8 x`**: `hit8 x →w x^{tri n} (s (gⁿ s) W)` for every `n`. -/
theorem hit8_stage (x n : ℕ) : ∃ W, Relation.ReflTransGen WStep (actList hit8 (var x))
    (iterX x (tri n) (app (app (h8s x) (iterT (h8g x) n (h8s x))) W)) := by
  rw [hit8_act]
  exact stage_gen (hit8_stageS x) (hit8_stageG x) n

/-! ### Q = M ∘ M ∘ BM ∘ B ∘ B is an instance too -/

theorem Q_stageS (x : ℕ) : StageS x (h5v x) (h5u x) := by
  intro A W
  refine ⟨W, ?_⟩
  unfold h5v h5u
  refine .head (WStep.appL _ (WStep.b _ _ _)) ?_
  refine .head (WStep.appL _ (WStep.m _)) ?_
  refine .head (WStep.appL _ (WStep.b _ _ _)) ?_
  exact .single (WStep.b _ _ _)

/-- `M (M (BM (B (B x)))) →w x^{tri n} (v (uⁿ v) W)`: the stages of `Q` (cf. `Q_stage`) from the
generic lemma. -/
theorem Q_stage_gen (x n : ℕ) : ∃ W, Relation.ReflTransGen WStep (app M (app M (h5v x)))
    (iterX x (tri n) (app (app (h5v x) (iterT (h5u x) n (h5v x))) W)) :=
  stage_gen (Q_stageS x) (hit5_stageG x) n

end TLCA4
