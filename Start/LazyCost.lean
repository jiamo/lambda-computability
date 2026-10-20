/-
**Call-by-need is exponentially cheaper than call-by-name on a family** — task `M25-CBNEED-COST`.

The family chains `n` arguments, each of which uses the previous one twice:

  `tfam n = (λx₀. (λx₁. ⋯ (λxₙ. xₙ) (xₙ₋₁ xₙ₋₁) ⋯) (x₀ x₀)) I`.

Under call-by-name, evaluating `x_{k+1} = x_k x_k` evaluates `x_k` twice, so the Krivine machine
makes `2ⁿ + n` β transitions (`Lazy.krivine_tfam`).  The lazy machine evaluates each `x_k` once,
and makes `2n + 1` β transitions (`Lazy.lazy_tfam`).
-/

import Start.LazyKrivine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lazy

open Krivine

/-- The body: `W 0 = x`, `W (m+1) = (λ. W m) (x x)`, where `x` is the innermost variable. -/
def W : ℕ → Lambda
  | 0 => .var 0
  | m + 1 => .app (.lam (W m)) (.app (.var 0) (.var 0))

/-- **The family**: `n` chained arguments, each using the previous one twice. -/
def tfam (n : ℕ) : Lambda := .app (.lam (W n)) (.lam (.var 0))

/-! ### The Krivine machine on the family -/

theorem _root_.Krivine.Run.cast {n b n' b' : ℕ} {s s' : State} (h : Run n b s s') (hn : n = n')
    (hb : b = b') : Run n' b' s s' := hn ▸ hb ▸ h

/-- The identity closure. -/
def kI : Clos := Clos.mk (.lam (.var 0)) []

/-- The environment after the `k`-th argument has been bound. -/
def en : ℕ → Env
  | 0 => [kI]
  | k + 1 => Clos.mk (.app (.var 0) (.var 0)) (en k) :: en k

theorem krivine_setup : ∀ (m k : ℕ),
    Run (2 * m) m ⟨W m, en k, []⟩ ⟨.var 0, en (k + m), []⟩ := by
  intro m
  induction m with
  | zero => intro k; exact Run.refl _
  | succ m ih =>
      intro k
      have h1 := Trans.app (.lam (W m)) (.app (.var 0) (.var 0)) (en k) []
      have h2 := Trans.beta (W m) (en k) (Clos.mk (.app (.var 0) (.var 0)) (en k)) []
      have h3 := ih (k + 1)
      have := (Run.single h1).trans ((Run.single h2).trans h3)
      simp only [Label.betaCount_app, Label.betaCount_beta] at this
      rw [show k + 1 + m = k + (m + 1) by omega] at this
      exact this.cast (by omega) (by omega)

theorem krivine_eval : ∀ (k : ℕ) (π : List Clos), ∃ N b,
    Run N b ⟨.var 0, en k, π⟩ ⟨.lam (.var 0), [], π⟩ ∧ b + 1 = 2 ^ k := by
  intro k
  induction k with
  | zero =>
      intro π
      exact ⟨1, 0, Run.single (Trans.var 0 (en 0) kI π rfl), rfl⟩
  | succ k ih =>
      intro π
      set c := Clos.mk (.var 0) (en k)
      obtain ⟨N₁, b₁, hr₁, hb₁⟩ := ih (c :: π)
      obtain ⟨N₂, b₂, hr₂, hb₂⟩ := ih π
      have h1 := Trans.var 0 (en (k + 1)) (Clos.mk (.app (.var 0) (.var 0)) (en k)) π rfl
      have h2 := Trans.app (.var 0) (.var 0) (en k) π
      have h3 := Trans.beta (.var 0) [] c π
      have h4 := Trans.var 0 [c] c π rfl
      have := (Run.single h1).trans ((Run.single h2).trans (hr₁.trans ((Run.single h3).trans
        ((Run.single h4).trans hr₂))))
      refine ⟨_, _, this, ?_⟩
      simp only [Label.betaCount_app, Label.betaCount_beta, Label.betaCount_var, pow_succ]
      omega

/-- **The Krivine machine makes `2ⁿ + n` β transitions on `tfam n`.** -/
theorem krivine_tfam (n : ℕ) :
    ∃ N f, Run N (2 ^ n + n) (State.init (tfam n)) f ∧ IsFinal f := by
  have h1 := Trans.app (.lam (W n)) (.lam (.var 0)) [] []
  have h2 := Trans.beta (W n) [] (Clos.mk (.lam (.var 0)) []) []
  have h3 := krivine_setup n 0
  rw [Nat.zero_add] at h3
  obtain ⟨N, b, h4, hb⟩ := krivine_eval n []
  have := (Run.single h1).trans ((Run.single h2).trans (h3.trans h4))
  simp only [Label.betaCount_app, Label.betaCount_beta, Nat.zero_add] at this
  exact ⟨_, _, this.cast rfl (by omega), (isFinal_iff _).2 (Or.inl ⟨⟨_, rfl⟩, rfl⟩)⟩

/-- Every halting Krivine run on `tfam n` makes exactly `2ⁿ + n` β transitions. -/
theorem krivine_tfam_beta {n N b : ℕ} {f : State} (h : Run N b (State.init (tfam n)) f)
    (hf : IsFinal f) : b = 2 ^ n + n := by
  obtain ⟨N', f', h', hf'⟩ := krivine_tfam n
  exact (h.final_unique hf h' hf').2.1

/-! ### The lazy machine on the family -/

/-- Reachability with a count of β transitions. -/
def LReach (b : ℕ) (s s' : LState) : Prop := ∃ n fs, LRun n b fs s s'

theorem LReach.refl (s : LState) : LReach 0 s s := ⟨0, [], LRun.refl s⟩

theorem LReach.step {l : LLabel} {b : ℕ} {s₁ s₂ s₃ : LState} (h : LTrans l s₁ s₂)
    (hr : LReach b s₂ s₃) : LReach (b + l.betaCount) s₁ s₃ := by
  obtain ⟨n, fs, hr⟩ := hr
  exact ⟨_, _, LRun.cons h hr⟩

theorem LReach.trans {b₁ b₂ : ℕ} {s₁ s₂ s₃ : LState} (h₁ : LReach b₁ s₁ s₂)
    (h₂ : LReach b₂ s₂ s₃) : LReach (b₁ + b₂) s₁ s₃ := by
  obtain ⟨n, fs, h₁⟩ := h₁
  induction h₁ with
  | refl s => simpa using h₂
  | @cons l n b fs _ _ _ hstep _ ih =>
      have := LReach.step hstep (ih h₂)
      rwa [show b + b₂ + l.betaCount = b + l.betaCount + b₂ by omega] at this

theorem LReach.cast {b b' : ℕ} {s s' : LState} (h : LReach b s s') (hb : b = b') :
    LReach b' s s' := hb ▸ h

/-- The lazy environment after the `k`-th argument has been bound. -/
def lenv : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => (k + 1) :: lenv k

theorem lenv_zero (k : ℕ) : (lenv k)[0]? = some k := by cases k <;> rfl

/-- The closure the `j`-th cell is allocated with. -/
def origL : ℕ → LClos
  | 0 => ⟨.lam (.var 0), []⟩
  | j + 1 => ⟨.app (.var 0) (.var 0), lenv j⟩

/-- The value every cell evaluates to. -/
def valI : LClos := ⟨.lam (.var 0), []⟩

theorem lazy_setup : ∀ (m k : ℕ) (H : List Cell), H.length = k + 1 →
    (∀ j ≤ k, H[j]? = some (.thunk (origL j))) →
    ∃ H' : List Cell, H'.length = k + m + 1 ∧ (∀ j ≤ k + m, H'[j]? = some (.thunk (origL j))) ∧
      LReach m ⟨W m, lenv k, [], H⟩ ⟨.var 0, lenv (k + m), [], H'⟩ := by
  intro m
  induction m with
  | zero => intro k H hl hH; exact ⟨H, hl, hH, LReach.refl _⟩
  | succ m ih =>
      intro k H hl hH
      have h1 := LTrans.app (.lam (W m)) (.app (.var 0) (.var 0)) (lenv k) [] H
      have h2 := LTrans.beta (W m) (lenv k) H.length []
        (H ++ [.thunk ⟨.app (.var 0) (.var 0), lenv k⟩])
      have hl' : (H ++ [Cell.thunk ⟨.app (.var 0) (.var 0), lenv k⟩]).length = k + 1 + 1 := by
        simp [hl]
      have hH' : ∀ j ≤ k + 1, (H ++ [Cell.thunk ⟨.app (.var 0) (.var 0), lenv k⟩])[j]? =
          some (.thunk (origL j)) := by
        intro j hj
        rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
        · rw [List.getElem?_append_left (by omega)]; exact hH j (by omega)
        · have : j = H.length := by omega
          subst this
          simp [hl, origL]
      obtain ⟨H', hlen, hcells, hr⟩ := ih (k + 1) _ hl' hH'
      refine ⟨H', by rw [hlen]; omega, fun j hj => hcells j (by omega), ?_⟩
      rw [show lenv (k + 1) = H.length :: lenv k by simp [lenv, hl]] at hr
      have := LReach.step h1 (LReach.step h2 hr)
      rw [show k + 1 + m = k + (m + 1) by omega] at this
      exact this.cast (by simp [LLabel.betaCount])

theorem lazy_eval : ∀ (k : ℕ) (S : List Frame) (H : List Cell),
    (∀ j ≤ k, H[j]? = some (.thunk (origL j))) →
    ∃ H' : List Cell, H.length ≤ H'.length ∧ (∀ j ≤ k, H'[j]? = some (.value (origL j) valI)) ∧
      (∀ j, k < j → j < H.length → H'[j]? = H[j]?) ∧
      LReach k ⟨.var 0, lenv k, S, H⟩ ⟨.lam (.var 0), [], S, H'⟩ := by
  intro k
  induction k with
  | zero =>
      intro S H hH
      have hc := hH 0 le_rfl
      have hlt : 0 < H.length := lt_of_getElem?_some hc
      have h1 := LTrans.force 0 (lenv 0) S H 0 (origL 0) rfl hc
      have h2 := LTrans.update (.var 0) [] 0 S (H.set 0 (.hole (origL 0))) (origL 0)
        (by simp [List.getElem?_set_self hlt])
      refine ⟨_, by simp, fun j hj => ?_, fun j hj _ => ?_, LReach.step h1 (LReach.step h2
        (LReach.refl _))⟩
      · obtain rfl : j = 0 := by omega
        simp [hlt, origL, valI]
      · simp [List.getElem?_set_ne (show 0 ≠ j by omega)]
  | succ k ih =>
      intro S H hH
      have hc := hH (k + 1) le_rfl
      have hlt : k + 1 < H.length := lt_of_getElem?_some hc
      set H₁ := H.set (k + 1) (.hole (origL (k + 1))) with hH₁
      have h1 := LTrans.force 0 (lenv (k + 1)) S H (k + 1) (origL (k + 1)) rfl hc
      have h2 := LTrans.app (.var 0) (.var 0) (lenv k) (.upd (k + 1) :: S) H₁
      set c : LClos := ⟨.var 0, lenv k⟩ with hc_def
      set H₂ := H₁ ++ [Cell.thunk c] with hH₂
      have hL : H₁.length = H.length := by simp [H₁]
      have hH₂c : ∀ j ≤ k, H₂[j]? = some (.thunk (origL j)) := by
        intro j hj
        rw [hH₂, List.getElem?_append_left (by rw [hL]; omega), hH₁,
          List.getElem?_set_ne (by omega)]
        exact hH j (by omega)
      obtain ⟨H₃, hl₃, hv₃, hu₃, hr₃⟩ := ih (.arg H₁.length :: .upd (k + 1) :: S) H₂ hH₂c
      have hlen₂ : H₂.length = H.length + 1 := by simp [H₂, hL]
      have hH₃L : H₃[H.length]? = some (.thunk c) := by
        rw [hu₃ _ (by omega) (by omega), hH₂, List.getElem?_append_right (by omega)]
        simp [hL]
      have hH₃k1 : H₃[k + 1]? = some (.hole (origL (k + 1))) := by
        rw [hu₃ _ (by omega) (by omega), hH₂, List.getElem?_append_left (by rw [hL]; omega)]
        simp [H₁, List.getElem?_set_self hlt]
      have hLt₃ : H.length < H₃.length := by omega
      have h3 := LTrans.beta (.var 0) [] H₁.length (.upd (k + 1) :: S) H₃
      rw [hL] at h2 h3 hr₃
      have h4 := LTrans.force 0 [H.length] (.upd (k + 1) :: S) H₃ H.length c rfl hH₃L
      set H₄ := H₃.set H.length (.hole c) with hH₄
      have hH₄k : H₄[k]? = some (.value (origL k) valI) := by
        rw [hH₄, List.getElem?_set_ne (by omega)]; exact hv₃ k le_rfl
      have h5 := LTrans.fetch 0 (lenv k) (.upd H.length :: .upd (k + 1) :: S) H₄ k (origL k)
        valI (lenv_zero k) hH₄k
      have h6 := LTrans.update (.var 0) [] H.length (.upd (k + 1) :: S) H₄ c
        (by simp [H₄, List.getElem?_set_self hLt₃])
      set H₅ := H₄.set H.length (.value c ⟨.lam (.var 0), []⟩) with hH₅
      have h7 := LTrans.update (.var 0) [] (k + 1) S H₅ (origL (k + 1))
        (by rw [hH₅, hH₄, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)];
            exact hH₃k1)
      refine ⟨H₅.set (k + 1) (.value (origL (k + 1)) ⟨.lam (.var 0), []⟩), ?_, ?_, ?_, ?_⟩
      · simp [H₅, H₄]; omega
      · intro j hj
        rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
        · rw [List.getElem?_set_ne (by omega), hH₅, List.getElem?_set_ne (by omega), hH₄,
            List.getElem?_set_ne (by omega)]
          exact hv₃ j (by omega)
        · obtain rfl : j = k + 1 := by omega
          rw [List.getElem?_set_self (by simp [H₅, H₄]; omega)]
          rfl
      · intro j hj hjl
        rw [List.getElem?_set_ne (by omega), hH₅, List.getElem?_set_ne (by omega), hH₄,
          List.getElem?_set_ne (by omega), hu₃ j (by omega) (by omega), hH₂,
          List.getElem?_append_left (by rw [hL]; omega), hH₁, List.getElem?_set_ne (by omega)]
      · have := LReach.step h1 (LReach.step h2 (hr₃.trans (LReach.step h3 (LReach.step h4
          (LReach.step h5 (LReach.step h6 (LReach.step h7 (LReach.refl _))))))))
        exact this.cast (by simp [LLabel.betaCount])

/-- **The lazy machine makes `2n + 1` β transitions on `tfam n`.** -/
theorem lazy_tfam (n : ℕ) :
    ∃ N fs s, LRun N (2 * n + 1) fs (LState.init (tfam n)) s ∧ LFinal s := by
  have h1 := LTrans.app (.lam (W n)) (.lam (.var 0)) [] [] []
  have h2 := LTrans.beta (W n) [] 0 [] [.thunk ⟨.lam (.var 0), []⟩]
  obtain ⟨H, hl, hc, hr⟩ := lazy_setup n 0 [.thunk ⟨.lam (.var 0), []⟩] rfl
    (fun j hj => by obtain rfl : j = 0 := by omega
                    rfl)
  rw [Nat.zero_add] at hc hr
  obtain ⟨H', -, -, -, hr'⟩ := lazy_eval n [] H hc
  obtain ⟨N, fs, hrun⟩ := (LReach.step h1 (LReach.step h2 (hr.trans hr'))).cast
    (b' := 2 * n + 1) (by simp [LLabel.betaCount]; omega)
  refine ⟨N, fs, _, hrun, ?_⟩
  rintro s' ⟨l, h⟩
  cases h

/-- **The exponential gap**: on `tfam n` the lazy machine halts after `2n + 1` β transitions,
while every halting run of the Krivine machine makes `2ⁿ + n`. -/
theorem cbneed_exponential_gap (n : ℕ) :
    (∃ N fs s, LRun N (2 * n + 1) fs (LState.init (tfam n)) s ∧ LFinal s ∧ ¬ HoleStuck s) ∧
      (∃ N f, Run N (2 ^ n + n) (State.init (tfam n)) f ∧ IsFinal f) ∧
      ∀ N b f, Run N b (State.init (tfam n)) f → IsFinal f → b = 2 ^ n + n := by
  obtain ⟨N, fs, s, hrun, hfin⟩ := lazy_tfam n
  obtain ⟨M, f, hf, hff⟩ := krivine_tfam n
  exact ⟨⟨N, fs, s, hrun, hfin, no_blackhole ⟨M, _, f, hf, hff⟩ hrun⟩, ⟨M, f, hf, hff⟩,
    fun _ _ _ h hf' => krivine_tfam_beta h hf'⟩

end Lazy
