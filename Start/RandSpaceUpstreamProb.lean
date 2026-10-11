import Start.LogspaceDeterministic

/-!
# Upstream acceptance probability as a recursion over coin flips

This library's own module (task `M27-HOST-RANDOMIZED-SPACE`).  For a machine of
`Start/LogspaceDeterministic.lean` (absorbed from openai/math), `acceptanceProbability x t` counts
the coin strings of length `t` after which the machine is in a state with output `true`, divided by
`2 ^ t`.  `ExactDerandomization.Machine.probFrom` is the same quantity as a recursion over the first
coin, from an arbitrary configuration, and `acceptanceProbability_eq_probFrom` proves the two equal.
-/

set_option autoImplicit false

namespace ExactDerandomization

namespace Machine

variable {q w h : ℕ} (M : Machine q w h) (x : Word)

/-- The run from an arbitrary configuration, consuming the coins from the front. -/
def runFrom : Configuration q w h x.length → CoinTape → ℕ → Configuration q w h x.length
  | c, _, 0 => c
  | c, coins, t + 1 => runFrom (M.step x (coins 0) c) (fun i => coins (i + 1)) t

/-- Probability of output `true` after `t` coin flips, from `c`, as a recursion. -/
def probFrom : ℕ → Configuration q w h x.length → ℚ
  | 0, c => if M.output c.state = some true then 1 else 0
  | t + 1, c => (probFrom t (M.step x false c) + probFrom t (M.step x true c)) / 2

theorem runFrom_succ' : ∀ (t : ℕ) (c : Configuration q w h x.length) (coins : CoinTape),
    M.runFrom x c coins (t + 1) = M.step x (coins t) (M.runFrom x c coins t)
  | 0, _, _ => rfl
  | t + 1, c, coins => by
      rw [runFrom, runFrom_succ' t]
      rfl

theorem run_eq_runFrom (coins : CoinTape) : ∀ t : ℕ,
    M.run x coins t = M.runFrom x (M.initial x.length) coins t
  | 0 => rfl
  | t + 1 => by rw [run_succ, runFrom_succ', run_eq_runFrom coins t]

theorem extendCoins_cons_zero {t : ℕ} (b : Bool) (bits : Fin t → Bool) :
    extendCoins (Fin.cons b bits : Fin (t + 1) → Bool) 0 = b := by
  simp [extendCoins]

theorem extendCoins_cons_succ {t : ℕ} (b : Bool) (bits : Fin t → Bool) :
    (fun i => extendCoins (Fin.cons b bits : Fin (t + 1) → Bool) (i + 1)) = extendCoins bits := by
  funext i
  unfold extendCoins
  by_cases hi : i < t
  · rw [dif_pos (by omega), dif_pos hi]
    exact Fin.cons_succ (α := fun _ => Bool) b bits ⟨i, hi⟩
  · rw [dif_neg (by omega), dif_neg hi]

/-- The number of coin strings of length `t` after which the run from `c` has output `true`. -/
def goodCount (t : ℕ) (c : Configuration q w h x.length) : ℕ :=
  (Finset.univ.filter (fun bits : Fin t → Bool =>
    M.output (M.runFrom x c (extendCoins bits) t).state = some true)).card

theorem goodCount_succ (t : ℕ) (c : Configuration q w h x.length) :
    M.goodCount x (t + 1) c = M.goodCount x t (M.step x false c) +
      M.goodCount x t (M.step x true c) := by
  classical
  unfold goodCount
  rw [← Finset.card_map (Fin.consEquiv (fun _ : Fin (t + 1) => Bool)).symm.toEmbedding]
  have hmap : (Finset.univ.filter (fun bits : Fin (t + 1) → Bool =>
      M.output (M.runFrom x c (extendCoins bits) (t + 1)).state = some true)).map
        (Fin.consEquiv (fun _ : Fin (t + 1) => Bool)).symm.toEmbedding =
      Finset.univ.filter (fun p : Bool × (Fin t → Bool) =>
        M.output (M.runFrom x (M.step x p.1 c) (extendCoins p.2) t).state = some true) := by
    ext ⟨b, bits⟩
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter, Finset.mem_univ,
      true_and]
    show M.output (M.runFrom x c (extendCoins (Fin.cons b bits : Fin (t + 1) → Bool))
      (t + 1)).state = some true ↔ _
    rw [runFrom, extendCoins_cons_zero, extendCoins_cons_succ]
  rw [hmap, Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_bool, Finset.card_filter,
    Finset.card_filter]
  exact Nat.add_comm _ _

theorem probFrom_eq_goodCount : ∀ (t : ℕ) (c : Configuration q w h x.length),
    M.probFrom x t c = (M.goodCount x t c : ℚ) / 2 ^ t
  | 0, c => by
      unfold probFrom goodCount
      by_cases ho : M.output c.state = some true
      · simp [ho, runFrom]
      · simp [ho, runFrom]
  | t + 1, c => by
      rw [probFrom, probFrom_eq_goodCount t, probFrom_eq_goodCount t, goodCount_succ]
      push_cast
      ring

/-- **The upstream acceptance probability is the coin-flip recursion from the initial
configuration.** -/
theorem acceptanceProbability_eq_probFrom (t : ℕ) :
    M.acceptanceProbability x t = M.probFrom x t (M.initial x.length) := by
  rw [probFrom_eq_goodCount]
  unfold acceptanceProbability goodCount
  simp only [run_eq_runFrom]

end Machine

end ExactDerandomization
