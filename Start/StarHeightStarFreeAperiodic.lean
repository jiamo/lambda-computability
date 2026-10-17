import Start.StarHeightTransfer

/-!
# Star-free languages are aperiodic (the converse of Schützenberger's theorem)

* `aperiodic_of_starFree`: if `L` is star-free (`HasHeightAtMost L 0`), there is `N` such that for
  all words `u v w`, `u vᴺ w ∈ L ↔ u vᴺ⁺¹ w ∈ L` (`wpow`, `Start/StarHeightTransfer.lean`).

The proof is by induction on a star-free expression (an expression of height `0` uses no star).
Letters, `0` and `1` need `N = 2`; union takes the maximum and complement keeps `N`.  For a
concatenation `L₁ L₂` with constants `N₁`, `N₂`, the constant `N₁ + N₂ + 1` works: in a
factorization `u vᴺ w = x y` the cut falls either after the first `N₁` (or `N₁ + 1`) copies of `v`,
and then `x` absorbs a copy, or before them, and then `y` contains the last `N₂` copies.
-/

namespace GeneralizedStarHeight

universe u

open scoped Computability

namespace Aperiodic

variable {A : Type u}

lemma wpow_add (v : List A) (a b : ℕ) : wpow v (a + b) = wpow v a ++ wpow v b := by
  unfold wpow; rw [List.replicate_add, List.flatten_append]

/-- One direction of aperiodicity, at exponent `N`. -/
def PumpUp (L : Language A) (N : ℕ) : Prop :=
  ∀ u v w : List A, u ++ wpow v N ++ w ∈ L → u ++ wpow v (N + 1) ++ w ∈ L

/-- The other direction, at exponent `N`. -/
def PumpDown (L : Language A) (N : ℕ) : Prop :=
  ∀ u v w : List A, u ++ wpow v (N + 1) ++ w ∈ L → u ++ wpow v N ++ w ∈ L

lemma shift_eq (u v w : List A) (N k : ℕ) :
    u ++ wpow v (N + k) ++ w = (u ++ wpow v k) ++ wpow v N ++ w := by
  rw [Nat.add_comm, wpow_add]; simp

lemma PumpUp.mono {L : Language A} {N : ℕ} (h : PumpUp L N) (k : ℕ) : PumpUp L (N + k) := by
  intro u v w hw
  rw [shift_eq] at hw
  have := h _ v w hw
  rwa [← shift_eq, show N + 1 + k = N + k + 1 by omega] at this

lemma PumpDown.mono {L : Language A} {N : ℕ} (h : PumpDown L N) (k : ℕ) :
    PumpDown L (N + k) := by
  intro u v w hw
  rw [show N + k + 1 = N + 1 + k by omega, shift_eq] at hw
  have := h _ v w hw
  rwa [← shift_eq] at this

/-- The combinatorial form of aperiodicity, at exponent `N`. -/
def Pump (L : Language A) (N : ℕ) : Prop :=
  ∀ u v w : List A, u ++ wpow v N ++ w ∈ L ↔ u ++ wpow v (N + 1) ++ w ∈ L

lemma pump_of (L : Language A) {N : ℕ} (h1 : PumpUp L N) (h2 : PumpDown L N) : Pump L N :=
  fun u v w => ⟨h1 u v w, h2 u v w⟩

lemma Pump.up {L : Language A} {N : ℕ} (h : Pump L N) : PumpUp L N := fun u v w => (h u v w).1

lemma Pump.down {L : Language A} {N : ℕ} (h : Pump L N) : PumpDown L N :=
  fun u v w => (h u v w).2

lemma Pump.mono {L : Language A} {N : ℕ} (h : Pump L N) (k : ℕ) : Pump L (N + k) :=
  pump_of L (h.up.mono k) (h.down.mono k)

lemma Pump.mono' {L : Language A} {N M : ℕ} (h : Pump L N) (hNM : N ≤ M) : Pump L M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
  exact h.mono k

/-- A language whose words all have length at most one is aperiodic at `2`. -/
lemma pump_short (L : Language A) (hL : ∀ x ∈ L, x.length ≤ 1) : Pump L 2 := by
  intro u v w
  rcases v with _ | ⟨a, v⟩
  · simp [wpow]
  · constructor <;> intro h <;> have := hL _ h <;> simp [wpow, List.replicate_succ] at this <;>
      omega

lemma pump_add {L M : Language A} {N : ℕ} (hL : Pump L N) (hM : Pump M N) : Pump (L + M) N := by
  intro u v w
  simp only [Language.mem_add]
  rw [hL u v w, hM u v w]

lemma pump_compl {L : Language A} {N : ℕ} (hL : Pump L N) : Pump Lᶜ N := by
  intro u v w
  show _ ∉ L ↔ _ ∉ L
  rw [hL u v w]

lemma pumpUp_mul {L M : Language A} {N₁ N₂ : ℕ} (hL : PumpUp L N₁) (hM : PumpUp M N₂) :
    PumpUp (L * M) (N₁ + N₂) := by
  intro u v w hw
  obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hw
  rw [wpow_add, show u ++ (wpow v N₁ ++ wpow v N₂) ++ w = (u ++ wpow v N₁) ++ (wpow v N₂ ++ w) by
    simp] at hxy
  rcases List.append_eq_append_iff.mp hxy with ⟨a', hx1, hy2⟩ | ⟨c', hx2, hc⟩
  · refine Language.mem_mul.mpr ⟨x, hx, a' ++ wpow v (N₂ + 1) ++ w,
      hM a' v w (by rw [hy2] at hy; simpa using hy), ?_⟩
    rw [show N₁ + N₂ + 1 = N₁ + (N₂ + 1) by omega, wpow_add v N₁ (N₂ + 1)]
    calc x ++ (a' ++ wpow v (N₂ + 1) ++ w) = (x ++ a') ++ wpow v (N₂ + 1) ++ w := by simp
      _ = _ := by rw [← hx1]; simp
  · refine Language.mem_mul.mpr ⟨u ++ wpow v (N₁ + 1) ++ c',
      hL u v c' (by rw [hx2] at hx; simpa using hx), y, hy, ?_⟩
    rw [show N₁ + N₂ + 1 = (N₁ + 1) + N₂ by omega, wpow_add v (N₁ + 1) N₂]
    calc u ++ wpow v (N₁ + 1) ++ c' ++ y = u ++ wpow v (N₁ + 1) ++ (c' ++ y) := by simp
      _ = _ := by rw [← hc]; simp

lemma pumpDown_mul {L M : Language A} {N₁ N₂ : ℕ} (hL : PumpDown L N₁) (hM : PumpDown M N₂) :
    PumpDown (L * M) (N₁ + N₂ + 1) := by
  intro u v w hw
  obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hw
  rw [show N₁ + N₂ + 1 + 1 = (N₁ + 1) + (N₂ + 1) by omega, wpow_add,
    show u ++ (wpow v (N₁ + 1) ++ wpow v (N₂ + 1)) ++ w =
      (u ++ wpow v (N₁ + 1)) ++ (wpow v (N₂ + 1) ++ w) by simp] at hxy
  rcases List.append_eq_append_iff.mp hxy with ⟨a', hx1, hy2⟩ | ⟨c', hx2, hc⟩
  · refine Language.mem_mul.mpr ⟨x, hx, a' ++ wpow v N₂ ++ w,
      hM a' v w (by rw [hy2] at hy; simpa using hy), ?_⟩
    rw [show N₁ + N₂ + 1 = (N₁ + 1) + N₂ by omega, wpow_add v (N₁ + 1) N₂]
    calc x ++ (a' ++ wpow v N₂ ++ w) = (x ++ a') ++ wpow v N₂ ++ w := by simp
      _ = _ := by rw [← hx1]; simp
  · refine Language.mem_mul.mpr ⟨u ++ wpow v N₁ ++ c',
      hL u v c' (by rw [hx2] at hx; simpa using hx), y, hy, ?_⟩
    rw [show N₁ + N₂ + 1 = N₁ + (N₂ + 1) by omega, wpow_add v N₁ (N₂ + 1)]
    calc u ++ wpow v N₁ ++ c' ++ y = u ++ wpow v N₁ ++ (c' ++ y) := by simp
      _ = _ := by rw [← hc]; simp

lemma pump_mul {L M : Language A} {N₁ N₂ : ℕ} (hL : Pump L N₁) (hM : Pump M N₂) :
    Pump (L * M) (N₁ + N₂ + 1) :=
  pump_of _ ((pumpUp_mul hL.up hM.up).mono 1) (pumpDown_mul hL.down hM.down)

lemma pump_of_expression : ∀ P : Expression A, P.height ≤ 0 → ∃ N, Pump P.language N
  | .zero, _ => ⟨2, pump_short _ fun x hx => hx.elim⟩
  | .one, _ => ⟨2, pump_short _ fun x hx => by
      have : x = [] := hx
      simp [this]⟩
  | .letter a, _ => ⟨2, pump_short _ fun x hx => by
      have : x = [a] := hx
      simp [this]⟩
  | .union P Q, h => by
      have hP : P.height ≤ 0 := le_trans (le_max_left _ _) h
      have hQ : Q.height ≤ 0 := le_trans (le_max_right _ _) h
      obtain ⟨N₁, h₁⟩ := pump_of_expression P hP
      obtain ⟨N₂, h₂⟩ := pump_of_expression Q hQ
      exact ⟨max N₁ N₂, pump_add (h₁.mono' (le_max_left _ _)) (h₂.mono' (le_max_right _ _))⟩
  | .concat P Q, h => by
      have hP : P.height ≤ 0 := le_trans (le_max_left _ _) h
      have hQ : Q.height ≤ 0 := le_trans (le_max_right _ _) h
      obtain ⟨N₁, h₁⟩ := pump_of_expression P hP
      obtain ⟨N₂, h₂⟩ := pump_of_expression Q hQ
      exact ⟨N₁ + N₂ + 1, pump_mul h₁ h₂⟩
  | .compl P, h => by
      obtain ⟨N, hN⟩ := pump_of_expression P h
      exact ⟨N, pump_compl hN⟩
  | .star P, h => by
      exfalso
      have : 1 + P.height ≤ 0 := h
      omega

end Aperiodic

/-- **Star-free languages are aperiodic** (the converse of Schützenberger's theorem, in
combinatorial form). -/
theorem aperiodic_of_starFree {A : Type u} {L : Language A} (h : HasHeightAtMost L 0) :
    ∃ N : ℕ, ∀ u v w : List A, u ++ wpow v N ++ w ∈ L ↔ u ++ wpow v (N + 1) ++ w ∈ L := by
  obtain ⟨P, rfl, hP⟩ := h
  exact Aperiodic.pump_of_expression P hP

end GeneralizedStarHeight
