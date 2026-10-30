import Start.StarHeightZ4Moving

/-!
# `Z4CorePM1`: the `Z₄` core with displacements `±1` (no displacement `2`)

* `z4core_pm1 : Z4CorePM1`.  Letters of displacement `0` other than the counted letter `x` are
  erased, the letters of displacement `+1` other than `x` are merged into `b`, those of
  displacement `-1` into `d` (an inverse alphabetic morphism, `vcountFrom_filterMap_zc`), and when
  `δ x = 3` the automorphism `q ↦ -q` of `ZMod 4` makes `δ x = 1`.  This leaves
  - case (a), `δ x = 0`: `zcA_height` (`Start/StarHeightZ4Walk.lean`);
  - case (m), `δ x = 1`: `zcM_height` (`Start/StarHeightZ4Moving.lean`).
* `z4core_of_rot2`: `Z4CoreHeightOne` follows from `Z4CoreRot2` alone.
* `height_one_F20_of_rot2`: every language recognized by the Frobenius group `F₂₀` has generalized
  star height at most one, provided `Z4CoreRot2` holds.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

/-- Transport of the count along an alphabetic morphism onto the alphabet `Fin 3`. -/
lemma vcountFrom_filterMap_zc {α : Type} [DecidableEq α] (δ : α → ZMod 4) (x : α)
    (σ : Fin 3 → ZMod 4) (φ : α → Option (Fin 3))
    (h0 : ∀ y, φ y = none → δ y = 0 ∧ y ≠ x)
    (h1 : ∀ y c, φ y = some c → σ c = δ y ∧ (y = x ↔ c = 0)) :
    ∀ (w : List α) (s : ZMod 4), vcountFrom δ 0 x s w = zc σ s (w.filterMap φ)
  | [], s => by simp [vcountFrom_nil, zc]
  | b :: w, s => by
      rw [vcountFrom_cons]
      cases hb : φ b with
      | none =>
          obtain ⟨hd, hx⟩ := h0 b hb
          rw [List.filterMap_cons, hb, ite_eq_right (fun h => hx h.1), hd, add_zero, zero_add]
          exact vcountFrom_filterMap_zc δ x σ φ h0 h1 w s
      | some c =>
          obtain ⟨hd, hx⟩ := h1 b c hb
          rw [List.filterMap_cons, hb, zc, ← hd, vcountFrom_filterMap_zc δ x σ φ h0 h1 w]
          congr 1
          by_cases hc : c = 0 ∧ s = 0
          · rw [ite_eq_left hc, ite_eq_left ⟨hx.mpr hc.1, hc.2⟩]
          · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨hx.mp h.1, h.2⟩)]

/-- The cases `δ x = 0` and `δ x = 1`. -/
theorem pm1_core_of_nonneg (α : Type) [Fintype α] [DecidableEq α] (δ : α → ZMod 4) (x : α)
    (n k : ℕ) (hk : k < n) (h2 : ∀ y, δ y ≠ 2) (hx : δ x = 0 ∨ δ x = 1) :
    HasHeightAtMost {w : List α | vcount δ 0 x w % n = k} 1 := by
  let φ : α → Option (Fin 3) := fun y =>
    if y = x then some 0 else if δ y = 1 then some 1 else if δ y = 3 then some 2 else none
  let σ : Fin 3 → ZMod 4 := if δ x = 0 then σa else σm
  have h0 : ∀ y, φ y = none → δ y = 0 ∧ y ≠ x := by
    intro y hy
    simp only [φ] at hy
    split_ifs at hy with e1 e2 e3
    refine ⟨?_, e1⟩
    rcases zmod4_cases (δ y) with e | e | e | e
    · exact e
    · exact absurd e e2
    · exact absurd e (h2 y)
    · exact absurd e e3
  have h1 : ∀ y c, φ y = some c → σ c = δ y ∧ (y = x ↔ c = 0) := by
    intro y c hy
    simp only [φ] at hy
    split_ifs at hy with e1 e2 e3 <;> simp only [Option.some.injEq] at hy <;> subst hy
    · subst e1
      refine ⟨?_, by simp⟩
      rcases hx with e | e
      · simp only [σ, ite_eq_left e, e]; rfl
      · simp only [σ, ite_eq_right (show δ y ≠ 0 by rw [e]; decide), e]; rfl
    · refine ⟨?_, by simp [e1]⟩
      rw [e2]
      simp only [σ]
      split_ifs <;> rfl
    · refine ⟨?_, by simp [e1]⟩
      rw [e3]
      simp only [σ]
      split_ifs <;> rfl
  have heq : ({w : List α | vcount δ 0 x w % n = k} : Language α) =
      invAlph φ {u : List (Fin 3) | zc σ 0 u % n = k} := by
    ext w
    show vcount δ 0 x w % n = k ↔ zc σ 0 (w.filterMap φ) % n = k
    rw [vcount_eq_vcountFrom, vcountFrom_filterMap_zc δ x σ φ h0 h1 w 0]
  rw [heq]
  rcases hx with e | e
  · have hσ : σ = σa := by simp only [σ, ite_eq_left e]
    rw [hσ]
    exact (zcA_height hk).invAlph φ
  · have hσ : σ = σm := by simp only [σ, ite_eq_right (show δ x ≠ 0 by rw [e]; decide)]
    rw [hσ]
    exact (zcM_height hk).invAlph φ

/-- **The `Z₄` core with displacements `±1`** (M28-STARHEIGHT-Z4-PM1). -/
theorem z4core_pm1 : Z4CorePM1 := by
  intro α _ _ δ x n k hk h2 _ _
  rcases zmod4_cases (δ x) with e | e | e | e
  · exact pm1_core_of_nonneg α δ x n k hk h2 (Or.inl e)
  · exact pm1_core_of_nonneg α δ x n k hk h2 (Or.inr e)
  · exact absurd e (h2 x)
  · have hneg : ∀ w, vcount δ 0 x w = vcount (fun a => -δ a) 0 x w := by
      intro w
      rw [vcount_eq_vcountFrom, vcount_eq_vcountFrom,
        ← vcountFrom_hom (negAddMonoidHom : ZMod 4 →+ ZMod 4) neg_injective δ 0 x 0 w]
      simp
    have : ({w : List α | vcount δ 0 x w % n = k} : Language α) =
        {w : List α | vcount (fun a => -δ a) 0 x w % n = k} := by
      ext w; show _ % n = k ↔ _ % n = k; rw [hneg]
    rw [this]
    refine pm1_core_of_nonneg α _ x n k hk (fun y => ?_) (Or.inr (by rw [e]; decide))
    intro hy
    exact h2 y (by rw [← neg_neg (δ y), hy]; decide)

/-- **The `Z₄` core from its rotation-`2` case alone.** -/
theorem z4core_of_rot2 (h2 : Z4CoreRot2) : Z4CoreHeightOne :=
  z4core_of_rot2_pm1 h2 z4core_pm1

/-- **`F₂₀`, conditional on `Z4CoreRot2` only.** -/
theorem height_one_F20_of_rot2 (h2 : Z4CoreRot2) {Alphabet : Type u} [Finite Alphabet]
    (T : FreeMonoid Alphabet →* F20) (F : Set F20) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 :=
  height_one_F20_of_rot2_pm1 h2 z4core_pm1 T F

end GeneralizedStarHeight
