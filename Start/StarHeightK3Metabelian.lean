import Start.StarHeightPSTLanguage
import Mathlib.GroupTheory.Solvable

/-!
# No metabelian group recognizes the count `K3`

Task `M28-STARHEIGHT-S3-CORE`, item S1 of big round 2 (run 4; rebuilt in run 7).

`K3 k = {w | b0count 0 w % 3 = k}` counts, modulo `3`, the letters `b` read in the state `0` of the
PST automaton (`Start/StarHeightPSTLanguage.lean`).

* `k3Perm w : Equiv.Perm (Fin 3 × ZMod 3)`, the action of `w` on (state, count modulo `3`);
  `k3Perm_apply`: it sends `(s, c)` to `(stateOf s w, c + b0count s w)`.
* `k3_doubleCommutator` (`decide`): `⁅⁅k3Perm [b,b], k3Perm [a]⁆, ⁅k3Perm [b], k3Perm [a]⁆⁆` is the
  shift `c ↦ c + 2` in every state.
* `K3_not_recognized_metabelian`: no finite group with trivial double commutators
  `⁅⁅g₁, g₂⁆, ⁅g₃, g₄⁆⁆ = 1` recognizes `K3 k` (`k < 3`);
  `K3_not_recognized_of_derivedSeries_two`: the same for `derivedSeries Γ 2 = ⊥`.

Proof: for `N = |Γ| · |Perm (Fin 3 × ZMod 3)|`, the word `u^(N-1)` acts as the inverse of `u` both in
`Γ` and on (state, count). The double-commutator word `W` on `a, b, a, bb` therefore maps to `1` in
`Γ` and adds `2` to the count from every state, so `(bb)^k W` and `(bb)^k` are identified by `Γ`
while their counts are `k + 2` and `k` modulo `3`.

This is a statement about recognizers, not about star height.
-/

open scoped commutatorElement

namespace GeneralizedStarHeight

namespace PST

open AB

/-- One letter acting on (state, count modulo `3`). -/
def k3StepFun (x : AB) (p : Fin 3 × ZMod 3) : Fin 3 × ZMod 3 :=
  (move p.1 x, p.2 + if x = b ∧ p.1 = 0 then 1 else 0)

/-- Its inverse (each letter is an involution on states). -/
def k3StepInv (x : AB) (p : Fin 3 × ZMod 3) : Fin 3 × ZMod 3 :=
  (move p.1 x, p.2 - if x = b ∧ move p.1 x = 0 then 1 else 0)

/-- One letter as a permutation of (state, count modulo `3`). -/
def k3Step (x : AB) : Equiv.Perm (Fin 3 × ZMod 3) where
  toFun := k3StepFun x
  invFun := k3StepInv x
  left_inv := by cases x <;> decide
  right_inv := by cases x <;> decide

/-- The action of a word on (state, count modulo `3`); the first letter acts first. -/
def k3Perm : List AB → Equiv.Perm (Fin 3 × ZMod 3)
  | [] => 1
  | x :: w => k3Perm w * k3Step x

theorem k3Perm_apply (w : List AB) (s : Fin 3) (c : ZMod 3) :
    k3Perm w (s, c) = (stateOf s w, c + (b0count s w : ZMod 3)) := by
  induction w generalizing s c with
  | nil => simp [k3Perm, stateOf, b0count]
  | cons x w ih =>
    show k3Perm w (k3StepFun x (s, c)) = _
    simp only [k3StepFun, ih, stateOf_cons, b0count, Nat.cast_add, Prod.mk.injEq, true_and]
    split_ifs <;> simp [add_assoc]

theorem k3Perm_append (u v : List AB) : k3Perm (u ++ v) = k3Perm v * k3Perm u := by
  induction u with
  | nil => simp [k3Perm]
  | cons x u ih => simp [k3Perm, ih, mul_assoc]

/-- The word `u` repeated `n` times. -/
def k3rep (n : ℕ) (u : List AB) : List AB := (List.replicate n u).flatten

theorem k3rep_succ (n : ℕ) (u : List AB) : k3rep (n + 1) u = k3rep n u ++ u := by
  simp [k3rep, List.replicate_succ']

theorem k3Perm_k3rep (n : ℕ) (u : List AB) : k3Perm (k3rep n u) = k3Perm u ^ n := by
  induction n with
  | zero => simp [k3rep, k3Perm]
  | succ n ih => rw [k3rep_succ, k3Perm_append, ih, pow_succ']

theorem T_k3rep {Γ : Type*} [Monoid Γ] (T : FreeMonoid AB →* Γ) (n : ℕ) (u : List AB) :
    T (FreeMonoid.ofList (k3rep n u)) = T (FreeMonoid.ofList u) ^ n := by
  induction n with
  | zero => simp [k3rep]
  | succ n ih => rw [k3rep_succ, FreeMonoid.ofList_append, map_mul, ih, pow_succ]

/-- **The double commutator** of the actions of `bb`, `a`, `b`, `a` is the shift by `2`. -/
theorem k3_doubleCommutator :
    ⁅⁅k3Perm [b, b], k3Perm [a]⁆, ⁅k3Perm [b], k3Perm [a]⁆⁆ =
      Equiv.prodCongr (Equiv.refl (Fin 3)) (Equiv.addRight (2 : ZMod 3)) := by
  decide

theorem k3_pow_pred_eq_inv {G : Type*} [Group G] {N : ℕ} (hN : 0 < N) {g : G} (hg : g ^ N = 1) :
    g ^ (N - 1) = g⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, Nat.sub_add_cancel hN, hg]

section Word

variable (N : ℕ)

/-- `u^(N-1)`, an inverse of `u` once `N` is a common exponent. -/
def k3inv (u : List AB) : List AB := k3rep (N - 1) u

/-- The commutator word `u⁻¹ v⁻¹ u v`. -/
def k3comm (u v : List AB) : List AB := k3inv N u ++ k3inv N v ++ u ++ v

/-- The double-commutator word on `a`, `b`, `a`, `bb`. -/
def k3W : List AB := k3comm N (k3comm N [a] [b]) (k3comm N [a] [b, b])

end Word

theorem k3Perm_k3inv {N : ℕ} (hN : 0 < N) (hP : ∀ g : Equiv.Perm (Fin 3 × ZMod 3), g ^ N = 1)
    (u : List AB) : k3Perm (k3inv N u) = (k3Perm u)⁻¹ := by
  rw [k3inv, k3Perm_k3rep, k3_pow_pred_eq_inv hN (hP _)]

theorem k3Perm_k3comm {N : ℕ} (hN : 0 < N) (hP : ∀ g : Equiv.Perm (Fin 3 × ZMod 3), g ^ N = 1)
    (u v : List AB) : k3Perm (k3comm N u v) = ⁅k3Perm v, k3Perm u⁆ := by
  simp only [k3comm, k3Perm_append, k3Perm_k3inv hN hP, commutatorElement_def, mul_assoc]

theorem T_k3inv {Γ : Type*} [Group Γ] (T : FreeMonoid AB →* Γ) {N : ℕ} (hN : 0 < N)
    (hΓ : ∀ g : Γ, g ^ N = 1) (u : List AB) :
    T (FreeMonoid.ofList (k3inv N u)) = (T (FreeMonoid.ofList u))⁻¹ := by
  rw [k3inv, T_k3rep, k3_pow_pred_eq_inv hN (hΓ _)]

theorem T_k3comm {Γ : Type*} [Group Γ] (T : FreeMonoid AB →* Γ) {N : ℕ} (hN : 0 < N)
    (hΓ : ∀ g : Γ, g ^ N = 1) (u v : List AB) :
    T (FreeMonoid.ofList (k3comm N u v)) =
      ⁅(T (FreeMonoid.ofList u))⁻¹, (T (FreeMonoid.ofList v))⁻¹⁆ := by
  simp only [k3comm, FreeMonoid.ofList_append, map_mul, T_k3inv T hN hΓ, commutatorElement_def,
    inv_inv]

/-- The word `W` acts as the shift by `2`. -/
theorem k3Perm_k3W {N : ℕ} (hN : 0 < N) (hP : ∀ g : Equiv.Perm (Fin 3 × ZMod 3), g ^ N = 1)
    (s : Fin 3) (c : ZMod 3) : k3Perm (k3W N) (s, c) = (s, c + 2) := by
  rw [k3W, k3Perm_k3comm hN hP, k3Perm_k3comm hN hP, k3Perm_k3comm hN hP, k3_doubleCommutator]
  rfl

/-- `W` maps to `1` in a group with trivial double commutators. -/
theorem T_k3W {Γ : Type*} [Group Γ] (hΓ2 : ∀ g₁ g₂ g₃ g₄ : Γ, ⁅⁅g₁, g₂⁆, ⁅g₃, g₄⁆⁆ = 1)
    (T : FreeMonoid AB →* Γ) {N : ℕ} (hN : 0 < N) (hΓ : ∀ g : Γ, g ^ N = 1) :
    T (FreeMonoid.ofList (k3W N)) = 1 := by
  rw [k3W, T_k3comm T hN hΓ, T_k3comm T hN hΓ, T_k3comm T hN hΓ, commutatorElement_inv,
    commutatorElement_inv]
  exact hΓ2 _ _ _ _

theorem b0count_k3rep_bb (n : ℕ) : stateOf 0 (k3rep n [b, b]) = 0 ∧ b0count 0 (k3rep n [b, b]) = n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [k3rep_succ, stateOf_append, b0count_append, ih.1, ih.2]
    exact ⟨rfl, rfl⟩

/-- **No metabelian group recognizes `K3 k`.** -/
theorem K3_not_recognized_metabelian {Γ : Type*} [Group Γ] [Finite Γ]
    (hΓ2 : ∀ g₁ g₂ g₃ g₄ : Γ, ⁅⁅g₁, g₂⁆, ⁅g₃, g₄⁆⁆ = 1) {k : ℕ} (hk : k < 3)
    (T : FreeMonoid AB →* Γ) (F : Set Γ) :
    {w : List AB | b0count 0 w % 3 = k} ≠ {w | T (FreeMonoid.ofList w) ∈ F} := by
  intro hL
  set N := Nat.card Γ * Nat.card (Equiv.Perm (Fin 3 × ZMod 3)) with hNdef
  have hN : 0 < N := Nat.mul_pos Nat.card_pos Nat.card_pos
  have hΓ : ∀ g : Γ, g ^ N = 1 := fun g => by
    rw [hNdef, pow_mul, pow_card_eq_one', one_pow]
  have hP : ∀ g : Equiv.Perm (Fin 3 × ZMod 3), g ^ N = 1 := fun g => by
    rw [hNdef, mul_comm, pow_mul, pow_card_eq_one', one_pow]
  obtain ⟨h0s, h0c⟩ := b0count_k3rep_bb k
  have hu : k3rep k [b, b] ∈ {w : List AB | b0count 0 w % 3 = k} := by
    show b0count 0 _ % 3 = k
    rw [h0c, Nat.mod_eq_of_lt hk]
  have hv : k3rep k [b, b] ++ k3W N ∈ {w | T (FreeMonoid.ofList w) ∈ F} := by
    rw [hL] at hu
    show T (FreeMonoid.ofList _) ∈ F
    rwa [FreeMonoid.ofList_append, map_mul, T_k3W hΓ2 T hN hΓ, mul_one]
  rw [← hL] at hv
  have hv' : b0count 0 (k3rep k [b, b] ++ k3W N) % 3 = k := hv
  rw [b0count_append, h0s, h0c] at hv'
  have hW := k3Perm_k3W hN hP 0 0
  rw [k3Perm_apply, Prod.mk.injEq, zero_add] at hW
  have h2 : ((b0count 0 (k3W N) : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := by
    rw [hW.2]; rfl
  rw [ZMod.natCast_eq_natCast_iff'] at h2
  omega

/-- The same, for `derivedSeries Γ 2 = ⊥`. -/
theorem K3_not_recognized_of_derivedSeries_two {Γ : Type*} [Group Γ] [Finite Γ]
    (hΓ : derivedSeries Γ 2 = ⊥) {k : ℕ} (hk : k < 3) (T : FreeMonoid AB →* Γ) (F : Set Γ) :
    {w : List AB | b0count 0 w % 3 = k} ≠ {w | T (FreeMonoid.ofList w) ∈ F} := by
  refine K3_not_recognized_metabelian (fun g₁ g₂ g₃ g₄ => ?_) hk T F
  have h1 : ∀ g h : Γ, ⁅g, h⁆ ∈ derivedSeries Γ 1 := fun g h => by
    rw [derivedSeries_succ]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)
  have h2 : ⁅⁅g₁, g₂⁆, ⁅g₃, g₄⁆⁆ ∈ derivedSeries Γ 2 := by
    rw [derivedSeries_succ]
    exact Subgroup.commutator_mem_commutator (h1 _ _) (h1 _ _)
  rw [hΓ] at h2
  exact (Subgroup.mem_bot).mp h2

end PST

end GeneralizedStarHeight
