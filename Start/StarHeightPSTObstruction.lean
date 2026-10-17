import Start.StarHeightPST

/-!
# `L_PST` is not recognized by a metabelian group

* `PST.pst_not_metabelian`: no finite group satisfying `[[x, y], [z, t]] = 1` recognizes `L_PST`.
* `PST.pst_not_abelian_by_abelian`: in particular, no finite group with an abelian normal subgroup
  `N` and abelian quotient `G ⧸ N` recognizes `L_PST`.

Every group-theoretic height-one theorem of this project (prime index, elementary abelian
quotient, `A₄`, the `Z₄` cases) is about such groups, so none of them applies to `L_PST` through a
recognizing group: a proof for `L_PST` has to go through a non-abelian core such as the `S₃`-core
(`Start/StarHeightPST.lean`).

The witness is `W = [[a, b], [a, bb]]`, with `x⁻¹` written as `x^(M-1)` for `M` a multiple of the
orders of both groups.  In any metabelian recognizer `W` acts as the empty word; in the recognizer
`S₄ × Z₂` of `L_PST` it is a nontrivial element of `V₄` that flips the parity of the `b` read in
state `0` (`W ∉ L_PST`, while `ε ∈ L_PST`).
-/

namespace GeneralizedStarHeight

namespace PST

open AB

/-- `u` repeated `n` times. -/
def wrep (u : List AB) (n : ℕ) : List AB := (List.replicate n u).flatten

/-- The commutator word `u v u^(M-1) v^(M-1)`. -/
def commW (M : ℕ) (u v : List AB) : List AB := u ++ v ++ wrep u (M - 1) ++ wrep v (M - 1)

lemma map_wrep {G : Type} [Monoid G] (T : FreeMonoid AB →* G) (u : List AB) (n : ℕ) :
    T (FreeMonoid.ofList (wrep u n)) = T (FreeMonoid.ofList u) ^ n := by
  induction n with
  | zero => simp [wrep]
  | succ n ih =>
      rw [wrep, List.replicate_succ, List.flatten_cons, FreeMonoid.ofList_append, map_mul, ← wrep,
        ih, pow_succ']

lemma map_commW {G : Type} [Group G] (T : FreeMonoid AB →* G) {M : ℕ} (hM : 0 < M)
    (hpow : ∀ g : G, g ^ M = 1) (u v : List AB) :
    T (FreeMonoid.ofList (commW M u v)) =
      T (FreeMonoid.ofList u) * T (FreeMonoid.ofList v) * (T (FreeMonoid.ofList u))⁻¹ *
        (T (FreeMonoid.ofList v))⁻¹ := by
  have hinv : ∀ g : G, g ^ (M - 1) = g⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hM, hpow])
  simp only [commW, FreeMonoid.ofList_append, map_mul, map_wrep, hinv]

/-- The witness `[[a, b], [a, bb]]`. -/
def witness (M : ℕ) : List AB := commW M (commW M [a] [b]) (commW M [a] [b, b])

lemma card_S4Z2 : Fintype.card (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2)) = 48 := by
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  rfl

lemma witness_not_mem (k : ℕ) : witness (48 * (k + 1)) ∉ LPST := by
  have hM : 0 < 48 * (k + 1) := by positivity
  have hpow : ∀ g : Equiv.Perm (Fin 4) × Multiplicative (ZMod 2), g ^ (48 * (k + 1)) = 1 := by
    intro g
    rw [pow_mul, ← card_S4Z2, pow_card_eq_one, one_pow]
  rw [LPST_recognized]
  show ¬ decode (recog (FreeMonoid.ofList _)) = _
  rw [witness, map_commW recog hM hpow, map_commW recog hM hpow, map_commW recog hM hpow]
  decide

/-- **`L_PST` is not recognized by a metabelian group.** -/
theorem pst_not_metabelian {G : Type} [Group G] [Fintype G]
    (hmeta : ∀ x y z t : G, (x * y * x⁻¹ * y⁻¹) * (z * t * z⁻¹ * t⁻¹) * (x * y * x⁻¹ * y⁻¹)⁻¹ *
      (z * t * z⁻¹ * t⁻¹)⁻¹ = 1)
    (T : FreeMonoid AB →* G) (F : Set G) : LPST ≠ {w | T (FreeMonoid.ofList w) ∈ F} := by
  intro hL
  set M := 48 * (Fintype.card G - 1 + 1) with hMdef
  have hcard : Fintype.card G - 1 + 1 = Fintype.card G := Nat.sub_add_cancel Fintype.card_pos
  have hM : 0 < M := by positivity
  have hpow : ∀ g : G, g ^ M = 1 := by
    intro g
    rw [hMdef, hcard, mul_comm, pow_mul, pow_card_eq_one, one_pow]
  have hW : T (FreeMonoid.ofList (witness M)) = T (FreeMonoid.ofList []) := by
    rw [witness, map_commW T hM hpow, map_commW T hM hpow, map_commW T hM hpow, hmeta,
      FreeMonoid.ofList_nil, map_one]
  have h1 : witness M ∈ LPST ↔ ([] : List AB) ∈ LPST := by
    rw [hL]
    show T _ ∈ F ↔ T _ ∈ F
    rw [hW]
  exact witness_not_mem _ (h1.mpr (by rw [LPST_eq_X]; exact Language.nil_mem_kstar _))

/-- **`L_PST` is not recognized by an abelian-by-abelian group.** -/
theorem pst_not_abelian_by_abelian {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hcomm : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ N)
    (T : FreeMonoid AB →* G) (F : Set G) : LPST ≠ {w | T (FreeMonoid.ofList w) ∈ F} := by
  refine pst_not_metabelian (fun x y z t => ?_) T F
  rw [hab _ (hcomm x y) _ (hcomm z t)]
  group

end PST

end GeneralizedStarHeight
