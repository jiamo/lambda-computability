import Start.StarHeightHCore
import Start.StarHeightA4Core
import Start.StarHeightZ4ModTwo
import Start.StarHeightS4

/-!
# The `H`-core modulo `2`, and the wreath product principle at exponent `2`

* `HCoreModTwo H`: every prefix-product count `hcount ρ g x` of `H` has height at most one
  modulo `2`.  It follows from `HCoreHeightOne H` (`HCoreHeightOne.modTwo`) and depends only on
  `H` up to isomorphism (`HCoreModTwo.of_mulEquiv`).
* `hcoreModTwo_zmod_four`: the `ZMod 4`-core modulo `2` holds (from `vcount_z4_mod_two_height`);
  `hcoreModTwo_zmod_prime`: so does the `ZMod p`-core for every prime `p`.
* `height_one_of_exponent_two_normal_of_core_mod_two`: if `N` is an abelian normal subgroup of a
  finite group `G` with `x * x = 1` on `N`, and the `G ⧸ N`-core modulo `2` holds, every language
  recognized by `G` has height at most one (`..._equiv` for `G ⧸ N ≃* H`).  The proof is that of
  `height_one_of_abelian_normal_of_core_equiv` with modulus `2` in place of `2 · |N|`: the
  kernel value only needs the counts modulo `2` (`valN_mod_two`), and the final state of the
  quotient walk is recovered from the counts modulo `2` by the flow identity.
* `height_one_S4_of_core_mod_two`: every language recognized by `S₄`, from the `S₃`-core
  modulo `2` (the Klein kernel has exponent `2`).
* `height_one_of_central_order_two_of_core_mod_two`: a group with a central subgroup of order
  `2` over a quotient whose core modulo `2` holds (e.g. `SL(2,3)` over `A₄`).
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

/-- **The `H`-core modulo `2`.** Every prefix-product count of `H` has height at most one
modulo `2`. -/
def HCoreModTwo (H : Type) [Group H] : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (ρ : α → H) (x : α) (g : H) (k : ℕ), k < 2 →
    HasHeightAtMost {w : List α | hcount ρ g x w % 2 = k} 1

/-- The core for every modulus gives the core modulo `2`. -/
theorem HCoreHeightOne.modTwo {H : Type} [Group H] (h : HCoreHeightOne H) : HCoreModTwo H :=
  fun α _ _ ρ x g k hk => h α ρ x g 2 k hk

namespace HCoreModTwo

variable {H : Type} [Group H]

/-- The core property modulo `2` is invariant under isomorphism. -/
theorem of_mulEquiv {H' : Type} [Group H'] (f : H ≃* H') (h : HCoreModTwo H) :
    HCoreModTwo H' := by
  intro α _ _ ρ x g k hk
  have := h α (fun a => f.symm (ρ a)) x (f.symm g) k hk
  have heq : ({w : List α | hcount ρ g x w % 2 = k} : Language α) =
      {w | hcount (fun a => f.symm (ρ a)) (f.symm g) x w % 2 = k} := by
    ext w
    show hcount ρ g x w % 2 = k ↔ hcount _ _ x w % 2 = k
    rw [hcount_eq_hcountFrom, hcount_eq_hcountFrom,
      ← hcountFrom_mulEquiv f (fun a => f.symm (ρ a)) (f.symm g) x 1 w]
    simp
  rw [heq]
  exact this

/-- The core property modulo `2` for alphabets in any universe. -/
theorem univ (h : HCoreModTwo H) {α : Type u} [Finite α] [DecidableEq α] (ρ : α → H) (x : α)
    (g : H) (k : ℕ) (hk : k < 2) :
    HasHeightAtMost {w : List α | hcount ρ g x w % 2 = k} 1 := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  have h0 := h (Fin m) (fun i => ρ (e.symm i)) (e x) g k hk
  have heq : {w : List α | hcount ρ g x w % 2 = k} =
      invAlph (fun a => some (e a)) {u | hcount (fun i => ρ (e.symm i)) g (e x) u % 2 = k} := by
    ext w
    have hfm : w.filterMap (fun a => some (e a)) = w.map e := by
      induction w with
      | nil => rfl
      | cons b w ih => simp [ih]
    show _ % 2 = k ↔ hcount _ g (e x) (w.filterMap _) % 2 = k
    rw [hfm, hcount_eq_hcountFrom, hcount_eq_hcountFrom, hcountFrom_map e e.injective]
    have : ((fun i => ρ (e.symm i)) ∘ e) = ρ := funext fun a => by simp
    rw [this]
  rw [heq]
  exact h0.invAlph _

end HCoreModTwo

/-- **The `ZMod 4`-core modulo `2`.** -/
theorem hcoreModTwo_zmod_four : HCoreModTwo (Multiplicative (ZMod 4)) := by
  intro α _ _ ρ x g k hk
  have := vcount_z4_mod_two_height (fun a => Multiplicative.toAdd (ρ a)) (Multiplicative.toAdd g)
    x k hk
  simpa only [← hcount_ofAdd_eq_vcount, ofAdd_toAdd] using this

/-- **The `ZMod p`-core modulo `2`**, for every prime `p`. -/
theorem hcoreModTwo_zmod_prime (p : ℕ) [Fact p.Prime] : HCoreModTwo (Multiplicative (ZMod p)) :=
  (hcore_zmod_prime p).modTwo

/-! ### The reduction at exponent `2` -/

section Assembly

open Classical

variable {Alphabet : Type u}

/-- **Reduction to the core modulo `2`, through an isomorphism.** Let `N` be an abelian normal
subgroup of a finite group `G` in which every element has order at most `2`.  If `G ⧸ N ≃* H`
and the `H`-core modulo `2` holds, every language recognized by `G` has generalized star height
at most one. -/
theorem height_one_of_exponent_two_normal_of_core_mod_two_equiv [Finite Alphabet] {G : Type}
    [Group G] [Fintype G] (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hexp : ∀ x ∈ N, x * x = 1) {H : Type} [Group H] (e : G ⧸ N ≃* H) (hcore : HCoreModTwo H)
    (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have := Fintype.ofFinite Alphabet
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hcore' : HCoreModTwo (G ⧸ N) := hcore.of_mulEquiv e.symm
  let ρ : Alphabet → G ⧸ N := fun b => psi N T (FreeMonoid.of b)
  let cnt : (G ⧸ N) × Alphabet → List Alphabet → ℕ := fun pr w => (tpairs N T 1 w).count pr
  have hval : ∀ w : List Alphabet, T (FreeMonoid.ofList w) =
      (valN N T hab (fun pr => cnt pr w % 2) : G) * rep N (psi N T (FreeMonoid.ofList w)) := by
    intro w
    have ht := telescope N T 1 w
    rw [rep_one, one_mul, one_mul, list_prod_cv N T hab, mul_inv_eq_iff_eq_mul,
      valN_mod_card N T hab (fun pr => (tpairs N T 1 w).count pr), valN_mod_two N T hab hexp] at ht
    exact ht
  -- the final state from the counts modulo `2`
  let fin : ((G ⧸ N) × Alphabet → ℕ) → (G ⧸ N) → Prop := fun r q =>
    (if q = 1 then 1 else 0 : ZMod 2) +
      ∑ x, ((r (q * (ρ x)⁻¹, x) : ZMod 2) + (r (q, x) : ZMod 2)) = 1
  have hfin : ∀ (w : List Alphabet) (q : G ⧸ N),
      fin (fun pr => cnt pr w % 2) q ↔ psi N T (FreeMonoid.ofList w) = q := by
    intro w q
    have hmod : ∀ c : ℕ, ((c % 2 : ℕ) : ZMod 2) = (c : ZMod 2) := fun c => ZMod.natCast_mod c 2
    have hid := congrArg (fun n : ℕ => (n : ZMod 2)) (flow_identity N T q w 1)
    simp only [one_mul, Nat.cast_add, Nat.cast_sum] at hid
    show (if q = 1 then 1 else 0 : ZMod 2) +
      ∑ x, (((cnt (q * (ρ x)⁻¹, x) w % 2 : ℕ) : ZMod 2) + ((cnt (q, x) w % 2 : ℕ) : ZMod 2)) = 1 ↔ _
    simp only [hmod, Finset.sum_add_distrib]
    have hc : ∀ (P : Prop) [Decidable P], (((if P then 1 else 0 : ℕ)) : ZMod 2) =
        if P then 1 else 0 := fun P _ => by split_ifs <;> simp
    rw [hc, hc] at hid
    have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
    have key : (if q = 1 then 1 else 0 : ZMod 2) + ((∑ x, (cnt (q * (ρ x)⁻¹, x) w : ZMod 2)) +
        ∑ x, (cnt (q, x) w : ZMod 2)) =
          if psi N T (FreeMonoid.ofList w) = q then 1 else 0 := by
      have hq1 : (if (1 : G ⧸ N) = q then 1 else 0 : ZMod 2) = if q = 1 then 1 else 0 := by
        simp only [eq_comm]
      rw [hq1] at hid
      calc _ = ((∑ x, (cnt (q * (ρ x)⁻¹, x) w : ZMod 2)) + (if q = 1 then 1 else 0 : ZMod 2)) +
              ∑ x, (cnt (q, x) w : ZMod 2) := by ring
        _ = _ := by
          rw [show (∑ x, (cnt (q * (ρ x)⁻¹, x) w : ZMod 2)) = ∑ x,
            ((tpairs N T 1 w).count (q * (psi N T (FreeMonoid.of x))⁻¹, x) : ZMod 2) from rfl,
            hid]
          rw [show (∑ x, (cnt (q, x) w : ZMod 2)) = ∑ x, ((tpairs N T 1 w).count (q, x) : ZMod 2)
            from rfl]
          rw [add_right_comm, h2, zero_add]
    rw [key]
    split_ifs with h
    · simp [h]
    · simp only [zero_ne_one, false_iff]; exact h
  refine height_one_of_residues_univ (ι := (G ⧸ N) × Alphabet) cnt (M := 2) (by norm_num) ?_ _
    (fun r => ∃ q, fin r q ∧ (valN N T hab r : G) * rep N q ∈ F) ?_
  · intro pr r hr
    have := hcore'.univ ρ pr.2 pr.1 r hr
    have heq : ({w | cnt pr w % 2 = r} : Language Alphabet) = {w | hcount ρ pr.1 pr.2 w % 2 = r} := by
      ext w
      show (tpairs N T 1 w).count pr % 2 = r ↔ hcount ρ pr.1 pr.2 w % 2 = r
      rw [hcount_eq_hcountFrom, ← tpairs_count_eq_hcountFrom]
    rw [heq]
    exact this
  · intro w
    show T (FreeMonoid.ofList w) ∈ F ↔ _
    constructor
    · intro hw
      exact ⟨psi N T (FreeMonoid.ofList w), (hfin w _).mpr rfl, by rw [← hval]; exact hw⟩
    · rintro ⟨q, hq, hF⟩
      have hpq := (hfin w q).mp hq
      rw [hval, hpq]
      exact hF

/-- **The wreath product principle at exponent `2`, with the core modulo `2`.** If `N` is an
abelian normal subgroup of a finite group `G` in which every element has order at most `2`, and
the `G ⧸ N`-core modulo `2` holds, every language recognized by `G` has generalized star height
at most one.  No hypothesis on the fibres of the walk in `G ⧸ N` is needed. -/
theorem height_one_of_exponent_two_normal_of_core_mod_two [Finite Alphabet] {G : Type} [Group G]
    [Fintype G] (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hexp : ∀ x ∈ N, x * x = 1) (hcore : HCoreModTwo (G ⧸ N)) (T : FreeMonoid Alphabet →* G)
    (F : Set G) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 :=
  height_one_of_exponent_two_normal_of_core_mod_two_equiv N hab hexp (MulEquiv.refl _) hcore T F

/-- **A central subgroup of order `2`.** If `N` is a central subgroup of order `2` of a finite
group `G`, `G ⧸ N ≃* H` and the `H`-core modulo `2` holds, every language recognized by `G` has
generalized star height at most one. -/
theorem height_one_of_central_order_two_of_core_mod_two [Finite Alphabet] {G : Type} [Group G]
    [Fintype G] (N : Subgroup G) [N.Normal] (hcen : ∀ x ∈ N, ∀ y : G, x * y = y * x)
    (hcard : Nat.card N = 2) {H : Type} [Group H] (e : G ⧸ N ≃* H) (hcore : HCoreModTwo H) (T : FreeMonoid Alphabet →* G)
    (F : Set G) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_exponent_two_normal_of_core_mod_two_equiv N (fun x hx y _ => hcen x hx y)
    (fun x hx => ?_) e hcore T F
  have h1 : (⟨x, hx⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
  rw [hcard, pow_two] at h1
  exact congrArg Subtype.val h1

/-- **A central extension of `A₄` by `Z₂`** (such as `SL(2,3)`): if the `A₄`-core modulo `2`
holds, every language recognized by `G` has generalized star height at most one. -/
theorem height_one_of_central_order_two_over_A4_of_core_mod_two [Finite Alphabet] {G : Type}
    [Group G] [Fintype G] (N : Subgroup G) [N.Normal] (hcen : ∀ x ∈ N, ∀ y : G, x * y = y * x)
    (hcard : Nat.card N = 2) (e : G ⧸ N ≃* alternatingGroup (Fin 4))
    (hcore : HCoreModTwo (alternatingGroup (Fin 4))) (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 :=
  height_one_of_central_order_two_of_core_mod_two N hcen hcard e hcore T F

end Assembly

/-! ### `S₄` over the `S₃`-core modulo `2` -/

/-- The Klein kernel of `S₄ → S₃` has exponent `2`. -/
lemma S4Klein.ker_sq : ∀ x ∈ S4Klein.kleinHom.ker, x * x = 1 := by
  intro x hx
  ext i
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id_eq]
  rw [S4Klein.mem_ker_apply hx (x i), S4Klein.mem_ker_apply hx i]
  generalize x 0 = a
  revert a i
  decide

/-- **`S₄` over the `S₃`-core modulo `2`.** If the `S₃`-core holds modulo `2`, every language
recognized by `S₄` has generalized star height at most one. -/
theorem height_one_S4_of_core_mod_two (hcore : HCoreModTwo (Equiv.Perm (Fin 3)))
    {Alphabet : Type u} [Finite Alphabet] (T : FreeMonoid Alphabet →* Equiv.Perm (Fin 4))
    (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 :=
  height_one_of_exponent_two_normal_of_core_mod_two_equiv S4Klein.kleinHom.ker S4Klein.ker_comm
    S4Klein.ker_sq S4Klein.quotEquiv hcore T F

end GeneralizedStarHeight
