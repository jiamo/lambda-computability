import Start.StarHeightElementary

/-!
# The `H`-core and the reduction to it

* `hcount ρ g x w`: the number of positions `i` of `w` with `w[i] = x` whose prefix product
  `((w.take i).map ρ).prod` (left to right) is `g`.
* `HCoreHeightOne H`: every `hcount ρ g x` has height at most one modulo every `n`.
* `HCoreHeightOne.of_mulEquiv`: the property depends only on `H` up to isomorphism.
* `hcount_ofAdd_eq_vcount`, `hcore_zmod_four_iff`: for `H = ZMod 4`, written multiplicatively,
  `hcount` is `vcount`, and `HCoreHeightOne` is equivalent to `Z4CoreHeightOne`.
* `hcore_zmod_prime`: the `ZMod p`-core holds for every prime `p` (from `zpcore`).
* `height_one_of_abelian_normal_of_core`: if `N` is an abelian normal subgroup of `G` and the
  `G ⧸ N`-core holds, every language recognized by `G` has height at most one
  (`height_one_of_abelian_normal_of_core_equiv` for an isomorphism `G ⧸ N ≃* H`).

The reduction is the wreath product principle as in `Start/StarHeightIndexPrime.lean`: the
telescoping writes `T w` through the counts of pairs (state in `G ⧸ N`, letter) modulo `|N|`.  The
final state `ψ w` is recovered from the same counts modulo `2` by the flow identity
`Σₓ #(enter q by x) + [q = 1] = Σₓ #(leave q by x) + [ψ w = q]` (`flow_identity`), so no
hypothesis on the quotient beyond its core is needed.
-/

namespace GeneralizedStarHeight

universe u v

open EpisodeAlgebra
open scoped Computability

/-! ### Prefix-product counts -/

section HCount

variable {α : Type u} [DecidableEq α] {H : Type}

open Classical

/-- The number of positions `i` with `w[i] = x` and `((w.take i).map ρ).prod = g`. -/
noncomputable def hcount [Monoid H] (ρ : α → H) (g : H) (x : α) (w : List α) : ℕ :=
  ((Finset.range w.length).filter
    (fun i => w[i]? = some x ∧ ((w.take i).map ρ).prod = g)).card

/-- `hcount`, read from the state `s`. -/
noncomputable def hcountFrom [Monoid H] (ρ : α → H) (g : H) (x : α) (s : H) (w : List α) : ℕ :=
  ((Finset.range w.length).filter
    (fun i => w[i]? = some x ∧ s * ((w.take i).map ρ).prod = g)).card

lemma hcount_eq_hcountFrom [Monoid H] (ρ : α → H) (g : H) (x : α) (w : List α) :
    hcount ρ g x w = hcountFrom ρ g x 1 w := by
  unfold hcount hcountFrom
  congr 1
  exact Finset.filter_congr fun i _ => by rw [one_mul]

lemma hcountFrom_nil [Monoid H] (ρ : α → H) (g : H) (x : α) (s : H) :
    hcountFrom ρ g x s [] = 0 := by
  simp [hcountFrom]

lemma hcountFrom_cons [Monoid H] (ρ : α → H) (g : H) (x : α) (s : H) (b : α) (w : List α) :
    hcountFrom ρ g x s (b :: w) =
      (if b = x ∧ s = g then 1 else 0) + hcountFrom ρ g x (s * ρ b) w := by
  simp only [hcountFrom, Finset.card_filter, List.length_cons, Finset.sum_range_succ']
  rw [add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [List.take_succ_cons, mul_assoc]

/-- Prefix counts along an injective renaming of letters. -/
lemma hcountFrom_map {β : Type v} [DecidableEq β] [Monoid H] (e : α → β)
    (he : Function.Injective e) (ρ : β → H) (g : H) (x : α) :
    ∀ (s : H) (w : List α), hcountFrom ρ g (e x) s (w.map e) = hcountFrom (ρ ∘ e) g x s w
  | s, [] => by simp [hcountFrom_nil]
  | s, b :: w => by
      rw [List.map_cons, hcountFrom_cons, hcountFrom_cons, hcountFrom_map e he ρ g x _ w]
      simp [he.eq_iff]

/-- Prefix counts along a monoid isomorphism. -/
lemma hcountFrom_mulEquiv {H' : Type} [Monoid H] [Monoid H'] (f : H ≃* H') (ρ : α → H) (g : H)
    (x : α) : ∀ (s : H) (w : List α),
      hcountFrom (fun a => f (ρ a)) (f g) x (f s) w = hcountFrom ρ g x s w
  | s, [] => by simp [hcountFrom_nil]
  | s, b :: w => by
      rw [hcountFrom_cons, hcountFrom_cons, ← map_mul, hcountFrom_mulEquiv f ρ g x _ w]
      simp [f.injective.eq_iff]

end HCount

/-- **The `H`-core.** Every prefix-product count of `H` has height at most one modulo every `n`. -/
def HCoreHeightOne (H : Type) [Group H] : Prop := ∀ (α : Type) [Fintype α] [DecidableEq α] (ρ : α → H) (x : α) (g : H) (n k : ℕ),
  k < n → HasHeightAtMost {w : List α | hcount ρ g x w % n = k} 1

namespace HCoreHeightOne

variable {H : Type} [Group H]

/-- The core property is invariant under isomorphism. -/
theorem of_mulEquiv {H' : Type} [Group H'] (f : H ≃* H') (h : HCoreHeightOne H) :
    HCoreHeightOne H' := by
  intro α _ _ ρ x g n k hk
  have := h α (fun a => f.symm (ρ a)) x (f.symm g) n k hk
  have heq : ({w : List α | hcount ρ g x w % n = k} : Language α) =
      {w | hcount (fun a => f.symm (ρ a)) (f.symm g) x w % n = k} := by
    ext w
    show hcount ρ g x w % n = k ↔ hcount _ _ x w % n = k
    rw [hcount_eq_hcountFrom, hcount_eq_hcountFrom,
      ← hcountFrom_mulEquiv f (fun a => f.symm (ρ a)) (f.symm g) x 1 w]
    simp
  rw [heq]
  exact this

/-- The core property for alphabets in any universe. -/
theorem univ (h : HCoreHeightOne H) {α : Type u} [Finite α] [DecidableEq α] (ρ : α → H) (x : α)
    (g : H) (n k : ℕ) (hk : k < n) :
    HasHeightAtMost {w : List α | hcount ρ g x w % n = k} 1 := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  have h0 := h (Fin m) (fun i => ρ (e.symm i)) (e x) g n k hk
  have heq : {w : List α | hcount ρ g x w % n = k} =
      invAlph (fun a => some (e a)) {u | hcount (fun i => ρ (e.symm i)) g (e x) u % n = k} := by
    ext w
    have hfm : w.filterMap (fun a => some (e a)) = w.map e := by
      induction w with
      | nil => rfl
      | cons b w ih => simp [ih]
    show _ % n = k ↔ hcount _ g (e x) (w.filterMap _) % n = k
    rw [hfm, hcount_eq_hcountFrom, hcount_eq_hcountFrom, hcountFrom_map e e.injective]
    have : ((fun i => ρ (e.symm i)) ∘ e) = ρ := funext fun a => by simp
    rw [this]
  rw [heq]
  exact h0.invAlph _

end HCoreHeightOne

/-! ### `ZMod 4` and `ZMod p` -/

/-- For an additive group written multiplicatively, `hcount` is `vcount`. -/
lemma hcountFrom_ofAdd_eq_vcountFrom {α : Type u} [DecidableEq α] {V : Type} [AddMonoid V]
    (δ : α → V) (q : V) (x : α) : ∀ (s : V) (w : List α),
      hcountFrom (fun a => Multiplicative.ofAdd (δ a)) (Multiplicative.ofAdd q) x
        (Multiplicative.ofAdd s) w = vcountFrom δ q x s w
  | s, [] => by simp [hcountFrom_nil, vcountFrom_nil]
  | s, b :: w => by
      rw [hcountFrom_cons, vcountFrom_cons, ← ofAdd_add, hcountFrom_ofAdd_eq_vcountFrom δ q x _ w]
      by_cases hs : s = q
      · subst hs; simp
      · have hs' : Multiplicative.ofAdd s ≠ Multiplicative.ofAdd q :=
          fun h => hs (Multiplicative.ofAdd.injective h)
        simp [hs, hs']

/-- **Bridge.** For `H = ZMod 4`, written multiplicatively, `hcount` is `vcount`. -/
lemma hcount_ofAdd_eq_vcount {α : Type u} [DecidableEq α] (δ : α → ZMod 4) (q : ZMod 4) (x : α)
    (w : List α) :
    hcount (fun a => Multiplicative.ofAdd (δ a)) (Multiplicative.ofAdd q) x w = vcount δ q x w := by
  rw [hcount_eq_hcountFrom, vcount_eq_vcountFrom, ← hcountFrom_ofAdd_eq_vcountFrom]
  rfl

/-- `Z4CoreHeightOne` is the `ZMod 4`-core, read at every state. -/
theorem vcount_z4_height (h4 : Z4CoreHeightOne) {α : Type u} [Finite α]
    [DecidableEq α] (δ : α → ZMod 4) (q : ZMod 4) (x : α) (n k : ℕ) (hk : k < n) :
    HasHeightAtMost {w : List α | vcount δ q x w % n = k} 1 := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  let δ' : Option (Fin m) → ZMod 4 := fun o => o.elim (-q) (fun i => δ (e.symm i))
  let g : α → Option (Fin m) := fun a => some (e a)
  have hg : Function.Injective g := fun a b h => e.injective (Option.some.inj h)
  let φ : α → Option (Option (Fin m)) := fun a => some (g a)
  have h0 := h4 (Option (Fin m)) δ' (g x) n k hk
  have heq : {w : List α | vcount δ q x w % n = k} =
      invAlph φ (leftQuot none {u | vcount δ' 0 (g x) u % n = k}) := by
    ext w
    have hfm : w.filterMap φ = w.map g := by
      induction w with
      | nil => rfl
      | cons b w ih => simp [φ, ih]
    show _ % n = k ↔ vcount δ' 0 (g x) (none :: w.filterMap φ) % n = k
    rw [hfm, vcount_eq_vcountFrom, vcount_eq_vcountFrom, vcountFrom_cons,
      vcountFrom_map g hg δ' 0 x]
    have hcomp : δ' ∘ g = δ := funext fun a => by simp [δ', g]
    have hne : ¬ (none = g x ∧ (0 : ZMod 4) = 0) := fun h => by simp [g] at h
    rw [ite_eq_right hne, zero_add, hcomp, vcountFrom_shift δ 0 x q (0 + δ' none) w]
    simp [δ']
  rw [heq]
  exact (h0.leftQuot none).invAlph φ

/-- **`Z4CoreHeightOne` is an instance of the `H`-core**, and conversely. -/
theorem hcore_zmod_four_iff : HCoreHeightOne (Multiplicative (ZMod 4)) ↔ Z4CoreHeightOne := by
  constructor
  · intro h α _ _ δ x n k hk
    have := h α (fun a => Multiplicative.ofAdd (δ a)) x (Multiplicative.ofAdd 0) n k hk
    simpa only [hcount_ofAdd_eq_vcount] using this
  · intro h α _ _ ρ x g n k hk
    have := vcount_z4_height h (fun a => Multiplicative.toAdd (ρ a)) (Multiplicative.toAdd g) x
      n k hk
    simpa only [← hcount_ofAdd_eq_vcount, ofAdd_toAdd] using this

/-- **The `ZMod p`-core** holds for every prime `p`. -/
theorem hcore_zmod_prime (p : ℕ) [Fact p.Prime] : HCoreHeightOne (Multiplicative (ZMod p)) := by
  intro α _ _ ρ x g n k hk
  have := vcount_zp_height p (fun a => Multiplicative.toAdd (ρ a)) (Multiplicative.toAdd g) x n k hk
  have heq : ({w : List α | hcount ρ g x w % n = k} : Language α) =
      {w | vcount (fun a => Multiplicative.toAdd (ρ a)) (Multiplicative.toAdd g) x w % n = k} := by
    ext w
    show hcount ρ g x w % n = k ↔ vcount _ _ x w % n = k
    rw [hcount_eq_hcountFrom, vcount_eq_vcountFrom, ← hcountFrom_ofAdd_eq_vcountFrom]
    simp
  rw [heq]
  exact this

/-! ### The reduction -/

/-- `height_one_of_residues`, for index types in any universe. -/
theorem height_one_of_residues_univ {α : Type u} {ι : Type v} [Finite ι] (g : ι → List α → ℕ) {M : ℕ}
    (hM : 0 < M) (hg : ∀ i r, r < M → HasHeightAtMost {w | g i w % M = r} 1) (L : Language α)
    (P : (ι → ℕ) → Prop) (hL : ∀ w, w ∈ L ↔ P (fun i => g i w % M)) :
    HasHeightAtMost L 1 := by
  have heq : L = ⨆ z : {z : ι → Fin M // P (fun i => (z i : ℕ))},
      ⨅ i, ({w | g i w % M = z.1 i} : Language α) := by
    ext w
    constructor
    · intro hw
      refine Language.mem_iSup.mpr ⟨⟨fun i => ⟨g i w % M, Nat.mod_lt _ hM⟩, (hL w).mp hw⟩, ?_⟩
      exact HasHeightAtMost.mem_iInf_lang.mpr fun i => rfl
    · intro hw
      obtain ⟨z, hz⟩ := Language.mem_iSup.mp hw
      have hz' := HasHeightAtMost.mem_iInf_lang.mp hz
      rw [hL w]
      have : (fun i => g i w % M) = fun i => (z.1 i : ℕ) := funext fun i => hz' i
      rw [this]
      exact z.2
  rw [heq]
  exact HasHeightAtMost.iSup _ fun z => HasHeightAtMost.iInf _ fun i => hg i _ (z.1 i).2

section Assembly

open Classical

variable {Alphabet : Type u}

lemma tpairs_count_eq_hcountFrom {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    (T : FreeMonoid Alphabet →* G) (q' : G ⧸ N) (a : Alphabet) :
    ∀ (w : List Alphabet) (q : G ⧸ N), (tpairs N T q w).count (q', a) =
      hcountFrom (fun b => psi N T (FreeMonoid.of b)) q' a q w
  | [], q => by simp [tpairs, hcountFrom_nil]
  | b :: w, q => by
      rw [tpairs, List.count_cons, hcountFrom_cons, tpairs_count_eq_hcountFrom N T q' a w, add_comm]
      congr 1
      by_cases hb : b = a
      · subst hb
        by_cases hq : q = q'
        · simp [hq]
        · simp [hq]
      · simp [hb]

/-- **The flow identity.** Entries into `q'` plus `[start = q']` equal exits from `q'` plus
`[end = q']`. -/
lemma flow_identity [Fintype Alphabet] {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    (T : FreeMonoid Alphabet →* G) (q' : G ⧸ N) :
    ∀ (w : List Alphabet) (q : G ⧸ N),
      (∑ x, (tpairs N T q w).count (q' * (psi N T (FreeMonoid.of x))⁻¹, x)) +
          (if q = q' then 1 else 0) =
        (∑ x, (tpairs N T q w).count (q', x)) +
          (if q * psi N T (FreeMonoid.ofList w) = q' then 1 else 0)
  | [], q => by simp [tpairs]
  | b :: w, q => by
      have ih := flow_identity N T q' w (q * psi N T (FreeMonoid.of b))
      simp only [tpairs, List.count_cons, Finset.sum_add_distrib]
      have h1 : (∑ x : Alphabet,
          if ((q, b) == (q' * (psi N T (FreeMonoid.of x))⁻¹, x)) = true then 1 else 0) =
          if q * psi N T (FreeMonoid.of b) = q' then 1 else 0 := by
        rw [Finset.sum_eq_single b]
        · simp [eq_mul_inv_iff_mul_eq]
        · intro x _ hx
          simp [Ne.symm hx]
        · simp
      have h2 : (∑ x : Alphabet, if ((q, b) == (q', x)) = true then 1 else 0) =
          if q = q' then 1 else 0 := by
        rw [Finset.sum_eq_single b]
        · simp
        · intro x _ hx
          simp [Ne.symm hx]
        · simp
      rw [h1, h2]
      have h3 : q * psi N T (FreeMonoid.ofList (b :: w)) =
          q * psi N T (FreeMonoid.of b) * psi N T (FreeMonoid.ofList w) := by
        rw [FreeMonoid.ofList_cons, map_mul, mul_assoc]
      rw [h3]
      omega

/-- **Reduction to the core, through an isomorphism.** -/
theorem height_one_of_abelian_normal_of_core_equiv [Finite Alphabet] {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) {H : Type} [Group H]
    (e : G ⧸ N ≃* H) (hcore : HCoreHeightOne H) (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have := Fintype.ofFinite Alphabet
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hcore' : HCoreHeightOne (G ⧸ N) := hcore.of_mulEquiv e.symm
  have hcardN : 0 < Nat.card N := Nat.card_pos
  set M := 2 * Nat.card N with hMdef
  have hM : 0 < M := by omega
  let ρ : Alphabet → G ⧸ N := fun b => psi N T (FreeMonoid.of b)
  let cnt : (G ⧸ N) × Alphabet → List Alphabet → ℕ := fun pr w => (tpairs N T 1 w).count pr
  have hval : ∀ w : List Alphabet, T (FreeMonoid.ofList w) =
      (valN N T hab (fun pr => cnt pr w % Nat.card N) : G) *
        rep N (psi N T (FreeMonoid.ofList w)) := by
    intro w
    have ht := telescope N T 1 w
    rw [rep_one, one_mul, one_mul, list_prod_cv N T hab, mul_inv_eq_iff_eq_mul] at ht
    exact ht
  -- the final state from the counts modulo `2`
  let fin : ((G ⧸ N) × Alphabet → ℕ) → (G ⧸ N) → Prop := fun r q =>
    (if q = 1 then 1 else 0 : ZMod 2) +
      ∑ x, ((r (q * (ρ x)⁻¹, x) : ZMod 2) + (r (q, x) : ZMod 2)) = 1
  have hfin : ∀ (w : List Alphabet) (q : G ⧸ N),
      fin (fun pr => cnt pr w % M) q ↔ psi N T (FreeMonoid.ofList w) = q := by
    intro w q
    have hmod : ∀ c : ℕ, ((c % M : ℕ) : ZMod 2) = (c : ZMod 2) := by
      intro c
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod_of_dvd _ (by rw [hMdef]; exact dvd_mul_right 2 _)]
    have hid := congrArg (fun n : ℕ => (n : ZMod 2)) (flow_identity N T q w 1)
    simp only [one_mul, Nat.cast_add, Nat.cast_sum] at hid
    show (if q = 1 then 1 else 0 : ZMod 2) +
      ∑ x, (((cnt (q * (ρ x)⁻¹, x) w % M : ℕ) : ZMod 2) + ((cnt (q, x) w % M : ℕ) : ZMod 2)) = 1 ↔ _
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
  refine height_one_of_residues_univ (ι := (G ⧸ N) × Alphabet) cnt hM ?_ _
    (fun r => ∃ q, fin r q ∧ (valN N T hab (fun pr => r pr % Nat.card N) : G) * rep N q ∈ F) ?_
  · intro pr r hr
    have := hcore'.univ ρ pr.2 pr.1 M r hr
    have heq : ({w | cnt pr w % M = r} : Language Alphabet) = {w | hcount ρ pr.1 pr.2 w % M = r} := by
      ext w
      show (tpairs N T 1 w).count pr % M = r ↔ hcount ρ pr.1 pr.2 w % M = r
      rw [hcount_eq_hcountFrom, ← tpairs_count_eq_hcountFrom]
    rw [heq]
    exact this
  · intro w
    have hmm : (fun pr => cnt pr w % M % Nat.card N) = fun pr => cnt pr w % Nat.card N := by
      funext pr
      exact Nat.mod_mod_of_dvd _ (by rw [hMdef]; exact dvd_mul_left _ 2)
    show T (FreeMonoid.ofList w) ∈ F ↔ _
    simp only [hmm]
    constructor
    · intro hw
      exact ⟨psi N T (FreeMonoid.ofList w), (hfin w _).mpr rfl, by rw [← hval]; exact hw⟩
    · rintro ⟨q, hq, hF⟩
      have hpq := (hfin w q).mp hq
      rw [hval, hpq]
      exact hF

/-- **Reduction to the core.** If `N` is an abelian normal subgroup of a finite group `G` and the
`G ⧸ N`-core holds, every language recognized by `G` has generalized star height at most one. -/
theorem height_one_of_abelian_normal_of_core [Finite Alphabet] {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hcore : HCoreHeightOne (G ⧸ N)) (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 :=
  height_one_of_abelian_normal_of_core_equiv N hab (MulEquiv.refl _) hcore T F

end Assembly

end GeneralizedStarHeight
