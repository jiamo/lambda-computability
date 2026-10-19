import Start.StarHeightIndexFourLetters
import Start.StarHeightElementary

/-!
# The `Z₄` core modulo `2`

Let `δ : α → ZMod 4`.  Write the state of the `δ`-walk as `s = R + 2C`, where `R` is the state of
the walk `δ₁ y := if δ y = 2 then 0 else δ y` (no rotation `2`) and `C` is the number of rotation-`2`
letters read so far.  Then modulo `2`

  `[s = q] ≡ [R ≡ q (mod 2)] + [R = q + 2] + [R ≡ q (mod 2)]·C`,

and counting at the positions reading `x` (`vcount_z4_mod_two`):

  `vcount δ q x w ≡ vcount δ₂ q̄ x w + vcount δ₁ (q + 2) x w + vcount δ₃ (q̄, 1) x w  (mod 2)`,

with `δ₂ y := δ̄ y : ZMod 2` and `δ₃ y := (δ̄ y, [δ y = 2]) : ZMod 2 × ZMod 2` (`q̄` the reduction
modulo `2`).  The first and the last are translation automata on `(Z/2)ʳ`
(`vcount_height_one_prime`); the middle one avoids `2` (`vcount_z4_height_no2`).  Hence:

* `vcount_z4_mod_two_height`: every letter-in-state count on `ZMod 4` has height at most one
  modulo `2`, in every state; `z4core_mod_two` (state `0`) and `z4Rot2Abc_mod_two`.
* `height_one_of_abelian_cyclic_index_four_two`: abelian-by-`Z₄` groups whose kernel has
  exponent `2` (the counts are only needed modulo `2`: `valN_mod_two` of `StarHeightA4Core.lean`).
* `height_one_of_exponent_two_kernel`: the wreath product principle at exponent `2` (counts of the
  walk in `G ⧸ N` modulo `2` suffice when the abelian kernel has exponent `2`).
* `height_one_Z2_wr_Z4`: the wreath product `Z₂ ≀ Z₄ = (ZMod 4 → ZMod 2) ⋊ Z₄`, of order `64`.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

/-- Reduction modulo `2`. -/
abbrev red4 : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)

/-- The displacements with rotation `2` removed. -/
def dNo2 {α : Type u} (δ : α → ZMod 4) (y : α) : ZMod 4 := if δ y = 2 then 0 else δ y

/-- The displacements modulo `2`. -/
def dRed {α : Type u} (δ : α → ZMod 4) (y : α) : ZMod 2 := red4 (δ y)

/-- The displacements modulo `2`, together with the parity of the rotation-`2` letters. -/
def dPair {α : Type u} (δ : α → ZMod 4) (y : α) : ZMod 2 × ZMod 2 :=
  (red4 (δ y), if δ y = 2 then 1 else 0)

/-- The pointwise identity behind `vcount_z4_mod_two`. -/
lemma indicator_z4_mod_two : ∀ (r q : ZMod 4) (c : ZMod 2),
    ((if r + (if c = 1 then 2 else 0) = q then 1 else 0 : ℕ) : ZMod 2) =
      ((if red4 r = red4 q then 1 else 0 : ℕ) : ZMod 2) +
        ((if r = q + 2 then 1 else 0 : ℕ) : ZMod 2) +
          ((if (red4 r, c) = (red4 q, 1) then 1 else 0 : ℕ) : ZMod 2) := by
  decide

lemma red4_two : red4 2 = 0 := by decide

lemma carry_step : ∀ (c : ZMod 2),
    (if c + 1 = 1 then (2 : ZMod 4) else 0) = (if c = 1 then 2 else 0) + 2 := by
  decide

section Identity

variable {α : Type u} [DecidableEq α]

/-- The identity, read from arbitrary states `s = r + 2c`. -/
lemma vcountFrom_z4_mod_two (δ : α → ZMod 4) (q : ZMod 4) (x : α) :
    ∀ (w : List α) (r : ZMod 4) (c : ZMod 2),
      ((vcountFrom δ q x (r + if c = 1 then 2 else 0) w : ℕ) : ZMod 2) =
        (vcountFrom (dRed δ) (red4 q) x (red4 r) w : ZMod 2) +
          (vcountFrom (dNo2 δ) (q + 2) x r w : ZMod 2) +
            (vcountFrom (dPair δ) (red4 q, 1) x (red4 r, c) w : ZMod 2)
  | [], r, c => by simp [vcountFrom_nil]
  | b :: w, r, c => by
      rw [vcountFrom_cons, vcountFrom_cons, vcountFrom_cons, vcountFrom_cons]
      have hs : r + (if c = 1 then 2 else 0) + δ b =
          (r + dNo2 δ b) + if (c + if δ b = 2 then 1 else 0) = 1 then 2 else 0 := by
        unfold dNo2
        by_cases hb : δ b = 2
        · simp only [hb, if_true, add_zero, carry_step]
          abel
        · simp only [hb, if_false, add_zero]
          abel
      have hr : red4 r + dRed δ b = red4 (r + dNo2 δ b) := by
        unfold dRed dNo2
        by_cases hb : δ b = 2
        · rw [if_pos hb, hb, add_zero, red4_two, add_zero]
        · simp [hb]
      have hp : (red4 r, c) + dPair δ b = (red4 (r + dNo2 δ b), c + if δ b = 2 then 1 else 0) := by
        rw [← hr]; rfl
      rw [hs, hr, hp]
      push_cast
      rw [vcountFrom_z4_mod_two δ q x w]
      by_cases hbx : b = x
      · subst hbx
        have := indicator_z4_mod_two r q c
        simp only [true_and]
        push_cast at this
        rw [this]
        ring
      · simp only [hbx, false_and, if_false]
        ring

/-- **The `Z₄` identity modulo `2`.** -/
theorem vcount_z4_mod_two (δ : α → ZMod 4) (q : ZMod 4) (x : α) (w : List α) :
    (vcount δ q x w : ZMod 2) =
      (vcount (fun y => (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) (δ y))
          (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) q) x w : ZMod 2) +
        (vcount (fun y => if δ y = 2 then 0 else δ y) (q + 2) x w : ZMod 2) +
          (vcount (fun y => ((ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) (δ y),
              if δ y = 2 then (1 : ZMod 2) else 0))
            ((ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) q, 1) x w : ZMod 2) := by
  have := vcountFrom_z4_mod_two δ q x w 0 0
  simp only [map_zero, show ((0 : ZMod 2) = 1) = False by decide, if_false,
    add_zero] at this
  simp only [vcount_eq_vcountFrom]
  exact this

end Identity

/-! ### Height one modulo `2` -/

/-- Every letter-in-state count of a translation automaton on `ZMod 4` has generalized star
height at most one modulo `2`, in every state. -/
theorem vcount_z4_mod_two_height {α : Type u} [Finite α] [DecidableEq α] (δ : α → ZMod 4)
    (q : ZMod 4) (x : α) (k : ℕ) (hk : k < 2) :
    HasHeightAtMost {w : List α | vcount δ q x w % 2 = k} 1 := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine height_one_of_residues (ι := Fin 3)
    (fun i w => if i = 0 then vcount (dRed δ) (red4 q) x w
      else if i = 1 then vcount (dNo2 δ) (q + 2) x w
      else vcount (dPair δ) (red4 q, 1) x w) (M := 2) (by norm_num) ?_ _
    (fun z => ((z 0 : ℕ) : ZMod 2) + (z 1 : ZMod 2) + (z 2 : ZMod 2) = (k : ZMod 2)) ?_
  · intro i r hr
    fin_cases i
    · exact vcount_height_one_prime (p := 2) (V := ZMod 2) _ _ x 2 r hr
    · refine vcount_z4_height_no2 (dNo2 δ) (fun y => ?_) _ x 2 r hr
      unfold dNo2
      split_ifs with h
      · decide
      · exact h
    · exact vcount_height_one_prime (p := 2) (V := ZMod 2 × ZMod 2) _ _ x 2 r hr
  · intro w
    change vcount δ q x w % 2 = k ↔ _
    simp only [Fin.isValue, if_true, show ((1 : Fin 3) = 0) = False by decide,
      show ((2 : Fin 3) = 0) = False by decide, show ((2 : Fin 3) = 1) = False by decide,
      if_false, ZMod.natCast_mod]
    have hid := vcount_z4_mod_two δ q x w
    change _ = _ + (vcount (dNo2 δ) (q + 2) x w : ZMod 2) + _ at hid
    rw [show (vcount (dRed δ) (red4 q) x w : ZMod 2) + (vcount (dNo2 δ) (q + 2) x w : ZMod 2) +
      (vcount (dPair δ) (red4 q, 1) x w : ZMod 2) = (vcount δ q x w : ZMod 2) from hid.symm,
      ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hk]

/-- **The `Z₄` core modulo `2`.** -/
theorem z4core_mod_two : ∀ (α : Type) [Fintype α] [DecidableEq α] (δ : α → ZMod 4) (x : α)
    (k : ℕ), k < 2 → HasHeightAtMost {w : List α | vcount δ 0 x w % 2 = k} 1 :=
  fun _ _ _ δ x k hk => vcount_z4_mod_two_height δ 0 x k hk

/-- **`Z4Rot2Abc` modulo `2`.** -/
theorem z4Rot2Abc_mod_two : ∀ k, k < 2 →
    HasHeightAtMost
      {w : List (Fin 3) | vcount (![0, 1, 2] : Fin 3 → ZMod 4) 0 0 w % 2 = k} 1 :=
  fun k hk => z4core_mod_two (Fin 3) _ 0 k hk

/-! ### Abelian-by-`Z₄` with an elementary abelian `2`-kernel -/

section Assembly

open Classical

variable {Alphabet : Type u}

/-- **Abelian-by-`Z₄` with an elementary abelian `2`-kernel.** If `N` is an abelian normal
subgroup of index `4` of a finite group `G`, every element of `N` has order at most `2`, and
`G ⧸ N` is cyclic, every language recognized by `G` has generalized star height at most one. -/
theorem height_one_of_abelian_cyclic_index_four_two [Finite Alphabet] {G : Type} [Group G]
    [Fintype G] (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hexp : ∀ x ∈ N, x * x = 1) (hidx : N.index = 4) (hcyc : IsCyclic (G ⧸ N))
    (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have := Fintype.ofFinite Alphabet
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hcardA : Nat.card (Additive (G ⧸ N)) = 4 := hidx
  let f : Additive (G ⧸ N) ≃+ ZMod 4 :=
    (zmodAddCyclicAddEquiv (isAddCyclic_additive_iff.2 hcyc)).symm.trans
      (ZMod.ringEquivCongr hcardA).toAddEquiv
  have hQ : ∀ x y : G ⧸ N, x * y = y * x :=
    fun x y => (IsCyclic.commGroup (α := G ⧸ N)).mul_comm x y
  let δV : Alphabet → Additive (G ⧸ N) := fun a => Additive.ofMul (psi N T (FreeMonoid.of a))
  let δ : Alphabet → ZMod 4 := fun a => f (δV a)
  have hcount : ∀ (w : List Alphabet) (pr : (G ⧸ N) × Alphabet),
      (tpairs N T 1 w).count pr = vcount δ (f (Additive.ofMul pr.1)) pr.2 w := by
    intro w pr
    rw [vcount_eq_vcountFrom, tpairs_count_eq_vcountFrom N T pr.1 pr.2 w 1,
      ← vcountFrom_hom f.toAddMonoidHom f.injective δV]
    simp only [δ, AddEquiv.coe_toAddMonoidHom]
    congr 1
    show f (Additive.ofMul 1) = 0
    exact map_zero f
  have hval : ∀ w : List Alphabet, T (FreeMonoid.ofList w) =
      (valN N T hab (fun pr => (tpairs N T 1 w).count pr % 2) : G) *
        rep N (psi N T (FreeMonoid.ofList w)) := by
    intro w
    have ht := telescope N T 1 w
    rw [rep_one, one_mul, one_mul, list_prod_cv N T hab, mul_inv_eq_iff_eq_mul,
      valN_mod_card N T hab (fun pr => (tpairs N T 1 w).count pr),
      valN_mod_two N T hab hexp] at ht
    exact ht
  let Idx := {z : (G ⧸ N) × ((G ⧸ N) × Alphabet → Fin 2) //
    (valN N T hab (fun pr => (z.2 pr : ℕ)) : G) * rep N z.1 ∈ F}
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) = ⨆ z : Idx,
      ({w | psi N T (FreeMonoid.ofList w) = z.1.1} ⊓
        ⨅ pr : (G ⧸ N) × Alphabet,
          {w | vcount δ (f (Additive.ofMul pr.1)) pr.2 w % 2 = z.1.2 pr}) := by
    ext w
    constructor
    · intro hw
      refine Language.mem_iSup.mpr ⟨⟨(psi N T (FreeMonoid.ofList w), fun pr =>
        ⟨(tpairs N T 1 w).count pr % 2, Nat.mod_lt _ (by norm_num)⟩), ?_⟩, rfl, ?_⟩
      · show _ ∈ F
        rw [← hval]; exact hw
      · refine HasHeightAtMost.mem_iInf_lang.mpr fun pr => ?_
        show _ = _
        simp only
        rw [hcount]
    · intro hw
      obtain ⟨z, hz1, hz2⟩ := Language.mem_iSup.mp hw
      have hz2' := HasHeightAtMost.mem_iInf_lang.mp hz2
      show T (FreeMonoid.ofList w) ∈ F
      rw [hval]
      have hres : (fun pr => (tpairs N T 1 w).count pr % 2) =
          fun pr => (z.1.2 pr : ℕ) := by
        funext pr
        rw [hcount]; exact hz2' pr
      have hz1' : psi N T (FreeMonoid.ofList w) = z.1.1 := hz1
      rw [hres, hz1']
      exact z.2
  rw [heq]
  refine HasHeightAtMost.iSup _ fun z => HasHeightAtMost.inter ?_ ?_
  · simpa using height_one_of_comm hQ (psi N T) {z.1.1}
  · exact HasHeightAtMost.iInf _ fun pr =>
      vcount_z4_mod_two_height δ _ pr.2 (z.1.2 pr) (z.1.2 pr).2

/-- **The wreath product principle at exponent `2`.** Let `N` be an abelian normal subgroup of a
finite group `G` in which every element has order at most `2`, and `T : FreeMonoid Alphabet →* G`.
If the fibres of the walk in `G ⧸ N` and the residues modulo `2` of its letter-in-state counts
(`tpairs`) have height at most one, every language recognized by `G` through `T` has height at
most one. -/
theorem height_one_of_exponent_two_kernel [Finite Alphabet] {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hexp : ∀ x ∈ N, x * x = 1) (T : FreeMonoid Alphabet →* G)
    (hwalk : ∀ q : G ⧸ N, HasHeightAtMost {w : List Alphabet | psi N T (FreeMonoid.ofList w) = q} 1)
    (hcount : ∀ (pr : (G ⧸ N) × Alphabet) (k : ℕ), k < 2 →
      HasHeightAtMost {w : List Alphabet | (tpairs N T 1 w).count pr % 2 = k} 1)
    (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have := Fintype.ofFinite Alphabet
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hval : ∀ w : List Alphabet, T (FreeMonoid.ofList w) =
      (valN N T hab (fun pr => (tpairs N T 1 w).count pr % 2) : G) *
        rep N (psi N T (FreeMonoid.ofList w)) := by
    intro w
    have ht := telescope N T 1 w
    rw [rep_one, one_mul, one_mul, list_prod_cv N T hab, mul_inv_eq_iff_eq_mul,
      valN_mod_card N T hab (fun pr => (tpairs N T 1 w).count pr),
      valN_mod_two N T hab hexp] at ht
    exact ht
  let Idx := {z : (G ⧸ N) × ((G ⧸ N) × Alphabet → Fin 2) //
    (valN N T hab (fun pr => (z.2 pr : ℕ)) : G) * rep N z.1 ∈ F}
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) = ⨆ z : Idx,
      ({w | psi N T (FreeMonoid.ofList w) = z.1.1} ⊓
        ⨅ pr : (G ⧸ N) × Alphabet, {w | (tpairs N T 1 w).count pr % 2 = z.1.2 pr}) := by
    ext w
    constructor
    · intro hw
      refine Language.mem_iSup.mpr ⟨⟨(psi N T (FreeMonoid.ofList w), fun pr =>
        ⟨(tpairs N T 1 w).count pr % 2, Nat.mod_lt _ (by norm_num)⟩), ?_⟩, rfl, ?_⟩
      · show _ ∈ F
        rw [← hval]; exact hw
      · exact HasHeightAtMost.mem_iInf_lang.mpr fun pr => rfl
    · intro hw
      obtain ⟨z, hz1, hz2⟩ := Language.mem_iSup.mp hw
      have hz2' := HasHeightAtMost.mem_iInf_lang.mp hz2
      show T (FreeMonoid.ofList w) ∈ F
      rw [hval]
      have hres : (fun pr => (tpairs N T 1 w).count pr % 2) = fun pr => (z.1.2 pr : ℕ) :=
        funext fun pr => hz2' pr
      have hz1' : psi N T (FreeMonoid.ofList w) = z.1.1 := hz1
      rw [hres, hz1']
      exact z.2
  rw [heq]
  exact HasHeightAtMost.iSup _ fun z => HasHeightAtMost.inter (hwalk z.1.1)
    (HasHeightAtMost.iInf _ fun pr => hcount pr _ (z.1.2 pr).2)

end Assembly

/-! ### The wreath product `Z₂ ≀ Z₄` -/

/-- The base group `(ZMod 4 → ZMod 2)` of `Z₂ ≀ Z₄`, written multiplicatively. -/
abbrev Z2Base := Multiplicative (ZMod 4 → ZMod 2)

/-- The shift of coordinates by `e`: `(e · g) i = g (i - e)`. -/
def z2shift (e : ZMod 4) : Z2Base ≃* Z2Base where
  toFun g := Multiplicative.ofAdd (fun i => Multiplicative.toAdd g (i - e))
  invFun g := Multiplicative.ofAdd (fun i => Multiplicative.toAdd g (i + e))
  left_inv g := by funext i; simp
  right_inv g := by funext i; simp
  map_mul' g h := by funext i; rfl

/-- `ZMod 4` acting on the base by shifting the coordinates. -/
def z2shiftHom : Multiplicative (ZMod 4) →* MulAut Z2Base where
  toFun e := z2shift (Multiplicative.toAdd e)
  map_one' := by ext g i; simp [z2shift]
  map_mul' a b := by
    ext g i
    show Multiplicative.toAdd g (i - (Multiplicative.toAdd a + Multiplicative.toAdd b)) =
      Multiplicative.toAdd g (i - Multiplicative.toAdd a - Multiplicative.toAdd b)
    rw [sub_sub]

/-- **The wreath product `Z₂ ≀ Z₄ = (ZMod 4 → ZMod 2) ⋊ ZMod 4`**, of order `64`. -/
abbrev Z2WrZ4 := Z2Base ⋊[z2shiftHom] Multiplicative (ZMod 4)

namespace Z2WrZ4

instance : Fintype Z2WrZ4 :=
  Fintype.ofEquiv (Z2Base × Multiplicative (ZMod 4))
    ⟨fun p => ⟨p.1, p.2⟩, fun x => (x.1, x.2), fun _ => rfl, fun _ => rfl⟩

lemma card : Fintype.card Z2WrZ4 = 64 := rfl

/-- The base group, as the kernel of the projection to `Z₄`. -/
def base : Subgroup Z2WrZ4 := (SemidirectProduct.rightHom : Z2WrZ4 →* _).ker

instance : base.Normal := MonoidHom.normal_ker _

lemma mem_base {x : Z2WrZ4} : x ∈ base ↔ x.right = 1 := Iff.rfl

lemma base_comm : ∀ x ∈ base, ∀ y ∈ base, x * y = y * x := by
  intro x hx y hy
  rw [mem_base] at hx hy
  ext1
  · simp [SemidirectProduct.mul_left, hx, hy, mul_comm]
  · simp [hx, hy]

lemma base_sq : ∀ x ∈ base, x * x = 1 := by
  intro x hx
  rw [mem_base] at hx
  ext1
  · simp only [SemidirectProduct.mul_left, hx, map_one, MulAut.one_apply,
      SemidirectProduct.one_left]
    funext i
    show Multiplicative.toAdd x.left i + Multiplicative.toAdd x.left i = 0
    exact CharTwo.add_self_eq_zero _
  · simp [hx]

lemma base_index : base.index = 4 := by
  rw [base, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr SemidirectProduct.rightHom_surjective, Subgroup.card_top]
  simp

lemma quotient_isCyclic : IsCyclic (Z2WrZ4 ⧸ base) :=
  isCyclic_of_surjective
    (QuotientGroup.quotientKerEquivOfSurjective _ SemidirectProduct.rightHom_surjective).symm
    (MulEquiv.surjective _)

end Z2WrZ4

/-- **`Z₂ ≀ Z₄`.** Every language recognized by the wreath product
`Z₂ ≀ Z₄ = (ZMod 4 → ZMod 2) ⋊ ZMod 4` (order `64`) has generalized star height at most one.

No earlier theorem of the repository covers this group.  By computer
(`docs/goal/evidence/M28-STARHEIGHT-Z4-MOD-TWO-search/wreath_facts.py`): it has nilpotency class
`4` (lower central series of orders `64, 8, 4, 2, 1`), so it does not divide `UT₄(Z/n)` (class
`3`); its Frattini subgroup `G²[G, G]` has order `16` and is non-abelian, so
`height_one_of_frattini_abelian` does not apply; and none of its three subgroups of index `2` is
abelian, so it has no abelian subgroup of prime index.  It does not divide `A ⋊ (Z₂)ⁿ` with `A`
abelian (the PST 1992 class): a divisor `H/K` of such a group has the abelian normal subgroup
`(H ∩ A)K/K` with elementary abelian quotient, which must contain the Frattini subgroup.  The
existing `height_one_of_abelian_cyclic_index_four` needs the open `Z4CoreHeightOne`. -/
theorem height_one_Z2_wr_Z4 {Alphabet : Type u} [Finite Alphabet]
    (T : FreeMonoid Alphabet →* Z2WrZ4) (F : Set Z2WrZ4) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 :=
  height_one_of_abelian_cyclic_index_four_two Z2WrZ4.base Z2WrZ4.base_comm Z2WrZ4.base_sq
    Z2WrZ4.base_index Z2WrZ4.quotient_isCyclic T F

end GeneralizedStarHeight
