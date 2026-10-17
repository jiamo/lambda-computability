import Start.StarHeightZpCoreHeight

/-!
# Abelian normal subgroups of prime index

* `vcount_zp_height`: every letter-in-state count on `ZMod p` (`p` prime) has height at most one
  modulo every `n` (from `zpcore`, every state being reached by a fresh first letter).
* `height_one_of_abelian_prime_index`: if `N` is an abelian normal subgroup of prime index `p`
  of a finite group `G`, every language recognized by `G` has generalized star height at most one.
* `height_one_of_abelian_index_five`: the case `p = 5`.
* `G55`, the nonabelian group `Z₁₁ ⋊ Z₅` of order `55`, and `height_one_G55`.

The assembly is that of `Start/StarHeightIndexFour.lean`: the telescoping writes `T w` through the
counts of pairs (state in `G ⧸ N`, letter), and `G ⧸ N ≅ ZMod p` is cyclic since `p` is prime.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

/-- **Every state.** -/
theorem vcount_zp_height (p : ℕ) [Fact p.Prime] {α : Type u} [Finite α]
    [DecidableEq α] (δ : α → ZMod p) (q : ZMod p) (x : α) (n k : ℕ) (hk : k < n) :
    HasHeightAtMost {w : List α | vcount δ q x w % n = k} 1 := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  let δ' : Option (Fin m) → ZMod p := fun o => o.elim (-q) (fun i => δ (e.symm i))
  let g : α → Option (Fin m) := fun a => some (e a)
  have hg : Function.Injective g := fun a b h => e.injective (Option.some.inj h)
  let φ : α → Option (Option (Fin m)) := fun a => some (g a)
  have h0 := zpcore p (Option (Fin m)) δ' (g x) n k hk
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
    have hne : ¬ (none = g x ∧ (0 : ZMod p) = 0) := fun h => by simp [g] at h
    rw [if_neg hne, zero_add, hcomp, vcountFrom_shift δ 0 x q (0 + δ' none) w]
    simp [δ']
  rw [heq]
  exact (h0.leftQuot none).invAlph φ

section Assembly

open Classical

variable {Alphabet : Type u}

/-- **Abelian normal subgroups of prime index.** If `N` is an abelian normal subgroup of prime
index `p` in a finite group `G`, every language recognized by `G` has generalized star height at
most one. -/
theorem height_one_of_abelian_prime_index [Finite Alphabet] {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) {p : ℕ}
    [hp : Fact p.Prime] (hidx : N.index = p)
    (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have := Fintype.ofFinite Alphabet
  have hcyc : IsCyclic (G ⧸ N) := isCyclic_of_prime_card hidx
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hcardN : 0 < Nat.card N := Nat.card_pos
  have hcardA : Nat.card (Additive (G ⧸ N)) = p := hidx
  let f : Additive (G ⧸ N) ≃+ ZMod p :=
    (zmodAddCyclicAddEquiv (isAddCyclic_additive_iff.2 hcyc)).symm.trans
      (ZMod.ringEquivCongr hcardA).toAddEquiv
  have hQ : ∀ x y : G ⧸ N, x * y = y * x :=
    fun x y => (IsCyclic.commGroup (α := G ⧸ N)).mul_comm x y
  let δV : Alphabet → Additive (G ⧸ N) := fun a => Additive.ofMul (psi N T (FreeMonoid.of a))
  let δ : Alphabet → ZMod p := fun a => f (δV a)
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
      (valN N T hab (fun pr => (tpairs N T 1 w).count pr % Nat.card N) : G) *
        rep N (psi N T (FreeMonoid.ofList w)) := by
    intro w
    have ht := telescope N T 1 w
    rw [rep_one, one_mul, one_mul, list_prod_cv N T hab, mul_inv_eq_iff_eq_mul] at ht
    exact ht
  let Idx := {z : (G ⧸ N) × ((G ⧸ N) × Alphabet → Fin (Nat.card N)) //
    (valN N T hab (fun pr => (z.2 pr : ℕ)) : G) * rep N z.1 ∈ F}
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) = ⨆ z : Idx,
      ({w | psi N T (FreeMonoid.ofList w) = z.1.1} ⊓
        ⨅ pr : (G ⧸ N) × Alphabet,
          {w | vcount δ (f (Additive.ofMul pr.1)) pr.2 w % Nat.card N = z.1.2 pr}) := by
    ext w
    constructor
    · intro hw
      refine Language.mem_iSup.mpr ⟨⟨(psi N T (FreeMonoid.ofList w), fun pr =>
        ⟨(tpairs N T 1 w).count pr % Nat.card N, Nat.mod_lt _ hcardN⟩), ?_⟩, rfl, ?_⟩
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
      have hres : (fun pr => (tpairs N T 1 w).count pr % Nat.card N) =
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
      vcount_zp_height p δ _ pr.2 (Nat.card N) (z.1.2 pr) (z.1.2 pr).2

/-- **Abelian normal subgroups of index five.** -/
theorem height_one_of_abelian_index_five [Finite Alphabet] {G : Type} [Group G] [Fintype G] (N : Subgroup G)
    [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hidx : N.index = 5) (T : FreeMonoid Alphabet →* G)
    (F : Set G) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact height_one_of_abelian_prime_index N hab hidx T F

end Assembly

/-! ### The group `Z₁₁ ⋊ Z₅` of order `55` -/

/-- `Z₁₁ ⋊ Z₅`: `5` acts on `ZMod 11` through multiplication by `3` (of order `5`). -/
@[ext] structure G55 where
  /-- The `Z₁₁` part. -/
  b : ZMod 11
  /-- The `Z₅` part. -/
  e : ZMod 5
  deriving DecidableEq

namespace G55

/-- The action: `3 ^ e`. -/
def tw (e : ZMod 5) : ZMod 11 := 3 ^ e.val

lemma tw_add : ∀ e e' : ZMod 5, tw (e + e') = tw e * tw e' := by decide

lemma tw_zero : tw 0 = 1 := by decide

instance : Mul G55 := ⟨fun g h => ⟨g.b + tw g.e * h.b, g.e + h.e⟩⟩
instance : One G55 := ⟨⟨0, 0⟩⟩
instance : Inv G55 := ⟨fun g => ⟨-(tw (-g.e) * g.b), -g.e⟩⟩

lemma mul_def (g h : G55) : g * h = ⟨g.b + tw g.e * h.b, g.e + h.e⟩ := rfl

instance : Group G55 where
  mul_assoc f g h := by
    ext
    · simp only [mul_def, tw_add]; ring
    · simp only [mul_def]; ring
  one_mul f := by ext <;> simp [mul_def, show (1 : G55) = ⟨0, 0⟩ from rfl, tw_zero]
  mul_one f := by ext <;> simp [mul_def, show (1 : G55) = ⟨0, 0⟩ from rfl]
  inv_mul_cancel f := by
    ext
    · show -(tw (-f.e) * f.b) + tw (-f.e) * f.b = 0
      ring
    · show -f.e + f.e = 0
      ring

/-- `G55 ≃ ZMod 11 × ZMod 5`. -/
def equivProd : G55 ≃ ZMod 11 × ZMod 5 where
  toFun g := (g.b, g.e)
  invFun q := ⟨q.1, q.2⟩

instance : Fintype G55 := Fintype.ofEquiv _ equivProd.symm

lemma card : Fintype.card G55 = 55 := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, ZMod.card, ZMod.card]

/-- `G55` is not abelian. -/
lemma not_comm : ∃ g h : G55, g * h ≠ h * g :=
  ⟨⟨1, 0⟩, ⟨0, 1⟩, by decide⟩

/-- The projection onto `Z₅`. -/
def proj : G55 →* Multiplicative (ZMod 5) where
  toFun g := Multiplicative.ofAdd g.e
  map_one' := rfl
  map_mul' _ _ := rfl

lemma proj_surjective : Function.Surjective proj := fun u => ⟨⟨0, Multiplicative.toAdd u⟩, rfl⟩

/-- The normal subgroup `Z₁₁`. -/
def base : Subgroup G55 := proj.ker

instance : base.Normal := MonoidHom.normal_ker _

lemma mem_base {g : G55} : g ∈ base ↔ g.e = 0 := Iff.rfl

lemma base_comm : ∀ x ∈ base, ∀ y ∈ base, x * y = y * x := by
  intro x hx y hy
  rw [mem_base] at hx hy
  ext
  · simp only [mul_def, hx, hy, tw_zero, one_mul, add_comm]
  · simp only [mul_def, hx, hy]

lemma base_index : base.index = 5 := by
  rw [base, Subgroup.index_ker, MonoidHom.range_eq_top.mpr proj_surjective, Subgroup.card_top,
    Nat.card_eq_fintype_card]
  rfl

end G55

/-- **`Z₁₁ ⋊ Z₅`.** Every language recognized by the nonabelian group of order `55` has
generalized star height at most one. -/
theorem height_one_G55 {Alphabet : Type u} [Finite Alphabet] (T : FreeMonoid Alphabet →* G55)
    (F : Set G55) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 :=
  height_one_of_abelian_index_five G55.base G55.base_comm G55.base_index T F

end GeneralizedStarHeight
