import Start.StarHeightBourne

/-!
# Abelian-by-`Z₄` groups: reduction to the `Z₄` core

* `Z4CoreHeightOne`: for every finite alphabet, every `δ : α → ZMod 4`, every letter `x` and every
  `k < n`, the words with `vcount δ 0 x w ≡ k (mod n)` have generalized star height at most one.
  (`vcount δ 0 x w` counts the positions reading `x` in state `0` of the translation automaton on
  `ZMod 4`, read from `0`.)
* `vcount_z4_height_of_core`: under `Z4CoreHeightOne`, the same holds in every state `q`
  (a fresh letter of displacement `-q`, a left quotient and an inverse alphabetic morphism).
* `height_one_of_abelian_cyclic_index_four`: under `Z4CoreHeightOne`, every language recognized by
  a finite group with an abelian normal subgroup `N` of index `4` and cyclic quotient has height at
  most one.  The proof is the assembly of `height_one_of_abelian_normal_exponent_three`, with
  `Additive (G ⧸ N) ≃+ ZMod 4`.
* `F20`: the affine maps `x ↦ a·x + b` of `ZMod 5` (`a` a unit), the Frobenius group of order `20`;
  the translations form an abelian normal subgroup of index `4` with cyclic quotient
  (`F20.transl_index`, `F20.quotient_isCyclic`), hence `height_one_F20_of_core`.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

/-- **The `Z₄` core.** Letter-in-state-`0` counts of translation automata on `ZMod 4` have
height at most one modulo every `n`. -/
def Z4CoreHeightOne : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (δ : α → ZMod 4) (x : α) (n k : ℕ),
    k < n → HasHeightAtMost {w : List α | vcount δ 0 x w % n = k} 1

/-! ### Transporting `vcountFrom` -/

section Transport

variable {α : Type u} [DecidableEq α]

lemma vcountFrom_map {β : Type} [DecidableEq β] {V : Type} [AddMonoid V] (g : α → β)
    (hg : Function.Injective g) (δ : β → V) (q : V) (x : α) :
    ∀ (s : V) (w : List α), vcountFrom δ q (g x) s (w.map g) = vcountFrom (δ ∘ g) q x s w
  | s, [] => by simp [vcountFrom_nil]
  | s, b :: w => by
      rw [List.map_cons, vcountFrom_cons, vcountFrom_cons, vcountFrom_map g hg δ q x _ w]
      congr 1
      split_ifs <;> simp_all [hg.eq_iff]

lemma vcountFrom_shift {V : Type} [AddCommGroup V] (δ : α → V) (q : V) (x : α) (t : V) :
    ∀ (s : V) (w : List α), vcountFrom δ q x s w = vcountFrom δ (q + t) x (s + t) w
  | s, [] => by simp [vcountFrom_nil]
  | s, b :: w => by
      rw [vcountFrom_cons, vcountFrom_cons, vcountFrom_shift δ q x t _ w,
        show s + δ b + t = s + t + δ b by abel]
      congr 1
      split_ifs <;> simp_all

lemma vcountFrom_hom {V W : Type} [AddMonoid V] [AddMonoid W] (f : V →+ W)
    (hf : Function.Injective f) (δ : α → V) (q : V) (x : α) :
    ∀ (s : V) (w : List α), vcountFrom (fun a => f (δ a)) (f q) x (f s) w = vcountFrom δ q x s w
  | s, [] => by simp [vcountFrom_nil]
  | s, b :: w => by
      rw [vcountFrom_cons, vcountFrom_cons, ← map_add, vcountFrom_hom f hf δ q x _ w]
      congr 1
      split_ifs <;> simp_all [hf.eq_iff]

end Transport

/-! ### Every state from state `0` -/

/-- Under the core hypothesis, every letter-in-state count on `ZMod 4` has height at most one. -/
theorem vcount_z4_height_of_core (hcore : Z4CoreHeightOne) {α : Type u} [Finite α]
    [DecidableEq α] (δ : α → ZMod 4) (q : ZMod 4) (x : α) (n k : ℕ) (hk : k < n) :
    HasHeightAtMost {w : List α | vcount δ q x w % n = k} 1 := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  let δ' : Option (Fin m) → ZMod 4 := fun o => o.elim (-q) (fun i => δ (e.symm i))
  let g : α → Option (Fin m) := fun a => some (e a)
  have hg : Function.Injective g := fun a b h => e.injective (Option.some.inj h)
  let φ : α → Option (Option (Fin m)) := fun a => some (g a)
  have h0 := hcore (Option (Fin m)) δ' (g x) n k hk
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

/-! ### Assembly -/

section Assembly

open Classical

variable {Alphabet : Type u}

/-- **Abelian-by-`Z₄`, conditional on the core.** If `N` is an abelian normal subgroup of index
`4` in a finite group `G` and `G ⧸ N` is cyclic, every language recognized by `G` has generalized
star height at most one, provided `Z4CoreHeightOne` holds. -/
theorem height_one_of_abelian_cyclic_index_four (hcore : Z4CoreHeightOne) [Finite Alphabet]
    {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hidx : N.index = 4)
    (hcyc : IsCyclic (G ⧸ N))
    (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have := Fintype.ofFinite Alphabet
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hcardN : 0 < Nat.card N := Nat.card_pos
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
      vcount_z4_height_of_core hcore δ _ pr.2 (Nat.card N) (z.1.2 pr) (z.1.2 pr).2

end Assembly

/-! ### The Frobenius group `F₂₀ = AGL(1, 5)` -/

/-- The affine map `x ↦ a·x + b` of `ZMod 5`, with `a` a unit. -/
@[ext] structure F20 where
  /-- The translation part. -/
  b : ZMod 5
  /-- The linear part. -/
  a : (ZMod 5)ˣ
  deriving DecidableEq

namespace F20

/-- The affine map as a function. -/
def toFun (f : F20) (x : ZMod 5) : ZMod 5 := (f.a : ZMod 5) * x + f.b

instance : Mul F20 := ⟨fun f g => ⟨(f.a : ZMod 5) * g.b + f.b, f.a * g.a⟩⟩
instance : One F20 := ⟨⟨0, 1⟩⟩
instance : Inv F20 := ⟨fun f => ⟨-((f.a⁻¹ : (ZMod 5)ˣ) : ZMod 5) * f.b, f.a⁻¹⟩⟩

lemma mul_def (f g : F20) : f * g = ⟨(f.a : ZMod 5) * g.b + f.b, f.a * g.a⟩ := rfl

/-- Multiplication is composition of affine maps. -/
lemma toFun_mul (f g : F20) (x : ZMod 5) : (f * g).toFun x = f.toFun (g.toFun x) := by
  simp only [toFun, mul_def, Units.val_mul]; ring

instance : Group F20 where
  mul_assoc f g h := by ext <;> simp only [mul_def, Units.val_mul] <;> ring
  one_mul f := by ext <;> simp [mul_def, show (1 : F20) = ⟨0, 1⟩ from rfl]
  mul_one f := by ext <;> simp [mul_def, show (1 : F20) = ⟨0, 1⟩ from rfl]
  inv_mul_cancel f := by
    ext
    · show ((f.a⁻¹ : (ZMod 5)ˣ) : ZMod 5) * f.b + -((f.a⁻¹ : (ZMod 5)ˣ) : ZMod 5) * f.b = 0
      ring
    · show ((f.a⁻¹ * f.a : (ZMod 5)ˣ) : ZMod 5) = ((1 : (ZMod 5)ˣ) : ZMod 5)
      rw [inv_mul_cancel]

/-- `F20 ≃ ZMod 5 × (ZMod 5)ˣ`. -/
def equivProd : F20 ≃ ZMod 5 × (ZMod 5)ˣ where
  toFun f := (f.b, f.a)
  invFun p := ⟨p.1, p.2⟩

instance : Fintype F20 := Fintype.ofEquiv _ equivProd.symm

lemma card : Fintype.card F20 = 20 := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, ZMod.card, ZMod.card_units_eq_totient]
  decide

/-- `F20` is not abelian. -/
lemma not_comm : ∃ f g : F20, f * g ≠ g * f :=
  ⟨⟨1, 1⟩, ⟨0, -1⟩, by decide⟩

/-- The linear part. -/
def lin : F20 →* (ZMod 5)ˣ where
  toFun f := f.a
  map_one' := rfl
  map_mul' _ _ := rfl

lemma lin_surjective : Function.Surjective lin := fun u => ⟨⟨0, u⟩, rfl⟩

/-- The translations `x ↦ x + b`. -/
def transl : Subgroup F20 := lin.ker

instance : transl.Normal := MonoidHom.normal_ker _

lemma mem_transl {f : F20} : f ∈ transl ↔ f.a = 1 := Iff.rfl

lemma transl_comm : ∀ x ∈ transl, ∀ y ∈ transl, x * y = y * x := by
  intro x hx y hy
  rw [mem_transl] at hx hy
  ext
  · simp only [mul_def, hx, hy, Units.val_one, one_mul, add_comm]
  · simp only [mul_def, hx, hy]

lemma transl_index : transl.index = 4 := by
  rw [transl, Subgroup.index_ker, MonoidHom.range_eq_top.mpr lin_surjective, Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  decide

lemma quotient_isCyclic : IsCyclic (F20 ⧸ transl) :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  isCyclic_of_surjective (QuotientGroup.quotientKerEquivOfSurjective lin lin_surjective).symm
    (MulEquiv.surjective _)

end F20

/-- **`F₂₀`, conditional on the core.** Under `Z4CoreHeightOne`, every language recognized by the
Frobenius group of order `20` has generalized star height at most one. -/
theorem height_one_F20_of_core (hcore : Z4CoreHeightOne) {Alphabet : Type u} [Finite Alphabet]
    (T : FreeMonoid Alphabet →* F20) (F : Set F20) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 :=
  height_one_of_abelian_cyclic_index_four hcore F20.transl F20.transl_comm F20.transl_index
    F20.quotient_isCyclic T F

end GeneralizedStarHeight
