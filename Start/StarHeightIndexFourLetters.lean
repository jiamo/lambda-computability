import Start.StarHeightZ4PM1

/-!
# Index four without a core hypothesis, under a condition on the letters

Let `N` be an abelian normal subgroup of index `4` of a finite group `G` with `G ⧸ N` cyclic, and
`T : FreeMonoid Alphabet →* G`.

* `height_one_of_abelian_cyclic_index_four_of_letters`: if (a) no letter maps to the element of
  order `2` of `G ⧸ N`, or (b) no letter maps to an element of order `4`, every language `T⁻¹(F)`
  has generalized star height at most one.
* `height_one_F20_of_letters`: for `F₂₀`, when no letter is of the form `x ↦ -x + β`, or no letter
  is of the form `x ↦ ±2x + β`.

The reduction of `Start/StarHeightIndexFour.lean` counts letters in every state `q` of `ZMod 4` by
prepending a fresh letter to the word.  It is redone here so that the fresh letters respect the
condition on the letters: in case (a) `j = (-q).val` copies of a fresh letter of displacement `1`;
in case (b) a fresh letter of displacement `2` for `q ∈ {0, 2}`, while for odd `q` the count is `0`.
The core instances used are then `z4core_pm1`, `z4core_rot01`, `z4core_rot03` (displacements in
`{0, 1, 3}`) and `z4core_rot02` (displacements in `{0, 2}`).
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

/-! ### The core instances -/

/-- Displacements avoiding `2`. -/
theorem z4core_no2 (α : Type) [Fintype α] [DecidableEq α] (δ : α → ZMod 4) (hδ : ∀ y, δ y ≠ 2)
    (x : α) (n k : ℕ) (hk : k < n) :
    HasHeightAtMost {w : List α | vcount δ 0 x w % n = k} 1 := by
  by_cases h1 : ∃ y, δ y = 1
  · by_cases h3 : ∃ y, δ y = 3
    · exact z4core_pm1 α δ x n k hk hδ h1 h3
    · push Not at h3
      refine z4core_rot01 δ (fun y => ?_) x n k hk
      have := hδ y; have := h3 y
      rcases zmod4_cases (δ y) with e | e | e | e <;> simp_all
  · push Not at h1
    refine z4core_rot03 δ (fun y => ?_) x n k hk
    have := hδ y; have := h1 y
    rcases zmod4_cases (δ y) with e | e | e | e <;> simp_all

/-! ### Every state, by fresh letters respecting the condition -/

section Fresh

variable {α : Type u} [DecidableEq α]

lemma vcountFrom_replicate {V : Type} [AddMonoid V] (δ : α → V) (q : V) (x a : α) (hax : a ≠ x) :
    ∀ (j : ℕ) (s : V) (w : List α),
      vcountFrom δ q x s (List.replicate j a ++ w) = vcountFrom δ q x (s + j • δ a) w
  | 0, s, w => by simp
  | j + 1, s, w => by
      rw [List.replicate_succ, List.cons_append, vcountFrom_cons, if_neg (fun h => hax h.1),
        zero_add, vcountFrom_replicate δ q x a hax j, succ_nsmul', add_assoc]

lemma leftQuot_replicate_height {β : Type} [DecidableEq β] {L : Language β}
    (h : HasHeightAtMost L 1) (a : β) :
    ∀ j : ℕ, HasHeightAtMost {w : List β | List.replicate j a ++ w ∈ L} 1
  | 0 => h
  | j + 1 => by
      have heq : ({w : List β | List.replicate (j + 1) a ++ w ∈ L} : Language β) =
          leftQuot a {w : List β | List.replicate j a ++ w ∈ L} := by
        ext w
        show List.replicate (j + 1) a ++ w ∈ L ↔ List.replicate j a ++ (a :: w) ∈ L
        rw [List.replicate_succ', List.append_assoc, List.singleton_append]
      rw [heq]
      exact (leftQuot_replicate_height h a j).leftQuot a

/-- **Every state from fresh letters.** If the core holds for all displacement maps into a set `S`
of `ZMod 4`, and `j • d₀ = -q` with `d₀ ∈ S`, the count in state `q` has height at most one for
every displacement map into `S`. -/
theorem vcount_z4_height_of_fresh (S : ZMod 4 → Prop)
    (hcore : ∀ (β : Type) [Fintype β] [DecidableEq β] (δ : β → ZMod 4), (∀ y, S (δ y)) →
      ∀ (x : β) (n k : ℕ), k < n → HasHeightAtMost {w : List β | vcount δ 0 x w % n = k} 1)
    {d₀ : ZMod 4} (hd₀ : S d₀) (j : ℕ) [Finite α] (δ : α → ZMod 4) (hδ : ∀ y, S (δ y))
    (q : ZMod 4) (hq : j • d₀ = -q) (x : α) (n k : ℕ) (hk : k < n) :
    HasHeightAtMost {w : List α | vcount δ q x w % n = k} 1 := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  let δ' : Option (Fin m) → ZMod 4 := fun o => o.elim d₀ (fun i => δ (e.symm i))
  let g : α → Option (Fin m) := fun a => some (e a)
  have hg : Function.Injective g := fun a b h => e.injective (Option.some.inj h)
  let φ : α → Option (Option (Fin m)) := fun a => some (g a)
  have hS : ∀ y, S (δ' y) := by
    rintro (_ | i)
    · exact hd₀
    · exact hδ _
  have h0 := hcore (Option (Fin m)) δ' hS (g x) n k hk
  have heq : {w : List α | vcount δ q x w % n = k} =
      invAlph φ {w | List.replicate j none ++ w ∈ {u | vcount δ' 0 (g x) u % n = k}} := by
    ext w
    have hfm : w.filterMap φ = w.map g := by
      induction w with
      | nil => rfl
      | cons b w ih => simp [φ, ih]
    show _ % n = k ↔ vcount δ' 0 (g x) (List.replicate j none ++ w.filterMap φ) % n = k
    rw [hfm, vcount_eq_vcountFrom, vcount_eq_vcountFrom,
      vcountFrom_replicate δ' 0 (g x) none (by simp [g]), vcountFrom_map g hg δ' 0 x]
    have hcomp : δ' ∘ g = δ := funext fun a => by simp [δ', g]
    rw [hcomp, vcountFrom_shift δ 0 x q (0 + j • δ' none) w]
    simp [δ', hq]
  rw [heq]
  exact (leftQuot_replicate_height h0 none j).invAlph φ

lemma zmod4_even_add {s d : ZMod 4} (hs : s = 0 ∨ s = 2) (hd : d = 0 ∨ d = 2) :
    s + d = 0 ∨ s + d = 2 := by
  rcases hs with rfl | rfl <;> rcases hd with rfl | rfl <;> decide

lemma vcountFrom_odd (δ : α → ZMod 4) (hδ : ∀ y, δ y = 0 ∨ δ y = 2) (q : ZMod 4)
    (hq : ¬ (q = 0 ∨ q = 2)) (x : α) :
    ∀ (w : List α) (s : ZMod 4), (s = 0 ∨ s = 2) → vcountFrom δ q x s w = 0
  | [], _, _ => vcountFrom_nil ..
  | b :: w, s, hs => by
      rw [vcountFrom_cons, if_neg (fun h => hq (by rw [← h.2]; exact hs)), zero_add]
      exact vcountFrom_odd δ hδ q hq x w _ (zmod4_even_add hs (hδ b))

/-- Case (a): no displacement `2`. -/
theorem vcount_z4_height_no2 [Finite α] (δ : α → ZMod 4) (hδ : ∀ y, δ y ≠ 2) (q : ZMod 4)
    (x : α) (n k : ℕ) (hk : k < n) :
    HasHeightAtMost {w : List α | vcount δ q x w % n = k} 1 :=
  vcount_z4_height_of_fresh (fun d => d ≠ 2) (fun β _ _ δ hδ x n k hk => z4core_no2 β δ hδ x n k hk)
    (d₀ := 1) (by decide) (-q).val δ hδ q (by simp) x n k hk

/-- Case (b): displacements in `{0, 2}`. -/
theorem vcount_z4_height_even [Finite α] (δ : α → ZMod 4) (hδ : ∀ y, δ y = 0 ∨ δ y = 2)
    (q : ZMod 4) (x : α) (n k : ℕ) (hk : k < n) :
    HasHeightAtMost {w : List α | vcount δ q x w % n = k} 1 := by
  have hcore : ∀ (β : Type) [Fintype β] [DecidableEq β] (δ : β → ZMod 4),
      (∀ y, δ y = 0 ∨ δ y = 2) → ∀ (x : β) (n k : ℕ), k < n →
        HasHeightAtMost {w : List β | vcount δ 0 x w % n = k} 1 :=
    fun β _ _ δ hδ x n k hk => z4core_rot02 δ hδ x n k hk
  by_cases hq : q = 0 ∨ q = 2
  · rcases hq with rfl | rfl
    · exact vcount_z4_height_of_fresh (fun d => d = 0 ∨ d = 2) hcore (d₀ := 2) (Or.inr rfl) 0 δ hδ 0 (by decide) x n k hk
    · exact vcount_z4_height_of_fresh (fun d => d = 0 ∨ d = 2) hcore (d₀ := 2) (Or.inr rfl) 1 δ hδ 2 (by decide) x n k hk
  · have h0 : ∀ w, vcount δ q x w = 0 := fun w => by
      rw [vcount_eq_vcountFrom]; exact vcountFrom_odd δ hδ q hq x w 0 (Or.inl rfl)
    by_cases hk0 : k = 0
    · have : {w : List α | vcount δ q x w % n = k} = ⊤ := by
        ext w; simp [h0, hk0]
      rw [this]; exact HasHeightAtMost.top 1
    · have : {w : List α | vcount δ q x w % n = k} = (0 : Language α) := by
        ext w
        constructor
        · intro h
          have h' : vcount δ q x w % n = k := h
          rw [h0, Nat.zero_mod] at h'
          exact absurd h'.symm hk0
        · intro h; exact absurd h (Language.notMem_zero w)
      rw [this]; exact HasHeightAtMost.zero 1

end Fresh

/-! ### Assembly -/

lemma addOrderOf_two_z4 : addOrderOf (2 : ZMod 4) = 2 := by
  rw [addOrderOf_eq_iff (by norm_num)]; exact ⟨by decide, by decide⟩

lemma addOrderOf_one_z4 : addOrderOf (1 : ZMod 4) = 4 := by
  rw [addOrderOf_eq_iff (by norm_num)]; exact ⟨by decide, by decide⟩

lemma addOrderOf_three_z4 : addOrderOf (3 : ZMod 4) = 4 := by
  rw [addOrderOf_eq_iff (by norm_num)]; exact ⟨by decide, by decide⟩

section Assembly

open Classical

variable {Alphabet : Type u}

/-- **Index four, condition on the letters** (M28-STARHEIGHT-INDEX-FOUR-LETTERS).  Let `N` be an
abelian normal subgroup of index `4` of a finite group `G` with `G ⧸ N` cyclic.  If no letter
maps to the element of order `2` of `G ⧸ N`, or no letter maps to an element of order `4`, every
language recognized through `T` has generalized star height at most one. -/
theorem height_one_of_abelian_cyclic_index_four_of_letters [Finite Alphabet]
    {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hidx : N.index = 4)
    (hcyc : IsCyclic (G ⧸ N)) (T : FreeMonoid Alphabet →* G)
    (hlet : (∀ a, orderOf (psi N T (FreeMonoid.of a)) ≠ 2) ∨
      (∀ a, orderOf (psi N T (FreeMonoid.of a)) ≠ 4)) (F : Set G) :
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
  have hord : ∀ a, orderOf (psi N T (FreeMonoid.of a)) = addOrderOf (δ a) := fun a => by
    rw [← addOrderOf_ofMul_eq_orderOf]
    exact (addOrderOf_injective f.toAddMonoidHom f.injective _).symm
  have hvc : ∀ (q : ZMod 4) (x : Alphabet) (k : ℕ), k < Nat.card N →
      HasHeightAtMost {w : List Alphabet | vcount δ q x w % Nat.card N = k} 1 := by
    intro q x k hk
    rcases hlet with h | h
    · refine vcount_z4_height_no2 δ (fun y hy => h y ?_) q x _ k hk
      rw [hord, hy]
      exact addOrderOf_two_z4
    · refine vcount_z4_height_even δ (fun y => ?_) q x _ k hk
      have hy := h y
      rw [hord] at hy
      rcases zmod4_cases (δ y) with e | e | e | e
      · exact Or.inl e
      · rw [e] at hy; exact absurd addOrderOf_one_z4 hy
      · exact Or.inr e
      · rw [e] at hy; exact absurd addOrderOf_three_z4 hy
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
  · exact HasHeightAtMost.iInf _ fun pr => hvc _ pr.2 _ (z.1.2 pr).2

end Assembly

/-! ### `F₂₀` -/

lemma F20.orderOf_psi {Alphabet : Type u} (T : FreeMonoid Alphabet →* F20) (a : Alphabet) :
    orderOf (psi F20.transl T (FreeMonoid.of a)) = orderOf (T (FreeMonoid.of a)).a := by
  let e := QuotientGroup.quotientKerEquivOfSurjective F20.lin F20.lin_surjective
  exact (orderOf_injective e.toMonoidHom e.injective (psi F20.transl T (FreeMonoid.of a))).symm.trans
    rfl

lemma units5_order_two {u : (ZMod 5)ˣ} (h : orderOf u = 2) : u = -1 := by
  rw [orderOf_eq_iff (by norm_num)] at h
  have h1 : u ≠ 1 := by simpa using h.2 1 (by norm_num) (by norm_num)
  have key : ∀ u : (ZMod 5)ˣ, u ^ 2 = 1 → u ≠ 1 → u = -1 := by decide
  exact key u h.1 h1

lemma units5_order_four {u : (ZMod 5)ˣ} (h : orderOf u = 4) :
    (u : ZMod 5) = 2 ∨ (u : ZMod 5) = 3 := by
  rw [orderOf_eq_iff (by norm_num)] at h
  have h1 : u ≠ 1 := by simpa using h.2 1 (by norm_num) (by norm_num)
  have h2 : u ^ 2 ≠ 1 := h.2 2 (by norm_num) (by norm_num)
  have key : ∀ u : (ZMod 5)ˣ, u ≠ 1 → u ^ 2 ≠ 1 → (u : ZMod 5) = 2 ∨ (u : ZMod 5) = 3 := by
    decide
  exact key u h1 h2

/-- **`F₂₀` under a condition on the letters.** If no letter is of the form `x ↦ -x + β`, or no
letter is of the form `x ↦ ±2x + β`, every language recognized through `T` has generalized star
height at most one. -/
theorem height_one_F20_of_letters {Alphabet : Type u} [Finite Alphabet]
    (T : FreeMonoid Alphabet →* F20)
    (hlet : (∀ a, (T (FreeMonoid.of a)).a ≠ -1) ∨
      (∀ a, ((T (FreeMonoid.of a)).a : ZMod 5) ≠ 2 ∧ ((T (FreeMonoid.of a)).a : ZMod 5) ≠ 3))
    (F : Set F20) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_abelian_cyclic_index_four_of_letters F20.transl F20.transl_comm
    F20.transl_index F20.quotient_isCyclic T ?_ F
  rcases hlet with h | h
  · left
    intro a ha
    rw [F20.orderOf_psi] at ha
    exact h a (units5_order_two ha)
  · right
    intro a ha
    rw [F20.orderOf_psi] at ha
    rcases units5_order_four ha with e | e
    · exact (h a).1 e
    · exact (h a).2 e

end GeneralizedStarHeight
