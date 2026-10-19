import Start.StarHeightAabbTwo
import Start.StarHeightPST
import Start.StarHeightCoreHeight
import Start.StarHeightUT4
import Start.StarHeightIndexPrime
import Start.StarHeightCommutative

/-!
# Groups all of whose languages have height at most one form a pseudovariety

* `GroupHeightOne G`: every language recognized by `G` (over a finite alphabet in `Type`) has
  generalized star height at most one.  `GroupHeightOne.univ` gives the same for alphabets in
  any universe.
* Closure: `of_mulEquiv`, `of_injective` (subgroups), `of_surjective` (quotients), `prod` and
  `pi` (finite products of finite groups), and `of_dvd_pi` (a quotient of a subgroup of a
  finite product).
* Instances: commutative groups, `Z2WrZ4`, `UT4 n`, `A₄`, groups with an abelian normal subgroup
  of prime index, the Frattini-abelian groups, and finite groups with an abelian exponent-`2`
  normal subgroup whose quotient is `≅ Z₄`.
-/

namespace GeneralizedStarHeight

universe u

open scoped Computability

/-- **Good groups.** Every language recognized by `G` over a finite alphabet has generalized
star height at most one. -/
def GroupHeightOne (G : Type) [Group G] : Prop :=
  ∀ (α : Type) [Finite α] (T : FreeMonoid α →* G) (F : Set G),
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1

namespace GroupHeightOne

variable {G H : Type} [Group G] [Group H]

lemma ofList_map {α β : Type*} (ψ : α → β) (w : List α) :
    FreeMonoid.ofList (w.map ψ) = FreeMonoid.map ψ (FreeMonoid.ofList w) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [List.map_cons, FreeMonoid.ofList_cons, FreeMonoid.ofList_cons, map_mul, ih]
      rfl

/-- `GroupHeightOne` for alphabets in any universe. -/
theorem univ (hG : GroupHeightOne G) {α : Type u} [Finite α] (T : FreeMonoid α →* G)
    (F : Set G) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  have h0 := hG (Fin m) (T.comp (FreeMonoid.map e.symm)) F
  have heq : {w : List α | T (FreeMonoid.ofList w) ∈ F} =
      invAlph (fun a => some (e a)) {u | T.comp (FreeMonoid.map e.symm) (FreeMonoid.ofList u) ∈ F} := by
    ext w
    have hfm : w.filterMap (fun a => some (e a)) = w.map e := by
      induction w with
      | nil => rfl
      | cons b w ih => simp [ih]
    show _ ↔ T.comp (FreeMonoid.map e.symm) (FreeMonoid.ofList (w.filterMap _)) ∈ F
    rw [hfm, ofList_map, MonoidHom.comp_apply, ← MonoidHom.comp_apply (FreeMonoid.map e.symm),
      ← FreeMonoid.map_comp, ← ofList_map]
    simp
  rw [heq]
  exact h0.invAlph _

/-- **Subgroups**: `GroupHeightOne` passes along injective homomorphisms. -/
theorem of_injective (f : H →* G) (hf : Function.Injective f) (hG : GroupHeightOne G) :
    GroupHeightOne H := by
  intro α _ T F
  have heq : {w : List α | T (FreeMonoid.ofList w) ∈ F} =
      {w | (f.comp T) (FreeMonoid.ofList w) ∈ f '' F} := by
    ext w
    simp only [Set.mem_ofPred_eq, MonoidHom.comp_apply, hf.mem_set_image]
  rw [heq]
  exact hG α _ _

/-- **Quotients**: `GroupHeightOne` passes along surjective homomorphisms. -/
theorem of_surjective (f : G →* H) (hf : Function.Surjective f) (hG : GroupHeightOne G) :
    GroupHeightOne H := by
  intro α _ T F
  let T' : FreeMonoid α →* G := FreeMonoid.lift fun a => Function.surjInv hf (T (FreeMonoid.of a))
  have hT : f.comp T' = T := FreeMonoid.hom_eq fun a => by
    simp [T', Function.surjInv_eq hf]
  have heq : {w : List α | T (FreeMonoid.ofList w) ∈ F} =
      {w | T' (FreeMonoid.ofList w) ∈ f ⁻¹' F} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [← MonoidHom.comp_apply, hT]
  rw [heq]
  exact hG α _ _

/-- **Isomorphisms.** -/
theorem of_mulEquiv (e : G ≃* H) (hG : GroupHeightOne G) : GroupHeightOne H :=
  of_surjective e.toMonoidHom e.surjective hG

/-- **Binary products** of finite groups. -/
theorem prod [Finite G] [Finite H] (hG : GroupHeightOne G) (hH : GroupHeightOne H) :
    GroupHeightOne (G × H) :=
  fun α _ T F => height_one_prod (fun T F => hG α T F) (fun T F => hH α T F) T F

/-- **Finite products** of finite groups. -/
theorem pi {ι : Type} [Finite ι] {K : ι → Type} [∀ i, Group (K i)] [∀ i, Finite (K i)]
    (hK : ∀ i, GroupHeightOne (K i)) : GroupHeightOne (∀ i, K i) := by
  intro α _ T F
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language α) = ⨆ g : F,
      ⨅ i, {w | (Pi.evalMonoidHom K i).comp T (FreeMonoid.ofList w) ∈ ({g.1 i} : Set (K i))} := by
    ext w
    constructor
    · intro hw
      refine Language.mem_iSup.mpr ⟨⟨_, hw⟩, ?_⟩
      exact HasHeightAtMost.mem_iInf_lang.mpr fun i => rfl
    · intro hw
      obtain ⟨g, hg⟩ := Language.mem_iSup.mp hw
      have hg' := HasHeightAtMost.mem_iInf_lang.mp hg
      have : T (FreeMonoid.ofList w) = g.1 := funext fun i => hg' i
      show T (FreeMonoid.ofList w) ∈ F
      rw [this]
      exact g.2
  rw [heq]
  exact HasHeightAtMost.iSup _ fun g => HasHeightAtMost.iInf _ fun i => hK i α _ _

/-- **Division of a finite product**: a quotient of a subgroup of a finite product of finite
`GroupHeightOne` groups is `GroupHeightOne`. -/
theorem of_dvd_pi {ι : Type} [Finite ι] {K : ι → Type} [∀ i, Group (K i)] [∀ i, Finite (K i)]
    (hK : ∀ i, GroupHeightOne (K i)) (S : Subgroup (∀ i, K i)) (f : S →* H)
    (hf : Function.Surjective f) : GroupHeightOne H :=
  of_surjective f hf (of_injective S.subtype S.subtype_injective (pi hK))

end GroupHeightOne

/-! ### Instances -/

/-- Finite commutative groups. -/
theorem groupHeightOne_of_comm {G : Type} [Group G] [Fintype G] (hG : ∀ x y : G, x * y = y * x) :
    GroupHeightOne G :=
  fun _ _ T F => height_one_of_comm hG T F

/-- `Z₂ ≀ Z₄`. -/
theorem groupHeightOne_Z2WrZ4 : GroupHeightOne Z2WrZ4 :=
  fun _ _ T F => height_one_Z2_wr_Z4 T F

/-- `UT₄(ZMod n)`. -/
theorem groupHeightOne_UT4 (n : ℕ) [NeZero n] : GroupHeightOne (UT4 n) :=
  fun _ _ T F => height_one_UT4 n T F

/-- `A₄`. -/
theorem groupHeightOne_alternatingGroup_four : GroupHeightOne (alternatingGroup (Fin 4)) :=
  fun _ _ T F => height_one_alternatingGroup_four T F

/-- Finite groups with an abelian normal subgroup of prime index. -/
theorem groupHeightOne_of_abelian_prime_index {G : Type} [Group G] [Fintype G] (N : Subgroup G)
    [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) {p : ℕ} [Fact p.Prime]
    (hidx : N.index = p) : GroupHeightOne G :=
  fun _ _ T F => height_one_of_abelian_prime_index N hab hidx T F

/-- Finite groups whose subgroup generated by commutators and `p`-th powers is abelian. -/
theorem groupHeightOne_of_frattini_abelian {G : Type} [Group G] [Fintype G] {p : ℕ}
    [Fact p.Prime]
    (hab : ∀ x ∈ commPowSubgroup G p, ∀ y ∈ commPowSubgroup G p, x * y = y * x) :
    GroupHeightOne G :=
  fun _ _ T F => height_one_of_frattini_abelian hab T F

/-- Finite groups with an abelian exponent-`2` normal subgroup whose quotient is `≅ Z₄`. -/
theorem groupHeightOne_of_exponent_two_normal_z4 {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hexp : ∀ x ∈ N, x * x = 1) (e : G ⧸ N ≃* Multiplicative (ZMod 4)) : GroupHeightOne G :=
  fun _ _ T F =>
    height_one_of_exponent_two_normal_of_core_mod_two_equiv N hab hexp e hcoreModTwo_zmod_four T F

end GeneralizedStarHeight
