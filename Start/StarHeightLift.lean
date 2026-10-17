import Start.StarHeightCosetFamily

/-!
# Height one from observers of words, and the lift theorem

* `height_one_of_determined`: if a family of observers of *words* `ob i : List α → X i` determines
  the value `T w` in a finite set `M`, and every fibre of every observer has generalized star
  height at most one, then every language `{w | T w ∈ F}` has height at most one.  The observers
  need not factor through `T`: this is how automata whose letters do not act through `T` enter.
* `height_one_of_lift`: the lift theorem.  Let `π : E →* G` and `S : FreeMonoid α →* E` with
  `π ∘ S = T`.  If the subgroups `H i` of the finite group `E` have height-one coset languages
  and meet inside `ker π`, then every language recognized by `T` has height at most one.
-/

namespace GeneralizedStarHeight

universe u

variable {α : Type u}

/-- **Observers of words that determine the value give height one.**  The observers take values
in finite types. -/
theorem height_one_of_determined {M : Type*} (T : List α → M) {ι : Type*} [Finite ι]
    {X : ι → Type*} [∀ i, Finite (X i)] (ob : ∀ i, List α → X i)
    (hdet : ∀ u v : List α, (∀ i, ob i u = ob i v) → T u = T v)
    (hgood : ∀ i (x : X i), HasHeightAtMost {w | ob i w = x} 1) (F : Set M) :
    HasHeightAtMost {w | T w ∈ F} 1 := by
  classical
  let R := {o : ∀ i, X i // ∃ w, T w ∈ F ∧ ∀ i, ob i w = o i}
  have heq : ({w | T w ∈ F} : Language α) =
      ⨆ o : R, ⨅ i, ({w | ob i w = o.1 i} : Language α) := by
    ext w
    constructor
    · intro hw
      exact Language.mem_iSup.mpr
        ⟨⟨fun i => ob i w, w, hw, fun _ => rfl⟩, HasHeightAtMost.mem_iInf_lang.mpr fun _ => rfl⟩
    · intro hw
      obtain ⟨⟨o, v, hv, hvo⟩, hg⟩ := Language.mem_iSup.mp hw
      have hE := hdet w v fun i => (HasHeightAtMost.mem_iInf_lang.mp hg i).trans (hvo i).symm
      show T w ∈ F
      rw [hE]
      exact hv
  rw [heq]
  exact HasHeightAtMost.iSup _ fun o => HasHeightAtMost.iInf _ fun i => hgood i _

open scoped Pointwise

/-- **The lift theorem.**  If `π ∘ S = T`, and the subgroups `H i` of the finite group `E` have
height-one coset languages and meet inside `ker π`, then every language recognized by `T` has
generalized star height at most one. -/
theorem height_one_of_lift {G E : Type*} [Group G] [Group E] [Fintype E]
    (T : FreeMonoid α →* G) (S : FreeMonoid α →* E) (π : E →* G) (hπ : π.comp S = T)
    {ι : Type*} [Fintype ι] (H : ι → Subgroup E)
    (hgood : ∀ i (g : E), HasHeightAtMost {w | S (FreeMonoid.ofList w) ∈ (H i : Set E) * {g}} 1)
    (hD : ⨅ i, H i ≤ π.ker) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  classical
  refine height_one_of_determined (fun w => T (FreeMonoid.ofList w)) (X := fun _ => Set E)
    (fun i w => (H i : Set E) * {S (FreeMonoid.ofList w)}) ?_ ?_ F
  · intro u v huv
    have hmem : S (FreeMonoid.ofList u) * (S (FreeMonoid.ofList v))⁻¹ ∈ ⨅ i, H i :=
      Subgroup.mem_iInf.mpr fun i => (mem_coset_iff (H i) _ _).mp
        ((coset_eq_iff (H i) _ _).mp (huv i))
    have hk := hD hmem
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk
    simp only [← hπ, MonoidHom.comp_apply]
    exact hk
  · intro i x
    by_cases hx : ∃ g : E, (H i : Set E) * {g} = x
    · obtain ⟨g, rfl⟩ := hx
      have heq : ({w : List α | (H i : Set E) * {S (FreeMonoid.ofList w)} = (H i : Set E) * {g}} :
          Language α) = {w | S (FreeMonoid.ofList w) ∈ (H i : Set E) * {g}} := by
        ext w
        exact coset_eq_iff (H i) _ g
      rw [heq]
      exact hgood i g
    · have hempty : ({w : List α | (H i : Set E) * {S (FreeMonoid.ofList w)} = x} : Language α) =
          (0 : Language α) := by
        ext w
        constructor
        · intro hw
          exact absurd ⟨_, hw⟩ hx
        · intro hw
          exact absurd hw (by simp [Language.zero_def])
      rw [hempty]
      exact HasHeightAtMost.zero 1

end GeneralizedStarHeight
