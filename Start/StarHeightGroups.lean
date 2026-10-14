import Start.StarHeightCommutative

/-!
# The single split from the first-return code (towards height two for finite groups)

* `singleSplit_of_firstReturn`: the refinement of `singleSplit_of_fiber_height`.  It asks only
  that the first-return code `firstReturn T` to `1` has height at most one, and that each fiber of
  `T` restricted to the remainder of that code has height at most one.  With
  `height_two_of_singleSplit` this gives height at most two for every language recognized by `T`.

For a morphism `T` into a finite group, `T⁻¹(1) = (firstReturn T)∗`, and `firstReturn_eq`
expresses `firstReturn T` by boolean operations and products from `T⁻¹(1)`, so the first
hypothesis asks for no more than height one of `T⁻¹(1)`.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

section FirstReturn

variable {Alphabet : Type u}

/-- The single-split hypothesis from height one of the first-return code and of the fibers of
the remainder. -/
theorem singleSplit_of_firstReturn {M : Type} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M)
    (hE1 : HasHeightAtMost (firstReturn T) 1)
    (hrem : ∀ d, HasHeightAtMost
      {w | w ∈ remainder (firstReturn T) ∧ T (FreeMonoid.ofList w) = d} 1) :
    SingleSplit T := by
  classical
  have hE : PrefixCode (firstReturn T) := firstReturn_prefixCode T
  refine ⟨firstReturn T, Unit, inferInstance, fun _ _ => (), fun _ => firstReturn T,
    fun _ => 1, hE, hE1, ?_, ?_, ?_, fun _ => hE1, fun _ => HasHeightAtMost.one 1, ?_⟩
  · exact hrem
  · intro x y es u v hes hu hv huv
    rw [Language.mem_one] at hv
    subst hv
    rw [List.append_nil] at huv
    cases es with
    | nil =>
      exfalso
      have := List.eq_nil_of_prefix_nil huv
      exact hu.1 this
    | cons e fs =>
      refine ⟨e, fs, rfl, ?_, rfl⟩
      rw [List.append_nil]
      have heE := hes e (by simp)
      have hep : e <+: (e :: fs).flatten := List.prefix_append _ _
      rcases List.prefix_or_prefix_of_prefix huv hep with h | h
      · exact hE.2 u hu e heE h
      · exact (hE.2 e heE u hu h).symm
  · intro e he _ x
    exact Language.mem_mul.mpr ⟨e, he, [], (Language.mem_one _).mpr rfl, List.append_nil e⟩
  · intro d
    refine ⟨if d = 1 then Set.univ else ∅, ?_⟩
    ext w
    constructor
    · rintro ⟨hw, hT⟩
      have hd : d = 1 := by
        obtain ⟨es, rfl, hes⟩ := Language.mem_kstar.mp hw
        exact hT.symm.trans (firstReturn_T es hes)
      subst hd
      have hg : w ∈ graph (firstReturn T) (fun _ _ => ()) () () := by
        rw [graph_unit_eq_kstar]
        exact hw
      exact Language.mem_iSup.mpr ⟨((), (), (), ()),
        Language.mem_iSup.mpr ⟨by simp, ⟨hg, hg⟩⟩⟩
    · intro h
      obtain ⟨r, hr⟩ := Language.mem_iSup.mp h
      obtain ⟨hrR, hw⟩ := Language.mem_iSup.mp hr
      by_cases hd : d = 1
      · subst hd
        have hw1 := hw.1
        rw [graph_unit_eq_kstar] at hw1
        refine ⟨hw1, ?_⟩
        obtain ⟨es, rfl, hes⟩ := Language.mem_kstar.mp hw1
        exact firstReturn_T es hes
      · simp [hd] at hrR

/-- Height one of the fiber over `1` gives height one of the first-return code. -/
theorem firstReturn_height_of_fiber_one {M : Type} [Monoid M] (T : FreeMonoid Alphabet →* M)
    (h1 : HasHeightAtMost {w | T (FreeMonoid.ofList w) = 1} 1) :
    HasHeightAtMost (firstReturn T) 1 := by
  rw [firstReturn_eq]
  have h := h1.inter (HasHeightAtMost.one (Alphabet := Alphabet) 1).compl
  exact h.inter (h.concat (HasHeightAtMost.one 1).compl).compl

/-- Height at most two for every language recognized by `T`, from the two height-one
hypotheses of `singleSplit_of_firstReturn`. -/
theorem height_two_of_firstReturn [Finite Alphabet] {M : Type} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M)
    (hE1 : HasHeightAtMost (firstReturn T) 1)
    (hrem : ∀ d, HasHeightAtMost
      {w | w ∈ remainder (firstReturn T) ∧ T (FreeMonoid.ofList w) = d} 1)
    (F : Set M) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 2 :=
  height_two_of_singleSplit T (singleSplit_of_firstReturn T hE1 hrem) F

end FirstReturn

end GeneralizedStarHeight
