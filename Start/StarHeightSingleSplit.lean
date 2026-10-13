import Start.StarHeightMain

/-!
# Generalized star height two from a single split

`GeneralizedStarHeight.main` reaches height three through two nested applications of
`EpisodeAlgebra.split_height` (`0 → 2 → 3`).  This module isolates the hypothesis under which
one application suffices.

`SingleSplit T` asks for a prefix code `E` of height at most one whose remainder fibers have
height at most one, deterministic updates `G` on a finite state set with tests of height at
most one that are sound on `E` and available on every episode of `E` (no skipped episodes),
and every fiber of `T` on `E∗` a finite union of intersections of two graph languages of `G`
over `E` (the shape produced by `AffineRecovery.recovery`).

* `height_two_of_singleSplit`: under `SingleSplit T`, every language recognized by `T` has
  generalized star height at most two.
* `main_two_of_singleSplit`: if every morphism into a finite monoid satisfies `SingleSplit`,
  every regular language has generalized star height at most two.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

/-- The single-split hypothesis for a morphism `T` into a finite monoid. -/
def SingleSplit {Alphabet : Type u} {M : Type} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M) : Prop :=
  ∃ (E : Language Alphabet) (S : Type) (_ : Fintype S) (G : List Alphabet → S → S)
    (P Q : S → Language Alphabet),
    PrefixCode E ∧ HasHeightAtMost E 1 ∧
    (∀ d, HasHeightAtMost {w | w ∈ remainder E ∧ T (FreeMonoid.ofList w) = d} 1) ∧
    SplitSound E G P Q ∧ SplitAvailable E 0 G P Q ∧
    (∀ x, HasHeightAtMost (P x) 1) ∧ (∀ y, HasHeightAtMost (Q y) 1) ∧
    ∀ d, ∃ R : Set (S × S × S × S),
      {w | w ∈ E∗ ∧ T (FreeMonoid.ofList w) = d} =
        ⨆ r ∈ R, graph E G r.1 r.2.1 ⊓ graph E G r.2.2.1 r.2.2.2

/-- One split with no skipped episodes gives height two for every graph language. -/
theorem single_split_graph_height {Alphabet : Type u} {S : Type} [Finite S]
    {E : Language Alphabet} (hE : PrefixCode E) (G : List Alphabet → S → S)
    (P Q : S → Language Alphabet) (hs : SplitSound E G P Q) (ha : SplitAvailable E 0 G P Q)
    (hD : HasHeightAtMost E 1) (hP : ∀ x, HasHeightAtMost (P x) 1)
    (hQ : ∀ y, HasHeightAtMost (Q y) 1) (x y : S) :
    HasHeightAtMost (graph E G x y) 2 := by
  have h := split_height hE le_rfl (bot_le) G P Q hs ha 0 hD hP hQ
    (fun x y => empty_skip_height G x y) x y
  simpa using h

/-- Under `SingleSplit T`, every language recognized by `T` has height at most two. -/
theorem height_two_of_singleSplit {Alphabet : Type u} [Finite Alphabet] {M : Type}
    [Monoid M] [Fintype M] (T : FreeMonoid Alphabet →* M) (hT : SingleSplit T)
    (F : Set M) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 2 := by
  classical
  obtain ⟨E, S, hS, G, P, Q, hE, hEh, hB, hs, ha, hP, hQ, hfib⟩ := hT
  let A : M → Language Alphabet := fun d => {w | w ∈ E∗ ∧ T (FreeMonoid.ofList w) = d}
  let B : M → Language Alphabet := fun f => {w | w ∈ remainder E ∧ T (FreeMonoid.ofList w) = f}
  have hA : ∀ d, HasHeightAtMost (A d) 2 := by
    intro d
    obtain ⟨R, hR⟩ := hfib d
    change HasHeightAtMost {w | w ∈ E∗ ∧ T (FreeMonoid.ofList w) = d} 2
    rw [hR]
    have hfin : (R : Set (S × S × S × S)).Finite := Set.toFinite R
    have heq : (⨆ r ∈ R, graph E G r.1 r.2.1 ⊓ graph E G r.2.2.1 r.2.2.2) =
        ⨆ r ∈ hfin.toFinset, graph E G r.1 r.2.1 ⊓ graph E G r.2.2.1 r.2.2.2 := by
      simp only [Set.Finite.mem_toFinset]
    rw [heq]
    apply HasHeightAtMost.finset_iSup
    intro r _
    exact (single_split_graph_height hE G P Q hs ha hEh hP hQ _ _).inter
      (single_split_graph_height hE G P Q hs ha hEh hP hQ _ _)
  let I := {p : M × M // p.1 * p.2 ∈ F}
  have hU : HasHeightAtMost (⨆ p : I, A p.1.1 * B p.1.2) 2 :=
    HasHeightAtMost.iSup _ (fun p => (hA p.1.1).concat ((hB p.1.2).mono (by decide)))
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) =
      ⨆ p : I, A p.1.1 * B p.1.2 := by
    ext w
    constructor
    · intro hw
      obtain ⟨es, r, hes, hr, hwr⟩ := factor_remainder hE.1 w
      let d := T (FreeMonoid.ofList es.flatten)
      let f := T (FreeMonoid.ofList r)
      have hdf : d * f ∈ F := by
        change T (FreeMonoid.ofList es.flatten) * T (FreeMonoid.ofList r) ∈ F
        rw [← map_mul]
        change T (FreeMonoid.ofList (es.flatten ++ r)) ∈ F
        rw [← hwr]
        exact hw
      apply Language.mem_iSup.mpr
      refine ⟨⟨(d, f), hdf⟩, Language.mem_mul.mpr ⟨es.flatten, ?_, r, ?_, hwr.symm⟩⟩
      · exact ⟨Language.join_mem_kstar hes, rfl⟩
      · exact ⟨hr, rfl⟩
    · intro hw
      obtain ⟨p, hp⟩ := Language.mem_iSup.mp hw
      obtain ⟨a, ha, b, hb, rfl⟩ := Language.mem_mul.mp hp
      change T (FreeMonoid.ofList a * FreeMonoid.ofList b) ∈ F
      rw [map_mul, ha.2, hb.2]
      exact p.2
  exact heq.symm ▸ hU

/-- If every morphism into a finite monoid admits a single split, every regular language has
generalized star height at most two. -/
theorem main_two_of_singleSplit {Alphabet : Type u} [Finite Alphabet]
    (h : ∀ (M : Type) [Monoid M] [Fintype M] (T : FreeMonoid Alphabet →* M),
      SingleSplit T)
    (L : Language Alphabet) (hL : L.IsRegular) : HasHeightAtMost L 2 := by
  classical
  rcases isEmpty_or_nonempty Alphabet with hA | hA
  · apply HasHeightAtMost.finite L _ 2
    apply (Set.finite_singleton ([] : List Alphabet)).subset
    intro w _
    cases w with
    | nil => rfl
    | cons a w => exact isEmptyElim a
  · obtain ⟨M, hM, hfin, T, F, hTF⟩ := FiniteRecognition.of_regular hL
    let : Monoid M := hM
    let : Fintype M := hfin
    have heq : L = ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) := by
      ext w
      exact hTF w
    rw [heq]
    exact height_two_of_singleSplit T (h M T) F

end GeneralizedStarHeight
