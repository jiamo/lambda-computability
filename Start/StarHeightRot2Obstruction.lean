import Start.StarHeightZ4Walk
import Start.StarHeightStarFreeAperiodic

/-!
# The rotation-`2` obstruction

Alphabet `Fin 3` with displacements `![0, 1, 2]` in `ZMod 4` (`a`, `b`, `c` = letters `0`, `1`, `2`),
the smallest instance of `Z4CoreRot2`.

* `rot2_Xc_not_starFree`: the first-return code to `0` (`Xc`, `Start/StarHeightZ4Walk.lean`) is not
  star-free.  With `u = b c`, `v = c`, `w = b`, the word `u vᴺ w = b cᴺ⁺¹ b` is a first return iff
  `N + 1` is odd, so no `N` satisfies the conclusion of `aperiodic_of_starFree`.
* `rot2_no_long_c_run`: a star-free language `Y` on which `(#b + 2·#c) mod 4` is constant contains
  no word with a factor `cᴺ`, for the `N` given by `aperiodic_of_starFree`: one more `c` changes
  `#b + 2·#c` by `2` modulo `4`.

Together these are the formal part of the obstruction described in
`docs/goal/evidence/M28-STARHEIGHT-ROT2-OBSTRUCTION.md`.
-/

namespace GeneralizedStarHeight

open scoped Computability

/-- The displacements of the smallest rotation-`2` instance. -/
def σr2 : Fin 3 → ZMod 4 := ![0, 1, 2]

lemma wpow_single {α : Type*} (a : α) (n : ℕ) : wpow [a] n = List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wpow_succ, ih, List.replicate_succ]; rfl

lemma walk_rot2_c_run : ∀ j : ℕ,
    (List.replicate j (2 : Fin 3)).foldl (walk4St σr2) 1 = (if j % 2 = 0 then 1 else 3) ∧
    (List.replicate j (2 : Fin 3)).foldl (walk4St σr2) 3 = (if j % 2 = 0 then 3 else 1)
  | 0 => by simp
  | j + 1 => by
      obtain ⟨h1, h3⟩ := walk_rot2_c_run j
      have e1 : walk4St σr2 1 2 = 3 := by decide
      have e3 : walk4St σr2 3 2 = 1 := by decide
      rw [List.replicate_succ, List.foldl_cons, List.foldl_cons, e1, e3, h1, h3]
      constructor <;> split_ifs <;> first | rfl | omega

/-- `b cᵏ b` is a first return to `0` iff `k` is odd. -/
lemma rot2_bcb_mem_Xc (k : ℕ) :
    (1 :: (List.replicate k (2 : Fin 3) ++ [1])) ∈ Xc σr2 ↔ k % 2 = 1 := by
  rw [Xc_eq_walk]
  show (1 :: (List.replicate k (2 : Fin 3) ++ [1])).foldl (walk4St σr2) 0 = 4 ↔ k % 2 = 1
  have e0 : walk4St σr2 0 1 = 1 := by decide
  rw [List.foldl_cons, e0, List.foldl_append, (walk_rot2_c_run k).1]
  split_ifs with h
  · have : walk4St σr2 1 1 = 2 := by decide
    simp only [List.foldl_cons, List.foldl_nil, this]
    constructor
    · intro h'; exact absurd h' (by decide)
    · intro h'; omega
  · have : walk4St σr2 3 1 = 4 := by decide
    simp only [List.foldl_cons, List.foldl_nil, this]
    constructor
    · intro _; omega
    · intro _; trivial

/-- **The first-return code of the rotation-`2` instance is not star-free.** -/
theorem rot2_Xc_not_starFree : ¬ HasHeightAtMost (Xc σr2) 0 := by
  intro h
  obtain ⟨N, hN⟩ := aperiodic_of_starFree h
  have key := hN [1, 2] [2] [1]
  have e : ∀ M : ℕ, [(1 : Fin 3), 2] ++ wpow [2] M ++ [1] =
      1 :: (List.replicate (M + 1) (2 : Fin 3) ++ [1]) := by
    intro M
    rw [wpow_single, List.replicate_succ]
    rfl
  rw [e, e, rot2_bcb_mem_Xc, rot2_bcb_mem_Xc] at key
  omega

/-- `#b + 2·#c`, the displacement of a word modulo `4`, as a natural number. -/
def rot2Weight (y : List (Fin 3)) : ℕ := y.count 1 + 2 * y.count 2

lemma rot2Weight_append (y z : List (Fin 3)) :
    rot2Weight (y ++ z) = rot2Weight y + rot2Weight z := by
  simp only [rot2Weight, List.count_append]; ring

lemma rot2Weight_replicate (n : ℕ) : rot2Weight (List.replicate n 2) = 2 * n := by
  simp [rot2Weight, List.count_replicate]

/-- **A star-free language on which `#b + 2·#c` is constant modulo `4` has no long runs of `c`.** -/
theorem rot2_no_long_c_run {Y : Language (Fin 3)} (hY : HasHeightAtMost Y 0)
    (hconst : ∀ y ∈ Y, ∀ z ∈ Y, rot2Weight y % 4 = rot2Weight z % 4) :
    ∃ N : ℕ, ∀ s t : List (Fin 3), s ++ List.replicate N 2 ++ t ∉ Y := by
  obtain ⟨N, hN⟩ := aperiodic_of_starFree hY
  refine ⟨N, fun s t hmem => ?_⟩
  have hmem' : s ++ List.replicate (N + 1) 2 ++ t ∈ Y := by
    have := (hN s [2] t).mp (by rw [wpow_single]; exact hmem)
    rwa [wpow_single] at this
  have := hconst _ hmem _ hmem'
  simp only [rot2Weight_append, rot2Weight_replicate] at this
  omega

end GeneralizedStarHeight
