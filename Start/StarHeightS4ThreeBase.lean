import Start.StarHeightS4Coxeter

/-!
# Helpers for lifted certificates of `S₄` over three letters

* `mkPerm4`: a permutation of `Fin 4` from a table and its inverse table;
* `stN`, `good_baseN`: if the return automaton of an `n`-state automaton over three letters has an
  aperiodic transformation monoid (checked by `decide`), every state language has generalized
  star height at most one.
-/

namespace GeneralizedStarHeight

namespace S4Three

open S4Two

/-- A permutation of `Fin 4` from a table and its inverse table. -/
def mkPerm4 (f g : Fin 4 → Fin 4) (h1 : ∀ i, g (f i) = i := by decide)
    (h2 : ∀ i, f (g i) = i := by decide) : Equiv.Perm (Fin 4) :=
  ⟨f, g, h1, h2⟩

/-- The states of the return automaton on `n` states with base `p`. -/
def stN (n : ℕ) (p : Fin n) : List (Option (Fin n × Bool)) :=
  (List.finRange n).map (fun q => some (q, false)) ++ [some (p, true), none]

lemma stN_closed {n : ℕ} (δ : Fin n → Fin 3 → Fin n) (p : Fin n) :
    ∀ s ∈ stN n p, ∀ x, DFAReturn.retAut δ p s x ∈ stN n p := by
  intro s _ x
  rcases s with _ | ⟨q, _ | _⟩
  · simp [DFAReturn.retAut, stN]
  · by_cases h : δ q x = p
    · simp [DFAReturn.retAut, stN, h]
    · simp [DFAReturn.retAut, stN, h]
  · simp [DFAReturn.retAut, stN]

/-- **A good base point of an `n`-state automaton over three letters.** -/
lemma good_baseN {n : ℕ} (δ : Fin n → Fin 3 → Fin n) (p : Fin n) (N : ℕ)
    (hcert : Aperiodic.certOK (stN n p) [0, 1, 2] (DFAReturn.retAut δ p)
      (Aperiodic.dfaCert (stN n p) [0, 1, 2] (DFAReturn.retAut δ p) 400) N = true) (q : Fin n) :
    HasHeightAtMost {w : List (Fin 3) | DFAReturn.runQ δ p w = q} 1 := by
  have hsf : ∀ P : Option (Fin n × Bool) → Prop,
      HasHeightAtMost {w : List (Fin 3) |
        P (w.foldl (DFAReturn.retAut δ p) (some (p, false)))} 0 :=
    fun P => Aperiodic.starFree_of_dfa_closed (stN n p) (some (p, false)) (by simp [stN])
      [0, 1, 2] S4Cox.letters3_mem (DFAReturn.retAut δ p) (stN_closed δ p) _ N hcert P
  refine height_one_of_starFree_returns δ p q ?_ ?_
  · rw [DFAReturn.firstReturn_eq_retAut]
    exact hsf fun s => s = some (p, true)
  · rw [DFAReturn.avoidTo_eq_retAut]
    exact hsf fun s => s = some (q, false)

end S4Three

end GeneralizedStarHeight
