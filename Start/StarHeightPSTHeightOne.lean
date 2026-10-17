import Start.StarHeightPSTReturns
import Start.StarHeightDFAReturns
import Start.StarHeightAperiodic

/-!
# `L_PST` has generalized star height exactly one

* `PST.b0count_mod_two`: the number of `b` read in the state `0` of the `S₃` automaton is, mod `2`,
  the number of `b` plus a bit read off the states of two automata: the `S₃` automaton `stateOf 0`
  (`a = (0 1)`, `b = (0 2)`) and the `S₄` automaton `s4state` on four points (`a = (0 1)`,
  `b = (0 1 2 3)`).
* `PST.s4state_height`: every state language of `s4state` has height at most one, by
  `height_one_of_starFree_returns`: its first-return code to `0`, `(a ∪ b)(a ∪ b a* b a* b)`, and
  its paths avoiding `0` are star-free (`Aperiodic.starFree_of_dfa_closed`).
* `PST.K_height_one`, `PST.LPST_height_one`: `K` is a finite union of intersections of state
  languages of three automata (`|w|_b mod 2`, `stateOf 0`, `s4state`), each of height at most one;
  then `pst_candidate_iff`.
* `PST.LPST_not_starFree`: `a^(2k) ∈ L_PST`, `a^(2k+1) ∉ L_PST`, so `L_PST` is not aperiodic.

Each factor automaton has star-free first returns, while their product does not
(`pst_firstReturn_not_starFree`); the `S₄` factor is not metabelian (`pst_not_metabelian`).
-/

namespace GeneralizedStarHeight

namespace PST

open AB

/-- The `S₄` automaton on four points: `a = (0 1)`, `b = (0 1 2 3)`. -/
def move4 : Fin 4 → AB → Fin 4
  | q, a => ![1, 0, 2, 3] q
  | q, b => ![1, 2, 3, 0] q

/-- The state `0·w` of the `S₄` automaton. -/
def s4state (w : List AB) : Fin 4 := w.foldl move4 0

/-- The states of the `S₄` automaton contributing a `1`, for each state of the `S₃` automaton. -/
def Qs : Fin 3 → Finset (Fin 4) := ![{1, 2}, {0, 2}, {2, 3}]

lemma s4state_append_single (w : List AB) (x : AB) : s4state (w ++ [x]) = move4 (s4state w) x := by
  rw [s4state, List.foldl_append]
  rfl

/-- The finite step check on `Fin 2 × Fin 3 × Fin 4 × AB`. -/
lemma qs_step : ∀ (r : Fin 2) (s : Fin 3) (q : Fin 4) (x : AB),
    ((r.val + if q ∈ Qs s then 1 else 0) % 2 + if x = b ∧ s = 0 then 1 else 0) % 2 =
      (r.val + (if x = b then 1 else 0) + if move4 q x ∈ Qs (move s x) then 1 else 0) % 2 := by
  decide

lemma count_b_single (x : AB) : [x].count b = if x = b then 1 else 0 := by
  cases x <;> rfl

/-- **The identity.** -/
theorem b0count_mod_two (w : List AB) :
    b0count 0 w % 2 = (w.count b + if s4state w ∈ Qs (stateOf 0 w) then 1 else 0) % 2 := by
  induction w using List.reverseRecOn with
  | nil => decide
  | append_singleton w x ih =>
      rw [b0count_append_single, List.count_append, count_b_single, stateOf_append_single,
        s4state_append_single]
      generalize stateOf 0 w = s, s4state w = q, w.count b = C, b0count 0 w = B at ih ⊢
      have h := qs_step ⟨C % 2, Nat.mod_lt _ (by norm_num)⟩ s q x
      simp only at h
      generalize (if q ∈ Qs s then 1 else 0) = I at ih h
      generalize (if x = b ∧ s = 0 then 1 else 0) = J at h ⊢
      generalize (if x = b then 1 else 0) = X at h ⊢
      generalize (if move4 q x ∈ Qs (move s x) then 1 else 0) = I' at h ⊢
      omega

/-! ### The state languages of the `S₄` automaton -/

/-- The reachable states of `DFAReturn.retAut move4 0`. -/
def ret4States : List (Option (Fin 4 × Bool)) :=
  [some (0, false), some (1, false), some (2, false), some (3, false), some (0, true), none]

lemma ret4_closed : ∀ q ∈ ret4States, ∀ x : AB, DFAReturn.retAut move4 0 q x ∈ ret4States := by
  decide

lemma ret4_cert : Aperiodic.certOK ret4States [a, b] (DFAReturn.retAut move4 0)
    (Aperiodic.dfaCert ret4States [a, b] (DFAReturn.retAut move4 0) 100) 6 = true := by
  decide +kernel

lemma ret4_starFree (P : Option (Fin 4 × Bool) → Prop) :
    HasHeightAtMost {w : List AB | P (w.foldl (DFAReturn.retAut move4 0) (some (0, false)))} 0 :=
  Aperiodic.starFree_of_dfa_closed ret4States (some (0, false)) (by decide) [a, b]
    (fun x => by cases x <;> decide) _ ret4_closed _ _ ret4_cert P

/-- The first-return code of the `S₄` automaton to `0`, `(a ∪ b)(a ∪ b a* b a* b)`, is
star-free. -/
theorem s4_firstReturn_starFree : HasHeightAtMost (DFAReturn.firstReturn move4 (0 : Fin 4)) 0 := by
  rw [DFAReturn.firstReturn_eq_retAut]
  exact ret4_starFree (fun s => s = some (0, true))

/-- The paths of the `S₄` automaton from `0` to `q` avoiding `0` are star-free. -/
theorem s4_avoidTo_starFree (q : Fin 4) : HasHeightAtMost (DFAReturn.avoidTo move4 0 q) 0 := by
  rw [DFAReturn.avoidTo_eq_retAut]
  exact ret4_starFree (fun s => s = some (q, false))

/-- **The state languages of the `S₄` automaton have height at most one.** -/
theorem s4state_height (q : Fin 4) : HasHeightAtMost {w : List AB | s4state w = q} 1 :=
  height_one_of_starFree_returns move4 0 q s4_firstReturn_starFree (s4_avoidTo_starFree q)

/-! ### Assembly -/

/-- The parity of `b`. -/
lemma countB_height (r : ℕ) : HasHeightAtMost {w : List AB | w.count b % 2 = r} 1 :=
  countIn_height b (K := {k | k % 2 = r}) (m := 0) (p := 2) (by norm_num)
    (fun k _ => by simp [Nat.add_mod_right])

/-- The bit of `(r, s, q)`. -/
def fBit (r : Fin 2) (s : Fin 3) (q : Fin 4) : ℕ := (r.val + if q ∈ Qs s then 1 else 0) % 2

/-- The piece of `K` indexed by `(r, s, q)`. -/
def Kpiece (t : Fin 2 × Fin 3 × Fin 4) : Language AB :=
  if fBit t.1 t.2.1 t.2.2 = 0 then
    ({w | w.count b % 2 = t.1.val} ⊓ {w | stateOf 0 w = t.2.1}) ⊓ {w | s4state w = t.2.2}
  else 0

lemma K_eq_iSup : K = ⨆ t, Kpiece t := by
  ext w
  rw [mem_K, Language.mem_iSup, b0count_mod_two]
  constructor
  · intro h
    refine ⟨(⟨w.count b % 2, Nat.mod_lt _ (by norm_num)⟩, stateOf 0 w, s4state w), ?_⟩
    have hf : fBit ⟨w.count b % 2, Nat.mod_lt _ (by norm_num)⟩ (stateOf 0 w) (s4state w) = 0 := by
      simp only [fBit]
      omega
    simp only [Kpiece, hf, if_true]
    exact ⟨⟨rfl, rfl⟩, rfl⟩
  · rintro ⟨⟨r, s, q⟩, ht⟩
    simp only [Kpiece] at ht
    split_ifs at ht with hf
    · obtain ⟨⟨h1, h2⟩, h3⟩ := ht
      have h1' : w.count b % 2 = r.val := h1
      have h2' : stateOf 0 w = s := h2
      have h3' : s4state w = q := h3
      simp only [fBit] at hf
      rw [h2', h3']
      omega
    · exact absurd ht (by simp)

/-- **`K` has height at most one.** -/
theorem K_height_one : HasHeightAtMost K 1 := by
  rw [K_eq_iSup]
  refine HasHeightAtMost.iSup _ fun t => ?_
  unfold Kpiece
  split_ifs
  · exact ((countB_height _).inter (stateOf_height _)).inter (s4state_height _)
  · exact HasHeightAtMost.zero 1

/-- **`L_PST` has generalized star height at most one.** -/
theorem LPST_height_one : HasHeightAtMost LPST 1 :=
  pst_candidate_iff.mpr K_height_one

/-! ### `L_PST` is not star-free -/

lemma stateOf_rep_a_even : ∀ (m : ℕ) (s : Fin 3), stateOf s (List.replicate (2 * m) a) = s
  | 0, _ => rfl
  | m + 1, s => by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, List.replicate_succ, List.replicate_succ,
        stateOf_cons, stateOf_cons, stateOf_rep_a_even m]
      revert s
      decide

lemma rep_a_even_mem (m : ℕ) : List.replicate (2 * m) a ∈ LPST := by
  rw [mem_LPST, stateOf_rep_a_even, b0count_rep_a]
  exact ⟨rfl, rfl⟩

lemma rep_a_odd_not_mem (m : ℕ) : List.replicate (2 * m + 1) a ∉ LPST := by
  rw [mem_LPST, List.replicate_succ, stateOf_cons, stateOf_rep_a_even]
  intro h
  exact absurd h.1 (by decide)

/-- **`L_PST` is not star-free.** -/
theorem LPST_not_starFree : ¬ HasHeightAtMost LPST 0 := by
  intro h
  obtain ⟨N, hN⟩ := aperiodic_of_starFree h
  have hw : ∀ M, wpow [a] M = List.replicate M a := by
    intro M
    induction M with
    | zero => rfl
    | succ M ih => rw [wpow_succ, ih, List.replicate_succ]; rfl
  have key := hN [] [a] (List.replicate N a)
  simp only [hw, List.nil_append, ← List.replicate_add] at key
  rw [show N + N = 2 * N by ring, show N + 1 + N = 2 * N + 1 by ring] at key
  exact rep_a_odd_not_mem N (key.mp (rep_a_even_mem N))

end PST

end GeneralizedStarHeight
