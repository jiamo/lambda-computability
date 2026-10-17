import Start.StarHeightPST
import Start.StarHeightStarFreeAperiodic

/-!
# In every permutation automaton recognizing `L_PST`, first returns are not star-free

* `PST.pst_firstReturn_not_starFree`: let `δ : Q → AB → Q` be a finite automaton whose letters act
  bijectively, and suppose `L_PST = {w | q₀·w ∈ F}`.  Then the first-return code to `q₀` is not
  star-free.

So the route that closes the `Z_p` core (the stabilizer of a state is the star of a star-free
first-return code, `zpX_starFree`) is not available for `L_PST` in any recognizing permutation
automaton, however large.  The witnesses are `bb aᵉᴺ bᵏ ∈ X` and `bb aᵉᴺ⁺¹ bᵏ ∉ X`, where `e` is
the order of `a` on `Q` and `bᵏ` is the shortest return from `q₀·bb` to `q₀`: after `bb` the state
of the minimal automaton is `(0, odd)`, which `a` swaps with `(1, odd)` without ever passing through
`(0, even)`.
-/

namespace GeneralizedStarHeight

namespace PST

open AB

section Automaton

variable {Q : Type} (δ : Q → AB → Q)

/-- The run of an automaton. -/
def runQ (q : Q) (w : List AB) : Q := w.foldl δ q

/-- The first-return code to `q₀`. -/
def firstReturn (q₀ : Q) : Language AB :=
  {w | w ≠ [] ∧ runQ δ q₀ w = q₀ ∧ ∀ i, 0 < i → i < w.length → runQ δ q₀ (w.take i) ≠ q₀}

lemma runQ_append (q : Q) (u v : List AB) : runQ δ q (u ++ v) = runQ δ (runQ δ q u) v :=
  List.foldl_append

lemma runQ_replicate (x : AB) (hx : Function.Bijective (fun q => δ q x)) (q : Q) (k : ℕ) :
    runQ δ q (List.replicate k x) = (Equiv.ofBijective _ hx ^ k) q := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, show runQ δ q (x :: List.replicate k x) =
        runQ δ (δ q x) (List.replicate k x) from rfl, ih, pow_succ, Equiv.Perm.mul_apply]
      rfl

end Automaton

lemma move_injective : ∀ (x : AB) (s t : Fin 3), move s x = move t x → s = t := by decide

lemma stateOf_injective : ∀ (w : List AB) (s t : Fin 3), stateOf s w = stateOf t w → s = t
  | [], _, _, h => h
  | x :: w, s, t, h => move_injective x s t (stateOf_injective w _ _ h)

lemma stateOf_rep_a_ne_two : ∀ (i : ℕ) (s : Fin 3), s ≠ 2 → stateOf s (List.replicate i a) ≠ 2
  | 0, s, hs => hs
  | i + 1, s, hs => by
      rw [List.replicate_succ, stateOf_cons]
      exact stateOf_rep_a_ne_two i _ (by revert s; decide)

lemma b0count_rep_a : ∀ (i : ℕ) (s : Fin 3), b0count s (List.replicate i a) = 0
  | 0, _ => rfl
  | i + 1, s => by
      rw [List.replicate_succ, b0count, b0count_rep_a i]
      rfl

lemma bb_rep_a_not_mem (i : ℕ) : [b, b] ++ List.replicate i a ∉ LPST := by
  rw [mem_LPST, b0count_append, b0count_rep_a]
  intro h
  exact absurd h.2 (by decide)

/-- **First returns are not star-free in any permutation recognizer of `L_PST`.** -/
theorem pst_firstReturn_not_starFree {Q : Type} [Finite Q] (δ : Q → AB → Q)
    (hperm : ∀ x, Function.Bijective (fun q => δ q x)) (q₀ : Q) (F : Set Q)
    (hL : ∀ w, w ∈ LPST ↔ runQ δ q₀ w ∈ F) : ¬ HasHeightAtMost (firstReturn δ q₀) 0 := by
  intro hX
  obtain ⟨N, hN⟩ := aperiodic_of_starFree hX
  -- returning to `q₀` forces membership in `L_PST`
  have hret : ∀ s, runQ δ q₀ s = q₀ → s ∈ LPST := by
    intro s hs
    rw [hL, hs, ← show runQ δ q₀ [] = q₀ from rfl, ← hL, LPST_eq_X]
    exact Language.nil_mem_kstar _
  set πa := Equiv.ofBijective _ (hperm a)
  set πb := Equiv.ofBijective _ (hperm b)
  set e := orderOf πa with he
  have hepos : 0 < e := orderOf_pos πa
  set p := runQ δ q₀ [b, b] with hp
  have hpa : ∀ n, runQ δ p (List.replicate (e * n) a) = p := by
    intro n
    rw [runQ_replicate δ a (hperm a), pow_mul, pow_orderOf_eq_one, one_pow]
    rfl
  have hex : ∃ k, runQ δ p (List.replicate k b) = q₀ := by
    refine ⟨2 * orderOf πb - 2, ?_⟩
    have hb2 : p = (πb ^ 2) q₀ := by
      rw [hp, show [b, b] = List.replicate 2 b from rfl, runQ_replicate δ b (hperm b)]
    have hob : 0 < orderOf πb := orderOf_pos πb
    rw [runQ_replicate δ b (hperm b), hb2, ← Equiv.Perm.mul_apply, ← pow_add,
      Nat.sub_add_cancel (by omega), pow_mul', pow_orderOf_eq_one, one_pow]
    rfl
  classical
  set k := Nat.find hex with hk
  have hkspec : runQ δ p (List.replicate k b) = q₀ := Nat.find_spec hex
  have hkmin : ∀ j < k, runQ δ p (List.replicate j b) ≠ q₀ := fun j hj => Nat.find_min hex hj
  -- the word `bb aᵉᴺ bᵏ` is a first return
  have hmem : [b, b] ++ List.replicate (e * N) a ++ List.replicate k b ∈ firstReturn δ q₀ := by
    refine ⟨by simp, ?_, ?_⟩
    · rw [runQ_append, runQ_append, ← hp, hpa, hkspec]
    · intro i hi0 hil
      by_cases hi : i ≤ 2 + e * N
      · intro hq
        have hpre := hret _ hq
        rcases Nat.lt_or_ge i 2 with h1 | h2
        · have : i = 1 := by omega
          subst this
          have h1 : ([b, b] ++ List.replicate (e * N) a ++ List.replicate k b).take 1 = [b] := by
            simp
          rw [h1, mem_LPST] at hpre
          exact absurd hpre.1 (by decide)
        · have htake : ([b, b] ++ List.replicate (e * N) a ++ List.replicate k b).take i =
              [b, b] ++ List.replicate (i - 2) a := by
            rw [List.append_assoc, List.take_append, List.take_of_length_le (by simp; omega),
              List.take_append, List.take_replicate, List.length_replicate,
              show min (i - [b, b].length) (e * N) = i - 2 by simp; omega]
            simp
            omega
          rw [htake] at hpre
          exact bb_rep_a_not_mem _ hpre
      · have htake : ([b, b] ++ List.replicate (e * N) a ++ List.replicate k b).take i =
            [b, b] ++ List.replicate (e * N) a ++ List.replicate (i - 2 - e * N) b := by
          rw [List.take_append, List.take_of_length_le (by simp; omega), List.take_replicate,
            List.length_append, List.length_replicate]
          simp only [List.length_cons, List.length_nil]
          congr 2
          simp at hil
          omega
        rw [htake, runQ_append, runQ_append, ← hp, hpa]
        exact hkmin _ (by simp at hil; omega)
  -- and `bb aᵉᴺ⁺¹ bᵏ` is not
  have hnot : [b, b] ++ List.replicate (e * N + 1) a ++ List.replicate k b ∉ firstReturn δ q₀ := by
    rintro ⟨-, hq, -⟩
    have h2 := (mem_LPST _).mp (hret _ hq)
    have h1 := (mem_LPST _).mp (hret _ (by rw [runQ_append, runQ_append, ← hp, hpa, hkspec]) :
      [b, b] ++ List.replicate (e * N) a ++ List.replicate k b ∈ LPST)
    rw [List.replicate_succ', ← List.append_assoc] at h2
    simp only [stateOf_append] at h1 h2
    have hfix := stateOf_injective _ _ _ (h2.1.trans h1.1.symm)
    have hne := stateOf_rep_a_ne_two (e * N) (stateOf 0 [b, b]) (by decide)
    revert hfix hne
    generalize stateOf (stateOf 0 [b, b]) (List.replicate (e * N) a) = s
    revert s
    decide
  -- contradiction with aperiodicity
  obtain ⟨d, hd⟩ : ∃ d, e * N = d + N := ⟨e * N - N, by have := Nat.le_mul_of_pos_left N hepos; omega⟩
  have key := hN ([b, b] ++ List.replicate d a) [a] (List.replicate k b)
  have hw : ∀ M, wpow [a] M = List.replicate M a := by
    intro M
    induction M with
    | zero => rfl
    | succ M ih => rw [wpow_succ, ih, List.replicate_succ]; rfl
  rw [hw, hw] at key
  rw [hd] at hmem hnot
  simp only [List.append_assoc, List.replicate_add] at key hmem hnot
  exact hnot (key.mp hmem)

end PST

end GeneralizedStarHeight
