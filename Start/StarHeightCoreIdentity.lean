import Start.StarHeightCoreCode

/-!
# The counting identity for `coreCount`

* `comp w`: the first letter and the last three letters of `w` (all of `w` if `|w| ≤ 4`).
* `cls`: the twelve block classes `F₁, …, F₁₂` (and `0` for the other blocks), read off `comp`;
  `dval` their coefficients.  `Fcls i` is the class `F_{i+1}`.
* `acCount u`: the occurrences of the factor `02` read from state `1`; `acCount0` the same from
  state `0`.
* `core_identity`: for `u` in state `0`,
  `3·coreCount u + acCount u = |u|₀ + Σᵢ dᵢ·Nᵢ(u)`, where `Nᵢ(u)` is the number of blocks of `u`
  in `Fᵢ`.
* `acCount0_eq`: `acCount0 u = N₁(u)` for every `u`.

Both are proved by one invariant of a finite automaton (the state of the walk and `comp` of the
current incomplete block), checked on its reachable states.
-/

namespace GeneralizedStarHeight

open EpisodeAlgebra
open scoped Computability

/-! ### First letter and last three letters -/

/-- The first letter and the last three letters. -/
def comp (w : W3) : W3 := if w.length ≤ 4 then w else w.take 1 ++ w.drop (w.length - 3)

lemma comp_short {w : W3} (h : w.length ≤ 4) : comp w = w := by simp [comp, h]

lemma comp_long (x : Fin 3) {m y : W3} (hm : m ≠ []) (hy : y.length = 3) :
    comp (x :: (m ++ y)) = x :: y := by
  have hm' : 1 ≤ m.length := List.length_pos_iff.mpr hm
  unfold comp
  rw [if_neg (by simp; omega)]
  simp only [List.length_cons, List.length_append, hy, List.take_succ_cons, List.take_zero,
    List.singleton_append, List.cons.injEq, true_and]
  rw [show m.length + 3 + 1 - 3 = m.length + 1 by omega, List.drop_succ_cons,
    List.drop_left]

lemma exists_long {w : W3} (h : 5 ≤ w.length) :
    ∃ x m y, m ≠ [] ∧ y.length = 3 ∧ w = x :: (m ++ y) := by
  obtain ⟨x, r, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (l := w) (by omega))
  simp only [List.length_cons] at h
  refine ⟨x, r.take (r.length - 3), r.drop (r.length - 3), ?_, by simp; omega, by simp⟩
  intro hn
  have := congrArg List.length hn
  simp at this; omega

lemma comp_snoc (w : W3) (a : Fin 3) : comp (w ++ [a]) = comp (comp w ++ [a]) := by
  by_cases h : w.length ≤ 4
  · rw [comp_short h]
  · obtain ⟨x, m, y, hm, hy, rfl⟩ := exists_long (by omega : 5 ≤ w.length)
    rw [comp_long x hm hy]
    match y, hy with
    | [y₁, y₂, y₃], _ =>
      have e1 : x :: [y₁, y₂, y₃] ++ [a] = x :: ([y₁] ++ [y₂, y₃, a]) := rfl
      have e2 : x :: (m ++ [y₁, y₂, y₃]) ++ [a] = x :: ((m ++ [y₁]) ++ [y₂, y₃, a]) := by simp
      rw [e1, e2, comp_long x (by simp) rfl, comp_long x (by simp) rfl]

lemma comp_getLast (w : W3) : (comp w).getLast? = w.getLast? := by
  by_cases h : w.length ≤ 4
  · rw [comp_short h]
  · obtain ⟨x, m, y, hm, hy, rfl⟩ := exists_long (by omega : 5 ≤ w.length)
    have hy' : y ≠ [] := List.ne_nil_of_length_pos (by omega)
    rw [comp_long x hm hy, List.getLast?_cons, List.getLast?_cons,
      List.getLast?_append_of_ne_nil _ hy']

lemma comp_nil : comp [] = [] := rfl

/-! ### The classes -/

/-- The twelve block classes. -/
def cls (c : W3) : Fin 13 :=
  if c = [0, 2] then 1
  else if c.head? = some 0 ∧ c.length = 4 ∧ c.getLast? = some 2 then 2
  else if c.head? = some 0 ∧ c.drop (c.length - 2) = [0, 1] then 3
  else if c.head? = some 0 ∧ c.drop (c.length - 2) = [1, 0] then 4
  else if c.head? = some 0 ∧ c.drop (c.length - 2) = [1, 1] then 5
  else if c.head? = some 1 ∧ c.drop (c.length - 2) = [0, 0] then 6
  else if c.head? = some 1 ∧ c.drop (c.length - 2) = [0, 1] then 7
  else if c.head? = some 1 ∧ c.drop (c.length - 2) = [1, 0] then 8
  else if c = [2, 0] then 9
  else if c.head? = some 2 ∧ c.length = 4 ∧ c.drop 1 = [2, 1, 0] then 10
  else if c.head? = some 2 ∧ c.length = 4 ∧ c.drop 1 = [2, 0, 0] then 11
  else if c.head? = some 2 ∧ c.length = 4 ∧ c.drop 1 = [2, 0, 1] then 12
  else 0

/-- The coefficients `d₁, …, d₁₂` (and `0`). -/
def dval : Fin 13 → ℤ := ![0, 2, 2, 1, 1, 2, -2, -1, -1, -1, -1, -2, -1]

/-- The class `F_{i+1}`. -/
def Fcls (i : Fin 12) : Language (Fin 3) := coreX ⊓ {e | cls (comp e) = i.succ}

/-- The blocks outside `F_{i+1}`. -/
def Fco (i : Fin 12) : Language (Fin 3) := coreX ⊓ {e | cls (comp e) ≠ i.succ}

/-- The number of blocks of `u` in `F_{i+1}`. -/
noncomputable def Ncnt (i : Fin 12) (u : W3) : ℕ := bcount (Fcls i) (split u).1

/-! ### Occurrences of `02` -/

/-- Occurrences of `02` whose `2` is read in state `h`; `s` is the current state, `p` the
previous letter. -/
def acQ (h : ZMod 3) : ZMod 3 → Option (Fin 3) → W3 → ℕ
  | _, _, [] => 0
  | s, p, b :: w => (if p = some 0 ∧ b = 2 ∧ s = h then 1 else 0) + acQ h (s + step3 b) (some b) w

/-- **The factor `02` read from state `1`.** -/
def acCount (u : W3) : ℕ := acQ 2 0 none u

/-- The factor `02` read from state `0`. -/
def acCount0 (u : W3) : ℕ := acQ 1 0 none u

lemma acQ_snoc (h : ZMod 3) (a : Fin 3) :
    ∀ (u : W3) (s : ZMod 3) (p : Option (Fin 3)), acQ h s p (u ++ [a]) =
      acQ h s p u + if (u.getLast?.or p) = some 0 ∧ a = 2 ∧ s + dsum step3 u = h then 1 else 0
  | [], s, p => by simp [acQ, dsum]
  | b :: u, s, p => by
      have e : (b :: u).getLast?.or p = u.getLast?.or (some b) := by
        rw [List.getLast?_cons]
        cases u.getLast? <;> rfl
      rw [List.cons_append, acQ, acQ, acQ_snoc h a u, dsum_cons, e]
      simp only [add_assoc]

lemma acQ_shift (h c : ZMod 3) :
    ∀ (w : W3) (s : ZMod 3) (p : Option (Fin 3)), acQ h s p w = acQ (h + c) (s + c) p w
  | [], _, _ => rfl
  | b :: w, s, p => by
      rw [acQ, acQ, acQ_shift h c w, show s + step3 b + c = s + c + step3 b by ring]
      congr 2
      simp only [add_left_inj]

lemma acQ_prev (h s : ZMod 3) {p p' : Option (Fin 3)} (hp : p ≠ some 0) (hp' : p' ≠ some 0) :
    ∀ w : W3, acQ h s p w = acQ h s p' w
  | [] => rfl
  | b :: w => by simp [acQ, hp, hp']

lemma acCount_eq_cons (u : W3) : acCount u = acCount0 (2 :: u) := by
  unfold acCount acCount0
  rw [acQ, acQ_shift 2 2 u 0 none]
  simp only [reduceCtorEq, false_and, if_false, zero_add]
  exact acQ_prev _ _ (by simp) (by simp) u

/-! ### The invariant -/

/-- The potential `3·coreCount − |u|₀ + acCount − Σ dᵢ Nᵢ`. -/
noncomputable def Phi (u : W3) : ℤ :=
  3 * (coreCount u : ℤ) - (u.count 0 : ℤ) + (acCount u : ℤ) -
    ∑ i : Fin 12, dval i.succ * (Ncnt i u : ℤ)

/-- `acCount0 − N₁`. -/
noncomputable def Psi (u : W3) : ℤ := (acCount0 u : ℤ) - (Ncnt 0 u : ℤ)

/-- The scanning automaton with the two potentials. -/
def idStep (q : ZMod 3 × W3 × ℤ × ℤ) (a : Fin 3) : ZMod 3 × W3 × ℤ × ℤ :=
  (q.1 + step3 a, if q.1 + step3 a = 0 then [] else comp (q.2.1 ++ [a]),
    q.2.2.1 + (if a = 0 ∧ q.1 = 0 then 3 else 0) - (if a = 0 then 1 else 0) +
      (if a = 2 ∧ q.2.1.getLast? = some 0 ∧ q.1 = 2 then 1 else 0) -
      (if q.1 + step3 a = 0 then dval (cls (comp (q.2.1 ++ [a]))) else 0),
    q.2.2.2 + (if a = 2 ∧ q.2.1.getLast? = some 0 ∧ q.1 = 1 then 1 else 0) -
      (if q.1 + step3 a = 0 ∧ cls (comp (q.2.1 ++ [a])) = 1 then 1 else 0))

/-- The state of the scanning automaton after `u`. -/
noncomputable def idState (u : W3) : ZMod 3 × W3 × ℤ × ℤ :=
  (dsum step3 (split u).2, comp (split u).2, Phi u, Psi u)

lemma mem_coreX_snoc {t : W3} (ht : t ∈ NoRet) {a : Fin 3} (h0 : dsum step3 (t ++ [a]) = 0) :
    t ++ [a] ∈ coreX := by
  refine ⟨by simp, h0, fun p hp hne hpe => ?_⟩
  rcases List.prefix_concat_iff.mp hp with h | h
  · exact absurd h hpe
  · exact ht p h hne

lemma coreCount_snoc (u : W3) (a : Fin 3) :
    coreCount (u ++ [a]) = coreCount u + if a = 0 ∧ dsum step3 u = 0 then 1 else 0 := by
  unfold coreCount
  rw [zcount_append]
  simp [zcount]

open Classical in
lemma bcount_snoc (L : Language (Fin 3)) (es : List W3) (e : W3) :
    bcount L (es ++ [e]) = bcount L es + if e ∈ L then 1 else 0 := by
  classical
  unfold bcount
  rw [List.countP_append]
  simp [List.countP_cons]

lemma Ncnt_snoc (i : Fin 12) (u : W3) (a : Fin 3) :
    Ncnt i (u ++ [a]) = Ncnt i u + if dsum step3 ((split u).2 ++ [a]) = 0 ∧
      cls (comp ((split u).2 ++ [a])) = i.succ then 1 else 0 := by
  unfold Ncnt
  rw [split_snoc]
  unfold splitStep
  split_ifs with h1 h2 h3
  · rw [bcount_snoc, if_pos (show _ ∈ Fcls i from ⟨mem_coreX_snoc (split_spec u).2.2 h1, h2.2⟩)]
  · rw [bcount_snoc, if_neg]
    rintro ⟨-, h⟩
    exact h2 ⟨h1, h⟩
  · exact absurd h3.1 h1
  · rfl

lemma getLast_of_dsum_ne_zero {u : W3} (h : dsum step3 u ≠ 0) :
    u.getLast? = (split u).2.getLast? := by
  have ht : (split u).2 ≠ [] := by
    intro h'
    rw [dsum_split, h'] at h
    exact h (by simp [dsum])
  conv_lhs => rw [← (split_spec u).1]
  exact List.getLast?_append_of_ne_nil _ ht

lemma acQ_snoc_core (h : ZMod 3) (hh : h ≠ 0) (u : W3) (a : Fin 3) :
    acQ h 0 none (u ++ [a]) = acQ h 0 none u + if a = 2 ∧
      (comp (split u).2).getLast? = some 0 ∧ dsum step3 (split u).2 = h then 1 else 0 := by
  rw [acQ_snoc, zero_add, ← dsum_split]
  congr 1
  by_cases hu : dsum step3 u = h
  · have hne : dsum step3 u ≠ 0 := by rw [hu]; exact hh
    rw [comp_getLast, ← getLast_of_dsum_ne_zero hne]
    simp only [Option.or_none]
    apply if_congr _ rfl rfl
    tauto
  · rw [if_neg (by tauto), if_neg (by tauto)]

lemma dval_sum (x : Fin 13) :
    ∑ i : Fin 12, dval i.succ * ((if x = i.succ then 1 else 0 : ℕ) : ℤ) = dval x := by
  fin_cases x <;> simp [Fin.sum_univ_succ, dval]

lemma idState_snoc (u : W3) (a : Fin 3) : idState (u ++ [a]) = idStep (idState u) a := by
  have hs : dsum step3 ((split u).2 ++ [a]) = dsum step3 (split u).2 + step3 a := by
    rw [dsum_append]; simp [dsum]
  unfold idState idStep
  simp only
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only
    rw [split_snoc]
    unfold splitStep
    split_ifs with h
    · rw [← hs, h]; simp [dsum]
    · exact hs
  · simp only
    rw [split_snoc]
    unfold splitStep
    by_cases h : dsum step3 ((split u).2 ++ [a]) = 0
    · simp only [if_pos h]
      rw [if_pos (by rw [← hs]; exact h)]
      rfl
    · simp only [if_neg h]
      rw [if_neg (by rw [← hs]; exact h)]
      exact comp_snoc _ _
  · simp only [Phi]
    rw [coreCount_snoc, List.count_append, acCount, acQ_snoc_core 2 (by decide), ← acCount]
    simp only [Ncnt_snoc, Nat.cast_add, mul_add, Finset.sum_add_distrib]
    have hsum : ∑ i : Fin 12, dval i.succ * ((if dsum step3 ((split u).2 ++ [a]) = 0 ∧
        cls (comp ((split u).2 ++ [a])) = i.succ then 1 else 0 : ℕ) : ℤ) =
        if dsum step3 ((split u).2 ++ [a]) = 0 then
          dval (cls (comp ((split u).2 ++ [a]))) else 0 := by
      split_ifs with h0
      · simp only [h0, true_and]
        exact dval_sum _
      · simp [h0]
    have hz : ((List.count 0 [a] : ℕ) : ℤ) = if a = 0 then 1 else 0 := by
      fin_cases a <;> rfl
    rw [← hs, dsum_split u, ← comp_snoc, hsum, hz]
    split_ifs <;> push_cast <;> ring
  · simp only [Psi]
    rw [acCount0, acQ_snoc_core 1 (by decide), ← acCount0, Ncnt_snoc, ← comp_snoc, hs,
      Fin.succ_zero_eq_one]
    split_ifs <;> push_cast <;> ring

lemma idState_eq_foldl (u : W3) : idState u = u.foldl idStep (0, [], 0, 0) := by
  induction u using List.reverseRecOn with
  | nil =>
      simp only [idState, Phi, Psi, Ncnt, split, List.foldl_nil]
      simp [dsum, comp, coreCount, zcount, acCount, acCount0, acQ, bcount]
  | append_singleton u a ih => rw [idState_snoc, ih, List.foldl_append]; rfl

/-- The predicate checked on the reachable states. -/
def idGood (q : ZMod 3 × W3 × ℤ × ℤ) : Bool :=
  (if q.1 = 0 ∧ q.2.1 = [] then q.2.2.1 = 0 else true) && q.2.2.2 = 0

lemma id_check : checkInv [0, 1, 2] idStep (0, [], 0, 0) idGood
    (explore [0, 1, 2] idStep 40 [(0, [], 0, 0)] [(0, [], 0, 0)]) = true := by
  decide +kernel

lemma idGood_all (u : W3) : idGood (idState u) = true := by
  rw [idState_eq_foldl]
  exact checkInv_spec letters3 id_check u

/-- **The identity.** For `u` in state `0`:
`3·coreCount u + acCount u = |u|₀ + Σᵢ dᵢ·Nᵢ(u)`. -/
theorem core_identity {u : W3} (h : dsum step3 u = 0) :
    3 * (coreCount u : ℤ) + (acCount u : ℤ) =
      (u.count 0 : ℤ) + ∑ i : Fin 12, dval i.succ * (Ncnt i u : ℤ) := by
  have hg := idGood_all u
  have ht := (split_of_dsum_zero h).1
  have : Phi u = 0 := by
    simp only [idGood, idState, ht, comp_nil] at hg
    simp [dsum] at hg
    exact hg.1
  unfold Phi at this
  linarith

/-- **`02` from state `0` counts the blocks in `F₁`.** -/
theorem acCount0_eq (u : W3) : acCount0 u = Ncnt 0 u := by
  have hg := idGood_all u
  have : Psi u = 0 := by
    simp only [idGood, idState, Bool.and_eq_true] at hg
    exact of_decide_eq_true hg.2
  unfold Psi at this
  omega

end GeneralizedStarHeight
