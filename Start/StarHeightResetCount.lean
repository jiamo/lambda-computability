import Start.StarHeightCommutative

/-!
# Counting in reset automata, at generalized star height one

A *reset automaton* on a finite alphabet: the letters satisfying `K` keep the state, every other
letter `b` resets it to `ρ b`.  `rcount K ρ qs a q u` counts the positions of `u` that read the
letter `a` (a keeping letter) while the automaton, started in `q`, is in the state `qs`.

* `HasHeightAtMost.allIn`: words over a subalphabet are star-free.
* `stateIs_height`: the words driving `q` to `q'` are star-free (`rstate_eq_iff`).
* `rcountMod_height`: for `m > 0`, `{u | rcount K ρ qs a q u % m = r}` has height at most one.
  This is `countMod_height` of `Start/StarHeightCommutative.lean` with "the letter `a`" replaced
  by "a position reading `a` in state `qs`".
-/

namespace GeneralizedStarHeight

universe u

open scoped Computability

variable {α : Type u}

/-- Words all of whose letters satisfy `K`. -/
def allIn (K : α → Prop) : Language α := {w | ∀ b ∈ w, K b}

/-- One-letter words with a letter satisfying `X`. -/
def letters (X : α → Prop) : Language α := {w | ∃ b, X b ∧ w = [b]}

namespace HasHeightAtMost

lemma letters_height [Finite α] (X : α → Prop) (n : ℕ) : HasHeightAtMost (letters X) n := by
  apply HasHeightAtMost.finite
  show Set.Finite {w : List α | ∃ b, X b ∧ w = [b]}
  refine (Set.finite_range (fun b : α => [b])).subset ?_
  rintro w ⟨b, _, rfl⟩
  exact ⟨b, rfl⟩

lemma allIn_eq (K : α → Prop) :
    allIn K = ((⊤ : Language α) * letters (fun b => ¬ K b) * ⊤)ᶜ := by
  ext w
  constructor
  · intro hw hm
    obtain ⟨xy, hxy, z, _, rfl⟩ := Language.mem_mul.mp hm
    obtain ⟨x, _, y, ⟨b, hb, rfl⟩, rfl⟩ := Language.mem_mul.mp hxy
    exact hb (hw b (by simp))
  · intro hw b hb
    by_contra hK
    obtain ⟨x, z, rfl⟩ := List.append_of_mem hb
    apply hw
    refine Language.mem_mul.mpr ⟨x ++ [b], Language.mem_mul.mpr
      ⟨x, trivial, [b], ⟨b, hK, rfl⟩, rfl⟩, z, trivial, by simp⟩

lemma allIn_height [Finite α] (K : α → Prop) (n : ℕ) : HasHeightAtMost (allIn K) n := by
  rw [allIn_eq]
  exact (((top n).concat (letters_height _ n)).concat (top n)).compl

end HasHeightAtMost

section Reset

variable (K : α → Prop) [DecidablePred K] {Q : Type} (ρ : α → Q)

/-- One step of the reset automaton. -/
def rstep (q : Q) (b : α) : Q := if K b then q else ρ b

/-- The state reached from `q` after reading a word. -/
def rstate (q : Q) : List α → Q
  | [] => q
  | b :: u => rstate (rstep K ρ q b) u

/-- Number of positions reading `a` in the state `qs`. -/
def rcount [DecidableEq α] [DecidableEq Q] (qs : Q) (a : α) (q : Q) : List α → ℕ
  | [] => 0
  | b :: u => (if b = a ∧ q = qs then 1 else 0) + rcount qs a (rstep K ρ q b) u

variable {K ρ}

theorem rstate_append (q : Q) (u v : List α) :
    rstate K ρ q (u ++ v) = rstate K ρ (rstate K ρ q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons b u ih => exact ih _

theorem rstate_snoc (q : Q) (v : List α) (b : α) :
    rstate K ρ q (v ++ [b]) = if K b then rstate K ρ q v else ρ b := by
  rw [rstate_append]
  rfl

/-- The state after `v` is `q'` iff either `v` has no resetting letter and `q = q'`, or the last
resetting letter of `v` resets to `q'`. -/
theorem rstate_eq_iff (q q' : Q) (v : List α) :
    rstate K ρ q v = q' ↔ (q = q' ∧ ∀ b ∈ v, K b) ∨
      ∃ x y z, v = x ++ y :: z ∧ ¬ K y ∧ ρ y = q' ∧ ∀ b ∈ z, K b := by
  induction v using List.reverseRecOn with
  | nil => simp [rstate]
  | append_singleton v b ih =>
      rw [rstate_snoc]
      by_cases hb : K b
      · rw [ite_eq_left hb, ih]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨x, y, z, rfl, hy, hρ, hz⟩)
          · left
            refine ⟨h1, fun c hc => ?_⟩
            rcases List.mem_append.1 hc with hc | hc
            · exact h2 c hc
            · rw [List.mem_singleton.1 hc]; exact hb
          · right
            refine ⟨x, y, z ++ [b], by simp, hy, hρ, fun c hc => ?_⟩
            rcases List.mem_append.1 hc with hc | hc
            · exact hz c hc
            · rw [List.mem_singleton.1 hc]; exact hb
        · rintro (⟨h1, h2⟩ | ⟨x, y, z, heq, hy, hρ, hz⟩)
          · exact .inl ⟨h1, fun c hc => h2 c (by simp [hc])⟩
          · right
            rcases List.eq_nil_or_concat' z with rfl | ⟨z', c, rfl⟩
            · have h := List.append_inj' (show v ++ [b] = x ++ [y] from heq) rfl
              simp only [List.cons.injEq, and_true] at h
              exact absurd (h.2 ▸ hb) hy
            · have h := List.append_inj'
                (show v ++ [b] = (x ++ y :: z') ++ [c] by rw [heq]; simp) rfl
              simp only [List.cons.injEq, and_true] at h
              exact ⟨x, y, z', h.1, hy, hρ, fun d hd => hz d (by simp [hd])⟩
      · rw [ite_eq_right hb]
        constructor
        · intro h
          exact .inr ⟨v, b, [], rfl, hb, h, by simp⟩
        · rintro (⟨_, h2⟩ | ⟨x, y, z, heq, hy, hρ, hz⟩)
          · exact absurd (h2 b (by simp)) hb
          · rcases List.eq_nil_or_concat' z with rfl | ⟨z', c, rfl⟩
            · have h := List.append_inj' (show v ++ [b] = x ++ [y] from heq) rfl
              simp only [List.cons.injEq, and_true] at h
              rw [h.2]; exact hρ
            · have h := List.append_inj'
                (show v ++ [b] = (x ++ y :: z') ++ [c] by rw [heq]; simp) rfl
              simp only [List.cons.injEq, and_true] at h
              exact absurd (h.2 ▸ hz c (by simp)) hb

variable [DecidableEq α] [DecidableEq Q]

theorem rcount_append (qs : Q) (a : α) (q : Q) (u v : List α) :
    rcount K ρ qs a q (u ++ v) = rcount K ρ qs a q u + rcount K ρ qs a (rstate K ρ q u) v := by
  induction u generalizing q with
  | nil => simp [rcount, rstate]
  | cons b u ih =>
      simp only [List.cons_append, rcount, ih, rstate]
      omega

/-- The words driving `q` to `q'`. -/
def stateIs (K : α → Prop) [DecidablePred K] (ρ : α → Q) (q q' : Q) : Language α :=
  {v | rstate K ρ q v = q'}

omit [DecidableEq α] in
theorem stateIs_eq (q q' : Q) :
    stateIs K ρ q q' = (if q = q' then allIn K else 0) +
      (⊤ : Language α) * letters (fun y => ¬ K y ∧ ρ y = q') * allIn K := by
  ext v
  change rstate K ρ q v = q' ↔ _
  rw [rstate_eq_iff, Language.mem_add]
  apply or_congr
  · by_cases h : q = q'
    · simp only [h, ite_true, true_and]; rfl
    · simp only [h, ite_false, false_and]
      exact iff_of_false id (Language.notMem_zero v)
  · constructor
    · rintro ⟨x, y, z, rfl, hy, hρ, hz⟩
      exact Language.mem_mul.mpr ⟨x ++ [y], Language.mem_mul.mpr
        ⟨x, trivial, [y], ⟨y, ⟨hy, hρ⟩, rfl⟩, rfl⟩, z, hz, by simp⟩
    · intro hm
      obtain ⟨xy, hxy, z, hz, rfl⟩ := Language.mem_mul.mp hm
      obtain ⟨x, _, w, ⟨y, ⟨hy, hρ⟩, rfl⟩, rfl⟩ := Language.mem_mul.mp hxy
      exact ⟨x, y, z, by simp, hy, hρ, hz⟩

omit [DecidableEq α] in
theorem stateIs_height [Finite α] (q q' : Q) (n : ℕ) :
    HasHeightAtMost (stateIs K ρ q q') n := by
  rw [stateIs_eq]
  refine HasHeightAtMost.union ?_ (((HasHeightAtMost.top n).concat
    (HasHeightAtMost.letters_height _ n)).concat (HasHeightAtMost.allIn_height K n))
  split_ifs
  · exact HasHeightAtMost.allIn_height K n
  · exact HasHeightAtMost.zero n

variable (qs : Q) (a : α)

/-- Words whose number of counted positions is `r` modulo `m`. -/
def rmod (K : α → Prop) [DecidablePred K] (ρ : α → Q) (qs : Q) (a : α) (q : Q) (m r : ℕ) :
    Language α := {u | rcount K ρ qs a q u % m = r}

/-- Words with no counted position. -/
def rzero (K : α → Prop) [DecidablePred K] (ρ : α → Q) (qs : Q) (a : α) (q : Q) :
    Language α := {u | rcount K ρ qs a q u = 0}

/-- Words ending at their first counted position. -/
def rfirst (K : α → Prop) [DecidablePred K] (ρ : α → Q) (qs : Q) (a : α) (q : Q) :
    Language α := (rzero K ρ qs a q ⊓ stateIs K ρ q qs) * {[a]}

theorem rcount_ne_zero_iff (q : Q) (u : List α) :
    rcount K ρ qs a q u ≠ 0 ↔ ∃ x y, u = x ++ a :: y ∧ rstate K ρ q x = qs := by
  constructor
  · intro h
    induction u generalizing q with
    | nil => exact absurd rfl h
    | cons b u ih =>
        by_cases hb : b = a ∧ q = qs
        · obtain ⟨rfl, rfl⟩ := hb
          exact ⟨[], u, rfl, rfl⟩
        · have h' : rcount K ρ qs a (rstep K ρ q b) u ≠ 0 := by
            simpa [rcount, hb] using h
          obtain ⟨x, y, rfl, hx⟩ := ih _ h'
          exact ⟨b :: x, y, rfl, hx⟩
  · rintro ⟨x, y, rfl, hx⟩
    rw [rcount_append, hx]
    simp [rcount]

theorem rzero_eq (q : Q) :
    rzero K ρ qs a q = (stateIs K ρ q qs * {[a]} * ⊤)ᶜ := by
  ext u
  change rcount K ρ qs a q u = 0 ↔ u ∉ (stateIs K ρ q qs * {[a]} * ⊤)
  rw [← not_iff_not, ← Ne, rcount_ne_zero_iff, not_not]
  constructor
  · rintro ⟨x, y, rfl, hx⟩
    exact Language.mem_mul.mpr ⟨x ++ [a], Language.mem_mul.mpr ⟨x, hx, [a], rfl, rfl⟩,
      y, trivial, by simp⟩
  · intro hm
    obtain ⟨xa, hxa, y, _, rfl⟩ := Language.mem_mul.mp hm
    obtain ⟨x, hx, w, hw, rfl⟩ := Language.mem_mul.mp hxa
    rw [Set.mem_singleton_iff.1 hw]
    exact ⟨x, y, by simp, hx⟩

theorem rzero_height [Finite α] (q : Q) (n : ℕ) : HasHeightAtMost (rzero K ρ qs a q) n := by
  rw [rzero_eq]
  exact (((stateIs_height q qs n).concat (HasHeightAtMost.letter a n)).concat
    (HasHeightAtMost.top n)).compl

theorem rfirst_height [Finite α] (q : Q) (n : ℕ) : HasHeightAtMost (rfirst K ρ qs a q) n :=
  ((rzero_height qs a q n).inter (stateIs_height q qs n)).concat (HasHeightAtMost.letter a n)

variable {qs a}

theorem rcount_rfirst {q : Q} {y : List α} (hy : y ∈ rfirst K ρ qs a q) :
    rcount K ρ qs a q y = 1 ∧ rstate K ρ q y = rstep K ρ qs a := by
  obtain ⟨v, ⟨hv0, hvs⟩, w, hw, rfl⟩ := Language.mem_mul.mp hy
  rw [Set.mem_singleton_iff.1 hw]
  change rcount K ρ qs a q v = 0 at hv0
  change rstate K ρ q v = qs at hvs
  refine ⟨?_, ?_⟩
  · rw [rcount_append, hv0, hvs]; simp [rcount]
  · rw [rstate_append, hvs]; rfl

theorem rcount_split (k : ℕ) :
    ∀ (q : Q) (u : List α), rcount K ρ qs a q u = k + 1 →
      ∃ y u', u = y ++ u' ∧ y ∈ rfirst K ρ qs a q ∧
        rcount K ρ qs a (rstep K ρ qs a) u' = k := by
  intro q u h
  induction u generalizing q with
  | nil => simp [rcount] at h
  | cons b u ih =>
      by_cases hb : b = a ∧ q = qs
      · obtain ⟨rfl, rfl⟩ := hb
        refine ⟨[b], u, rfl, Language.mem_mul.mpr ⟨[], ⟨rfl, rfl⟩, [b], rfl, rfl⟩, ?_⟩
        simpa [rcount, Nat.add_comm] using h
      · have h' : rcount K ρ qs a (rstep K ρ q b) u = k + 1 := by
          simpa [rcount, hb] using h
        obtain ⟨y, u', rfl, hy, hu'⟩ := ih _ h'
        obtain ⟨v, ⟨hv0, hvs⟩, w, hw, rfl⟩ := Language.mem_mul.mp hy
        refine ⟨b :: (v ++ w), u', by simp, Language.mem_mul.mpr ⟨b :: v, ⟨?_, ?_⟩, w, hw, rfl⟩,
          hu'⟩
        · change rcount K ρ qs a q (b :: v) = 0
          change rcount K ρ qs a (rstep K ρ q b) v = 0 at hv0
          simp [rcount, hb, hv0]
        · exact hvs

/-- Words with exactly `k` counted positions, from the state reached after a counted
position. -/
theorem rcount_eq_pow (k : ℕ) :
    ({u | rcount K ρ qs a (rstep K ρ qs a) u = k} : Language α) =
      rfirst K ρ qs a (rstep K ρ qs a) ^ k * rzero K ρ qs a (rstep K ρ qs a) := by
  induction k with
  | zero => simp only [pow_zero, one_mul]; rfl
  | succ k ih =>
      rw [pow_succ', mul_assoc, ← ih]
      ext u
      constructor
      · intro hu
        obtain ⟨y, u', rfl, hy, hu'⟩ := rcount_split k _ u hu
        exact Language.mem_mul.mpr ⟨y, hy, u', hu', rfl⟩
      · intro hu
        obtain ⟨y, hy, u', hu', rfl⟩ := Language.mem_mul.mp hu
        obtain ⟨h1, h2⟩ := rcount_rfirst hy
        change rcount K ρ qs a (rstep K ρ qs a) u' = k at hu'
        change rcount K ρ qs a (rstep K ρ qs a) (y ++ u') = k + 1
        rw [rcount_append, h1, h2, hu', Nat.add_comm]

theorem rcountMod_next_eq {m : ℕ} {r : ℕ} (hr : r < m) :
    rmod K ρ qs a (rstep K ρ qs a) m r =
      (rfirst K ρ qs a (rstep K ρ qs a) ^ m)∗ *
        (rfirst K ρ qs a (rstep K ρ qs a) ^ r * rzero K ρ qs a (rstep K ρ qs a)) := by
  ext u
  constructor
  · intro hu
    change rcount K ρ qs a _ u % m = r at hu
    have hk : rcount K ρ qs a (rstep K ρ qs a) u =
        m * (rcount K ρ qs a (rstep K ρ qs a) u / m) + r := by
      rw [← hu]; exact (Nat.div_add_mod _ _).symm
    have hmem : u ∈ ({u' | rcount K ρ qs a (rstep K ρ qs a) u' =
        m * (rcount K ρ qs a (rstep K ρ qs a) u / m) + r} : Language α) := hk
    rw [rcount_eq_pow, pow_add, pow_mul, mul_assoc] at hmem
    obtain ⟨x, hx, y, hy, rfl⟩ := Language.mem_mul.mp hmem
    refine Language.mem_mul.mpr ⟨x, ?_, y, hy, rfl⟩
    rw [Language.kstar_eq_iSup_pow]
    exact Language.mem_iSup.mpr ⟨_, hx⟩
  · intro hu
    obtain ⟨x, hx, y, hy, rfl⟩ := Language.mem_mul.mp hu
    rw [Language.kstar_eq_iSup_pow] at hx
    obtain ⟨j, hj⟩ := Language.mem_iSup.mp hx
    have hmem : x ++ y ∈ (rfirst K ρ qs a (rstep K ρ qs a) ^ m) ^ j *
        (rfirst K ρ qs a (rstep K ρ qs a) ^ r * rzero K ρ qs a (rstep K ρ qs a)) :=
      Language.mem_mul.mpr ⟨x, hj, y, hy, rfl⟩
    rw [← mul_assoc, ← pow_mul, ← pow_add, ← rcount_eq_pow] at hmem
    change rcount K ρ qs a _ (x ++ y) = m * j + r at hmem
    change rcount K ρ qs a _ (x ++ y) % m = r
    rw [hmem, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

omit [DecidableEq α] in
lemma pow_height {L : Language α} {n : ℕ} (h : HasHeightAtMost L n) (k : ℕ) :
    HasHeightAtMost (L ^ k) n := by
  induction k with
  | zero => rw [pow_zero]; exact HasHeightAtMost.one n
  | succ k ih => rw [pow_succ]; exact ih.concat h

theorem rcountMod_next_height [Finite α] {m : ℕ} {r : ℕ} (hr : r < m) :
    HasHeightAtMost (rmod K ρ qs a (rstep K ρ qs a) m r) 1 := by
  rw [rcountMod_next_eq hr]
  have h0 := rfirst_height (K := K) (ρ := ρ) qs a (rstep K ρ qs a) 0
  have hstar := (pow_height h0 m).star
  exact hstar.concat ((pow_height (h0.mono (Nat.zero_le 1)) r).concat
    (rzero_height qs a _ 1))

omit [DecidableEq α] in
lemma mod_pred (k : ℕ) {m : ℕ} (hm : 0 < m) : k % m = ((k + 1) % m + m - 1) % m := by
  have h1 : k + m = (k + 1) + (m - 1) := by omega
  calc k % m = (k + m) % m := (Nat.add_mod_right k m).symm
    _ = ((k + 1) % m + (m - 1) % m) % m := by rw [h1, Nat.add_mod]
    _ = ((k + 1) % m + m - 1) % m := by
        rw [Nat.mod_eq_of_lt (by omega : m - 1 < m)]
        congr 1
        omega

theorem rcountMod_eq {m : ℕ} (hm : 0 < m) {r : ℕ} (hr : r < m) (q : Q) :
    rmod K ρ qs a q m r =
      (if r = 0 then rzero K ρ qs a q else 0) +
        rfirst K ρ qs a q *
          rmod K ρ qs a (rstep K ρ qs a) m ((r + m - 1) % m) := by
  ext u
  rw [Language.mem_add]
  constructor
  · intro hu
    change rcount K ρ qs a q u % m = r at hu
    rcases Nat.eq_zero_or_pos (rcount K ρ qs a q u) with h0 | hpos
    · left
      rw [h0, Nat.zero_mod] at hu
      subst hu
      exact h0
    · right
      obtain ⟨k, hk⟩ : ∃ k, rcount K ρ qs a q u = k + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      obtain ⟨y, u', rfl, hy, hu'⟩ := rcount_split k q u hk
      refine Language.mem_mul.mpr ⟨y, hy, u', ?_, rfl⟩
      change rcount K ρ qs a _ u' % m = (r + m - 1) % m
      rw [hu', ← hu, hk]
      exact mod_pred k hm
  · rintro (h | h)
    · split_ifs at h with hr0
      · change rcount K ρ qs a q u = 0 at h
        change rcount K ρ qs a q u % m = r
        rw [h, hr0, Nat.zero_mod]
      · exact absurd h (Language.notMem_zero u)
    · obtain ⟨y, hy, u', hu', rfl⟩ := Language.mem_mul.mp h
      obtain ⟨h1, h2⟩ := rcount_rfirst hy
      change rcount K ρ qs a _ u' % m = (r + m - 1) % m at hu'
      change rcount K ρ qs a q (y ++ u') % m = r
      rw [rcount_append, h1, h2, Nat.add_comm, Nat.add_mod, hu', ← Nat.add_mod, show r + m - 1 + 1 = r + m by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hr]

/-- **Counting positions in a given state, modulo `m`, at height one.** -/
theorem rcountMod_height [Finite α] {m : ℕ} (hm : 0 < m) {r : ℕ} (hr : r < m)
    (q : Q) : HasHeightAtMost (rmod K ρ qs a q m r) 1 := by
  rw [rcountMod_eq hm hr q]
  refine HasHeightAtMost.union ?_ ((rfirst_height qs a q 1).concat
    (rcountMod_next_height (Nat.mod_lt _ hm)))
  split_ifs
  · exact rzero_height qs a q 1
  · exact HasHeightAtMost.zero 1

end Reset

end GeneralizedStarHeight
