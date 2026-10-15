/-
**The pigeonhole principle needs exponential-size resolution refutations.**

Task `M22-HAKEN-PHP`.

* `Complexity.Sat.PHP.php n` — the CNF `PHP(n+1, n)`: variables `p i j = var n i j` (pigeon
  `i ≤ n` sits in hole `j < n`), one clause `p i 0 ∨ … ∨ p i (n-1)` per pigeon and one clause
  `¬p i j ∨ ¬p k j` per hole `j` and pair of pigeons `i < k`.
* `Complexity.Sat.PHP.php_unsat` — `PHP(n+1, n)` is unsatisfiable.
* **`Complexity.Sat.PHP.php_refutation_size`** — every resolution refutation of `PHP(n+1, n)`
  (`Complexity.Sat.Refutation`, `Start/Resolution.lean`) has size at least `2^n`, i.e. the
  constant is `c = 1`.

The resolution derivations of `Start/Resolution.lean` are trees (`Deriv.res` takes two
subderivations, and `Deriv.size` counts the nodes of the tree), so this is the lower bound for
tree-like resolution.  The proof is the Prover–Delayer argument (Pudlák–Impagliazzo), unrolled
into an induction on the derivation: walking from the empty clause to a leaf, always keeping a
partial assignment `ρ` that falsifies the current clause and whose true entries form a partial
matching of pigeons to holes.  At a resolution step on an unassigned variable `p i j` whose
pigeon and hole are both free, both branches are followed and the potential `pot ρ` (the number of
matched pairs plus the number of "free" false entries) grows by at most one, so the tree doubles;
at every other step it does not grow.  A falsified pigeon clause forces `pot ρ ≥ n`, and no hole
clause is ever falsified.  Hence the derivation has at least `2^(n - pot ρ)` nodes, and `2^n` at the
root, where `ρ` is empty.
-/

import Start.Resolution

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Sat.PHP

open Classical

/-! ### The formula -/

/-- The variable "pigeon `i` sits in hole `j`". -/
def var (n i j : ℕ) : ℕ := n * i + j

/-- Pigeon `i` sits in some hole. -/
def pigeonClause (n i : ℕ) : Clause := (List.range n).map fun j => (true, var n i j)

/-- Pigeons `i` and `k` do not share hole `j`. -/
def holeClause (n i k j : ℕ) : Clause := [(false, var n i j), (false, var n k j)]

/-- All hole clauses. -/
def holeClauses (n : ℕ) : Cnf :=
  (List.range n).flatMap fun j => (List.range (n + 1)).flatMap fun i =>
    (List.range (n + 1)).filterMap fun k => if i < k then some (holeClause n i k j) else none

/-- **`PHP(n+1, n)`**: `n + 1` pigeons, `n` holes. -/
def php (n : ℕ) : Cnf := (List.range (n + 1)).map (pigeonClause n) ++ holeClauses n

theorem mem_php {n : ℕ} {C : Clause} (h : C ∈ php n) :
    (∃ i ≤ n, C = pigeonClause n i) ∨ (∃ i k j, i < k ∧ k ≤ n ∧ j < n ∧ C = holeClause n i k j) := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
    exact .inl ⟨i, by simp at hi; omega, rfl⟩
  · simp only [holeClauses, List.mem_flatMap, List.mem_range, List.mem_filterMap,
      Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨j, hj, i, hi, k, hk, hik, rfl⟩ := h
    exact .inr ⟨i, k, j, hik, by omega, hj, rfl⟩

theorem var_inj {n a c i j : ℕ} (hc : c < n) (hj : j < n) (h : var n a c = var n i j) :
    a = i ∧ c = j := by
  unfold var at h
  have h1 : (n * a + c) / n = (n * i + j) / n := by rw [h]
  have h2 : (n * a + c) % n = (n * i + j) % n := by rw [h]
  have hn : 0 < n := by omega
  rw [Nat.add_comm (n * a), Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hc,
    Nat.add_comm (n * i), Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hj] at h1
  rw [Nat.add_comm (n * a), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc,
    Nat.add_comm (n * i), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj] at h2
  omega

/-! ### Unsatisfiability -/

/-- **`PHP(n+1, n)` is unsatisfiable.** -/
theorem php_unsat (n : ℕ) : ∀ σ, cnfVal σ (php n) = false := by
  intro σ
  by_contra hσ
  rw [Bool.not_eq_false, cnfVal_eq_true] at hσ
  have hp : ∀ i : Fin (n + 1), ∃ j : Fin n, σ.getD (var n i j) false = true := by
    intro i
    have := hσ (pigeonClause n i) (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 i.2, rfl⟩))
    obtain ⟨l, hl, hv⟩ := clauseVal_eq_true.1 this
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
    exact ⟨⟨j, by simpa using hj⟩, hv⟩
  choose f hf using hp
  simp only [List.getD_eq_getElem?_getD] at hf
  have hinj : Function.Injective f := by
    intro i k hik
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with h | h
    · have := hσ (holeClause n i k (f i)) (List.mem_append_right _ (by
        simp only [holeClauses, List.mem_flatMap, List.mem_range, List.mem_filterMap,
          Option.ite_none_right_eq_some, Option.some.injEq]
        exact ⟨f i, (f i).2, i, i.2, k, k.2, h, rfl⟩))
      obtain ⟨l, hl, hv⟩ := clauseVal_eq_true.1 this
      simp only [holeClause, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · simp [litVal_false, hf i] at hv
      · simp [litVal_false, hik, hf k] at hv
    · have := hσ (holeClause n k i (f k)) (List.mem_append_right _ (by
        simp only [holeClauses, List.mem_flatMap, List.mem_range, List.mem_filterMap,
          Option.ite_none_right_eq_some, Option.some.injEq]
        exact ⟨f k, (f k).2, k, k.2, i, i.2, h, rfl⟩))
      obtain ⟨l, hl, hv⟩ := clauseVal_eq_true.1 this
      simp only [holeClause, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · simp [litVal_false, hf k] at hv
      · simp [litVal_false, ← hik, hf i] at hv
  have := Fintype.card_le_of_injective f hinj
  simp at this

/-! ### Partial assignments and the potential -/

/-- A partial assignment. -/
abbrev PAssign := ℕ → Option Bool

/-- `ρ` falsifies every literal of `C`. -/
def Falsifies (ρ : PAssign) (C : Clause) : Prop := ∀ l ∈ C, ρ l.2 = some (!l.1)

/-- The pigeon/hole grid. -/
def grid (n : ℕ) : Finset (ℕ × ℕ) := Finset.range (n + 1) ×ˢ Finset.range n

def matched (n : ℕ) (ρ : PAssign) (i : ℕ) : Prop := ∃ j < n, ρ (var n i j) = some true

def taken (n : ℕ) (ρ : PAssign) (j : ℕ) : Prop := ∃ i ≤ n, ρ (var n i j) = some true

/-- The true entries: a partial matching. -/
noncomputable def mset (n : ℕ) (ρ : PAssign) : Finset (ℕ × ℕ) :=
  (grid n).filter fun p => ρ (var n p.1 p.2) = some true

/-- The false entries whose pigeon and hole are both free. -/
noncomputable def zset (n : ℕ) (ρ : PAssign) : Finset (ℕ × ℕ) :=
  (grid n).filter fun p => ρ (var n p.1 p.2) = some false ∧ ¬ matched n ρ p.1 ∧ ¬ taken n ρ p.2

/-- The Delayer's potential. -/
noncomputable def pot (n : ℕ) (ρ : PAssign) : ℕ := (mset n ρ).card + (zset n ρ).card

/-- No two pigeons in the same hole. -/
def Inv (n : ℕ) (ρ : PAssign) : Prop :=
  ∀ i k j, i ≤ n → k ≤ n → j < n → ρ (var n i j) = some true → ρ (var n k j) = some true → i = k

theorem mem_grid {n : ℕ} {p : ℕ × ℕ} : p ∈ grid n ↔ p.1 ≤ n ∧ p.2 < n := by
  simp [grid]

/-- A falsified pigeon clause forces the potential up to `n`. -/
theorem pot_ge_of_pigeon {n : ℕ} {ρ : PAssign} {i : ℕ} (hi : i ≤ n)
    (h : Falsifies ρ (pigeonClause n i)) : n ≤ pot n ρ := by
  have hf : ∀ j < n, ρ (var n i j) = some false := by
    intro j hj
    exact h _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  have hnm : ¬ matched n ρ i := by
    rintro ⟨j, hj, h'⟩
    rw [hf j hj] at h'
    cases h'
  let g : ℕ → ℕ × ℕ := fun j => if hj : taken n ρ j then (Classical.choose hj, j) else (i, j)
  have hg : ∀ j, (g j).2 = j := by
    intro j
    simp only [g]
    split <;> rfl
  have hmaps : ∀ j ∈ Finset.range n, g j ∈ mset n ρ ∪ zset n ρ := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases ht : taken n ρ j
    · have hspec := Classical.choose_spec ht
      apply Finset.mem_union_left
      simp only [g, dif_pos ht, mset, Finset.mem_filter, mem_grid]
      exact ⟨⟨hspec.1, hj⟩, hspec.2⟩
    · apply Finset.mem_union_right
      simp only [g, dif_neg ht, zset, Finset.mem_filter, mem_grid]
      exact ⟨⟨hi, hj⟩, hf j hj, hnm, ht⟩
  have hinj : Set.InjOn g (Finset.range n : Set ℕ) := by
    intro a _ b _ hab
    rw [← hg a, ← hg b, hab]
  have := Finset.card_le_card_of_injOn g hmaps hinj
  rw [Finset.card_range] at this
  exact this.trans (Finset.card_union_le _ _)

/-- No hole clause is falsified. -/
theorem not_falsifies_hole {n : ℕ} {ρ : PAssign} (hρ : Inv n ρ) {i k j : ℕ} (hik : i < k)
    (hk : k ≤ n) (hj : j < n) : ¬ Falsifies ρ (holeClause n i k j) := by
  intro h
  have h1 := h (false, var n i j) (by simp [holeClause])
  have h2 := h (false, var n k j) (by simp [holeClause])
  have := hρ i k j (by omega) hk hj h1 h2
  omega

theorem eq_of_var_eq {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ grid n) {i j : ℕ} (hj : j < n)
    (h : var n p.1 p.2 = var n i j) : p = (i, j) := by
  rw [mem_grid] at hp
  obtain ⟨h1, h2⟩ := var_inj hp.2 hj h
  exact Prod.ext h1 h2

section Update

variable {n : ℕ} {ρ : PAssign} {x : ℕ} {b : Bool}

theorem update_of_ne {v : ℕ} (h : v ≠ x) : Function.update ρ x (some b) v = ρ v :=
  Function.update_of_ne h _ _

theorem update_true_iff (hx : ρ x = none) (v : ℕ) :
    Function.update ρ x (some b) v = some true ↔ ρ v = some true ∨ (v = x ∧ b = true) := by
  by_cases hv : v = x
  · subst hv; simp [hx]
  · simp [hv]

theorem matched_mono (hx : ρ x = none) {i : ℕ} (h : matched n ρ i) :
    matched n (Function.update ρ x (some b)) i := by
  obtain ⟨j, hj, h⟩ := h
  exact ⟨j, hj, (update_true_iff hx _).2 (.inl h)⟩

theorem taken_mono (hx : ρ x = none) {j : ℕ} (h : taken n ρ j) :
    taken n (Function.update ρ x (some b)) j := by
  obtain ⟨i, hi, h⟩ := h
  exact ⟨i, hi, (update_true_iff hx _).2 (.inl h)⟩

theorem matched_false_iff (hx : ρ x = none) {i : ℕ} :
    matched n (Function.update ρ x (some false)) i ↔ matched n ρ i := by
  simp only [matched, update_true_iff hx, Bool.false_eq_true, and_false, or_false]

theorem taken_false_iff (hx : ρ x = none) {j : ℕ} :
    taken n (Function.update ρ x (some false)) j ↔ taken n ρ j := by
  simp only [taken, update_true_iff hx, Bool.false_eq_true, and_false, or_false]

theorem mset_false (hx : ρ x = none) :
    mset n (Function.update ρ x (some false)) = mset n ρ := by
  ext p
  simp only [mset, Finset.mem_filter, update_true_iff hx, Bool.false_eq_true, and_false,
    or_false]

theorem mset_sub (hx : ρ x = none) {i j : ℕ} (hj : j < n) (hxv : x = var n i j) :
    mset n (Function.update ρ x (some b)) ⊆ insert (i, j) (mset n ρ) := by
  intro p hp
  simp only [mset, Finset.mem_filter, update_true_iff hx] at hp
  rcases hp with ⟨hg, h | ⟨hv, -⟩⟩
  · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hg, h⟩)
  · rw [eq_of_var_eq hg hj (hv.trans hxv)]
    exact Finset.mem_insert_self _ _

theorem zset_false_sub (hx : ρ x = none) {i j : ℕ} (hj : j < n) (hxv : x = var n i j) :
    zset n (Function.update ρ x (some false)) ⊆ insert (i, j) (zset n ρ) := by
  intro p hp
  simp only [zset, Finset.mem_filter, matched_false_iff hx, taken_false_iff hx] at hp
  obtain ⟨hg, hv, hm, ht⟩ := hp
  by_cases hpx : var n p.1 p.2 = x
  · rw [eq_of_var_eq hg hj (hpx.trans hxv)]
    exact Finset.mem_insert_self _ _
  · rw [update_of_ne hpx] at hv
    exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hg, hv, hm, ht⟩)

theorem zset_forced_sub (hx : ρ x = none) {i j : ℕ} (hj : j < n) (hxv : x = var n i j)
    (hf : matched n ρ i ∨ taken n ρ j) :
    zset n (Function.update ρ x (some false)) ⊆ zset n ρ := by
  intro p hp
  simp only [zset, Finset.mem_filter, matched_false_iff hx, taken_false_iff hx] at hp
  obtain ⟨hg, hv, hm, ht⟩ := hp
  by_cases hpx : var n p.1 p.2 = x
  · rw [eq_of_var_eq hg hj (hpx.trans hxv)] at hm ht
    exact absurd hf (by tauto)
  · rw [update_of_ne hpx] at hv
    exact Finset.mem_filter.2 ⟨hg, hv, hm, ht⟩

theorem zset_true_sub (hx : ρ x = none) :
    zset n (Function.update ρ x (some true)) ⊆ zset n ρ := by
  intro p hp
  simp only [zset, Finset.mem_filter] at hp
  obtain ⟨hg, hv, hm, ht⟩ := hp
  have hpx : var n p.1 p.2 ≠ x := by
    rintro hpx
    rw [hpx, Function.update_self] at hv
    cases hv
  rw [update_of_ne hpx] at hv
  exact Finset.mem_filter.2 ⟨hg, hv, fun h => hm (matched_mono hx h),
    fun h => ht (taken_mono hx h)⟩

theorem pot_forced (hx : ρ x = none) {i j : ℕ} (hj : j < n) (hxv : x = var n i j)
    (hf : matched n ρ i ∨ taken n ρ j) : pot n (Function.update ρ x (some false)) ≤ pot n ρ := by
  unfold pot
  rw [mset_false hx]
  have := Finset.card_le_card (zset_forced_sub hx hj hxv hf)
  omega

theorem pot_free (hx : ρ x = none) {i j : ℕ} (hj : j < n) (hxv : x = var n i j) (b : Bool) :
    pot n (Function.update ρ x (some b)) ≤ pot n ρ + 1 := by
  unfold pot
  cases b
  · rw [mset_false hx]
    have := (Finset.card_le_card (zset_false_sub hx hj hxv)).trans (Finset.card_insert_le _ _)
    omega
  · have h1 := (Finset.card_le_card (mset_sub (b := true) hx hj hxv)).trans
      (Finset.card_insert_le _ _)
    have h2 := Finset.card_le_card (zset_true_sub (n := n) hx)
    omega

/-- Outside the grid an update changes nothing that the potential sees. -/
theorem pot_outside (hx : ∀ i ≤ n, ∀ j < n, var n i j ≠ x) :
    pot n (Function.update ρ x (some b)) = pot n ρ := by
  have hv : ∀ i ≤ n, ∀ j < n, Function.update ρ x (some b) (var n i j) = ρ (var n i j) :=
    fun i hi j hj => update_of_ne (hx i hi j hj)
  have hm : ∀ i ≤ n, (matched n (Function.update ρ x (some b)) i ↔ matched n ρ i) := by
    intro i hi
    exact exists_congr fun j => and_congr_right fun hj => by rw [hv i hi j hj]
  have ht : ∀ j < n, (taken n (Function.update ρ x (some b)) j ↔ taken n ρ j) := by
    intro j hj
    exact exists_congr fun i => and_congr_right fun hi => by rw [hv i hi j hj]
  unfold pot mset zset
  congr 2
  · exact Finset.filter_congr fun p hp => by
      rw [mem_grid] at hp
      rw [hv _ hp.1 _ hp.2]
  · exact Finset.filter_congr fun p hp => by
      rw [mem_grid] at hp
      rw [hv _ hp.1 _ hp.2, hm _ hp.1, ht _ hp.2]

theorem inv_false (hρ : Inv n ρ) (hx : ρ x = none) : Inv n (Function.update ρ x (some false)) := by
  intro i k j hi hk hj h1 h2
  rw [update_true_iff hx] at h1 h2
  simp only [Bool.false_eq_true, and_false, or_false] at h1 h2
  exact hρ i k j hi hk hj h1 h2

theorem inv_true (hρ : Inv n ρ) (hx : ρ x = none) {i j : ℕ} (hi : i ≤ n) (hj : j < n)
    (hxv : x = var n i j) (ht : ¬ taken n ρ j) : Inv n (Function.update ρ x (some true)) := by
  intro a c d ha hc hd h1 h2
  rw [update_true_iff hx] at h1 h2
  rcases h1 with h1 | ⟨h1, -⟩ <;> rcases h2 with h2 | ⟨h2, -⟩
  · exact hρ a c d ha hc hd h1 h2
  · obtain ⟨rfl, rfl⟩ := var_inj hd hj (h2.trans hxv)
    exact absurd ⟨a, ha, h1⟩ ht
  · obtain ⟨rfl, rfl⟩ := var_inj hd hj (h1.trans hxv)
    exact absurd ⟨c, hc, h2⟩ ht
  · exact (var_inj hd hj (h1.trans hxv)).1.trans (var_inj hd hj (h2.trans hxv)).1.symm

theorem agree_update (hx : ρ x = none) :
    ∀ v, ρ v ≠ none → Function.update ρ x (some b) v = ρ v := by
  intro v hv
  apply update_of_ne
  rintro rfl
  exact hv hx

end Update

/-! ### The lower bound -/

theorem falsifies_left {ρ ρ' : PAssign} {k : ℕ} {C D : Clause} (hk : ρ' k = some false)
    (hagree : ∀ v, ρ v ≠ none → ρ' v = ρ v) (hF : Falsifies ρ (resolvent k C D)) :
    Falsifies ρ' C := by
  intro l hl
  by_cases hl' : l = (true, k)
  · subst hl'
    simpa using hk
  · have h := hF l (List.mem_append_left _ (List.mem_filter.2 ⟨hl, by simpa using hl'⟩))
    rw [hagree _ (by rw [h]; simp)]
    exact h

theorem falsifies_right {ρ ρ' : PAssign} {k : ℕ} {C D : Clause} (hk : ρ' k = some true)
    (hagree : ∀ v, ρ v ≠ none → ρ' v = ρ v) (hF : Falsifies ρ (resolvent k C D)) :
    Falsifies ρ' D := by
  intro l hl
  by_cases hl' : l = (false, k)
  · subst hl'
    simpa using hk
  · have h := hF l (List.mem_append_right _ (List.mem_filter.2 ⟨hl, by simpa using hl'⟩))
    rw [hagree _ (by rw [h]; simp)]
    exact h

theorem pow_sub_le {n a b : ℕ} (h : a ≤ b) : 2 ^ (n - b) ≤ 2 ^ (n - a) :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The Delayer bound.**  A derivation of a clause falsified by a Delayer state `ρ` has at least
`2^(n - pot ρ)` nodes. -/
theorem size_ge_of_falsifies {n : ℕ} : ∀ {C : Clause} (d : Deriv (php n) C) (ρ : PAssign),
    Inv n ρ → Falsifies ρ C → 2 ^ (n - pot n ρ) ≤ d.size := by
  intro C d
  induction d with
  | ax hC =>
      intro ρ hρ hF
      rcases mem_php hC with ⟨i, hi, rfl⟩ | ⟨i, k, j, hik, hk, hj, rfl⟩
      · have := pot_ge_of_pigeon hi hF
        simp [Nat.sub_eq_zero_of_le this, Deriv.size]
      · exact absurd hF (not_falsifies_hole hρ hik hk hj)
  | @res C₁ C₂ k d₁ d₂ _ _ ih₁ ih₂ =>
      intro ρ hρ hF
      simp only [Deriv.size]
      cases hk : ρ k with
      | some bk =>
          cases bk
          · have := ih₁ ρ hρ (falsifies_left hk (fun _ _ => rfl) hF)
            omega
          · have := ih₂ ρ hρ (falsifies_right hk (fun _ _ => rfl) hF)
            omega
      | none =>
          by_cases hgrid : ∃ i ≤ n, ∃ j < n, var n i j = k
          · obtain ⟨i, hi, j, hj, hkv⟩ := hgrid
            by_cases hf : matched n ρ i ∨ taken n ρ j
            · have h1 := ih₁ _ (inv_false hρ hk)
                (falsifies_left (Function.update_self _ _ _) (agree_update hk) hF)
              have h2 := pow_sub_le (n := n) (pot_forced hk hj hkv.symm hf)
              omega
            · have h0 := ih₁ _ (inv_false hρ hk)
                (falsifies_left (Function.update_self _ _ _) (agree_update hk) hF)
              have h1 := ih₂ _ (inv_true hρ hk hi hj hkv.symm (fun h => hf (.inr h)))
                (falsifies_right (Function.update_self _ _ _) (agree_update hk) hF)
              have p0 := pow_sub_le (n := n) (pot_free hk hj hkv.symm false)
              have p1 := pow_sub_le (n := n) (pot_free hk hj hkv.symm true)
              by_cases hm : n ≤ pot n ρ
              · rw [Nat.sub_eq_zero_of_le hm]
                simp
              · have : n - pot n ρ = (n - (pot n ρ + 1)) + 1 := by omega
                rw [this, pow_succ]
                omega
          · have hout : ∀ i ≤ n, ∀ j < n, var n i j ≠ k := fun i hi j hj h =>
              hgrid ⟨i, hi, j, hj, h⟩
            have h1 := ih₁ _ (inv_false hρ hk)
              (falsifies_left (Function.update_self _ _ _) (agree_update hk) hF)
            rw [pot_outside hout] at h1
            omega

/-- **Every resolution refutation of `PHP(n+1, n)` has at least `2^n` nodes.** -/
theorem php_refutation_size (n : ℕ) (d : Refutation (php n)) : 2 ^ n ≤ d.size := by
  have h := size_ge_of_falsifies d (fun _ => none) (by
    intro i k j _ _ _ h
    cases h) (by intro l hl; cases hl)
  have hpot : pot n (fun _ => none) = 0 := by
    simp [pot, mset, zset]
  rwa [hpot, Nat.sub_zero] at h

/-- The packaged statement of the row: `PHP(n+1, n)` is unsatisfiable, and every refutation has
size at least `2^(c n)` with `c = 1`. -/
theorem haken_php (n : ℕ) :
    (∀ σ, cnfVal σ (php n) = false) ∧ ∀ d : Refutation (php n), 2 ^ (1 * n) ≤ d.size :=
  ⟨php_unsat n, fun d => by simpa using php_refutation_size n d⟩

end Complexity.Sat.PHP
