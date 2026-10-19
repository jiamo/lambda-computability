import Start.StarHeightShear

/-!
# The length-4 frontier as coloured pair counts

For a word `u` and a function `g` of prefixes, `psum x g u` is the sum of `g (u.take i)` over the
positions `i` of `u` reading `x`.  Nesting it gives pair sums over `i < j`:

  `wpair wt x y u = Σ_{i < j, u_i = x, u_j = y} wt (u.take i) (u.take j)`,

and with a colouring `col : List α → C` of the prefixes the *coloured pair count*

  `cpair col x y e f u = #{(i, j) : i < j, u_i = x, u_j = y, col (u.take i) = e, col (u.take j) = f}`.

Exact identities over `ℕ`, with `A v = |v|_a`:

* `scount_abac_eq_wpair`: `scount [a,b,a,c] u = Σ_{i<j, u_i = b, u_j = c} A_i (A_j − A_i)`;
* `scount_aabb_eq_wpair`: `scount [a,a,b,b] u = Σ_{i<j, u_i = u_j = b} (A_i choose 2)`.

Hence modulo `2` (`scount_abac_cast_cpair`, `scount_aabb_cast_cpair`): `scount abac` counts the
pairs (`b` read while `A` is odd) before (`c` read while `A` is even), and `scount aabb` counts the
pairs (`b` read while `A ≡ 2, 3 mod 4`) before (any `b`).

For the parity colour `col v = (|v|_a : ZMod 2)` and distinct `a, b, c`, the row and column sums
`cpair col b c 0 f + cpair col b c 1 f` and `cpair col b c e 0 + cpair col b c e 1` are good
modulo `2` (`goodMod_two_cpair_row`, `goodMod_two_cpair_col`).  So the four `cpair col b c e f`
agree modulo `2` up to good counts, and each is good modulo `2` iff `L(abac, k, 2)` has height at
most one (`cpair_mod_two_iff_abac`).
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

section Defs

variable {α : Type u} [DecidableEq α]

/-- The sum of `g (u.take i)` over the positions `i` of `u` reading `x`. -/
def psum (x : α) (g : List α → ℕ) (u : List α) : ℕ :=
  ∑ i ∈ Finset.range u.length, if u[i]? = some x then g (u.take i) else 0

/-- The weighted pair sum `Σ_{i < j, u_i = x, u_j = y} wt (u.take i) (u.take j)`. -/
def wpair (wt : List α → List α → ℕ) (x y : α) (u : List α) : ℕ :=
  psum y (fun v => psum x (fun v' => wt v' v) v) u

/-- **The coloured pair count**: the number of pairs `i < j` with `u_i = x`, `u_j = y`,
`col (u.take i) = e` and `col (u.take j) = f`. -/
def cpair {C : Type} [DecidableEq C] (col : List α → C) (x y : α) (e f : C) (u : List α) : ℕ :=
  wpair (fun v' v => if col v' = e ∧ col v = f then 1 else 0) x y u

lemma psum_nil (x : α) (g : List α → ℕ) : psum x g [] = 0 := by simp [psum]

lemma psum_snoc (x : α) (g : List α → ℕ) (u : List α) (z : α) :
    psum x g (u ++ [z]) = psum x g u + if z = x then g u else 0 := by
  unfold psum
  rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [List.getElem?_append_left hi, List.take_append_of_le_length hi.le]
  · simp

lemma psum_congr (x : α) (g h : List α → ℕ) (u : List α)
    (hgh : ∀ i, i < u.length → g (u.take i) = h (u.take i)) : psum x g u = psum x h u :=
  Finset.sum_congr rfl fun i hi => by rw [hgh i (Finset.mem_range.mp hi)]

lemma psum_add (x : α) (g h : List α → ℕ) (u : List α) :
    psum x (fun v => g v + h v) u = psum x g u + psum x h u := by
  unfold psum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

lemma psum_mul_left (x : α) (c : ℕ) (g : List α → ℕ) (u : List α) :
    psum x (fun v => c * g v) u = c * psum x g u := by
  unfold psum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

lemma psum_cast {R : Type} [CommRing R] (x : α) (g h : List α → ℕ) (u : List α)
    (hgh : ∀ i, i < u.length → (g (u.take i) : R) = h (u.take i)) :
    (psum x g u : R) = psum x h u := by
  unfold psum
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  split_ifs
  · exact hgh i (Finset.mem_range.mp hi)
  · rfl

lemma psum_zero (x : α) (u : List α) : psum x (fun _ => 0) u = 0 := by simp [psum]

lemma count_snoc_ite (a z : α) (u : List α) :
    (u ++ [z]).count a = u.count a + if z = a then 1 else 0 := by
  rw [List.count_append]
  congr 1
  by_cases h : z = a
  · subst h; simp
  · simp [h]

/-- A letter-in-state count is a `psum`. -/
lemma vcount_eq_psum {V : Type} [AddMonoid V] [DecidableEq V] (δ : α → V) (q : V) (x : α) (u : List α) :
    vcount δ q x u = psum x (fun v => if (v.map δ).sum = q then 1 else 0) u := by
  classical
  unfold vcount psum
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : u[i]? = some x
  · by_cases h2 : ((u.take i).map δ).sum = q
    · rw [if_pos ⟨h1, h2⟩, if_pos h1]; exact (if_pos h2).symm
    · rw [if_neg (fun h => h2 h.2), if_pos h1]; exact (if_neg h2).symm
  · rw [if_neg (fun h => h1 h.1), if_neg h1]

/-- `scount (w ++ [y]) u` sums `scount w` over the positions reading `y`. -/
lemma scount_snoc_eq_psum (w : List α) (y : α) (u : List α) :
    scount (w ++ [y]) u = psum y (scount w) u := by
  induction u using List.reverseRecOn with
  | nil => cases w <;> simp [psum_nil]
  | append_singleton u z ih => rw [scount_snoc, psum_snoc, ih]

end Defs

/-! ### The exact identities -/

section Exact

variable {α : Type u} [DecidableEq α]

lemma count_le_of_take (a : α) (u : List α) (i : ℕ) : (u.take i).count a ≤ u.count a :=
  (List.take_sublist i u).count_le a

/-- `scount aba + Σ_b A_t² = A · scount ab`. -/
lemma scount_aba_add {a b : α} (hab : a ≠ b) (u : List α) :
    scount [a, b, a] u + psum b (fun v => v.count a * v.count a) u =
      u.count a * psum b (fun v => v.count a) u := by
  induction u using List.reverseRecOn with
  | nil => simp [psum_nil]
  | append_singleton u z ih =>
      have e1 := scount_snoc a z u [a, b]
      have e2 : scount [a, b] u = psum b (fun v => v.count a) u := by
        rw [show [a, b] = [a] ++ [b] from rfl, scount_snoc_eq_psum]
        exact psum_congr _ _ _ _ fun i _ => scount_singleton a _
      simp only [List.cons_append, List.nil_append] at e1
      rw [e1, psum_snoc, psum_snoc, count_snoc_ite, ← e2]
      rw [← e2] at ih
      split_ifs with h1 h2 h2
      · exact absurd (h1.symm.trans h2) hab
      · nlinarith [ih]
      · nlinarith [ih]
      · nlinarith [ih]

/-- `scount aba = Σ_b A_t (A − A_t)`. -/
lemma scount_aba_eq_psum {a b : α} (hab : a ≠ b) (u : List α) :
    scount [a, b, a] u = psum b (fun v => v.count a * (u.count a - v.count a)) u := by
  have h := scount_aba_add hab u
  have h2 : psum b (fun v => v.count a * (u.count a - v.count a)) u +
      psum b (fun v => v.count a * v.count a) u = u.count a * psum b (fun v => v.count a) u := by
    rw [← psum_add, ← psum_mul_left]
    refine psum_congr _ _ _ _ fun i _ => ?_
    have := count_le_of_take a u i
    rw [← Nat.mul_add, Nat.sub_add_cancel this, Nat.mul_comm]
  omega

/-- **`abac` as a pair sum**: `scount [a,b,a,c] u = Σ_{i<j, u_i = b, u_j = c} A_i (A_j − A_i)`. -/
theorem scount_abac_eq_wpair {a b c : α} (hab : a ≠ b) (u : List α) :
    scount [a, b, a, c] u = wpair (fun v' v => v'.count a * (v.count a - v'.count a)) b c u := by
  rw [show [a, b, a, c] = [a, b, a] ++ [c] from rfl, scount_snoc_eq_psum]
  exact psum_congr _ _ _ _ fun i _ => scount_aba_eq_psum hab _

/-- `scount aa = A choose 2`. -/
lemma scount_aa (a : α) (u : List α) : scount [a, a] u = (u.count a).choose 2 := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u z ih =>
      have e1 := scount_snoc a z u [a]
      simp only [List.cons_append, List.nil_append] at e1
      rw [e1, ih, scount_singleton, List.count_append]
      by_cases hz : z = a
      · subst hz
        simp [Nat.choose_succ_succ', add_comm]
      · simp [hz]

/-- **`aabb` as a pair sum**: `scount [a,a,b,b] u = Σ_{i<j, u_i = u_j = b} (A_i choose 2)`. -/
theorem scount_aabb_eq_wpair (a b : α) (u : List α) :
    scount [a, a, b, b] u = wpair (fun v' _ => (v'.count a).choose 2) b b u := by
  rw [show [a, a, b, b] = [a, a, b] ++ [b] from rfl, scount_snoc_eq_psum]
  refine psum_congr _ _ _ _ fun i _ => ?_
  rw [show [a, a, b] = [a, a] ++ [b] from rfl, scount_snoc_eq_psum]
  exact psum_congr _ _ _ _ fun j _ => scount_aa a _

/-! ### The congruences modulo `2` -/

lemma mul_sub_cast_two (m n : ℕ) (h : m ≤ n) :
    ((m * (n - m) : ℕ) : ZMod 2) =
      ((if ((m : ZMod 2) = 1 ∧ (n : ZMod 2) = 0) then 1 else 0 : ℕ) : ZMod 2) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  push_cast
  generalize (m : ZMod 2) = x
  generalize (d : ZMod 2) = y
  revert x y
  decide

lemma choose_two_mod_two (n : ℕ) : n.choose 2 % 2 = if 2 ≤ n % 4 then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
      rw [h, Nat.choose_one_right]
      split_ifs at ih ⊢ <;> omega

/-- **`abac` modulo `2`**: the pairs (`b` read while `A` is odd) before (`c` read while `A` is
even). -/
theorem scount_abac_cast_cpair {a b c : α} (hab : a ≠ b) (u : List α) :
    (scount [a, b, a, c] u : ZMod 2) =
      cpair (fun v => (v.count a : ZMod 2)) b c 1 0 u := by
  rw [scount_abac_eq_wpair hab, wpair, cpair, wpair]
  refine psum_cast _ _ _ _ fun j hj => psum_cast _ _ _ _ fun i hi => ?_
  rw [mul_sub_cast_two _ _ (count_le_of_take a (u.take j) i)]

/-- **`aabb` modulo `2`**: the pairs (`b` read while `A ≡ 2, 3 mod 4`) before (any `b`). -/
theorem scount_aabb_cast_cpair (a b : α) (u : List α) :
    (scount [a, a, b, b] u : ZMod 2) =
      cpair (fun v => decide (2 ≤ v.count a % 4)) b b true true u +
        cpair (fun v => decide (2 ≤ v.count a % 4)) b b true false u := by
  rw [scount_aabb_eq_wpair, cpair, cpair, wpair, wpair, wpair, ← Nat.cast_add, ← psum_add]
  refine psum_cast _ _ _ _ fun j _ => ?_
  rw [← psum_add]
  refine psum_cast _ _ _ _ fun i _ => ?_
  rw [← ZMod.natCast_mod, choose_two_mod_two]
  by_cases h1 : 2 ≤ (List.take i (List.take j u)).count a % 4 <;>
    by_cases h2 : 2 ≤ (List.take j u).count a % 4 <;> simp [h1, h2]

end Exact

/-! ### Row and column sums for the parity colour -/

section Parity

variable {α : Type u} [DecidableEq α]

/-- The parity colour `|v|_a mod 2`. -/
def parCol (a : α) (v : List α) : ZMod 2 := (v.count a : ZMod 2)

/-- The translation automaton `(|·|_x mod 2, |·|_z mod 2)` on `ZMod 2 × ZMod 2`. -/
def pairStep (x z : α) (y : α) : ZMod 2 × ZMod 2 :=
  ((if y = x then 1 else 0), (if y = z then 1 else 0))

lemma pairStep_sum (x z : α) (v : List α) :
    (v.map (pairStep x z)).sum = ((v.count x : ZMod 2), (v.count z : ZMod 2)) :=
  sum_map_pair_indicator 2 x z v

lemma count_eq_psum (x : α) (u : List α) : u.count x = psum x (fun _ => 1) u := by
  induction u using List.reverseRecOn with
  | nil => simp [psum_nil]
  | append_singleton u z ih =>
      rw [psum_snoc, List.count_append, ih]
      by_cases hz : z = x
      · subst hz; simp
      · simp [hz]

lemma sum_map_indicator_two (a : α) : ∀ v : List α,
    (v.map fun y => if y = a then (1 : ZMod 2) else 0).sum = (v.count a : ZMod 2)
  | [] => by simp
  | y :: v => by
      rw [List.map_cons, List.sum_cons, sum_map_indicator_two a v, List.count_cons]
      by_cases h : y = a
      · subst h; simp [add_comm]
      · simp [h]

/-- The row sum: pairs (any `b`) before (`c` at colour `f`), modulo `2`, is the count of `c` read
in state `(f, 1)` of `(|·|_a mod 2, |·|_b mod 2)`. -/
lemma cpair_row_cast (a b c : α) (f : ZMod 2) (u : List α) :
    ((cpair (parCol a) b c 0 f u + cpair (parCol a) b c 1 f u : ℕ) : ZMod 2) =
      vcount (pairStep a b) (f, 1) c u := by
  rw [vcount_eq_psum, cpair, cpair, wpair, wpair, ← psum_add]
  refine psum_cast _ _ _ _ fun j _ => ?_
  rw [← psum_add, pairStep_sum]
  by_cases hf : parCol a (u.take j) = f
  · have : psum b (fun v' => (if parCol a v' = 0 ∧ parCol a (List.take j u) = f then 1 else 0) +
        if parCol a v' = 1 ∧ parCol a (List.take j u) = f then 1 else 0) (List.take j u) =
        (u.take j).count b := by
      rw [count_eq_psum]
      refine psum_congr _ _ _ _ fun i _ => ?_
      have : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      rcases this (parCol a ((u.take j).take i)) with h | h <;> simp [h, hf]
    rw [this]
    unfold parCol at hf
    simp only [hf, Prod.mk.injEq, true_and]
    have : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases this ((u.take j).count b : ZMod 2) with h | h
    · rw [if_neg (by rw [h]; decide)]
      push_cast
      exact h
    · rw [if_pos h]
      push_cast
      exact h
  · have : psum b (fun v' => (if parCol a v' = 0 ∧ parCol a (List.take j u) = f then 1 else 0) +
        if parCol a v' = 1 ∧ parCol a (List.take j u) = f then 1 else 0) (List.take j u) = 0 := by
      exact (psum_congr _ _ (fun _ => 0) _ fun i _ => by simp [hf]).trans (psum_zero _ _)
    rw [this]
    unfold parCol at hf
    simp [hf]

/-- The column sum, exactly: pairs (`b` at colour `e`) before (any `c`), plus the sum of `C_i`
over those `b`, is (number of `b` at colour `e`) times `|u|_c`. -/
lemma cpair_col_add {b c : α} (hbc : b ≠ c) (a : α) (e : ZMod 2) (u : List α) :
    cpair (parCol a) b c e 0 u + cpair (parCol a) b c e 1 u +
      psum b (fun v => if parCol a v = e then v.count c else 0) u =
        psum b (fun v => if parCol a v = e then 1 else 0) u * u.count c := by
  induction u using List.reverseRecOn with
  | nil => simp [cpair, wpair, psum_nil]
  | append_singleton u z ih =>
      simp only [cpair, wpair] at ih ⊢
      rw [psum_snoc, psum_snoc, psum_snoc, psum_snoc, count_snoc_ite]
      have hsplit : psum b (fun v' => if parCol a v' = e ∧ parCol a u = 0 then 1 else 0) u +
          psum b (fun v' => if parCol a v' = e ∧ parCol a u = 1 then 1 else 0) u =
            psum b (fun v => if parCol a v = e then 1 else 0) u := by
        rw [← psum_add]
        refine psum_congr _ _ _ _ fun i _ => ?_
        have : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
        rcases this (parCol a u) with h | h <;> simp [h]
      split_ifs with h1 h2 h3 h2 h3 <;> first
        | exact absurd (h2.symm.trans h1) hbc
        | exact absurd (h1.symm.trans h2) hbc
        | nlinarith [ih, hsplit]

/-- The column sum modulo `2`. -/
lemma cpair_col_cast {b c : α} (hbc : b ≠ c) (a : α) (e : ZMod 2) (u : List α) :
    ((cpair (parCol a) b c e 0 u + cpair (parCol a) b c e 1 u : ℕ) : ZMod 2) =
      (vcount (fun y => if y = a then (1 : ZMod 2) else 0) e b u : ZMod 2) * (u.count c : ZMod 2) -
        vcount (pairStep a c) (e, 1) b u := by
  have h := cpair_col_add hbc a e u
  have h1 : (vcount (fun y => if y = a then (1 : ZMod 2) else 0) e b u : ZMod 2) =
      psum b (fun v => if parCol a v = e then 1 else 0) u := by
    rw [vcount_eq_psum]
    refine psum_cast _ _ _ _ fun i _ => ?_
    rw [sum_map_indicator_two]
    rfl
  have h2 : (vcount (pairStep a c) (e, 1) b u : ZMod 2) =
      psum b (fun v => if parCol a v = e then v.count c else 0) u := by
    rw [vcount_eq_psum]
    refine psum_cast _ _ _ _ fun i _ => ?_
    rw [pairStep_sum]
    unfold parCol
    have : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    by_cases he : ((List.take i u).count a : ZMod 2) = e
    · rcases this ((List.take i u).count c : ZMod 2) with hc | hc
      · simp [he, hc]
      · simp [he, hc]
    · simp [he]
  rw [h1, h2, eq_sub_iff_add_eq]
  have := congrArg (Nat.cast : ℕ → ZMod 2) h
  push_cast at this ⊢
  exact this

variable [Finite α]

/-- **The row sum is good modulo `2`.** -/
theorem goodMod_two_cpair_row (a b c : α) (f : ZMod 2) :
    GoodMod 2 (fun u => cpair (parCol a) b c 0 f u + cpair (parCol a) b c 1 f u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine goodMod_of_det (by norm_num) (fun _ : Unit => vcount (pairStep a b) (f, 1) c)
    (fun _ => (goodCount_vcount_prime (p := 2) _ _ _).goodMod 2) ?_
  intro u w h
  rw [cpair_row_cast, cpair_row_cast]
  exact h ()

/-- **The column sum is good modulo `2`.** -/
theorem goodMod_two_cpair_col {b c : α} (hbc : b ≠ c) (a : α) (e : ZMod 2) :
    GoodMod 2 (fun u => cpair (parCol a) b c e 0 u + cpair (parCol a) b c e 1 u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine goodMod_of_det (by norm_num)
    ![vcount (fun y => if y = a then (1 : ZMod 2) else 0) e b, fun u => u.count c,
      vcount (pairStep a c) (e, 1) b] ?_ ?_
  · intro i
    fin_cases i
    · exact (goodCount_vcount_prime (p := 2) _ _ _).goodMod 2
    · exact (goodCount_count c).goodMod 2
    · exact (goodCount_vcount_prime (p := 2) _ _ _).goodMod 2
  · intro u w h
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    rw [cpair_col_cast hbc, cpair_col_cast hbc, h0, h1, h2]

omit [DecidableEq α] [Finite α] in
/-- If `f ≡ g + h (mod 2)` with `h` good modulo `2`, then `f` is good modulo `2` when `g` is. -/
lemma GoodMod.two_of_add {f g h : List α → ℕ} (hg : GoodMod 2 g) (hh : GoodMod 2 h)
    (hfgh : ∀ u, (f u : ZMod 2) = g u + h u) : GoodMod 2 f := by
  refine goodMod_of_det (by norm_num) ![g, h] (fun i => by fin_cases i <;> assumption) ?_
  intro u w hu
  have h0 := hu 0; have h1 := hu 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [hfgh, hfgh, h0, h1]

omit [DecidableEq α] [Finite α] in
/-- A count congruent modulo `2` to a count good modulo `2` is good modulo `2`. -/
lemma GoodMod.two_congr {f g : List α → ℕ} (hg : GoodMod 2 g)
    (hfg : ∀ u, (f u : ZMod 2) = g u) : GoodMod 2 f :=
  goodMod_of_det (by norm_num) (fun _ : Unit => g) (fun _ => hg) fun u w h => by
    rw [hfg, hfg]; exact h ()

/-- **The four coloured counts agree modulo `2` up to good counts**: each `cpair col b c e f`
is congruent to `cpair col b c 1 0` plus a count that is good modulo `2`. -/
theorem cpair_mod_two_reduce {b c : α} (hbc : b ≠ c) (a : α) (e f : ZMod 2) :
    ∃ h : List α → ℕ, GoodMod 2 h ∧
      ∀ u, (cpair (parCol a) b c e f u : ZMod 2) = cpair (parCol a) b c 1 0 u + h u := by
  have : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have two : ∀ z : ZMod 2, z + z = 0 := by decide
  rcases this e with rfl | rfl <;> rcases this f with rfl | rfl
  · refine ⟨_, goodMod_two_cpair_row a b c 0, fun u => ?_⟩
    push_cast
    linear_combination (-1 : ZMod 2) * two (cpair (parCol a) b c 1 0 u : ZMod 2)
  · refine ⟨fun u => (cpair (parCol a) b c 0 1 u + cpair (parCol a) b c 1 1 u) +
      (cpair (parCol a) b c 1 0 u + cpair (parCol a) b c 1 1 u), ?_, fun u => ?_⟩
    · exact GoodMod.two_of_add (goodMod_two_cpair_row a b c 1) (goodMod_two_cpair_col hbc a 1)
        fun u => by push_cast; ring
    · push_cast
      linear_combination (-1 : ZMod 2) * two (cpair (parCol a) b c 1 0 u : ZMod 2) +
        (-1 : ZMod 2) * two (cpair (parCol a) b c 1 1 u : ZMod 2)
  · refine ⟨fun u => (cpair (parCol a) b c 0 0 u + cpair (parCol a) b c 1 0 u) +
      (cpair (parCol a) b c 0 0 u + cpair (parCol a) b c 1 0 u), ?_, fun u => ?_⟩
    · exact GoodMod.two_of_add (goodMod_two_cpair_row a b c 0) (goodMod_two_cpair_row a b c 0)
        fun u => by push_cast; ring
    · push_cast
      linear_combination (-1 : ZMod 2) * two (cpair (parCol a) b c 0 0 u : ZMod 2) +
        (-1 : ZMod 2) * two (cpair (parCol a) b c 1 0 u : ZMod 2)
  · refine ⟨_, goodMod_two_cpair_col hbc a 1, fun u => ?_⟩
    push_cast
    linear_combination (-1 : ZMod 2) * two (cpair (parCol a) b c 1 0 u : ZMod 2)

end Parity

/-- **Each coloured pair count of the parity walk is good modulo `2` iff `L(abac, k, 2)` has
height at most one** (letters `a = 0`, `b = 1`, `c = 2` of `Fin 3`, colour `|v|_a mod 2`). -/
theorem cpair_mod_two_iff_abac (e f : ZMod 2) :
    GoodMod 2 (cpair (parCol (0 : Fin 3)) 1 2 e f) ↔
      ∀ k, k < 2 → HasHeightAtMost {u : List (Fin 3) | scount [0, 1, 0, 2] u % 2 = k} 1 := by
  obtain ⟨h, hh, hred⟩ := cpair_mod_two_reduce (α := Fin 3) (b := 1) (c := 2) (by decide) 0 e f
  have two : ∀ z : ZMod 2, z + z = 0 := by decide
  have habac : ∀ u : List (Fin 3),
      (scount [0, 1, 0, 2] u : ZMod 2) = cpair (parCol (0 : Fin 3)) 1 2 1 0 u :=
    fun u => scount_abac_cast_cpair (by decide) u
  constructor
  · intro hg k hk
    have h10 : GoodMod 2 (cpair (parCol (0 : Fin 3)) 1 2 1 0) :=
      GoodMod.two_of_add hg hh fun u => by
        rw [hred u]
        linear_combination (-1 : ZMod 2) * two (h u : ZMod 2)
    exact GoodMod.two_congr h10 habac k hk
  · intro hs
    have h10 : GoodMod 2 (cpair (parCol (0 : Fin 3)) 1 2 1 0) :=
      GoodMod.two_congr (g := scount [0, 1, 0, 2]) (fun k hk => hs k hk) fun u => (habac u).symm
    exact GoodMod.two_of_add h10 hh hred

end GeneralizedStarHeight
