import Start.StarHeightZ4Core
import Start.StarHeightHCore

/-!
# Scattered subword counts of length at most three

`scount w u` is the number of occurrences of `w` as a scattered subword of `u`.

* `scount_abc_identity`: for distinct letters `a, b, c` and the letter map `ψ` sending `c` to `a`,
  `scount [a,b,c] u + scount [a,a,b] (ψ u) = |u|_c · scount [a,b] u + scount [a,a,b] u +
  scount [c,c,b] u`.
* `height_one_scount_pst`: PST Theorem 7.4, `{u | scount (xⁱ y xʲ) u ≡ k (mod n)}` has generalized
  star height at most one, for every modulus `n`.
* `height_one_scount_le_three`: every `{u | scount w u ≡ k (mod n)}` with `|w| ≤ 3` has height at
  most one, for every modulus `n` (PST 1992 did this for square-free `n` only).
* `height_one_abc_mod_four`: the smallest case that PST and Bourne left open, stated alone.

A count `g : List α → ℕ` is *good* (`GoodCount g`) when every residue class of `g` modulo every
`m` has height at most one.  Good counts are closed under sums, products, differences and inverse
letter maps, and a count whose residue modulo `m` is fixed by the residues of finitely many good
counts is good (`goodCount_of_det`, from `height_one_of_residues`).  The engine is the position
formula `scount (xⁱ y zʲ) u = Σ_{u_t = y} C(|u[0,t)|_x, i) · C(|u(t,end)|_z, j)`
(`scount_rep_eq_sum`): modulo `n` it is a combination of letter-in-state counts `vcount` of `y` in
the translation automaton of `x` on `ZMod N`, `N = 2 n i! j!`, and these are `pcount` counts of a
fixed letter (`pcount_fixed_height_one`, PST Proposition 6.6).
-/

namespace GeneralizedStarHeight

universe u v

open EpisodeAlgebra
open scoped Computability

/-! ### Scattered subword counts -/

section SCount

variable {α : Type u} [DecidableEq α]

/-- The number of occurrences of `w` as a scattered subword (subsequence) of `u`. -/
def scount : List α → List α → ℕ
  | [], _ => 1
  | _ :: _, [] => 0
  | y :: w, x :: u => scount (y :: w) u + if x = y then scount w u else 0

@[simp] lemma scount_nil_left (u : List α) : scount [] u = 1 := by
  cases u <;> rfl

@[simp] lemma scount_cons_nil (y : α) (w : List α) : scount (y :: w) [] = 0 := rfl

lemma scount_cons_cons (y x : α) (w u : List α) :
    scount (y :: w) (x :: u) = scount (y :: w) u + if x = y then scount w u else 0 := rfl

lemma count_cons_eq (x a : α) (l : List α) :
    (a :: l).count x = l.count x + if a = x then 1 else 0 := by
  rw [List.count_cons]
  simp

/-- A power of one letter: a binomial coefficient of a letter count. -/
lemma scount_replicate (z : α) : ∀ (j : ℕ) (u : List α), scount (List.replicate j z) u = (u.count z).choose j
  | 0, u => by simp
  | j + 1, [] => by simp [List.replicate_succ]
  | j + 1, a :: u => by
      rw [List.replicate_succ, scount_cons_cons, ← List.replicate_succ, scount_replicate z (j + 1) u,
        scount_replicate z j u, count_cons_eq]
      by_cases h : a = z
      · simp [h, Nat.choose_succ_succ', add_comm]
      · simp [h]

lemma scount_singleton (z : α) (u : List α) : scount [z] u = u.count z := by
  have := scount_replicate z 1 u
  simpa using this

/-- **The position formula.** -/
lemma scount_rep_eq_sum (x y z : α) (j : ℕ) : ∀ (u : List α) (i : ℕ),
    scount (List.replicate i x ++ y :: List.replicate j z) u =
      ∑ t ∈ Finset.range u.length, if u[t]? = some y then
        ((u.take t).count x).choose i * ((u.drop (t + 1)).count z).choose j else 0
  | [], i => by cases i <;> simp [List.replicate_succ]
  | a :: u, 0 => by
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.replicate_zero, List.nil_append, scount_cons_cons, scount_replicate,
        List.getElem?_cons_succ, List.take_succ_cons, List.drop_succ_cons, List.getElem?_cons_zero,
        List.take_zero, List.drop_zero, Nat.choose_zero_right, one_mul, Option.some.injEq]
      have ih := scount_rep_eq_sum x y z j u 0
      simp only [List.replicate_zero, List.nil_append, Nat.choose_zero_right, one_mul] at ih
      rw [ih]
  | a :: u, i + 1 => by
      rw [List.length_cons, Finset.sum_range_succ', List.replicate_succ, List.cons_append,
        scount_cons_cons, ← List.cons_append, ← List.replicate_succ, scount_rep_eq_sum x y z j u (i + 1),
        scount_rep_eq_sum x y z j u i]
      simp only [List.getElem?_cons_succ, List.take_succ_cons, List.drop_succ_cons, count_cons_eq,
        List.take_zero, List.count_nil, Nat.choose_zero_succ, zero_mul, ite_self, add_zero]
      by_cases h : a = x
      · simp only [h, ite_true, Nat.choose_succ_succ', add_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> ring
      · simp [h]

end SCount

/-! ### Good counts -/

section Good

variable {α : Type u}

/-- Every residue class of `g` modulo every `m` has height at most one. -/
def GoodCount (g : List α → ℕ) : Prop :=
  ∀ m r : ℕ, r < m → HasHeightAtMost {u | g u % m = r} 1

lemma natCast_eq_of_mod_eq {m M a b : ℕ} (hmM : m ∣ M) (h : a % M = b % M) :
    (a : ZMod m) = b :=
  (ZMod.natCast_eq_natCast_iff' a b m).mpr (Nat.ModEq.of_dvd hmM h)

/-- A count whose residues modulo every `m` are fixed by the residues of finitely many good
counts is good. -/
theorem goodCount_of_det {g : List α → ℕ}
    (h : ∀ m : ℕ, 0 < m → ∃ (ι : Type v) (_ : Finite ι) (f : ι → List α → ℕ) (M : ℕ), 0 < M ∧
      (∀ i, GoodCount (f i)) ∧ ∀ u w, (∀ i, f i u % M = f i w % M) → (g u : ZMod m) = g w) :
    GoodCount g := by
  intro m r hr
  obtain ⟨ι, hι, f, M, hM, hf, hdet⟩ := h m (by omega)
  refine height_one_of_residues_univ f hM (fun i r hr => hf i M r hr) _
    (fun z => ∃ u, (∀ i, f i u % M = z i) ∧ g u % m = r) ?_
  intro w
  constructor
  · intro hw
    exact ⟨w, fun i => rfl, hw⟩
  · rintro ⟨u, hu, hgu⟩
    have := hdet u w hu
    rw [ZMod.natCast_eq_natCast_iff'] at this
    show g w % m = r
    rw [← this, hgu]

lemma goodCount_const (c : ℕ) : GoodCount (fun _ : List α => c) :=
  goodCount_of_det.{u, 0} fun _ _ => ⟨Empty, inferInstance, fun e => e.elim, 1, one_pos,
    fun e => e.elim, fun _ _ _ => rfl⟩

lemma goodCount_binop {f g : List α → ℕ} (hf : GoodCount f) (hg : GoodCount g) (op : ℕ → ℕ → ℕ)
    (hop : ∀ m a b a' b' : ℕ, (a : ZMod m) = a' → (b : ZMod m) = b' →
      ((op a b : ℕ) : ZMod m) = op a' b') :
    GoodCount (fun u => op (f u) (g u)) :=
  goodCount_of_det.{u, 0} fun m hm => ⟨Bool, inferInstance, fun b => if b then f else g, m, hm,
    fun b => by cases b <;> simpa, fun u w h => hop m _ _ _ _
      (natCast_eq_of_mod_eq dvd_rfl (h true)) (natCast_eq_of_mod_eq dvd_rfl (h false))⟩

lemma GoodCount.add {f g : List α → ℕ} (hf : GoodCount f) (hg : GoodCount g) :
    GoodCount (fun u => f u + g u) :=
  goodCount_binop hf hg (· + ·) fun m a b a' b' ha hb => by push_cast; rw [ha, hb]

lemma GoodCount.mul {f g : List α → ℕ} (hf : GoodCount f) (hg : GoodCount g) :
    GoodCount (fun u => f u * g u) :=
  goodCount_binop hf hg (· * ·) fun m a b a' b' ha hb => by push_cast; rw [ha, hb]

/-- If `f + g = h` with `g` and `h` good, then `f` is good. -/
lemma GoodCount.of_add_eq {f g h : List α → ℕ} (hg : GoodCount g) (hh : GoodCount h)
    (heq : ∀ u, f u + g u = h u) : GoodCount f :=
  goodCount_of_det.{u, 0} fun m hm => ⟨Bool, inferInstance, fun b => if b then g else h, m, hm,
    fun b => by cases b <;> simpa, fun u w hw => by
      have h1 := natCast_eq_of_mod_eq (m := m) dvd_rfl (hw true)
      have h2 := natCast_eq_of_mod_eq (m := m) dvd_rfl (hw false)
      simp only [ite_true, Bool.false_eq_true, ite_false] at h1 h2
      have e1 : (f u : ZMod m) = h u - g u := by rw [← heq u]; push_cast; ring
      have e2 : (f w : ZMod m) = h w - g w := by rw [← heq w]; push_cast; ring
      rw [e1, e2, h1, h2]⟩

lemma GoodCount.congr {f g : List α → ℕ} (hf : GoodCount f) (h : ∀ u, f u = g u) : GoodCount g := by
  have : f = g := funext h
  exact this ▸ hf

/-- Inverse letter maps preserve good counts. -/
lemma GoodCount.comp_map [Finite α] {β : Type v} {g : List β → ℕ} (hg : GoodCount g) (ψ : α → β) :
    GoodCount (fun u => g (u.map ψ)) := by
  intro m r hr
  have heq : {u : List α | g (u.map ψ) % m = r} = invAlph (fun a => some (ψ a)) {w | g w % m = r} := by
    ext u
    have hfm : (u.filterMap fun a => some (ψ a)) = u.map ψ := by
      induction u with
      | nil => rfl
      | cons b u ih => simp [ih]
    show _ ↔ g (u.filterMap fun a => some (ψ a)) % m = r
    rw [hfm]
    rfl
  rw [heq]
  exact (hg m r hr).invAlph _

lemma goodCount_count [Finite α] [DecidableEq α] (x : α) : GoodCount (fun u : List α => u.count x) := by
  intro m r hr
  have := vcount_height_one_prime (p := 2) (V := ZMod 2) (fun _ : α => (0 : ZMod 2)) 0 x m r hr
  simpa only [vcount_eq_vcountFrom, vcountFrom_const_zero] using this

lemma goodCount_vcount_prime [Finite α] [DecidableEq α] {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] (δ : α → V) (q : V) (y : α) :
    GoodCount (fun u : List α => vcount δ q y u) :=
  fun m r hr => vcount_height_one_prime (p := p) δ q y m r hr

end Good

/-! ### Grouping positions by state -/

section Group

variable {α : Type u} [DecidableEq α] {V : Type} [AddCommMonoid V] [Fintype V] [DecidableEq V]

/-- The position sum of a state-dependent weight is a combination of letter-in-state counts. -/
lemma sum_pos_eq_sum_vcount {R : Type*} [CommRing R] (δ : α → V) (y : α) (u : List α) (W : V → R) :
    (∑ t ∈ Finset.range u.length, if u[t]? = some y then W ((u.take t).map δ).sum else 0) =
      ∑ q : V, W q * (vcount δ q y u : R) := by
  classical
  simp only [vcount, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : u[t]? = some y
  · simp only [h, ite_true, true_and]
    rw [Finset.sum_eq_single (((u.take t).map δ).sum)]
    · simp
    · intro q _ hq
      rw [ite_eq_right (Ne.symm hq), Nat.cast_zero, mul_zero]
    · simp
  · simp [h]

/-- The cast of `scount (xⁱ y zʲ) u`, given a weight that sees the state before each position and
the state of the whole word. -/
lemma scount_cast_eq_sum_vcount {R : Type*} [CommRing R] (x y z : α) (i j : ℕ) (δ : α → V)
    (W : V → V → R) (u : List α)
    (hW : ∀ t, u[t]? = some y → ((((u.take t).count x).choose i *
      ((u.drop (t + 1)).count z).choose j : ℕ) : R) = W ((u.take t).map δ).sum (u.map δ).sum) :
    (scount (List.replicate i x ++ y :: List.replicate j z) u : R) =
      ∑ q : V, W q (u.map δ).sum * (vcount δ q y u : R) := by
  rw [scount_rep_eq_sum, Nat.cast_sum, ← sum_pos_eq_sum_vcount δ y u (fun q => W q (u.map δ).sum)]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : u[t]? = some y
  · simp only [h, ite_true]
    exact hW t h
  · simp [h]

/-- Splitting a word at a position reading `y`. -/
lemma count_drop_of_getElem? {u : List α} {t : ℕ} {y : α} (h : u[t]? = some y) (z : α) :
    u.count z = (u.take t).count z + (if y = z then 1 else 0) + (u.drop (t + 1)).count z := by
  have ht : t < u.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    simp at h
  have hy : u[t] = y := by
    rw [List.getElem?_eq_getElem ht] at h
    exact Option.some.inj h
  conv_lhs => rw [← List.take_append_drop t u, List.drop_eq_getElem_cons ht]
  rw [List.count_append, count_cons_eq, hy]
  ring

lemma sum_map_indicator {R : Type*} [AddCommMonoidWithOne R] (x : α) :
    ∀ l : List α, (l.map fun a => if a = x then (1 : R) else 0).sum = (l.count x : R)
  | [] => by simp
  | b :: l => by
      rw [List.map_cons, List.sum_cons, sum_map_indicator x l, count_cons_eq]
      push_cast
      rw [add_comm]

end Group

/-! ### Binomial coefficients modulo `n` -/

section Binom

lemma descFactorial_add_sub_dvd (N : ℕ) : ∀ (i s : ℕ),
    (N : ℤ) ∣ ((s + N).descFactorial i : ℤ) - (s.descFactorial i : ℤ)
  | 0, s => by simp
  | i + 1, s => by
      have ih := descFactorial_add_sub_dvd N i s
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ]
      by_cases hi : i ≤ s
      · have e : ((s + N - i : ℕ) : ℤ) = ((s - i : ℕ) : ℤ) + N := by
          push_cast [hi, show i ≤ s + N by omega]; ring
        push_cast
        rw [e]
        have : ((s - i : ℕ) : ℤ) * ((s + N).descFactorial i : ℤ) + (N : ℤ) * (s + N).descFactorial i -
            ((s - i : ℕ) : ℤ) * (s.descFactorial i : ℤ) =
            ((s - i : ℕ) : ℤ) * (((s + N).descFactorial i : ℤ) - (s.descFactorial i : ℤ)) +
              (N : ℤ) * (s + N).descFactorial i := by ring
        rw [add_mul, this]
        exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_right _ _)
      · have h0 : s.descFactorial i = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        rw [h0, Nat.cast_zero, sub_zero] at ih
        push_cast
        rw [h0, Nat.cast_zero, mul_zero, sub_zero]
        exact dvd_mul_of_dvd_right ih _

lemma choose_add_sub_dvd (N i s : ℕ) :
    (N : ℤ) ∣ (i.factorial : ℤ) * (((s + N).choose i : ℤ) - (s.choose i : ℤ)) := by
  have := descFactorial_add_sub_dvd N i s
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at this
  push_cast at this
  rw [mul_sub]
  exact this

/-- `C(s, i)` modulo `n` depends only on `s` modulo `N` when `n · i! ∣ N`. -/
lemma choose_cast_add {n N i : ℕ} (hN : n * i.factorial ∣ N) (s : ℕ) :
    (((s + N).choose i : ℕ) : ZMod n) = (s.choose i : ZMod n) := by
  obtain ⟨c, hc⟩ := hN
  obtain ⟨d, hd⟩ := choose_add_sub_dvd N i s
  have hf : (i.factorial : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
  have : (((s + N).choose i : ℤ) - (s.choose i : ℤ)) = n * (c * d) := by
    apply mul_left_cancel₀ hf
    rw [hd, hc]; push_cast; ring
  rw [← Int.cast_natCast, ← Int.cast_natCast (R := ZMod n) (s.choose i),
    ← sub_eq_zero, ← Int.cast_sub, this, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

lemma choose_cast_mod {n N i : ℕ} (hN : n * i.factorial ∣ N) (s : ℕ) :
    (s.choose i : ZMod n) = ((s % N).choose i : ZMod n) := by
  conv_lhs => rw [← Nat.mod_add_div s N]
  generalize s / N = k
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, choose_cast_add hN, ih]

lemma choose_cast_val {n N i : ℕ} [NeZero N] (hN : n * i.factorial ∣ N) (s : ℕ) :
    (s.choose i : ZMod n) = (((s : ZMod N).val).choose i : ZMod n) := by
  rw [ZMod.val_natCast, ← choose_cast_mod hN]

end Binom

/-! ### PST Theorem 7.4 for every modulus -/

section PST

variable {α : Type u} [DecidableEq α]

/-- On `ZMod N`, a letter-in-state count of a fixed letter `y` for the counter of `x` is a
`pcount`. -/
lemma vcountFrom_line_eq_pcount {N : ℕ} [NeZero N] (x y : α) (hxy : x ≠ y) (a : ℕ) (ha : a < N) :
    ∀ (w : List α) (s : ℕ), vcountFrom (fun b => if b = x then (1 : ZMod N) else 0) (a : ZMod N) y
      (s : ZMod N) w = pcount (fun b => decide (b = x)) N a y s w
  | [], _ => by simp [vcountFrom_nil, pcount]
  | b :: w, s => by
      rw [vcountFrom_cons, pcount]
      have hs : (s : ZMod N) + (if b = x then (1 : ZMod N) else 0) =
          ((if decide (b = x) then s + 1 else s : ℕ) : ZMod N) := by
        by_cases hb : b = x <;> simp [hb]
      rw [hs, vcountFrom_line_eq_pcount x y hxy a ha w]
      congr 1
      have : (s : ZMod N) = (a : ZMod N) ↔ s % N = a := by
        rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha]
      simp only [this]

lemma goodCount_vcount_line [Finite α] {N : ℕ} [NeZero N] (hN : 2 ≤ N) (x y : α) (hxy : x ≠ y)
    (q : ZMod N) :
    GoodCount (fun u : List α => vcount (fun b => if b = x then (1 : ZMod N) else 0) q y u) := by
  intro m r hr
  have heq : {u : List α | vcount (fun b => if b = x then (1 : ZMod N) else 0) q y u % m = r} =
      {u | pcount (fun b => decide (b = x)) N q.val y 0 u % m = r} := by
    ext u
    show _ % m = r ↔ _ % m = r
    have h := vcountFrom_line_eq_pcount (N := N) x y hxy q.val (ZMod.val_lt q) u 0
    rw [Nat.cast_zero, ZMod.natCast_zmod_val] at h
    rw [vcount_eq_vcountFrom, h]
  rw [heq]
  exact pcount_fixed_height_one _ hN (ZMod.val_lt q) y (by simpa using hxy.symm) hr

/-- **PST Theorem 7.4, as a good count**: `scount (xⁱ y xʲ)`, every modulus. -/
theorem goodCount_scount_pst [Finite α] {x y : α} (hxy : x ≠ y) (i j : ℕ) :
    GoodCount (scount (List.replicate i x ++ y :: List.replicate j x)) := by
  classical
  apply goodCount_of_det.{u, 0}
  intro n hn
  set N := 2 * n * i.factorial * j.factorial with hNdef
  have hN2 : 2 ≤ N := by
    have := Nat.factorial_pos i; have := Nat.factorial_pos j
    have : 1 ≤ n * i.factorial * j.factorial := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [hNdef]; nlinarith
  have : NeZero N := ⟨by omega⟩
  have hi : n * i.factorial ∣ N := ⟨2 * j.factorial, by rw [hNdef]; ring⟩
  have hj : n * j.factorial ∣ N := ⟨2 * i.factorial, by rw [hNdef]; ring⟩
  let δ : α → ZMod N := fun b => if b = x then 1 else 0
  refine ⟨Option (ZMod N), inferInstance,
    fun o => match o with
      | none => fun u => u.count x
      | some q => fun u => vcount δ q y u,
    n * N, by positivity, ?_, ?_⟩
  · intro o
    cases o with
    | none => exact goodCount_count x
    | some q => exact goodCount_vcount_line hN2 x y hxy q
  · intro u w huw
    have key : ∀ v : List α, (scount (List.replicate i x ++ y :: List.replicate j x) v : ZMod n) =
        ∑ q : ZMod N, ((q.val.choose i : ℕ) : ZMod n) * (((v.count x : ZMod N) - q).val.choose j : ℕ) *
          (vcount δ q y v : ZMod n) := by
      intro v
      have hsum : ∀ l : List α, (l.map δ).sum = (l.count x : ZMod N) := sum_map_indicator x
      rw [scount_cast_eq_sum_vcount x y x i j δ
        (fun q T => ((q.val.choose i : ℕ) : ZMod n) * ((T - q).val.choose j : ℕ)) v, hsum]
      intro t ht
      rw [hsum, hsum]
      have hc := count_drop_of_getElem? ht x
      rw [ite_eq_right (Ne.symm hxy), add_zero] at hc
      push_cast
      rw [choose_cast_val hi, choose_cast_val hj]
      congr 4
      rw [hc]; push_cast; ring
    have hX : (u.count x : ZMod N) = (w.count x : ZMod N) :=
      natCast_eq_of_mod_eq (dvd_mul_left N n) (huw none)
    rw [key u, key w, hX]
    apply Finset.sum_congr rfl
    intro q _
    rw [natCast_eq_of_mod_eq (dvd_mul_right n N) (huw (some q))]

/-- **PST Theorem 7.4** for every modulus `n`. -/
theorem height_one_scount_pst {α : Type*} [Finite α] [DecidableEq α] {x y : α} (hxy : x ≠ y)
    (i j : ℕ) {n k : ℕ} (hk : k < n) :
    HasHeightAtMost {u : List α | scount (List.replicate i x ++ y :: List.replicate j x) u % n = k} 1 :=
  goodCount_scount_pst hxy i j n k hk

lemma goodCount_scount_replicate [Finite α] (x : α) (i : ℕ) :
    GoodCount (scount (List.replicate i x)) := by
  classical
  apply goodCount_of_det.{u, 0}
  intro n hn
  set N := n * i.factorial
  have : NeZero N := ⟨by positivity⟩
  refine ⟨Unit, inferInstance, fun _ u => u.count x, N, by positivity, fun _ => goodCount_count x, ?_⟩
  intro u w huw
  rw [scount_replicate, scount_replicate, choose_cast_mod (N := N) dvd_rfl,
    choose_cast_mod (N := N) (n := n) dvd_rfl (w.count x), huw ()]

end PST

/-! ### Three distinct letters -/

section ABC

variable {α : Type u} [DecidableEq α]

lemma scount_pair_cons (a b z : α) (u : List α) :
    scount [a, b] (z :: u) = scount [a, b] u + if z = a then u.count b else 0 := by
  rw [scount_cons_cons, scount_singleton]

lemma scount_pair_swap {b c : α} (hbc : b ≠ c) :
    ∀ u : List α, scount [b, c] u + scount [c, b] u = u.count b * u.count c
  | [] => rfl
  | z :: u => by
      rw [scount_pair_cons, scount_pair_cons, count_cons_eq, count_cons_eq]
      have ih := scount_pair_swap hbc u
      by_cases hb : z = b
      · subst hb; simp [hbc]; nlinarith
      · by_cases hc : z = c
        · subst hc; simp [Ne.symm hbc]; nlinarith
        · simp [hb, hc, ih]

lemma count_map_merge {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) (ψ : α → α)
    (hψ : ∀ z, ψ z = if z = c then a else z) :
    ∀ u : List α, (u.map ψ).count b = u.count b
  | [] => rfl
  | z :: u => by
      rw [List.map_cons, count_cons_eq, count_cons_eq, count_map_merge hab hbc ψ hψ u, hψ]
      by_cases hz : z = c
      · subst hz
        simp [hab, Ne.symm hbc]
      · simp [hz]

lemma scount_pair_merge {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ψ : α → α)
    (hψ : ∀ z, ψ z = if z = c then a else z) :
    ∀ u : List α, scount [a, b] (u.map ψ) = scount [a, b] u + scount [c, b] u
  | [] => rfl
  | z :: u => by
      rw [List.map_cons, scount_pair_cons, scount_pair_cons, scount_pair_cons,
        scount_pair_merge hab hbc hac ψ hψ u, count_map_merge hab hbc ψ hψ u, hψ]
      by_cases hzc : z = c
      · subst hzc
        simp [Ne.symm hac]
        ring
      · by_cases hza : z = a
        · subst hza
          simp [hac]
          ring
        · simp [hzc, hza]

/-- **The merging identity.** -/
theorem scount_abc_identity {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) (u : List α) :
    scount [a, b, c] u + scount [a, a, b] (u.map fun z => if z = c then a else z)
      = u.count c * scount [a, b] u + scount [a, a, b] u + scount [c, c, b] u := by
  set ψ : α → α := fun z => if z = c then a else z with hψdef
  have hψ : ∀ z, ψ z = if z = c then a else z := fun z => rfl
  induction u with
  | nil => rfl
  | cons z u ih =>
      have hm := scount_pair_merge hab hbc hac ψ hψ u
      have hs := scount_pair_swap hbc u
      simp only [List.map_cons, scount_cons_cons, scount_singleton, count_cons_eq]
      by_cases hza : z = a
      · subst hza
        have hψa : ψ z = z := by rw [hψ, ite_eq_right hac]
        simp only [hψa, ite_true, ite_eq_right hac, add_zero]
        nlinarith
      · by_cases hzc : z = c
        · subst hzc
          have hψc : ψ z = a := by rw [hψ, ite_eq_left rfl]
          simp only [hψc, hza, ite_true, ite_false, add_zero]
          nlinarith
        · have hψz : ψ z = z := by rw [hψ, ite_eq_right hzc]
          simp only [hψz, hza, hzc, ite_false, add_zero]
          linarith

lemma goodCount_scount_abc [Finite α] {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    GoodCount (scount [a, b, c]) := by
  have hab' : GoodCount (scount [a, b]) := goodCount_scount_pst (i := 1) (j := 0) hab
  have haab : GoodCount (scount [a, a, b]) := goodCount_scount_pst (i := 2) (j := 0) hab
  have hccb : GoodCount (scount [c, c, b]) := goodCount_scount_pst (i := 2) (j := 0) (Ne.symm hbc)
  have hmerge : GoodCount (fun u : List α => scount [a, a, b] (u.map fun z => if z = c then a else z)) :=
    haab.comp_map _
  have hrhs : GoodCount (fun u : List α => u.count c * scount [a, b] u + scount [a, a, b] u +
      scount [c, c, b] u) :=
    (((goodCount_count c).mul hab').add haab).add hccb
  exact GoodCount.of_add_eq hmerge hrhs (scount_abc_identity hab hbc hac)

/-- **Every word of length at most three**, as a good count. -/
theorem goodCount_scount_le_three [Finite α] (w : List α) (hw : w.length ≤ 3) :
    GoodCount (scount w) := by
  match w, hw with
  | [], _ => exact (goodCount_const 1).congr fun u => (scount_nil_left u).symm
  | [a], _ => exact goodCount_scount_replicate a 1
  | [a, b], _ =>
      by_cases hab : a = b
      · subst hab; exact goodCount_scount_replicate a 2
      · exact goodCount_scount_pst (i := 1) (j := 0) hab
  | [a, b, c], _ =>
      by_cases hab : a = b
      · subst hab
        by_cases hac : a = c
        · subst hac; exact goodCount_scount_replicate a 3
        · exact goodCount_scount_pst (i := 2) (j := 0) hac
      · by_cases hac : a = c
        · subst hac; exact goodCount_scount_pst (i := 1) (j := 1) hab
        · by_cases hbc : b = c
          · subst hbc; exact goodCount_scount_pst (i := 0) (j := 2) (Ne.symm hab)
          · exact goodCount_scount_abc hab hbc hac
  | _ :: _ :: _ :: _ :: _, h => exact absurd h (by simp)

end ABC

/-- **Length at most three, every modulus.** -/
theorem height_one_scount_le_three {α : Type*} [Finite α] [DecidableEq α] (w : List α)
    (hw : w.length ≤ 3) {n k : ℕ} (hk : k < n) :
    HasHeightAtMost {u : List α | scount w u % n = k} 1 :=
  goodCount_scount_le_three w hw n k hk

/-- **`L(abc, k, 4)`**: the smallest case left open by PST (1992) and Bourne (2017). -/
theorem height_one_abc_mod_four {k : ℕ} (hk : k < 4) :
    HasHeightAtMost {u : List (Fin 3) | scount [0, 1, 2] u % 4 = k} 1 :=
  height_one_scount_le_three [0, 1, 2] (by simp) hk

end GeneralizedStarHeight
