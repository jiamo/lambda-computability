import Start.StarHeightNilpotent

/-!
# The shapes `xⁱ y zʲ` modulo a prime

`height_one_scount_xyz_mod_prime`: for a prime `p`, `i, j < p` and letters `x, y, z` (which may
coincide), every residue class of `scount (xⁱ y zʲ)` modulo `p` has generalized star height at
most one.  The modulus is `p` itself.

`height_one_aabb_mod_prime` is the first length-four instance not covered by PST Theorem 7.4:
`L(aabb, k, p)` for an odd prime `p`.

`height_one_two_letters_length_four_mod_prime`: for an odd prime `p`, every word `w` of length four
over two letters `x, y` (`xxxx`, the PST shapes, `xxyy`, `xyxy`, `xyyx` and their mirror images)
has `L(w, k, p)` of height at most one.  `xyxy` and `xyyx` come from the product identities
`scount [x,y]² = 4 xxyy + 2 xyxy + 2 xxy + 2 xyy + xy` (`scount_xy_sq`; `2` is a unit modulo `p`)
and `|u|_x · scount [y,y,x] = xyyx + yxyx + 2 yyxx + yyx` (`count_mul_scount_yyx`).

Proof.  For `i < p`, `C(s, i)` modulo `p` depends only on `s` modulo `p` (`choose_cast_val_prime`;
`i!` is a unit modulo `p`).  By the position formula `scount_rep_eq_sum`,

  `scount (xⁱ y zʲ) u ≡ Σ_{q ∈ (Z/p)²} C(q₁, i) · C(|u|_z − q₂ − [y = z], j) · vcount δ q y u`

modulo `p`, where `δ` is the translation automaton on `(Z/p)²` in which `x` moves by `(1,0)` and
`z` by `(0,1)` (both, if `x = z`).  Each `vcount δ q y` has height one modulo every `n`
(`vcount_height_one_prime`), and so does `|u|_z`.
-/

namespace GeneralizedStarHeight

universe u

section Prime

variable {α : Type u} [DecidableEq α]

lemma choose_cast_add_prime {p : ℕ} [hp : Fact p.Prime] {i : ℕ} (hi : i < p) (s : ℕ) :
    (((s + p).choose i : ℕ) : ZMod p) = (s.choose i : ZMod p) := by
  obtain ⟨d, hd⟩ := choose_add_sub_dvd p i s
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hdvd : (p : ℤ) ∣ (i.factorial : ℤ) * (((s + p).choose i : ℤ) - (s.choose i : ℤ)) := ⟨d, hd⟩
  rcases hpi.dvd_or_dvd hdvd with h | h
  · exfalso
    have := (Nat.Prime.dvd_factorial hp.out).mp (Int.natCast_dvd_natCast.mp h)
    omega
  · rw [← sub_eq_zero, ← Int.cast_natCast, ← Int.cast_natCast (R := ZMod p) (s.choose i),
      ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h

lemma choose_cast_val_prime {p : ℕ} [Fact p.Prime] {i : ℕ} (hi : i < p) (s : ℕ) :
    (s.choose i : ZMod p) = (((s : ZMod p).val).choose i : ZMod p) := by
  rw [ZMod.val_natCast]
  conv_lhs => rw [← Nat.mod_add_div s p]
  generalize s / p = k
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, choose_cast_add_prime hi, ih]

lemma sum_map_pair_indicator (p : ℕ) (x z : α) : ∀ l : List α,
    (l.map fun a => ((if a = x then 1 else 0 : ZMod p), (if a = z then 1 else 0 : ZMod p))).sum =
      ((l.count x : ZMod p), (l.count z : ZMod p))
  | [] => by simp; rfl
  | b :: l => by
      rw [List.map_cons, List.sum_cons, sum_map_pair_indicator p x z l, count_cons_eq, count_cons_eq]
      ext <;> simp [add_comm]

/-- Every residue class of `scount (xⁱ y zʲ)` modulo `p` has height at most one. -/
lemma scount_xyz_residues_height [Finite α] (p : ℕ) [Fact p.Prime] {i j : ℕ}
    (hi : i < p) (hj : j < p) (x y z : α) : ∀ k, k < p →
    HasHeightAtMost {u : List α | scount (List.replicate i x ++ y :: List.replicate j z) u % p = k}
      1 := by
  classical
  intro k _
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let δ : α → ZMod p × ZMod p := fun a => ((if a = x then 1 else 0), (if a = z then 1 else 0))
  let g : Option (ZMod p × ZMod p) → List α → ℕ := fun o => match o with
    | none => fun u => u.count z
    | some q => fun u => vcount δ q y u
  refine height_one_of_residues g hp ?_ _
    (fun r => ∃ u, (∀ o, g o u % p = r o) ∧
      scount (List.replicate i x ++ y :: List.replicate j z) u % p = k) ?_
  · intro o r hr
    cases o with
    | none => exact goodCount_count z p r hr
    | some q => exact goodCount_vcount_prime (p := p) δ q y p r hr
  · have key : ∀ v : List α, (scount (List.replicate i x ++ y :: List.replicate j z) v : ZMod p) =
        ∑ q : ZMod p × ZMod p, ((q.1.val.choose i : ℕ) : ZMod p) *
          (((v.count z : ZMod p) - q.2 - (if y = z then 1 else 0)).val.choose j : ℕ) *
          (vcount δ q y v : ZMod p) := by
      intro v
      have hsum := sum_map_pair_indicator p x z
      rw [scount_cast_eq_sum_vcount x y z i j δ
        (fun q T => ((q.1.val.choose i : ℕ) : ZMod p) *
          ((T.2 - q.2 - (if y = z then 1 else 0)).val.choose j : ℕ)) v, hsum]
      intro t ht
      rw [hsum, hsum]
      have hc := count_drop_of_getElem? ht z
      push_cast
      rw [choose_cast_val_prime hi, choose_cast_val_prime hj]
      congr 4
      rw [hc]
      push_cast
      split_ifs <;> ring
    intro w
    constructor
    · intro hw
      exact ⟨w, fun o => rfl, hw⟩
    · rintro ⟨u, hu, hk'⟩
      show _ % p = k
      have hZ : (u.count z : ZMod p) = (w.count z : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff' _ _ p).mpr (hu none)
      have hV : ∀ q, (vcount δ q y u : ZMod p) = (vcount δ q y w : ZMod p) := fun q =>
        (ZMod.natCast_eq_natCast_iff' _ _ p).mpr (hu (some q))
      have := key u
      rw [hZ] at this
      simp only [hV] at this
      rw [← key w, ZMod.natCast_eq_natCast_iff'] at this
      rw [← this, hk']

/-- **The shapes `xⁱ y zʲ` modulo `p`.** -/
theorem height_one_scount_xyz_mod_prime [Finite α] (p : ℕ) [Fact p.Prime] {i j : ℕ}
    (hi : i < p) (hj : j < p) (x y z : α) {k : ℕ} (hk : k < p) :
    HasHeightAtMost {u : List α | scount (List.replicate i x ++ y :: List.replicate j z) u % p = k}
      1 :=
  scount_xyz_residues_height p hi hj x y z k hk

end Prime

/-- **`L(aabb, k, p)`** for an odd prime `p`. -/
theorem height_one_aabb_mod_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {k : ℕ} (hk : k < p) :
    HasHeightAtMost {u : List (Fin 2) | scount [0, 0, 1, 1] u % p = k} 1 := by
  have h3 : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)
  exact height_one_scount_xyz_mod_prime (α := Fin 2) p (i := 2) (j := 1) h3 (by omega) 0 1 1 hk

/-! ### Every word of length four over two letters, modulo an odd prime -/

section TwoLetters

variable {α : Type u} [DecidableEq α]

/-- Every residue class of `g` modulo `p` has height at most one. -/
def GoodMod (p : ℕ) (g : List α → ℕ) : Prop :=
  ∀ r, r < p → HasHeightAtMost {u | g u % p = r} 1

omit [DecidableEq α] in
lemma GoodCount.goodMod {g : List α → ℕ} (h : GoodCount g) (p : ℕ) : GoodMod p g :=
  fun r hr => h p r hr

omit [DecidableEq α] in
/-- A count whose residue modulo `p` is fixed by the residues modulo `p` of finitely many counts
that are good modulo `p` is good modulo `p`. -/
lemma goodMod_of_det {p : ℕ} (hp : 0 < p) {g : List α → ℕ} {ι : Type} [Finite ι]
    (f : ι → List α → ℕ) (hf : ∀ i, GoodMod p (f i))
    (hdet : ∀ u w, (∀ i, (f i u : ZMod p) = f i w) → (g u : ZMod p) = g w) : GoodMod p g := by
  intro r hr
  refine height_one_of_residues f hp (fun i r hr => hf i r hr) _
    (fun z => ∃ u, (∀ i, f i u % p = z i) ∧ g u % p = r) ?_
  intro w
  constructor
  · intro hw
    exact ⟨w, fun i => rfl, hw⟩
  · rintro ⟨u, hu, hgu⟩
    have := hdet u w fun i => (ZMod.natCast_eq_natCast_iff' _ _ p).mpr (hu i)
    rw [ZMod.natCast_eq_natCast_iff'] at this
    show g w % p = r
    rw [← this, hgu]

lemma two_ne_zero_zmod {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  have := hp.out.two_le
  omega

lemma two_mul_choose_two_add : ∀ n : ℕ, 2 * n.choose 2 + n = n * n
  | 0 => rfl
  | n + 1 => by
      have ih := two_mul_choose_two_add n
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith

/-- `|u|_c · scount [d, c] u = scount [c, d, c] u + 2 scount [d, c, c] u + scount [d, c] u`. -/
lemma count_mul_scount_dc {c d : α} (hcd : c ≠ d) :
    ∀ u : List α, u.count c * scount [d, c] u =
      scount [c, d, c] u + 2 * scount [d, c, c] u + scount [d, c] u
  | [] => rfl
  | z :: u => by
      have ih := count_mul_scount_dc hcd u
      have hcc := scount_replicate c 2 u
      simp only [List.replicate] at hcc
      have hC : 2 * scount [c, c] u + u.count c = u.count c * u.count c := by
        rw [hcc]; exact two_mul_choose_two_add _
      simp only [scount_cons_cons, scount_singleton, count_cons_eq]
      by_cases hzc : z = c
      · subst hzc
        simp only [if_true, if_neg hcd]
        nlinarith
      · by_cases hzd : z = d
        · subst hzd
          simp only [if_true, if_neg hzc, add_zero]
          nlinarith
        · simp only [if_neg hzc, if_neg hzd, add_zero]
          exact ih

/-- `scount [x, y] u ^ 2 = 4 xxyy + 2 xyxy + 2 xxy + 2 xyy + xy`. -/
lemma scount_xy_sq {x y : α} (hxy : x ≠ y) :
    ∀ u : List α, scount [x, y] u * scount [x, y] u =
      4 * scount [x, x, y, y] u + 2 * scount [x, y, x, y] u + 2 * scount [x, x, y] u +
        2 * scount [x, y, y] u + scount [x, y] u
  | [] => rfl
  | z :: u => by
      have ih := scount_xy_sq hxy u
      have hl := count_mul_scount_dc hxy.symm u
      have hyy := scount_replicate y 2 u
      simp only [List.replicate] at hyy
      have hY : 2 * scount [y, y] u + u.count y = u.count y * u.count y := by
        rw [hyy]; exact two_mul_choose_two_add _
      simp only [scount_cons_cons, scount_singleton]
      by_cases hzx : z = x
      · subst hzx
        simp only [if_true]
        nlinarith
      · simp only [if_neg hzx, add_zero]
        exact ih

/-- `|u|_x · scount [y, y, x] u = xyyx + yxyx + 2 yyxx + yyx`. -/
lemma count_mul_scount_yyx {x y : α} (hxy : x ≠ y) :
    ∀ u : List α, u.count x * scount [y, y, x] u =
      scount [x, y, y, x] u + scount [y, x, y, x] u + 2 * scount [y, y, x, x] u +
        scount [y, y, x] u
  | [] => rfl
  | z :: u => by
      have ih := count_mul_scount_yyx hxy u
      have hl := count_mul_scount_dc hxy u
      simp only [scount_cons_cons, count_cons_eq]
      by_cases hzx : z = x
      · subst hzx
        simp only [if_true, if_neg hxy, add_zero]
        nlinarith
      · by_cases hzy : z = y
        · subst hzy
          simp only [if_true, if_neg hzx, add_zero]
          nlinarith
        · simp only [if_neg hzx, if_neg hzy, add_zero]
          exact ih

variable [Finite α]

lemma goodMod_xxyy (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (x y : α) :
    GoodMod p (scount [x, x, y, y]) := by
  have h3 : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)
  exact scount_xyz_residues_height p (i := 2) (j := 1) h3 (by omega) x y y

lemma goodMod_xyxy (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {x y : α} (hxy : x ≠ y) :
    GoodMod p (scount [x, y, x, y]) := by
  refine goodMod_of_det (Fact.out : p.Prime).pos
    ![scount [x, y], scount [x, x, y, y], scount [x, x, y], scount [x, y, y]] ?_ ?_
  · intro i
    fin_cases i
    · exact (goodCount_scount_pst (i := 1) (j := 0) hxy).goodMod p
    · exact goodMod_xxyy p hp x y
    · exact (goodCount_scount_pst (i := 2) (j := 0) hxy).goodMod p
    · exact (goodCount_scount_pst (i := 0) (j := 2) hxy.symm).goodMod p
  · intro u w h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2 h3
    have eu := congrArg (fun n : ℕ => (n : ZMod p)) (scount_xy_sq hxy u)
    have ew := congrArg (fun n : ℕ => (n : ZMod p)) (scount_xy_sq hxy w)
    push_cast at eu ew
    apply mul_left_cancel₀ (two_ne_zero_zmod hp)
    linear_combination ew - eu + ((scount [x, y] u : ZMod p) + (scount [x, y] w : ZMod p) - 1) * h0 -
      4 * h1 - 2 * h2 - 2 * h3

lemma goodMod_xyyx (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {x y : α} (hxy : x ≠ y) :
    GoodMod p (scount [x, y, y, x]) := by
  refine goodMod_of_det (Fact.out : p.Prime).pos
    ![fun u => u.count x, scount [y, y, x], scount [y, x, y, x], scount [y, y, x, x]] ?_ ?_
  · intro i
    fin_cases i
    · exact (goodCount_count x).goodMod p
    · exact (goodCount_scount_pst (i := 2) (j := 0) hxy.symm).goodMod p
    · exact goodMod_xyxy p hp hxy.symm
    · exact goodMod_xxyy p hp y x
  · intro u w h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2 h3
    have eu := congrArg (fun n : ℕ => (n : ZMod p)) (count_mul_scount_yyx hxy u)
    have ew := congrArg (fun n : ℕ => (n : ZMod p)) (count_mul_scount_yyx hxy w)
    push_cast at eu ew
    linear_combination ew - eu + (scount [y, y, x] u : ZMod p) * h0 +
      (w.count x : ZMod p) * h1 - h2 - 2 * h3 - h1

/-- **Every word of length four over two letters, modulo an odd prime.** -/
theorem height_one_two_letters_length_four_mod_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (x y : α) (w : List α) (hw : w.length = 4) (hxy : ∀ z ∈ w, z = x ∨ z = y) {k : ℕ}
    (hk : k < p) : HasHeightAtMost {u : List α | scount w u % p = k} 1 := by
  suffices h : GoodMod p (scount w) from h k hk
  match w, hw with
  | [a, b, c, d], _ =>
    by_cases hne : x = y
    · subst hne
      have ha : a = x := by simpa using hxy a (by simp)
      have hb : b = x := by simpa using hxy b (by simp)
      have hc : c = x := by simpa using hxy c (by simp)
      have hd : d = x := by simpa using hxy d (by simp)
      subst ha hb hc hd
      exact (goodCount_scount_replicate _ 4).goodMod p
    · rcases hxy a (by simp) with rfl | rfl <;> rcases hxy b (by simp) with rfl | rfl <;>
        rcases hxy c (by simp) with rfl | rfl <;> rcases hxy d (by simp) with rfl | rfl
      · exact (goodCount_scount_replicate _ 4).goodMod p
      · exact (goodCount_scount_pst (i := 3) (j := 0) hne).goodMod p
      · exact (goodCount_scount_pst (i := 2) (j := 1) hne).goodMod p
      · exact goodMod_xxyy p hp _ _
      · exact (goodCount_scount_pst (i := 1) (j := 2) hne).goodMod p
      · exact goodMod_xyxy p hp hne
      · exact goodMod_xyyx p hp hne
      · exact (goodCount_scount_pst (i := 0) (j := 3) (Ne.symm hne)).goodMod p
      · exact (goodCount_scount_pst (i := 0) (j := 3) hne).goodMod p
      · exact goodMod_xyyx p hp (Ne.symm hne)
      · exact goodMod_xyxy p hp (Ne.symm hne)
      · exact (goodCount_scount_pst (i := 1) (j := 2) (Ne.symm hne)).goodMod p
      · exact goodMod_xxyy p hp _ _
      · exact (goodCount_scount_pst (i := 2) (j := 1) (Ne.symm hne)).goodMod p
      · exact (goodCount_scount_pst (i := 3) (j := 0) (Ne.symm hne)).goodMod p
      · exact (goodCount_scount_replicate _ 4).goodMod p

end TwoLetters

end GeneralizedStarHeight
