import Start.StarHeightNilpotent

/-!
# The unitriangular group `UT(4, Z/n)`

`UT4 n` is the group of `4 × 4` upper unitriangular matrices over `ZMod n`, stored by its six
entries above the diagonal, with the matrix product as group law.

`height_one_UT4`: every language recognized by `UT4 n` has generalized star height at most one.

For a morphism `T` with letter matrices `t x = T x`, the entries of `T w` are `ZMod n`
combinations of the residues of `scount v w` for the words `v` of length at most three
(`UT4.prod_eq_entries`); for instance the `(1,4)` entry is

  `Σ_x |w|_x t(x)₁₄ + Σ_{x,y} scount [x,y] w (t(x)₁₂ t(y)₂₄ + t(x)₁₃ t(y)₃₄)
     + Σ_{x,y,z} scount [x,y,z] w t(x)₁₂ t(y)₂₃ t(z)₃₄`.

So the language is decided by residues modulo `n` of counts of length at most three, each of
height at most one by `height_one_scount_le_three`.
-/

namespace GeneralizedStarHeight

universe u

/-- The `4 × 4` upper unitriangular matrices over `ZMod n`, by their entries above the diagonal. -/
@[ext] structure UT4 (n : ℕ) where
  /-- Entry `(1,2)`. -/
  a12 : ZMod n
  /-- Entry `(1,3)`. -/
  a13 : ZMod n
  /-- Entry `(1,4)`. -/
  a14 : ZMod n
  /-- Entry `(2,3)`. -/
  a23 : ZMod n
  /-- Entry `(2,4)`. -/
  a24 : ZMod n
  /-- Entry `(3,4)`. -/
  a34 : ZMod n

namespace UT4

variable {n : ℕ}

instance : Mul (UT4 n) :=
  ⟨fun g h => ⟨g.a12 + h.a12, g.a13 + g.a12 * h.a23 + h.a13,
    g.a14 + g.a12 * h.a24 + g.a13 * h.a34 + h.a14, g.a23 + h.a23, g.a24 + g.a23 * h.a34 + h.a24,
    g.a34 + h.a34⟩⟩
instance : One (UT4 n) := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩
instance : Inv (UT4 n) :=
  ⟨fun g => ⟨-g.a12, -g.a13 + g.a12 * g.a23, -g.a14 + g.a12 * g.a24 + g.a13 * g.a34 -
    g.a12 * g.a23 * g.a34, -g.a23, -g.a24 + g.a23 * g.a34, -g.a34⟩⟩

lemma mul_def (g h : UT4 n) :
    g * h = ⟨g.a12 + h.a12, g.a13 + g.a12 * h.a23 + h.a13,
      g.a14 + g.a12 * h.a24 + g.a13 * h.a34 + h.a14, g.a23 + h.a23, g.a24 + g.a23 * h.a34 + h.a24,
      g.a34 + h.a34⟩ := rfl

lemma one_def : (1 : UT4 n) = ⟨0, 0, 0, 0, 0, 0⟩ := rfl

instance : Group (UT4 n) where
  mul_assoc f g h := by ext <;> simp only [mul_def] <;> ring
  one_mul f := by ext <;> simp [mul_def, one_def]
  mul_one f := by ext <;> simp [mul_def, one_def]
  inv_mul_cancel f := by
    ext <;> simp only [mul_def, one_def] <;> show _ = (0 : ZMod n) <;> simp only [Inv.inv] <;> ring

/-- `UT4 n ≃ (ZMod n)⁶`. -/
def equivProd : UT4 n ≃ ZMod n × ZMod n × ZMod n × ZMod n × ZMod n × ZMod n where
  toFun g := (g.a12, g.a13, g.a14, g.a23, g.a24, g.a34)
  invFun q := ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2⟩

instance [NeZero n] : Finite (UT4 n) := Finite.of_equiv _ equivProd.symm

/-! ### The entries of `T w` -/

section Entries

variable {α : Type u} [Fintype α] [DecidableEq α] (t : α → UT4 n)

/-- The cast of a scattered subword count. -/
abbrev sc (w v : List α) : ZMod n := (scount v w : ZMod n)

/-- The entries of a product of letter matrices, as combinations of subword counts. -/
def entries (w : List α) : UT4 n where
  a12 := ∑ x, sc w [x] * (t x).a12
  a13 := ∑ x, sc w [x] * (t x).a13 + ∑ x, ∑ y, sc w [x, y] * ((t x).a12 * (t y).a23)
  a14 := ∑ x, sc w [x] * (t x).a14 +
    ∑ x, ∑ y, sc w [x, y] * ((t x).a12 * (t y).a24 + (t x).a13 * (t y).a34) +
    ∑ x, ∑ y, ∑ z, sc w [x, y, z] * ((t x).a12 * (t y).a23 * (t z).a34)
  a23 := ∑ x, sc w [x] * (t x).a23
  a24 := ∑ x, sc w [x] * (t x).a24 + ∑ x, ∑ y, sc w [x, y] * ((t x).a23 * (t y).a34)
  a34 := ∑ x, sc w [x] * (t x).a34

omit [Fintype α] in
lemma sc_cons (a y : α) (v w : List α) :
    sc (a :: w) (y :: v) = sc w (y :: v) + if a = y then sc (n := n) w v else 0 := by
  simp only [sc, scount_cons_cons]
  push_cast
  split_ifs <;> simp

lemma sum1 (a : α) (A B f : α → ZMod n) :
    ∑ x, (A x + if a = x then B x else 0) * f x = ∑ x, A x * f x + B a * f a := by
  simp [add_mul, Finset.sum_add_distrib, ite_mul]

lemma sum2 (a : α) (A : α → α → ZMod n) (B : α → ZMod n) (f : α → α → ZMod n) :
    ∑ x, ∑ y, (A x y + if a = x then B y else 0) * f x y =
      ∑ x, ∑ y, A x y * f x y + ∑ y, B y * f a y := by
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  congr 1
  have : ∀ x, (∑ y, if a = x then B y * f x y else 0) = if a = x then ∑ y, B y * f x y else 0 := by
    intro x; split_ifs <;> simp
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

lemma sum3 (a : α) (A : α → α → α → ZMod n) (B : α → α → ZMod n) (f : α → α → α → ZMod n) :
    ∑ x, ∑ y, ∑ z, (A x y z + if a = x then B y z else 0) * f x y z =
      ∑ x, ∑ y, ∑ z, A x y z * f x y z + ∑ y, ∑ z, B y z * f a y z := by
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  congr 1
  have : ∀ x, (∑ y, ∑ z, if a = x then B y z * f x y z else 0) =
      if a = x then ∑ y, ∑ z, B y z * f x y z else 0 := by
    intro x; split_ifs <;> simp
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

lemma entries_nil : entries t [] = 1 := by
  ext <;> simp [entries, sc, one_def]

lemma entries_cons (a : α) (w : List α) : entries t (a :: w) = t a * entries t w := by
  have h1 : ∀ x, sc (a :: w) [x] = sc w [x] + if a = x then (1 : ZMod n) else 0 := by
    intro x
    rw [sc_cons]
    simp [sc]
  have h2 : ∀ x y, sc (n := n) (a :: w) [x, y] = sc w [x, y] + if a = x then sc w [y] else 0 :=
    fun x y => sc_cons a x [y] w
  have h3 : ∀ x y z, sc (n := n) (a :: w) [x, y, z] = sc w [x, y, z] + if a = x then sc w [y, z] else 0 :=
    fun x y z => sc_cons a x [y, z] w
  have h1' : ∀ (f : α → ZMod n), ∑ x, sc (a :: w) [x] * f x = ∑ x, sc w [x] * f x + f a := by
    intro f
    simp only [h1]
    rw [sum1 a (fun x => sc w [x]) (fun _ => 1) f, one_mul]
  have h2' : ∀ (f : α → α → ZMod n), ∑ x, ∑ y, sc (a :: w) [x, y] * f x y =
      ∑ x, ∑ y, sc w [x, y] * f x y + ∑ y, sc w [y] * f a y := by
    intro f
    simp only [h2]
    exact sum2 a (fun x y => sc w [x, y]) (fun y => sc w [y]) f
  have h3' : ∀ (f : α → α → α → ZMod n), ∑ x, ∑ y, ∑ z, sc (a :: w) [x, y, z] * f x y z =
      ∑ x, ∑ y, ∑ z, sc w [x, y, z] * f x y z + ∑ y, ∑ z, sc w [y, z] * f a y z := by
    intro f
    simp only [h3]
    exact sum3 a (fun x y z => sc w [x, y, z]) (fun y z => sc w [y, z]) f
  ext
  · simp only [entries, mul_def, h1']; ring
  · simp only [entries, mul_def, h1', h2', Finset.mul_sum]
    simp only [mul_comm, mul_assoc]; ring
  · simp only [entries, mul_def, h1', h2', h3', Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    simp only [mul_comm, mul_left_comm, mul_assoc]; ring
  · simp only [entries, mul_def, h1']; ring
  · simp only [entries, mul_def, h1', h2', Finset.mul_sum]
    simp only [mul_comm, mul_assoc]; ring
  · simp only [entries, mul_def, h1']; ring

lemma prod_eq_entries : ∀ w : List α, (w.map t).prod = entries t w
  | [] => (entries_nil t).symm
  | a :: w => by rw [List.map_cons, List.prod_cons, prod_eq_entries w, entries_cons]

end Entries

end UT4

/-- **`UT(4, Z/n)`**: every language recognized by the group of `4 × 4` unitriangular matrices over
`ZMod n` has generalized star height at most one. -/
theorem height_one_UT4 {Alphabet : Type*} [Finite Alphabet] (n : ℕ) [NeZero n]
    (T : FreeMonoid Alphabet →* UT4 n) (F : Set (UT4 n)) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  classical
  have := Fintype.ofFinite Alphabet
  let t : Alphabet → UT4 n := fun x => T (FreeMonoid.of x)
  have hT : ∀ w : List Alphabet, T (FreeMonoid.ofList w) = UT4.entries t w := by
    intro w
    rw [← UT4.prod_eq_entries]
    induction w with
    | nil => simp
    | cons a w ih =>
        rw [List.map_cons, List.prod_cons, ← ih, FreeMonoid.ofList_cons, map_mul]
  let g : (Alphabet ⊕ (Alphabet × Alphabet) ⊕ (Alphabet × Alphabet × Alphabet)) →
      List Alphabet → ℕ
    | .inl x => scount [x]
    | .inr (.inl (x, y)) => scount [x, y]
    | .inr (.inr (x, y, z)) => scount [x, y, z]
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  refine height_one_of_residues_univ g hn ?_ _
    (fun r => ∃ w, (∀ i, g i w % n = r i) ∧ T (FreeMonoid.ofList w) ∈ F) ?_
  · intro i r hr
    rcases i with x | ⟨x, y⟩ | ⟨x, y, z⟩
    · exact height_one_scount_le_three [x] (by simp) hr
    · exact height_one_scount_le_three [x, y] (by simp) hr
    · exact height_one_scount_le_three [x, y, z] (by simp) hr
  · intro w
    constructor
    · intro hw
      exact ⟨w, fun i => rfl, hw⟩
    · rintro ⟨v, hv, hvF⟩
      show T (FreeMonoid.ofList w) ∈ F
      have e1 : ∀ x, UT4.sc (n := n) v [x] = UT4.sc w [x] := fun x =>
        (ZMod.natCast_eq_natCast_iff' _ _ n).mpr (hv (.inl x))
      have e2 : ∀ x y, UT4.sc (n := n) v [x, y] = UT4.sc w [x, y] := fun x y =>
        (ZMod.natCast_eq_natCast_iff' _ _ n).mpr (hv (.inr (.inl (x, y))))
      have e3 : ∀ x y z, UT4.sc (n := n) v [x, y, z] = UT4.sc w [x, y, z] := fun x y z =>
        (ZMod.natCast_eq_natCast_iff' _ _ n).mpr (hv (.inr (.inr (x, y, z))))
      have : UT4.entries t v = UT4.entries t w := by
        simp only [UT4.entries, e1, e2, e3]
      rw [hT, ← this, ← hT]
      exact hvF

end GeneralizedStarHeight
